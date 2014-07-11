/*
    PhilZ Touch - touch_gui library
    Copyright (C) <2014>  <phytowardt@gmail.com>

    This file is part of PhilZ Touch Recovery

    PhilZ Touch is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    PhilZ Touch is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with PhilZ Touch.  If not, see <http://www.gnu.org/licenses/>.

*/

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/reboot.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include <sys/wait.h>
#include <sys/limits.h>
#include <dirent.h>
#include <sys/stat.h>

// statfs
#include <sys/vfs.h>

#include <signal.h>
#include <sys/wait.h>

#include "bootloader.h"
#include "common.h"
#include "cutils/properties.h"
#include "install.h"
#include "make_ext4fs.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"
#include "recovery_ui.h"

#include "extendedcommands.h"
#include "advanced_functions.h"
#include "recovery_settings.h"
#include "nandroid.h"
#include "mounts.h"
#include "flashutils/flashutils.h"
#include "edify/expr.h"
#include <libgen.h>
#include "mtdutils/mtdutils.h"
#include "bmlutils/bmlutils.h"
#include "cutils/android_reboot.h"
#include "mmcutils/mmcutils.h"
#include "voldclient/voldclient.h"

#include "adb_install.h"
#include "libcrecovery/common.h" // __popen/__pclose

// md5 display
#include <pthread.h>
#include "digest/md5.h"

#ifdef PHILZ_TOUCH_RECOVERY
#include "libtouch_gui/gui_settings.h"
#endif

/*****************************************/
/*   DO NOT REMOVE THIS CREDITS HEARDER  */
/* IF YOU MODIFY ANY PART OF THIS SOURCE */
/*  YOU MUST AGREE TO SHARE THE CHANGES  */
/*                                       */
/*       Start PhilZ Menu settings       */
/*      Code written by PhilZ@xda        */
/*      Part of PhilZ Touch Recovery     */
/*****************************************/

#ifdef BOARD_RECOVERY_CREATE_SE_CONTAINER
#include <selinux/selinux.h>
#include <selinux/label.h>
#include <selinux/android.h>

static int nochange;
static int verbose;
int bakupcon_to_file(const char *pathname, const char *filename)
{
    int ret = 0;
    struct stat sb;
    char* filecontext = NULL;
    FILE * f = NULL;
    if (lstat(pathname, &sb) < 0) {
        LOGW("bakupcon_to_file: %s not found\n", pathname);
        return -1;
    }

    if (lgetfilecon(pathname, &filecontext) < 0) {
        LOGW("bakupcon_to_file: can't get %s context\n", pathname);
        ret = 1;
    }
    else {
        if ((f = fopen(filename, "a+")) == NULL) {
            LOGE("bakupcon_to_file: can't create %s\n", filename);
            return -1;
        }
        //fprintf(f, "chcon -h %s '%s'\n", filecontext, pathname);
        fprintf(f, "%s\t%s\n", pathname, filecontext);
        fclose(f);
        freecon(filecontext);
    }

    //skip read symlink directory
    if (S_ISLNK(sb.st_mode)) return 0;

    DIR *dir = opendir(pathname);
    // not a directory, carry on
    if (dir == NULL) return 0;

    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        char *entryname;
        if (!strcmp(entry->d_name, ".."))
            continue;
        if (!strcmp(entry->d_name, "."))
            continue;
        if (asprintf(&entryname, "%s/%s", pathname, entry->d_name) == -1)
            continue;
        if ((is_data_media() && (strncmp(entryname, "/data/media/", 12) == 0)) ||
                strncmp(entryname, "/data/data/com.google.android.music/files/", 42) == 0 )
            continue;

        bakupcon_to_file(entryname, filename);
        free(entryname);
    }

    closedir(dir);
    return ret;
}

void create_external_selinux_container() {
#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Choose a backup path", NULL };
#else
    static const char* headers[] = { "选择一个备份路径", NULL };
#endif
    char path[PATH_MAX];
    char* file;

    sprintf(path, "/sdcard/%s", CWM_BACKUP_PATH);    
    file = choose_file_menu(path, NULL, headers);
    if (file == NULL)
        return;

#ifndef USE_CHINESE_FONT
    ui_print("backing up /data selinux context...\n");
#else
    ui_print("正在备份 /data selinux context...\n");
#endif
    sprintf(path, "%s/data.context", file);
    if (bakupcon_to_file("/data", path) < 0)
        LOGE("备份 selinux context 出错！\n");
    else
#ifndef USE_CHINESE_FONT
        ui_print("backup /data selinux context completed.\n");
#else
        ui_print("备份 /data selinux context 完毕。\n");
#endif
    free(file);
}
#endif

// ignore_android_secure = 1: this will force skipping android secure from backup/restore jobs
static int ignore_android_secure = 0;


// time using gettimeofday()
// to get time in usec, we call timenow_usec() which will link here if clock_gettime fails
static long long gettime_usec() {
    struct timeval now;
    long long useconds;
    gettimeofday(&now, NULL);
    useconds = (long long)(now.tv_sec) * 1000000LL;
    useconds += (long long)now.tv_usec;
    return useconds;
}

// use clock_gettime for elapsed time
// this is nsec precise + less prone to issues for elapsed time
// unsigned integers cannot be negative (overflow): set error return code to 0 (1.1.1970 00:00)
unsigned long long gettime_nsec() {
    struct timespec ts;
    static int err = 0;

    if (err) return 0;

    if (clock_gettime(CLOCK_MONOTONIC, &ts) < 0) {
        LOGI("clock_gettime(CLOCK_MONOTONIC) failed: %s\n", strerror(errno));
        ++err;
        return 0;
    }

    unsigned long long nseconds = (unsigned long long)(ts.tv_sec) * 1000000000ULL;
    nseconds += (unsigned long long)(ts.tv_nsec);
    return nseconds;
}

// returns the current time in usec: 
long long timenow_usec() {
    // try clock_gettime
    unsigned long long nseconds;
    nseconds = gettime_nsec();
    if (nseconds == 0) {
        // LOGI("dropping to gettimeofday()\n");
        return gettime_usec();
    }

    return (long long)(nseconds / 1000ULL);
}

// returns the current time in msec: 
long long timenow_msec() {
    // first try using clock_gettime
    unsigned long long nseconds;
    nseconds = gettime_nsec();
    if (nseconds == 0) {
        // LOGI("dropping to gettimeofday()\n");
        return (gettime_usec() / 1000LL);
    }

    return (long long)(nseconds / 1000000ULL);
}

// check if a specified time interval is passed between 2 calls to this function
// before calling, reset timer by passing 0
// when timer reached, it will return 1 AND will reset the timer
// next call will start again from that point without needing to pass 0 to reset
static long long interval_passed_t_timer = 0;
int is_time_interval_passed(long long msec_interval) {
    long long t = timenow_msec();
    if (msec_interval != 0 && t - interval_passed_t_timer < msec_interval)
        return 0;

    interval_passed_t_timer = t;
    return 1;
}

//start print tail from custom log file
void ui_print_custom_logtail(const char* filename, int nb_lines) {
    char * backup_log;
    char tmp[PATH_MAX];
    FILE * f;
    int line=0;
    sprintf(tmp, "tail -n %d %s > /tmp/custom_tail.log", nb_lines, filename);
    __system(tmp);
    f = fopen("/tmp/custom_tail.log", "rb");
    if (f != NULL) {
        while (line < nb_lines) {
            backup_log = fgets(tmp, PATH_MAX, f);
            if (backup_log == NULL) break;
            ui_print("%s", tmp);
            line++;
        }
        fclose(f);
    } else
        LOGE("Cannot open /tmp/custom_tail.log\n");
}

// basename and dirname implementation that is thread safe, no free and doesn't modify argument
// it is extracted from NDK and modified dirname_r to never modify passed argument
// t_BaseName and t_DirName are threadsafe, but need free by caller
// todo: add error check when returning NULL as it will segfault
int BaseName_r(const char* path, char*  buffer, size_t  bufflen) {
    const char *endp, *startp;
    int len, result;

    /* Empty or NULL string gets treated as "." */
    if (path == NULL || *path == '\0') {
        startp  = ".";
        len     = 1;
        goto Exit;
    }

    /* Strip trailing slashes */
    endp = path + strlen(path) - 1;
    while (endp > path && *endp == '/') {
        endp--;
    }

    /* All slashes becomes "/" */
    if (endp == path && *endp == '/') {
        startp = "/";
        len    = 1;
        goto Exit;
    }

    /* Find the start of the base */
    startp = endp;
    while (startp > path && *(startp - 1) != '/') {
        startp--;
    }

    len = endp - startp +1;

Exit:
    result = len;
    if (buffer == NULL) {
        return result;
    }
    if (len > (int)bufflen-1) {
        len    = (int)bufflen-1;
        result = -1;
        errno  = ERANGE;
    }

    if (len >= 0) {
        memcpy( buffer, startp, len );
        buffer[len] = 0;
    }
    return result;
}

// thread unsafe
char* BaseName(const char* path) {
    static char* bname = NULL;
    int ret;

    if (bname == NULL) {
        bname = (char *)malloc(PATH_MAX);
        if (bname == NULL)
            return(NULL);
    }
    ret = BaseName_r(path, bname, PATH_MAX);
    return (ret < 0) ? NULL : bname;
}

int DirName_r(const char*  path, char*  buffer, size_t  bufflen) {
    const char *endp, *startp;
    int result, len;

    /* Empty or NULL string gets treated as "." */
    if (path == NULL || *path == '\0') {
        startp = ".";
        len  = 1;
        goto Exit;
    }

    /* Strip trailing slashes */
    endp = path + strlen(path) - 1;
    while (endp > path && *endp == '/') {
        endp--;
    }

    /* Find the start of the dir */
    while (endp > path && *endp != '/') {
        endp--;
    }

    /* Either the dir is "/" or there are no slashes */
    if (endp == path) {
        startp = (*endp == '/') ? "/" : ".";
        len  = 1;
        goto Exit;
    }

    do {
        endp--;
    } while (endp > path && *endp == '/');

    startp = path;
    len = endp - startp +1;

Exit:
    result = len;
    if (len+1 > PATH_MAX) {
        errno = ENAMETOOLONG;
        return -1;
    }
    if (buffer == NULL)
        return result;

    if (len > (int)bufflen-1) {
        len    = (int)bufflen-1;
        result = -1;
        errno  = ERANGE;
    }

    if (len >= 0) {
        memcpy( buffer, startp, len );
        buffer[len] = 0;
    }
    return result;
}

// thread unsafe
char* DirName(const char* path) {
    static char*  bname = NULL;
    int ret;

    if (bname == NULL) {
        bname = (char *)malloc(PATH_MAX);
        if (bname == NULL)
            return(NULL);
    }

    ret = DirName_r(path, bname, PATH_MAX);
    return (ret < 0) ? NULL : bname;
}

// thread safe dirname (free by caller)
char* t_DirName(const char* path) {
    int ret;
    char* bname = (char *)malloc(PATH_MAX);
    if (bname == NULL) {
        LOGE("t_DirName: memory error\n");
        return NULL;
    }

    ret = DirName_r(path, bname, PATH_MAX);
    if (ret < 0) {
        LOGE("t_DirName: error\n");
        return NULL;
    }
    
    return bname;
}

// thread safe basename (free by caller)
char* t_BaseName(const char* path) {
    int ret;
    char* bname = (char *)malloc(PATH_MAX);
    if (bname == NULL) {
        LOGE("t_BaseName: memory error\n");
        return NULL;
    }

    ret = BaseName_r(path, bname, PATH_MAX);
    if (ret < 0) {
        LOGE("t_BaseName: error\n");
        return NULL;
    }
    
    return bname;
}

// case insensitive C-string compare (adapted from titanic-fanatic)
int strcmpi(const char *str1, const char *str2) {
    int i = 0;
    int ret = 0;

    while (ret == 0 && str1[i] && str2[i]) {
        ret = tolower(str1[i]) - tolower(str2[i]);
        ++i;
    }

    return ret;
}

// delete a file
void delete_a_file(const char* filename) {
    ensure_path_mounted(filename);
    remove(filename);
}

// search for 'file' in 'dir': only last occurrence is returned if many!
// depth <= 0: no depth limit
// follow != 0: follow links
char* find_file_in_path(const char* dir, const char* filename, int depth, int follow) {
    FILE *fp;
    char* ret = NULL;
    char buff[PATH_MAX];
    char cmd[PATH_MAX];
    char suffix[2] = "";
    char options[64] = "";
    if (dir[strlen(dir) - 1] != '/')
        strcpy(suffix, "/");
    if (depth > 0)
        sprintf(options, " -maxdepth %d", depth);
    if (follow)
        strcat(options, " -follow");

    sprintf(cmd, "find %s%s%s -name '%s'", dir, suffix, options, filename);
    fp = __popen(cmd, "r");
    if (fp == NULL){
        return ret;
    }

    while (fgets(buff, sizeof(buff), fp) != NULL) {
        size_t len = strlen(buff);
        if (buff[len - 1] == '\n')
            buff[len - 1] = '\0';
        ret = strdup(buff);
    }

    __pclose(fp);
    return ret;
}

// check if file or folder exists
int file_found(const char* filename) {
    struct stat s;
    if (strncmp(filename, "/sbin/", 6) != 0 && strncmp(filename, "/res/", 5) != 0 && strncmp(filename, "/tmp/", 5) != 0) {
        // do not try to mount ramdisk, else it will error "unknown volume for path..."
        ensure_path_mounted(filename);
    }
    if (0 == lstat(filename, &s))
        return 1;

    return 0;
}

// check directory exists
int directory_found(const char* dir) {
    struct stat s;
    ensure_path_mounted(dir);
    lstat(dir, &s);
    if (S_ISDIR(s.st_mode))
        return 1;

    return 0;
}

// check if path is in ramdisk since volume_for_path() will be NULL on these
int is_path_ramdisk(const char* path) {
    const char *ramdisk_dirs[] = { "/sbin/", "/res/", "/tmp/", NULL };
    int i = 0;
    while (ramdisk_dirs[i] != NULL) {
        if (strncmp(path, ramdisk_dirs[i], strlen(ramdisk_dirs[i])) == 0)
            return 1;
        i++;
    }
    return 0;
}

// copy file (ramdisk check compatible)
int copy_a_file(const char* file_in, const char* file_out) {
    if (strcmp(file_in, file_out) == 0) {
        LOGI("source and destination files are same, skipping copy.\n");
        return 0;
    }

    if (!is_path_ramdisk(file_in) && ensure_path_mounted(file_in) != 0) {
        LOGE("copy: cannot mount volume %s\n", file_in);
        return -1;
    }

    if (!is_path_ramdisk(file_out) && ensure_path_mounted(file_out) != 0) {
        LOGE("copy: cannot mount volume %s\n", file_out);
        return -1;
    }

    // this will chmod directory to 777
    char tmp[PATH_MAX];
    sprintf(tmp, "%s", DirName(file_out));
    ensure_directory(tmp);
    FILE *fp = fopen(file_in, "rb");
    if (fp == NULL) {
        LOGE("copy: source file not found (%s)\n", file_in);
        return -1;
    }
    FILE *fp_out = fopen(file_out, "wb");
    if (fp_out == NULL) {
        LOGE("copy: failed to create destination file %s\n", file_out);
        fclose(fp);
        return -1;
    }

    // start copy
    size_t size;
    while ((size = fread(tmp, 1, sizeof(tmp), fp))) {
        fwrite(tmp, 1, size, fp_out);
    }
    fclose(fp);
    fclose(fp_out);
    return 0;
}

// append a string to text file, create the directories and file if it doesn't exist
int append_string_to_file(const char* filename, const char* string) {
    char tmp[PATH_MAX];
    int ret = -1;

    ensure_path_mounted(filename);
    mkdir(DirName(filename), S_IRWXU | S_IRWXG | S_IRWXO);

    FILE *file = fopen(filename, "a");
    if (file != NULL) {
        ret = fprintf(file, "%s", string);
        fclose(file);
    } else
        LOGE("Cannot append to %s\n", filename);

    return ret;
}

// get file size (by Dees_Troy - TWRP)
// needs ensure_path_mounted(Path) by caller
unsigned long Get_File_Size(const char* Path) {
    struct stat st;
    if (stat(Path, &st) != 0)
        return 0;
    return st.st_size;
}

// get partition size info (adapted from Dees_Troy - TWRP)
unsigned long long Total_Size = 0; // Overall size of the partition
unsigned long long Used_Size = 0; // Overall used space
unsigned long long Free_Size = 0; // Overall free space

// this needs the volume to be mounted by caller
// do not ensure path mounted here to avoid time loss when refreshing backup size during nandroid operations
int Get_Size_Via_statfs(const char* Path) {
    struct statfs st;
    Volume* volume;
    if (is_data_media_volume_path(Path))
        volume = volume_for_path("/data");
    else
        volume = volume_for_path(Path);
    if (NULL == volume) {
        LOGE("No volume found to get size from '%s'\n", Path);
        return -1;
    }

    if (volume->mount_point == NULL || statfs(volume->mount_point, &st) != 0) {
        LOGE("Unable to statfs for size '%s'\n", Path);
        return -1;
    }

    Total_Size = (unsigned long long)(st.f_blocks) * (unsigned long long)(st.f_bsize);
    Free_Size = (unsigned long long)(st.f_bfree) * (unsigned long long)(st.f_bsize);
    Used_Size = Total_Size - Free_Size;
    // LOGI("%s: tot=%llu, use=%llu, free=%llu\n", volume->mount_point, Total_Size, Used_Size, Free_Size); // debug
    return 0;
}

// try to resolve link from blk_device to real /dev/block/mmcblk or /dev/block/mtdblock
// free by caller
char* readlink_device_blk(const char* Path)
{
    char* mmcblk_from_link = NULL;
    Volume* vol;
    if (is_data_media_volume_path(Path))
        vol = volume_for_path("/data");
    else
        vol = volume_for_path(Path);
    if (vol == NULL)
        return NULL;

    char buf[1024];
    ssize_t len = readlink(vol->blk_device, buf, sizeof(buf)-1);
    if (len == -1) {
        LOGI("failed to get device mmcblk link '%s'\n", vol->blk_device);
        return NULL;
    }

    buf[len] = '\0';
    mmcblk_from_link = strdup(buf);
    LOGI("found device mmcblk link: '%s' -> '%s'\n", vol->blk_device, mmcblk_from_link);
    return mmcblk_from_link;
}

// alternate method for statfs (emmc, mtd, mtk...)
int Find_Partition_Size(const char* Path) {
    char line[512];
    char tmpdevice[1024];
    FILE* fp;
    Volume* volume;

    if (is_data_media_volume_path(Path))
        volume = volume_for_path("/data");
    else
        volume = volume_for_path(Path);

    if (volume == NULL) {
        LOGE("Failed to find partition size '%s'\n", Path);
        LOGE("  > invalid volume %s\n", Path);
        return -1;
    }

    // In this case, we'll first get the partitions we care about (with labels)
/*
    --> Start by checking if it is an MTK based device (cat /proc/dumchar_info)
    Part_Name    Size               StartAddr         Type   MapTo
    preloader    0x0000000000040000 0x0000000000000000   2   /dev/misc-sd
    dsp_bl       0x00000000005c0000 0x0000000000040000   2   /dev/misc-sd
    mbr          0x0000000000004000 0x0000000000000000   2   /dev/block/mmcblk0
    ebr1         0x0000000000004000 0x0000000000004000   2   /dev/block/mmcblk0p1
    pmt          0x0000000000400000 0x0000000000008000   2   /dev/block/mmcblk0
    nvram        0x0000000000500000 0x0000000000408000   2   /dev/block/mmcblk0
    seccfg       0x0000000000020000 0x0000000000908000   2   /dev/block/mmcblk0
    uboot        0x0000000000060000 0x0000000000928000   2   /dev/block/mmcblk0
    bootimg      0x0000000000600000 0x0000000000988000   2   /dev/block/mmcblk0
    recovery     0x0000000000600000 0x0000000000f88000   2   /dev/block/mmcblk0
    sec_ro       0x0000000000600000 0x0000000001588000   2   /dev/block/mmcblk0p2
    misc         0x0000000000060000 0x0000000001b88000   2   /dev/block/mmcblk0
    logo         0x0000000000300000 0x0000000001be8000   2   /dev/block/mmcblk0
    expdb        0x0000000000200000 0x0000000001ee8000   2   /dev/block/mmcblk0
    android      0x0000000020100000 0x00000000020e8000   2   /dev/block/mmcblk0p3
    cache        0x0000000020100000 0x00000000221e8000   2   /dev/block/mmcblk0p4
    usrdata      0x0000000020100000 0x00000000422e8000   2   /dev/block/mmcblk0p5
    fat          0x00000000854f8000 0x00000000623e8000   2   /dev/block/mmcblk0p6
    bmtpool      0x0000000001500000 0x00000000ff9f00a8   2   /dev/block/mmcblk0
    Part_Name:Partition name you should open;
    Size:size of partition
    StartAddr:Start Address of partition;
    Type:Type of partition(MTD=1,EMMC=2)
    MapTo:actual device you operate
*/
    fp = fopen("/proc/dumchar_info", "rt");
    if (fp != NULL) {
        while (fgets(line, sizeof(line), fp) != NULL) {
            char label[32], device[32];
            unsigned long size = 0;

            sscanf(line, "%s %lx %*x %*u %s", label, &size, device);

            // Skip header, annotation  and blank lines
            if ((strncmp(device, "/dev/", 5) != 0) || (strlen(line) < 8))
                continue;

            sprintf(tmpdevice, "/dev/");
            strcat(tmpdevice, label);
            if (volume->blk_device != NULL && strcmp(tmpdevice, volume->blk_device) == 0) {
                Total_Size = size;
                fclose(fp);
                return 0;
            }
            if (volume->blk_device2 != NULL && strcmp(tmpdevice, volume->blk_device2) == 0) {
                Total_Size = size;
                fclose(fp);
                return 0;
            }
        }

        fclose(fp);
    }

/*  It is not an MTK device entry:
    --> Try mtd / emmc devices (cat /proc/partitions):
    major minor #blocks name
    179  0 15388672 mmcblk0
    179  1    65536 mmcblk0p1
    179  2      512 mmcblk0p2
    179  3      512 mmcblk0p3
    179  4     2048 mmcblk0p4
    179  5      512 mmcblk0p5
    179  6    22528 mmcblk0p6
    179  7    22528 mmcblk0p7
*/
    int ret = -1;
    fp = fopen("/proc/partitions", "rt");
    if (fp != NULL) {
        // try to read blk_device link target for devices not using /dev/block/xxx in recovery.fstab
        char* mmcblk_from_link = readlink_device_blk(Path);
        while (fgets(line, sizeof(line), fp) != NULL) {
            unsigned long major, minor, blocks;
            char device[512];

            if (strlen(line) < 7 || line[0] == 'm')
                continue;

            sscanf(line + 1, "%lu %lu %lu %s", &major, &minor, &blocks, device);
            sprintf(tmpdevice, "/dev/block/");
            strcat(tmpdevice, device);

            if (volume->blk_device != NULL && strcmp(tmpdevice, volume->blk_device) == 0) {
                Total_Size = blocks * 1024ULL;
                //LOGI("%s(%s)=%llu\n", Path, volume->blk_device, Total_Size); // debug
                ret = 0;
            } else if (volume->blk_device2 != NULL && strcmp(tmpdevice, volume->blk_device2) == 0) {
                Total_Size = blocks * 1024ULL;
                ret = 0;
            } else if (mmcblk_from_link != NULL && strcmp(tmpdevice, mmcblk_from_link) == 0) {
                // get size from blk_device symlink to /dev/block/xxx
                free(mmcblk_from_link);
                Total_Size = blocks * 1024ULL;
                ret = 0;
            }
        }

        fclose(fp);
    }

    if (ret != 0)
        LOGE("Failed to find partition size '%s'\n", Path);
    return ret;
}
//----- End partition size

// get folder size (by Dees_Troy - TWRP)
// size of /data will include /data/media, so needs to be calculated by caller
// always ensure_path_mounted(Path) before calling it
// do not ensure_path_mounted(Path) here to avoid calling it on each opendir(subfolder)
unsigned long long Get_Folder_Size(const char* Path) {
    DIR* d;
    struct dirent* de;
    struct stat st;
    char path2[PATH_MAX]; char filename[PATH_MAX];
    unsigned long long dusize = 0;
    unsigned long long dutemp = 0;

    // Make a copy of path in case the data in the pointer gets overwritten later
    strcpy(path2, Path);

    d = opendir(path2);
    if (d == NULL) {
        LOGE("error opening '%s'\n", path2);
        LOGE("error: %s\n", strerror(errno));
        return 0;
    }

    while ((de = readdir(d)) != NULL) {
        if (de->d_type == DT_DIR && strcmp(de->d_name, ".") != 0 && strcmp(de->d_name, "..") != 0) {
            strcpy(filename, path2);
            strcat(filename, "/");
            strcat(filename, de->d_name);
            dutemp = Get_Folder_Size(filename);
            dusize += dutemp;
            dutemp = 0;
        } else if (de->d_type == DT_REG) {
            strcpy(filename, path2);
            strcat(filename, "/");
            strcat(filename, de->d_name);
            stat(filename, &st);
            dusize += (unsigned long long)(st.st_size);
        }
    }
    closedir(d);
    return dusize;
}

/*
Read a file to buffer: buffer must be freed by caller if return value is not NULL.
len is the total bytes we read if successful
That way we can use fwrite(str, len, fd) to copy the file
To use it as string argument, we must add terminating null by caller: buffer[len] = '\0';
Exp:
    unsigned long len = 0;
    char* buffer = read_file_to_buffer(md5file, &len);
    if (buffer != NULL) {
        buffer[len] = '\0';
        printf("buffer=%s\n", buffer);
        free(buffer);
    }
*/
char* read_file_to_buffer(const char* filepath, unsigned long *len) {
    if (!file_found(filepath)) {
        LOGE("read_file_to_buffer: '%s' not found\n", filepath);
        return NULL;
    }

    // obtain file size:
    unsigned long size = Get_File_Size(filepath);

    // allocate memory to contain the whole file:
    char* buffer = (char*)malloc(size + 1);
    if (buffer == NULL) {
        LOGE("read_file_to_buffer: memory error\n");
        return NULL;
    }

    FILE *file = fopen(filepath, "rb");
    if (file == NULL) {
        LOGE("read_file_to_buffer: can't open '%s'\n", filepath);
        free(buffer);
        return NULL;
    }

    // copy the file into the buffer:
    *len = fread(buffer, 1, size, file);
    if (size != *len) {
        LOGE("read_file_to_buffer: read error\n");
        free(buffer);
        fclose(file);
        return NULL;
    }

    fclose(file);
    return buffer;
}

/**********************************/
/*       Start md5sum display     */
/*    Original source by PhilZ    */
/*    MD5 code from twrpDigest    */
/*              by                */
/*    bigbiff/Dees_Troy TeamWin   */
/**********************************/

// calculate md5sum of filepath
// return 0 on success, 1 if cancelled by user, -1 on failure to open source file
// fills md5sum char array with the resulting md5sum
// functions calling this should first set the progress bar:
//    ui_reset_progress();
//    ui_show_progress(1, 0);
// and after it is done, reset the progress bar
//    ui_reset_progress();
static int cancel_md5digest = 0;
static int computeMD5(const char* filepath, char *md5sum) {
    struct MD5Context md5c;
    unsigned char md5sum_array[MD5LENGTH];
    unsigned char buf[1024];
    char hex[3];
    unsigned long size_total;
    unsigned long size_progress;
    unsigned len;
    int i;

    if (!file_found(filepath)) {
        LOGE("computeMD5: '%s' not found\n", filepath);
        return -1;
    }

    FILE *file = fopen(filepath, "rb");
    if (file == NULL) {
        LOGE("computeMD5: can't open %s\n", filepath);
        return -1;
    }

    size_total = Get_File_Size(filepath);
    size_progress = 0;
    cancel_md5digest = 0;
    MD5Init(&md5c);
    while (!cancel_md5digest && (len = fread(buf, 1, sizeof(buf), file)) > 0) {
        MD5Update(&md5c, buf, len);
        size_progress += len;
        if (size_total != 0)
            ui_set_progress((float)size_progress / (float)size_total);
    }

    if (!cancel_md5digest) {
        MD5Final(md5sum_array ,&md5c);
        strcpy(md5sum, "");
        for (i = 0; i < 16; ++i) {
            snprintf(hex, 3 ,"%02x", md5sum_array[i]);
            strcat(md5sum, hex);
        }
    }

    fclose(file);
    return cancel_md5digest;
}

// write calculated md5 to file or to log/screen if md5file is NULL
// returns negative value on failure or total number of bytes written on success (or 0 if only display md5)
// if cancelled by user in thread mode, it returns 1
int write_md5digest(const char* filepath, const char* md5file, int append) {
    int ret;
    char md5sum[PATH_MAX];

    ret = computeMD5(filepath, md5sum);
    if (ret != 0)
        return ret;

    if (md5file == NULL) {
        ui_print("%s\n", md5sum);
    } else {
        char* b = t_BaseName(filepath);
        strcat(md5sum, "  ");
        strcat(md5sum, b);
        strcat(md5sum, "\n");
        free(b);
        if (append)
            ret = append_string_to_file(md5file, md5sum);
        else
            ret = write_string_to_file(md5file, md5sum);
    }

    return ret;
}

// verify md5sum of filepath if it matches content from md5file
// if md5file == NULL, we try filepath.md5
int verify_md5digest(const char* filepath, const char* md5file) {
    char md5file2[PATH_MAX];
    int ret = -1;

    if (!file_found(filepath)) {
        LOGE("verify_md5digest: '%s' not found\n", filepath);
        return ret;
    }

    if (md5file != NULL) {
        sprintf(md5file2, "%s", md5file);
    } else {
        sprintf(md5file2, "%s.md5", filepath);
    }

    // read md5 sum from md5file2
    // read_file_to_buffer() will call file_found() function
    unsigned long len = 0;
    char* md5read = read_file_to_buffer(md5file2, &len);
    if (md5read == NULL)
        return ret;
    md5read[len] = '\0';

    // calculate md5sum of filepath and check if it matches what we read from md5file2
    // computeMD5() != 0 if cancelled by user in multi-threading mode (1) or if file not found (-1)
    // file.md5 is formatted like (new line at end):
    // 264c7c1e6f682cb99a07c283117f7f07  test_code.c\n
    char md5sum[PATH_MAX];
    if (0 == (ret = computeMD5(filepath, md5sum))) {
        char* b = t_BaseName(filepath);
        strcat(md5sum, "  ");
        strcat(md5sum, b);
        strcat(md5sum, "\n");
        free(b);
        if (strcmp(md5read, md5sum) != 0) {
            LOGE("MD5 calc: %s\n", md5sum);
            LOGE("Expected: %s\n", md5read);
            ret = -1;
        }
    }

    free(md5read);
    return ret;
}

// thread function called when installing zip files from menu
pthread_t tmd5_display;
pthread_t tmd5_verify;
static void *md5_display_thread(void *arg) {
    char filepath[PATH_MAX];
    ui_reset_progress();
    ui_show_progress(1, 0);
    sprintf(filepath, "%s", (char*)arg);
    write_md5digest(filepath, NULL, 0);
    ui_reset_progress();
    return NULL;
}

static void *md5_verify_thread(void *arg) {
    int ret;
    char filepath[PATH_MAX];

    sprintf(filepath, "%s", (char*)arg);
    ui_reset_progress();
    ui_show_progress(1, 0);
    ret = verify_md5digest(filepath, NULL);
    ui_reset_progress();

    // ret == 1 if cancelled by user: do not log
    if (ret < 0) {
#ifdef PHILZ_TOUCH_RECOVERY
        ui_print_preset_colors(1, "red");
#endif
#ifndef USE_CHINESE_FONT
        ui_print("MD5 check: error\n");
#else
        ui_print("MD5检查：错误\n");
#endif
    } else if (ret == 0) {
#ifdef PHILZ_TOUCH_RECOVERY
        ui_print_preset_colors(1, "green");
#endif
#ifndef USE_CHINESE_FONT
        ui_print("MD5 check: success\n");
#else
        ui_print("MD5检查：成功\n");
#endif
    }

    return NULL;
}

void start_md5_display_thread(char* filepath) {
    // ensure_path_mounted() is not thread safe, we must disable it when starting a thread for md5 checks
    // to install the zip file, we must re-enable the ensure_path_mounted() function: it is done when stopping the thread
    // at this point, filepath should be mounted by caller
    // we ensure primary storage is also mounted as it is needed by confirm_install() function
    ensure_path_mounted(get_primary_storage_path());
    set_ensure_mount_always_true(1);

    // show the message in color (cyan by default)
    // we will reset color before exiting the thread
#ifdef PHILZ_TOUCH_RECOVERY
    ui_print_preset_colors(1, NULL);
#endif
#ifndef USE_CHINESE_FONT
    ui_print("Calculating md5sum...\n");
#else
    ui_print("正在计算md5码...\n");
#endif

    pthread_create(&tmd5_display, NULL, &md5_display_thread, filepath);
}

void stop_md5_display_thread() {
    cancel_md5digest = 1;
    if (pthread_kill(tmd5_display, 0) != ESRCH)
#ifndef USE_CHINESE_FONT
        ui_print("Cancelling md5sum...\n");
#else
        ui_print("正在取消计算md5码...\n");
#endif

    pthread_join(tmd5_display, NULL);
    set_ensure_mount_always_true(0);
#ifdef PHILZ_TOUCH_RECOVERY
    ui_print_preset_colors(0, NULL);
#endif
}

void start_md5_verify_thread(char* filepath) {
    // ensure_path_mounted() is not thread safe, we must disable it when starting a thread for md5 checks
    // to install the zip file, we must re-enable the ensure_path_mounted() function: it is done when stopping the thread
    // at this point, filepath should be mounted by caller
    // we ensure primary storage is also mounted as it is needed by confirm_install() function
    ensure_path_mounted(get_primary_storage_path());
    set_ensure_mount_always_true(1);

    // show the message in color (cyan by default)
    // we will reset color before exiting the thread
#ifdef PHILZ_TOUCH_RECOVERY
    ui_print_preset_colors(1, NULL);
#endif
#ifndef USE_CHINESE_FONT
    ui_print("Verifying md5sum...\n");
#else
    ui_print("正在验证md5码...\n");
#endif

    pthread_create(&tmd5_verify, NULL, &md5_verify_thread, filepath);
}

void stop_md5_verify_thread() {
    cancel_md5digest = 1;
    if (pthread_kill(tmd5_verify, 0) != ESRCH)
#ifndef USE_CHINESE_FONT
        ui_print("Cancelling md5 check...\n");
#else
        ui_print("正在取消md5验证...\n");
#endif

    pthread_join(tmd5_verify, NULL);
    set_ensure_mount_always_true(0);
#ifdef PHILZ_TOUCH_RECOVERY
    ui_print_preset_colors(0, NULL);
#endif
}
// ------- End md5sum display


/**********************************/
/*       Start file parser        */
/*    Original source by PhilZ    */
/**********************************/
// todo: parse settings file in one pass and make pairs of key:value
// get value of key from a given config file
// always call with value[PROPERTY_VALUE_MAX] to prevent any buffer overflow caused by strcpy(value, strstr(line, "=") + 1);
int read_config_file(const char* config_file, const char *key, char *value, const char *value_def) {
    int ret = 0;
    char line[PROPERTY_VALUE_MAX];
    ensure_path_mounted(config_file);
    FILE *fp = fopen(config_file, "rb");
    if (fp != NULL) {
        while (fgets(line, sizeof(line), fp) != NULL) {
            if (strstr(line, key) != NULL && strncmp(line, key, strlen(key)) == 0 && line[strlen(key)] == '=') {
                // we found the key: try to get its value, remove trailing \n and ensure it is not an empty value
                strcpy(value, strstr(line, "=") + 1);
                if (value[strlen(value)-1] == '\n')
                    value[strlen(value)-1] = '\0';
                if (value[0] != '\0') {
                    fclose(fp);
                    LOGI("%s=%s\n", key, value);
                    return ret;
                }
            }
        }
        // either we didn't find the key or it has an empty value
        ret = 1;
        fclose(fp);
    } else {
        LOGI("Cannot open %s\n", config_file);
        ret = -1;
    }

    // set value to default
    strcpy(value, value_def);
    LOGI("%s set to default (%s)\n", key, value_def);
    return ret;
}

// set value of key in config file
int write_config_file(const char* config_file, const char* key, const char* value) {
    if (ensure_path_mounted(config_file) != 0) {
        LOGE("Cannot mount path for settings file: %s\n", config_file);
        return -1;
    }

    char config_file_tmp[PATH_MAX];
    char tmp[PATH_MAX];
    sprintf(config_file_tmp, "%s.tmp", config_file);
    sprintf(tmp, "%s", DirName(config_file_tmp));
    ensure_directory(tmp);
    delete_a_file(config_file_tmp);

    FILE *f_tmp = fopen(config_file_tmp, "wb");
    if (f_tmp == NULL) {
        LOGE("failed to create temporary settings file!\n");
        return -1;
    }

    FILE *fp = fopen(config_file, "rb");
    if (fp == NULL) {
        // we need to create a new settings file: write an info header
#ifndef USE_CHINESE_FONT
        const char* header[] = {
            "#PhilZ Touch Settings File\n",
            "#Edit only in appropriate UNIX format (Notepad+++...)\n",
            "#Entries are in the form of:\n",
            "#key=value\n",
            "#Do not add spaces in between!\n",
            "\n",
            NULL
        };
#else
        const char* header[] = {
            "#PhilZ Touch 设置文件\n",
            "#只能在恰当的UNIX格式下编辑 (Notepad+++...)\n",
            "#条目的格式：\n",
            "#key=value\n",
            "#不要在中间添加空格！\n",
            "\n",
            NULL
        };
#endif

        int i;
        for(i = 0; header[i] != NULL; i++) {
            fwrite(header[i], 1, strlen(header[i]), f_tmp);
        }
    } else {
        // parse existing config file and write new temporary file.
        char line[PROPERTY_VALUE_MAX];
        while (fgets(line, sizeof(line), fp) != NULL) {
            // ignore any existing line with key we want to set
            if (strstr(line, key) != NULL && strncmp(line, key, strlen(key)) == 0 && line[strlen(key)] == '=')
                continue;
            // ensure trailing \n, in case some one got a bad editor...
            if (line[strlen(line) - 1] != '\n')
                strcat(line, "\n");
            fwrite(line, 1, strlen(line), f_tmp);
        }
        fclose(fp);
    }

    // write new key=value entry
    char new_entry[PROPERTY_VALUE_MAX];
    sprintf(new_entry, "%s=%s\n", key, value);
    fwrite(new_entry, 1, strlen(new_entry), f_tmp);
    fclose(f_tmp);

    if (rename(config_file_tmp, config_file) != 0) {
        LOGE("failed to rename temporary settings file!\n");
        return -1;
    }

    // if we are editing recovery settings file, create a second copy on primary storage
    if (strcmp(PHILZ_SETTINGS_FILE, config_file) == 0) {
        sprintf(tmp, "%s/%s", get_primary_storage_path(), PHILZ_SETTINGS_FILE2);
        if (copy_a_file(config_file, tmp) != 0)
            LOGE("failed duplicating settings file to primary storage!\n");
    }

    LOGI("%s was set to %s\n", key, value);
    return 0;
}
//----- end file settings parser

// start wipe data and system options and menu
void wipe_data_menu() {
#ifndef USE_CHINESE_FONT
    static const char* headers[] = {  "Choose wipe option",
                                NULL
    };

    char* list[] = {
        "Wipe Data/Factory Reset",
        "Clean to Install a New ROM",
        NULL,
        NULL
    };

    if (is_data_media())
        list[2] = "Wipe user media (/data/media)";
#else
    static const char* headers[] = {  "选择清除选项",
                                NULL
    };

    char* list[] = {
        "清空 Data/恢复出厂设置",
        "为安装新的ROM清除",
        NULL,
        NULL
    };

    if (is_data_media())
        list[2] = "清空用户数据 (/data/media)";
#endif

    int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
    switch (chosen_item) {
        case 0: {
            wipe_data(true);
            break;
        }
        case 1: {
            //clean for new ROM: formats /data, /datadata, /cache, /system, /preload, /sd-ext, .android_secure
#ifndef USE_CHINESE_FONT
            if (confirm_selection("Wipe data, system +/- preload?", "Yes, I will install a new ROM!")) {
                wipe_data(false);
                ui_print("-- Wiping system...\n");
                erase_volume("/system");
                if (volume_for_path("/preload") != NULL) {
                    ui_print("-- Wiping preload...\n");
                    erase_volume("/preload");
                }
                ui_print("Now flash a new ROM!\n");
            }
#else
            if (confirm_selection("清空 data, system +/- preload？", "是的，我会安装一个新ROM!")) {
                wipe_data(false);
                ui_print("-- 正在清除 system...\n");
                erase_volume("/system");
                if (volume_for_path("/preload") != NULL) {
                    ui_print("-- 正在清除 preload...\n");
                    erase_volume("/preload");
                }
                ui_print("现在安装一个新ROM！\n");
            }
#endif
            break;
        }
        case 2: {
#ifndef USE_CHINESE_FONT
            if (confirm_selection("Confirm wipe of all user media?", "Yes - delete all user media")) {
                ui_print("\n-- Wiping media...\n");
                erase_volume("/data/media");
                ui_print("Media wipe complete.\n");
            }
#else
            if (confirm_selection("确定要清空所有用户数据？", "是的 - 清空所有的用户数据")) {
                ui_print("\n-- 正在清除 media...\n");
                erase_volume("/data/media");
                ui_print("Media 清除完毕。\n");
            }
#endif
            break;
        }
    }
}


/*****************************************/
/*      Start Multi-Flash Zip code       */
/*      Original code by PhilZ @xda      */
/*****************************************/
void show_multi_flash_menu() {
#ifndef USE_CHINESE_FONT
    static const char* headers_dir[] = {"Choose a set of zip files", NULL};
    static const char* headers[] = {"Select files to install...", NULL};
#else
    static const char* headers_dir[] = {"选择一系列zip文件", NULL};
    static const char* headers[] = {"选择文件来安装...", NULL};
#endif

    char tmp[PATH_MAX];
    char* zip_folder = NULL;
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

    // Browse sdcards until a valid multi_flash folder is found
    // first, look for MULTI_ZIP_FOLDER in /sdcard
    struct stat st;
    ensure_path_mounted(primary_path);
    sprintf(tmp, "%s/%s/", primary_path, MULTI_ZIP_FOLDER);
    stat(tmp, &st);
    if (S_ISDIR(st.st_mode)) {
        zip_folder = choose_file_menu(tmp, NULL, headers_dir);
        // zip_folder = NULL if no subfolders found or user chose Go Back
        if (no_files_found) {
#ifndef USE_CHINESE_FONT
            ui_print("At least one subfolder with zip files must be created under %s\n", tmp);
            ui_print("Looking in other storage...\n");
#else
            ui_print("在 %s 下面至少要有一个有zip文件的子目录\n", tmp);
            ui_print("正在在其他存储设备查找...\n");
#endif
        }
    } else {
        LOGI("%s not found. Searching other storage...\n", tmp);
    }

    // case MULTI_ZIP_FOLDER not found, or no subfolders or user selected Go Back (zip_folder == NULL)
    // search for MULTI_ZIP_FOLDER in other storage paths if they exist (extra_paths != NULL)
    int i = 0;
    struct stat s;
    if (extra_paths != NULL) {
        while (zip_folder == NULL && i < num_extra_volumes) {
            ensure_path_mounted(extra_paths[i]);
            sprintf(tmp, "%s/%s/", extra_paths[i], MULTI_ZIP_FOLDER);
            stat(tmp, &s);
            if (S_ISDIR(s.st_mode)) {
                zip_folder = choose_file_menu(tmp, NULL, headers_dir);
                if (no_files_found)
#ifndef USE_CHINESE_FONT
                    ui_print("At least one subfolder with zip files must be created under %s\n", tmp);
#else
                    ui_print("在 %s 下面至少要有一个有zip文件的子目录\n", tmp);
#endif
            }
            i++;
        }
    }

    // either MULTI_ZIP_FOLDER path not found (ui_print help)
    // or it was found but no subfolder (ui_print help above in no_files_found)
    // or user chose Go Back every time: return silently
    if (zip_folder == NULL) {
        if (!(S_ISDIR(st.st_mode)) && !(S_ISDIR(s.st_mode)))
#ifndef USE_CHINESE_FONT
            ui_print("Create at least 1 folder with your zip files under %s\n", MULTI_ZIP_FOLDER);
#else
            ui_print("在%s 下面创建至少一个含有zip文件的文件夹\n", MULTI_ZIP_FOLDER);
#endif
        return;
    }

    //gather zip files list
    int dir_len = strlen(zip_folder);
    int numFiles = 0;
    char** files = gather_files(zip_folder, ".zip", &numFiles);
    if (numFiles == 0) {
#ifndef USE_CHINESE_FONT
        ui_print("No zip files found under %s\n", zip_folder);
#else
        ui_print("在 %s 下面没有zip文件\n", zip_folder);
#endif
    } else {
        // start showing multi-zip menu
        char** list = (char**) malloc((numFiles + 3) * sizeof(char*));
#ifndef USE_CHINESE_FONT
        list[0] = strdup("Select/Unselect All");
        list[1] = strdup(">> Flash Selected Files <<");
#else
        list[0] = strdup("选择/取消选择所有");
        list[1] = strdup(">> 刷入选择的文件 <<");
#endif
        list[numFiles+2] = NULL; // Go Back Menu

        int i;
        for(i = 2; i < numFiles + 2; i++) {
            list[i] = strdup(files[i - 2] + dir_len - 4);
            strncpy(list[i], "(x) ", 4);
        }

        int select_all = 1;
        int chosen_item;
        for (;;) {
            chosen_item = get_menu_selection(headers, list, 0, 0);
            if (chosen_item == GO_BACK || chosen_item == REFRESH)
                break;
            if (chosen_item == 1)
                break;
            if (chosen_item == 0) {
                // select / unselect all
                select_all ^= 1;
                for(i = 2; i < numFiles + 2; i++) {
                    if (select_all) strncpy(list[i], "(x)", 3);
                    else strncpy(list[i], "( )", 3);
                }
            } else if (strncmp(list[chosen_item], "( )", 3) == 0) {
                strncpy(list[chosen_item], "(x)", 3);
            } else if (strncmp(list[chosen_item], "(x)", 3) == 0) {
                strncpy(list[chosen_item], "( )", 3);
            }
        }

        //flashing selected zip files
        if (chosen_item == 1) {
            char confirm[PATH_MAX];
#ifndef USE_CHINESE_FONT
            sprintf(confirm, "Yes - Install from %s", BaseName(zip_folder));
            if (confirm_selection("Install selected files?", confirm)) {
#else
            sprintf(confirm, "是的 - 从 %s 安装", BaseName(zip_folder));
            if (confirm_selection("安装选定的文件？", confirm)) {
#endif
                for(i = 2; i < numFiles + 2; i++) {
                    if (strncmp(list[i], "(x)", 3) == 0) {
#ifdef PHILZ_TOUCH_RECOVERY
                        force_wait = -1;
#endif
                        if (install_zip(files[i - 2]) != 0)
                            break;
                    }
                }
            }
        }
        free_string_array(list);
    }
    free_string_array(files);
    free(zip_folder);
}
//-------- End Multi-Flash Zip code


/*****************************************/
/*   DO NOT REMOVE THIS CREDITS HEARDER  */
/* IF YOU MODIFY ANY PART OF THIS SOURCE */
/*  YOU MUST AGREE TO SHARE THE CHANGES  */
/*                                       */
/*  Start open recovery script support   */
/*  Original code: Dees_Troy  at yahoo   */
/*  Original cwm port by sk8erwitskil    */
/*  Enhanced by PhilZ @xda               */
/*****************************************/

// check ors and extendedcommand boot scripts at boot (called from recovery.c)
// verifies that the boot script exists
// if found, try to edit the boot script file to fix paths in scripts generated by GooManager, ROM Manager or user
int check_boot_script_file(const char* boot_script) {
    if (!file_found(boot_script)) {
        LOGI("Ignoring '%s' boot-script: file not found\n", BaseName(boot_script));
        return -1;
    }

    LOGI("Script file found: '%s'\n", boot_script);
    char tmp[PATH_MAX];
    sprintf(tmp, "/sbin/bootscripts_mnt.sh %s %s", boot_script, get_primary_storage_path());
    if (0 != __system(tmp)) {
        // non fatal error
        LOGE("failed to fix boot script (%s)\n", strerror(errno));
        LOGE("run without fixing...\n");
    }

    return 0;
}

// run ors script on boot (called from recovery.c)
// this must be called after check_boot_script_file()
int run_ors_boot_script() {
    int ret = 0;
    char tmp[PATH_MAX];

    if (!file_found(ORS_BOOT_SCRIPT_FILE))
        return -1;

    // move formatted ors boot script to /tmp and run it from there
    sprintf(tmp, "cp -f %s /tmp/%s", ORS_BOOT_SCRIPT_FILE, BaseName(ORS_BOOT_SCRIPT_FILE));
    __system(tmp);
    remove(ORS_BOOT_SCRIPT_FILE);

    sprintf(tmp, "/tmp/%s", BaseName(ORS_BOOT_SCRIPT_FILE));
    return run_ors_script(tmp);
}

// sets the default backup volume for ors backup command
// default is primary storage
static void get_ors_backup_volume(char *volume) {
    char value_def[PATH_MAX];
    sprintf(value_def, "%s", get_primary_storage_path());
    read_config_file(PHILZ_SETTINGS_FILE, ors_backup_path.key, ors_backup_path.value, value_def);
    // on data media device, v == NULL if it is sdcard. But, it doesn't matter since value_def will be /sdcard in that case
    Volume* v = volume_for_path(ors_backup_path.value);
    if (v != NULL && ensure_path_mounted(ors_backup_path.value) == 0 && strcmp(ors_backup_path.value, v->mount_point) == 0)
        strcpy(volume, ors_backup_path.value);
    else strcpy(volume, value_def);
}

// choose ors backup volume and save user setting
static void choose_ors_volume() {
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

#ifndef USE_CHINESE_FONT
    static const char* headers[] = {  "Save ors backups to:",
                                NULL
    };
#else
    static const char* headers[] = {  "把ors备份保存到：",
                                NULL
    };
#endif

    static char* list[MAX_NUM_MANAGED_VOLUMES + 1];
    memset(list, 0, MAX_NUM_MANAGED_VOLUMES + 1);
    list[0] = strdup(primary_path);

    char buf[80];
    int i;
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++) {
            sprintf(buf, "%s", extra_paths[i]);
            list[i + 1] = strdup(buf);
        }
    }
    list[num_extra_volumes + 1] = NULL;

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    if (chosen_item != GO_BACK && chosen_item != REFRESH)
        write_config_file(PHILZ_SETTINGS_FILE, ors_backup_path.key, list[chosen_item]);

    free(list[0]);
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++)
            free(list[i + 1]);
    }
}


// Parse backup options in ors
// Stock CWM as of v6.x, doesn't support backup options
#define SCRIPT_COMMAND_SIZE 512

int ors_backup_command(const char* backup_path, const char* options) {
    is_custom_backup = 1;
    int old_enable_md5sum = enable_md5sum.value;
    enable_md5sum.value = 1;
    backup_boot = 0, backup_recovery = 0, backup_wimax = 0, backup_system = 0;
    backup_preload = 0, backup_data = 0, backup_cache = 0, backup_sdext = 0;
    reset_extra_partitions_state();
    int extra_partitions_num = get_extra_partitions_state();
    ignore_android_secure = 1;
    // yaffs2 partition must be backed up using default yaffs2 wrapper
    set_override_yaffs2_wrapper(0);
    nandroid_force_backup_format("tar");

#ifndef USE_CHINESE_FONT
    ui_print("Setting backup options:\n");
#else
    ui_print("设置备份选项：\n");
#endif
    char value1[SCRIPT_COMMAND_SIZE];
    int line_len, i;
    strcpy(value1, options);
    line_len = strlen(options);
    for (i=0; i<line_len; i++) {
        if (value1[i] == 'S' || value1[i] == 's') {
            backup_system = 1;
            ui_print("System\n");
            if (nandroid_add_preload.value) {
                backup_preload = 1;
#ifndef USE_CHINESE_FONT
                ui_print("Preload enabled in nandroid settings.\n");
                ui_print("It will be Processed with /system\n");
#else
                ui_print("备份Preload已经在nandroid设置中开启。\n");
                ui_print("他会和 /system 一起备份\n");
#endif
            }
        } else if (value1[i] == 'D' || value1[i] == 'd') {
            backup_data = 1;
            ui_print("Data\n");
        } else if (value1[i] == 'C' || value1[i] == 'c') {
            backup_cache = 1;
            ui_print("Cache\n");
        } else if (value1[i] == 'R' || value1[i] == 'r') {
            backup_recovery = 1;
            ui_print("Recovery\n");
        } else if (value1[i] == '1' || value1[i] == '2' || value1[i] == '3' || value1[i] == '4' || value1[i] == '5') {
            // ascii to integer
            int val = value1[i] - 48;
            if (val <= extra_partitions_num) {
                extra_partition[val - 1].backup_state = 1;
                ui_print("%s\n", extra_partition[val - 1].mount_point);
            }
        } else if (value1[i] == 'B' || value1[i] == 'b') {
            backup_boot = 1;
            ui_print("Boot\n");
        } else if (value1[i] == 'A' || value1[i] == 'a') {
            ignore_android_secure = 0;
            ui_print("Android secure\n");
        } else if (value1[i] == 'E' || value1[i] == 'e') {
            backup_sdext = 1;
            ui_print("SD-Ext\n");
        } else if (value1[i] == 'O' || value1[i] == 'o') {
            nandroid_force_backup_format("tgz");
#ifndef USE_CHINESE_FONT
            ui_print("Compression is on\n");
#else
            ui_print("压缩开启\n");
#endif
        } else if (value1[i] == 'M' || value1[i] == 'm') {
            enable_md5sum.value = 0;
#ifndef USE_CHINESE_FONT
            ui_print("MD5 Generation is off\n");
#else
            ui_print("MD5校验关闭\n");
#endif
        }
    }

    int ret = -1;
    if (file_found(backup_path)) {
        LOGE("Specified ors backup target '%s' already exists!\n", backup_path);
    } else if (twrp_backup_mode.value) {
        ret = twrp_backup(backup_path);
    } else {
        ret = nandroid_backup(backup_path);
    }

    is_custom_backup = 0;
    nandroid_force_backup_format("");
    set_override_yaffs2_wrapper(1);
    reset_custom_job_settings(0);
    enable_md5sum.value = old_enable_md5sum;
    return ret;
}

// run ors script code
// this can be started on boot or manually for custom ors
int run_ors_script(const char* ors_script) {
    FILE *fp = fopen(ors_script, "r");
    int ret_val = 0, cindex, line_len, i, remove_nl;
    char script_line[SCRIPT_COMMAND_SIZE], command[SCRIPT_COMMAND_SIZE],
         value[SCRIPT_COMMAND_SIZE], mount[SCRIPT_COMMAND_SIZE],
         value1[SCRIPT_COMMAND_SIZE], value2[SCRIPT_COMMAND_SIZE];
    char *val_start, *tok;

    if (fp != NULL) {
        while (fgets(script_line, SCRIPT_COMMAND_SIZE, fp) != NULL && ret_val == 0) {
            cindex = 0;
            line_len = strlen(script_line);
            if (line_len < 2)
                continue; // there's a blank line or line is too short to contain a command
            LOGI("script line: '%s'\n", script_line); // debug code
            for (i=0; i<line_len; i++) {
                if ((int)script_line[i] == 32) {
                    cindex = i;
                    i = line_len;
                }
            }
            memset(command, 0, sizeof(command));
            memset(value, 0, sizeof(value));
            if ((int)script_line[line_len - 1] == 10)
                remove_nl = 2;
            else
                remove_nl = 1;
            if (cindex != 0) {
                strncpy(command, script_line, cindex);
                LOGI("command is: '%s' and ", command);
                val_start = script_line;
                val_start += cindex + 1;
                if ((int) *val_start == 32)
                    val_start++; //get rid of space
                if ((int) *val_start == 51)
                    val_start++; //get rid of = at the beginning
                strncpy(value, val_start, line_len - cindex - remove_nl);
                LOGI("value is: '%s'\n", value);
            } else {
                strncpy(command, script_line, line_len - remove_nl + 1);
#ifndef USE_CHINESE_FONT
                ui_print("command is: '%s' and there is no value\n", command);
#else
                ui_print("命令是：'%s' 没有参数\n", command);
#endif
            }
            if (strcmp(command, "install") == 0) {
                // Install zip
#ifndef USE_CHINESE_FONT
                ui_print("Installing zip file '%s'\n", value);
#else
                ui_print("正在安装zip文件 '%s'\n", value);
#endif
                ensure_path_mounted(value);
                ret_val = install_zip(value);
                if (ret_val != INSTALL_SUCCESS) {
                    LOGE("Error installing zip file '%s'\n", value);
                    ret_val = 1;
                }
            } else if (strcmp(command, "wipe") == 0) {
                // Wipe
                if (strcmp(value, "cache") == 0 || strcmp(value, "/cache") == 0) {
#ifndef USE_CHINESE_FONT
                    ui_print("-- Wiping Cache Partition...\n");
                    erase_volume("/cache");
                    ui_print("-- Cache Partition Wipe Complete!\n");
#else
                    ui_print("-- 正在清除Cache分区...\n");
                    erase_volume("/cache");
                    ui_print("-- Cache分区清除完毕！\n");
#endif
                } else if (strcmp(value, "dalvik") == 0 || strcmp(value, "dalvick") == 0 || strcmp(value, "dalvikcache") == 0 || strcmp(value, "dalvickcache") == 0) {
#ifndef USE_CHINESE_FONT
                    ui_print("-- Wiping Dalvik Cache...\n");
#else
                    ui_print("-- 正在清除Dalvik Cache...\n");
#endif
                    if (0 != ensure_path_mounted("/data")) {
                        ret_val = 1;
                        break;
                    }
                    ensure_path_mounted("/sd-ext");
                    ensure_path_mounted("/cache");
                    if (no_wipe_confirm) {
                        //do not confirm before wipe for scripts started at boot
                        __system("rm -r /data/dalvik-cache");
                        __system("rm -r /cache/dalvik-cache");
                        __system("rm -r /sd-ext/dalvik-cache");
#ifndef USE_CHINESE_FONT
                        ui_print("Dalvik Cache wiped.\n");
#else
                        ui_print("Dalvik Cache已经被清除。\n");
#endif
                    } else {
#ifndef USE_CHINESE_FONT
                        if (confirm_selection( "Confirm wipe?", "Yes - Wipe Dalvik Cache")) {
#else
                        if (confirm_selection( "确认要清除？", "是 - 清除Dalvik Cache")) {
#endif
                            __system("rm -r /data/dalvik-cache");
                            __system("rm -r /cache/dalvik-cache");
                            __system("rm -r /sd-ext/dalvik-cache");
#ifndef USE_CHINESE_FONT
                            ui_print("Dalvik Cache wiped.\n");
#else
                            ui_print("Dalvik Cache已经被清除。\n");
#endif
                        }
                    }
                    ensure_path_unmounted("/data");
#ifndef USE_CHINESE_FONT
                    ui_print("-- Dalvik Cache Wipe Complete!\n");
#else
                    ui_print("-- Dalvik Cache清除结束！\n");
#endif
                } else if (strcmp(value, "data") == 0 || strcmp(value, "/data") == 0 || strcmp(value, "factory") == 0 || strcmp(value, "factoryreset") == 0) {
#ifndef USE_CHINESE_FONT
                    ui_print("-- Wiping Data Partition...\n");
                    wipe_data(0);
                    ui_print("-- Data Partition Wipe Complete!\n");
#else
                    ui_print("-- 正在清除Data分区...\n");
                    wipe_data(0);
                    ui_print("-- Data分区清除结束！\n");
#endif
                } else {
                    LOGE("Error with wipe command value: '%s'\n", value);
                    ret_val = 1;
                }
            } else if (strcmp(command, "backup") == 0) {
                char backup_path[PATH_MAX];
                char backup_volume[PATH_MAX];
                // read user set volume target
                get_ors_backup_volume(backup_volume);

                tok = strtok(value, " ");
                strcpy(value1, tok);
                tok = strtok(NULL, " ");
                if (tok != NULL) {
                    // command line has a name for backup folder
                    memset(value2, 0, sizeof(value2));
                    strcpy(value2, tok);
                    line_len = strlen(tok);
                    if ((int)value2[line_len - 1] == 10 || (int)value2[line_len - 1] == 13) {
                        if ((int)value2[line_len - 1] == 10 || (int)value2[line_len - 1] == 13)
                            remove_nl = 2;
                        else
                            remove_nl = 1;
                    } else
                        remove_nl = 0;

                    strncpy(value2, tok, line_len - remove_nl);
#ifndef USE_CHINESE_FONT
                    ui_print("Backup folder set to '%s'\n", value2);
#else
                    ui_print("备份目录设置到'%s'\n", value2);
#endif
                    if (twrp_backup_mode.value) {
                        char device_id[PROPERTY_VALUE_MAX];
                        get_device_id(device_id);
                        sprintf(backup_path, "%s/%s/%s/%s", backup_volume, TWRP_BACKUP_PATH, device_id, value2);
                    } else {
                        sprintf(backup_path, "%s/clockworkmod/backup/%s", backup_volume, value2);
                    }
                } else if (twrp_backup_mode.value) {
                    get_twrp_backup_path(backup_volume, backup_path);
                } else {
                    get_cwm_backup_path(backup_volume, backup_path);
                }
                if (0 != (ret_val = ors_backup_command(backup_path, value1)))
#ifndef USE_CHINESE_FONT
                    ui_print("Backup failed !!\n");
#else
                    ui_print("备份失败！！\n");
#endif
            } else if (strcmp(command, "restore") == 0) {
                // Restore
                tok = strtok(value, " ");
                strcpy(value1, tok);
#ifndef USE_CHINESE_FONT
                ui_print("Restoring '%s'\n", value1);
#else
                ui_print("正在恢复'%s'\n", value1);
#endif

                // custom restore settings
                is_custom_backup = 1;
                int old_enable_md5sum = enable_md5sum.value;
                enable_md5sum.value = 1;
                backup_boot = 0, backup_recovery = 0, backup_system = 0;
                backup_preload = 0, backup_data = 0, backup_cache = 0, backup_sdext = 0;
                reset_extra_partitions_state();
                int extra_partitions_num = get_extra_partitions_state();
                ignore_android_secure = 1; //disable

                // check what type of restore we need and force twrp mode in that case
                int old_twrp_backup_mode = twrp_backup_mode.value;
                if (strstr(value1, TWRP_BACKUP_PATH) != NULL)
                    twrp_backup_mode.value = 1;

                tok = strtok(NULL, " ");
                if (tok != NULL) {
                    memset(value2, 0, sizeof(value2));
                    strcpy(value2, tok);
#ifndef USE_CHINESE_FONT
                    ui_print("Setting restore options:\n");
#else
                    ui_print("设定恢复选项：\n");
#endif
                    line_len = strlen(value2);
                    for (i=0; i<line_len; i++) {
                        if (value2[i] == 'S' || value2[i] == 's') {
                            backup_system = 1;
                            ui_print("System\n");
                            if (nandroid_add_preload.value) {
                                backup_preload = 1;
#ifndef USE_CHINESE_FONT
                                ui_print("Preload enabled in nandroid settings.\n");
                                ui_print("It will be Processed with /system\n");
#else
                                ui_print("备份Preload已经在nandroid设置中开启。\n");
                                ui_print("他会和 /system 一起备份\n");
#endif
                            }
                        } else if (value2[i] == 'D' || value2[i] == 'd') {
                            backup_data = 1;
                            ui_print("Data\n");
                        } else if (value2[i] == 'C' || value2[i] == 'c') {
                            backup_cache = 1;
                            ui_print("Cache\n");
                        } else if (value2[i] == 'R' || value2[i] == 'r') {
                            backup_recovery = 1;
                            ui_print("Recovery\n");
                        } else if (value2[i] == '1' || value2[i] == '2' || value2[i] == '3' || value2[i] == '4' || value2[i] == '5') {
                            // ascii to integer
                            int val = value2[i] - 48;
                            if (val <= extra_partitions_num) {
                                extra_partition[val - 1].backup_state = 1;
                                ui_print("%s\n", extra_partition[val - 1].mount_point);
                            }
                        } else if (value2[i] == 'B' || value2[i] == 'b') {
                            backup_boot = 1;
                            ui_print("Boot\n");
                        } else if (value2[i] == 'A' || value2[i] == 'a') {
                            ignore_android_secure = 0;
                            ui_print("Android secure\n");
                        } else if (value2[i] == 'E' || value2[i] == 'e') {
                            backup_sdext = 1;
                            ui_print("SD-Ext\n");
                        } else if (value2[i] == 'M' || value2[i] == 'm') {
                            enable_md5sum.value = 0;
#ifndef USE_CHINESE_FONT
                            ui_print("MD5 Check is off\n");
#else
                            ui_print("MD5检查关闭\n");
#endif
                        }
                    }
                } else {
                    LOGI("No restore options set\n");
                    LOGI("Restoring default partitions");
                    backup_boot = 1, backup_system = 1;
                    backup_data = 1, backup_cache = 1, backup_sdext = 1;
                    ignore_android_secure = 0;
                    backup_preload = nandroid_add_preload.value;
                }

                if (twrp_backup_mode.value)
                    ret_val = twrp_restore(value1);
                else
                    ret_val = nandroid_restore(value1, backup_boot, backup_system, backup_data, backup_cache, backup_sdext, 0);
                
                if (ret_val != 0)
#ifndef USE_CHINESE_FONT
                    ui_print("Restore failed!\n");
#else
                    ui_print("恢复失败！\n");
#endif

                is_custom_backup = 0, twrp_backup_mode.value = old_twrp_backup_mode;
                reset_custom_job_settings(0);
                enable_md5sum.value = old_enable_md5sum;
            } else if (strcmp(command, "mount") == 0) {
                // Mount
                if (value[0] != '/') {
                    strcpy(mount, "/");
                    strcat(mount, value);
                } else
                    strcpy(mount, value);
                ensure_path_mounted(mount);
#ifndef USE_CHINESE_FONT
                ui_print("Mounted '%s'\n", mount);
#else
                ui_print("'%s'已经挂载\n", mount);
#endif
            } else if (strcmp(command, "unmount") == 0 || strcmp(command, "umount") == 0) {
                // Unmount
                if (value[0] != '/') {
                    strcpy(mount, "/");
                    strcat(mount, value);
                } else
                    strcpy(mount, value);
                ensure_path_unmounted(mount);
#ifndef USE_CHINESE_FONT
                ui_print("Unmounted '%s'\n", mount);
#else
                ui_print("'%s'已经取消挂载\n", mount);
#endif
            } else if (strcmp(command, "set") == 0) {
                // Set value
                tok = strtok(value, " ");
                strcpy(value1, tok);
                tok = strtok(NULL, " ");
                strcpy(value2, tok);
#ifndef USE_CHINESE_FONT
                ui_print("Setting function disabled in CWMR: '%s' to '%s'\n", value1, value2);
#else
                ui_print("设置在CWMR关闭的功能：'%s' to '%s'\n", value1, value2);
#endif
            } else if (strcmp(command, "mkdir") == 0) {
                // Make directory (recursive)
#ifndef USE_CHINESE_FONT
                ui_print("Recursive mkdir disabled in CWMR: '%s'\n", value);
#else
                ui_print("在CWMR关闭递归创建目录：'%s'\n", value);
#endif
            } else if (strcmp(command, "reboot") == 0) {
                // Reboot
            } else if (strcmp(command, "cmd") == 0) {
                if (cindex != 0) {
                    __system(value);
                } else {
                    LOGE("No value given for cmd\n");
                }
            } else if (strcmp(command, "print") == 0) {
                ui_print("%s\n", value);
            } else if (strcmp(command, "sideload") == 0) {
                // Install zip from sideload
#ifndef USE_CHINESE_FONT
                ui_print("Waiting for sideload...\n");
#else
                ui_print("正在等待sideload...\n");
#endif
                ret_val = enter_sideload_mode(INSTALL_SUCCESS);
                if (ret_val != INSTALL_SUCCESS)
                    LOGE("Error installing from sideload\n");
            } else {
                LOGE("Unrecognized script command: '%s'\n", command);
                ret_val = 1;
            }
        }
        fclose(fp);
#ifndef USE_CHINESE_FONT
        ui_print("Done processing script file\n");
#else
        ui_print("脚本文件执行结束\n");
#endif
    } else {
        LOGE("Error opening script file '%s'\n", ors_script);
        return 1;
    }
    return ret_val;
}

//show menu: select ors from default path
static int browse_for_file = 1; // 0 == stop browsing default file locations
static void choose_default_ors_menu(const char* volume_path) {
    if (ensure_path_mounted(volume_path) != 0) {
        LOGE("Can't mount %s\n", volume_path);
        browse_for_file = 1;
        return;
    }

    char ors_dir[PATH_MAX];
    sprintf(ors_dir, "%s/%s/", volume_path, RECOVERY_ORS_PATH);
    if (access(ors_dir, F_OK) == -1) {
        //custom folder does not exist
        browse_for_file = 1;
        return;
    }

#ifndef USE_CHINESE_FONT
    static const char* headers[] = {
        "Choose a script to run",
        "",
        NULL
    };
#else
    static const char* headers[] = {
        "选择一个脚本来运行",
        "",
        NULL
    };
#endif

    char* ors_file = choose_file_menu(ors_dir, ".ors", headers);
    if (no_files_found == 1) {
        //0 valid files to select, let's continue browsing next locations
#ifndef USE_CHINESE_FONT
        ui_print("No *.ors files in %s/%s\n", volume_path, RECOVERY_ORS_PATH);
#else
        ui_print("在%s/%s没有*.ors文件\n", volume_path, RECOVERY_ORS_PATH);
#endif
        browse_for_file = 1;
    } else {
        browse_for_file = 0;
        //we found ors scripts in RECOVERY_ORS_PATH folder: do not proceed other locations even if no file is chosen
    }

    if (ors_file == NULL) {
        //either no valid files found or we selected no files by pressing back menu
        return;
    }

    char confirm[PATH_MAX];
#ifndef USE_CHINESE_FONT
    sprintf(confirm, "Yes - Run %s", BaseName(ors_file));
    if (confirm_selection("Confirm run script?", confirm)) {
#else
    sprintf(confirm, "是 - 运行%s", BaseName(ors_file));
    if (confirm_selection("确认运行脚本？", confirm)) {
#endif
        run_ors_script(ors_file);
    }

    free(ors_file);
}

//show menu: browse for custom Open Recovery Script
static void choose_custom_ors_menu(const char* volume_path) {
    if (ensure_path_mounted(volume_path) != 0) {
        LOGE("Can't mount %s\n", volume_path);
        return;
    }

#ifndef USE_CHINESE_FONT
    static const char* headers[] = {"Choose .ors script to run", NULL};
#else
    static const char* headers[] = {"选择.ors脚本来运行", NULL};
#endif

    char* ors_file = choose_file_menu(volume_path, ".ors", headers);
    if (ors_file == NULL)
        return;

    char confirm[PATH_MAX];
#ifndef USE_CHINESE_FONT
    sprintf(confirm, "Yes - Run %s", BaseName(ors_file));
    if (confirm_selection("Confirm run script?", confirm)) {
#else
    sprintf(confirm, "是 - 运行%s", BaseName(ors_file));
    if (confirm_selection("确认运行脚本？", confirm)) {
#endif
        run_ors_script(ors_file);
    }

    free(ors_file);
}

//show menu: select sdcard volume to search for custom ors file
static void show_custom_ors_menu() {
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

#ifndef USE_CHINESE_FONT
    static const char* headers[] = {  "Search .ors script to run",
                                "",
                                NULL
    };
#else
    static const char* headers[] = {  "搜索.ors脚本来运行",
                                "",
                                NULL
    };
#endif

    static char* list[MAX_NUM_MANAGED_VOLUMES + 1];
#ifndef USE_CHINESE_FONT
    char list_prefix[] = "Search ";
#else
    char list_prefix[] = "搜索 ";
#endif
    char buf[256];
    memset(list, 0, MAX_NUM_MANAGED_VOLUMES + 1);
    sprintf(buf, "%s%s", list_prefix, primary_path);
    list[0] = strdup(buf);

    int i;
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++) {
            sprintf(buf, "%s%s", list_prefix, extra_paths[i]);
            list[i + 1] = strdup(buf);
        }
    }
    list[num_extra_volumes + 1] = NULL;

    int chosen_item;
    for (;;)
    {
        chosen_item = get_menu_selection(headers, list, 0, 0);
        if (chosen_item == GO_BACK || chosen_item == REFRESH)
            break;
        choose_custom_ors_menu(list[chosen_item] + strlen(list_prefix));
    }

    free(list[0]);
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++)
            free(list[i + 1]);
    }
}
//----------end open recovery script support


/**********************************/
/*       Start Get ROM Name       */
/*    Original source by PhilZ    */
/**********************************/
// formats a string to be compliant with filenames standard and limits its length to max_len
static void format_filename(char *valid_path, int max_len) {
    // remove non allowed chars (invalid file names) and limit valid_path filename to max_len chars
    // we could use a whitelist: ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-
    char invalid_fn[] = " /><%#*^$:;\"\\\t,?!{}()=+'¦|&";
    int i = 0;
    for(i=0; valid_path[i] != '\0' && i < max_len; i++) {
        size_t j = 0;
        while (j < strlen(invalid_fn)) {
            if (valid_path[i] == invalid_fn[j])
                valid_path[i] = '_';
            j++;
        }
        if (valid_path[i] == 13)
            valid_path[i] = '_';
    }

    valid_path[max_len] = '\0';
    if (valid_path[strlen(valid_path)-1] == '_') {
        valid_path[strlen(valid_path)-1] = '\0';
    }
}

// get rom_name function
// always call with rom_name[PROPERTY_VALUE_MAX]
#define MAX_ROM_NAME_LENGTH 31
void get_rom_name(char *rom_name) {
    const char *rom_id_key[] = { "ro.modversion", "ro.romversion", "ro.build.display.id", NULL };
    const char *key;
    int i = 0;

    sprintf(rom_name, "noname");
    while ((key = rom_id_key[i]) != NULL && strcmp(rom_name, "noname") == 0) {
        if (read_config_file("/system/build.prop", key, rom_name, "noname") < 0) {
#ifndef USE_CHINESE_FONT
            ui_print("failed to open /system/build.prop!\n");
            ui_print("using default noname.\n");
#else
            ui_print("打开/system/build.prop失败！\n");
            ui_print("使用默认没有名字\n");
#endif
            break;
        }
        i++;
    }

    if (strcmp(rom_name, "noname") != 0) {
        format_filename(rom_name, MAX_ROM_NAME_LENGTH);
    }
}


/**********************************/
/*   Misc Nandroid Settings Menu  */
/**********************************/
static void regenerate_md5_sum_menu() {
#ifndef USE_CHINESE_FONT
    if (!confirm_selection("This is not recommended!!", "Yes - Recreate New md5 Sum"))
#else
    if (!confirm_selection("不推荐该操作!!", "是 - 生成新的md5校验"))
#endif
        return;

    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

#ifndef USE_CHINESE_FONT
    char list_prefix[] = "Select from ";
#else
    char list_prefix[] = "选择列表 ";
#endif
    char buf[80];
#ifndef USE_CHINESE_FONT
    const char* headers[] = {"Regenerate md5 sum", "Select a backup to regenerate", NULL};
#else
    const char* headers[] = {"重新生成md5校验", "选择一个备份来重新生成", NULL};
#endif
    char* list[MAX_NUM_MANAGED_VOLUMES + 1];
    memset(list, 0, MAX_NUM_MANAGED_VOLUMES + 1);
    sprintf(buf, "%s%s", list_prefix, primary_path);
    list[0] = strdup(buf);

    int i;
    if (extra_paths != NULL) {
        for (i = 0; i < num_extra_volumes; i++) {
            sprintf(buf, "%s%s", list_prefix, extra_paths[i]);
            list[i + 1] = strdup(buf);
        }
    }
    list[num_extra_volumes + 1] = NULL;

    char tmp[PATH_MAX];
    int chosen_item = get_menu_selection(headers, list, 0, 0);
    if (chosen_item == GO_BACK || chosen_item == REFRESH)
        goto out;

    // select backup set and regenerate md5 sum
    sprintf(tmp, "%s/%s/", list[chosen_item] + strlen(list_prefix), CWM_BACKUP_PATH);
    if (ensure_path_mounted(tmp) != 0)
        goto out;

    char* file = choose_file_menu(tmp, "", headers);
    if (file == NULL)
        goto out;

    char backup_source[PATH_MAX];
    sprintf(backup_source, "%s", DirName(file));
#ifndef USE_CHINESE_FONT
    sprintf(tmp, "Process %s", BaseName(backup_source));
    if (confirm_selection("Regenerate md5 sum ?", tmp)) {
        if (0 == gen_nandroid_md5sum(backup_source))
            ui_print("Done generating md5 sum.\n");
#else
    sprintf(tmp, "对%s进行", BaseName(backup_source));
    if (confirm_selection("重新生成md5校验？", tmp)) {
        if (0 == gen_nandroid_md5sum(backup_source))
            ui_print("重新生成md5校验完毕。\n");
#endif
    }

    free(file);

out:
    free(list[0]);
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++)
            free(list[i + 1]);
    }
}

void misc_nandroid_menu() {
#ifndef USE_CHINESE_FONT
    const char* headers[] = {
        "Misc Nandroid Settings",
        "",
        NULL
    };
#else
    const char* headers[] = {
        "Nandroid杂项设置",
        "",
        NULL
    };
#endif

    char item_md5[MENU_MAX_COLS];
    char item_preload[MENU_MAX_COLS];
    char item_twrp_mode[MENU_MAX_COLS];
    char item_size_progress[MENU_MAX_COLS];
    char item_use_nandroid_simple_logging[MENU_MAX_COLS];
    char item_nand_progress[MENU_MAX_COLS];
    char item_prompt_low_space[MENU_MAX_COLS];
    char item_ors_path[MENU_MAX_COLS];
    char item_compress[MENU_MAX_COLS];

    char* list[] = {
        item_md5,
        item_preload,
        item_twrp_mode,
        item_size_progress,
        item_use_nandroid_simple_logging,
        item_nand_progress,
        item_prompt_low_space,
        item_ors_path,
        item_compress,
#ifndef USE_CHINESE_FONT
        "Default Backup Format...",
        "Regenerate md5 Sum",
#ifdef BOARD_RECOVERY_CREATE_SE_CONTAINER
        "Create /data selinux container",
#endif
#else
        "默认备份格式...",
        "重新生成md5校验",
#ifdef BOARD_RECOVERY_CREATE_SE_CONTAINER
        "创建/data selinux容器r",
#endif
#endif
        NULL
    };

    int hidenandprogress;
    char* primary_path = get_primary_storage_path();
    char hidenandprogress_file[PATH_MAX];
    sprintf(hidenandprogress_file, "%s/%s", primary_path, NANDROID_HIDE_PROGRESS_FILE);

    int fmt;
    for (;;) {
#ifndef USE_CHINESE_FONT
        if (enable_md5sum.value) ui_format_gui_menu(item_md5, "MD5 checksum", "(x)");
        else ui_format_gui_menu(item_md5, "MD5 checksum", "( )");

        if (volume_for_path("/preload") == NULL)
            ui_format_gui_menu(item_preload, "Include /preload", "N/A");
        else if (nandroid_add_preload.value) ui_format_gui_menu(item_preload, "Include /preload", "(x)");
        else ui_format_gui_menu(item_preload, "Include /preload", "( )");

        if (twrp_backup_mode.value) ui_format_gui_menu(item_twrp_mode, "Use TWRP Mode", "(x)");
        else ui_format_gui_menu(item_twrp_mode, "Use TWRP Mode", "( )");

        if (show_nandroid_size_progress.value)
            ui_format_gui_menu(item_size_progress, "Show Nandroid Size Progress", "(x)");
        else ui_format_gui_menu(item_size_progress, "Show Nandroid Size Progress", "( )");
        list[3] = item_size_progress;

        if (use_nandroid_simple_logging.value)
            ui_format_gui_menu(item_use_nandroid_simple_logging, "Use Simple Logging (faster)", "(x)");
        else ui_format_gui_menu(item_use_nandroid_simple_logging, "Use Simple Logging (faster)", "( )");
        list[4] = item_use_nandroid_simple_logging;

        hidenandprogress = file_found(hidenandprogress_file);
        if (hidenandprogress) {
            ui_format_gui_menu(item_nand_progress, "Hide Nandroid Progress", "(x)");
            list[3] = NULL;
            list[4] = NULL;
        } else ui_format_gui_menu(item_nand_progress, "Hide Nandroid Progress", "( )");

        if (nand_prompt_on_low_space.value)
            ui_format_gui_menu(item_prompt_low_space, "Prompt on Low Free Space", "(x)");
        else ui_format_gui_menu(item_prompt_low_space, "Prompt on Low Free Space", "( )");
#else
        if (enable_md5sum.value) ui_format_gui_menu(item_md5, "MD5校验", "(x)");
        else ui_format_gui_menu(item_md5, "MD5校验", "( )");

        if (volume_for_path("/preload") == NULL)
            ui_format_gui_menu(item_preload, "包括/preload", "N/A");
        else if (nandroid_add_preload.value) ui_format_gui_menu(item_preload, "包括/preload", "(x)");
        else ui_format_gui_menu(item_preload, "包括/preload", "( )");

        if (twrp_backup_mode.value) ui_format_gui_menu(item_twrp_mode, "使用TWRP模式", "(x)");
        else ui_format_gui_menu(item_twrp_mode, "使用TWRP模式", "( )");

        if (show_nandroid_size_progress.value)
            ui_format_gui_menu(item_size_progress, "显示Nandroid 进度", "(x)");
        else ui_format_gui_menu(item_size_progress, "显示Nandroid 进度", "( )");
        list[3] = item_size_progress;

        if (use_nandroid_simple_logging.value)
            ui_format_gui_menu(item_use_nandroid_simple_logging, "使用简单日志（更快）", "(x)");
        else ui_format_gui_menu(item_use_nandroid_simple_logging, "使用简单日志（更快）", "( )");
        list[4] = item_use_nandroid_simple_logging;

        hidenandprogress = file_found(hidenandprogress_file);
        if (hidenandprogress) {
            ui_format_gui_menu(item_nand_progress, "隐藏Nandroid进度", "(x)");
            list[3] = NULL;
            list[4] = NULL;
        } else ui_format_gui_menu(item_nand_progress, "隐藏Nandroid进度", "( )");

        if (nand_prompt_on_low_space.value)
            ui_format_gui_menu(item_prompt_low_space, "提示空间不足", "(x)");
        else ui_format_gui_menu(item_prompt_low_space, "提示空间不足", "( )");
#endif

        char ors_volume[PATH_MAX];
        get_ors_backup_volume(ors_volume);
#ifndef USE_CHINESE_FONT
        ui_format_gui_menu(item_ors_path,  "ORS Backup Target", ors_volume);

        fmt = nandroid_get_default_backup_format();
        if (fmt == NANDROID_BACKUP_FORMAT_TGZ) {
            if (compression_value.value == TAR_GZ_FAST)
                ui_format_gui_menu(item_compress, "Compression", "fast");
            else if (compression_value.value == TAR_GZ_LOW)
                ui_format_gui_menu(item_compress, "Compression", "low");
            else if (compression_value.value == TAR_GZ_MEDIUM)
                ui_format_gui_menu(item_compress, "Compression", "medium");
            else if (compression_value.value == TAR_GZ_HIGH)
                ui_format_gui_menu(item_compress, "Compression", "high");
            else ui_format_gui_menu(item_compress, "Compression", TAR_GZ_DEFAULT_STR); // useless but to not make exceptions
        } else
            ui_format_gui_menu(item_compress, "Compression", "No");
#else
        ui_format_gui_menu(item_ors_path,  "ORS备份目标", ors_volume);

        fmt = nandroid_get_default_backup_format();
        if (fmt == NANDROID_BACKUP_FORMAT_TGZ) {
            if (compression_value.value == TAR_GZ_FAST)
                ui_format_gui_menu(item_compress, "压缩", "快速");
            else if (compression_value.value == TAR_GZ_LOW)
                ui_format_gui_menu(item_compress, "压缩", "低");
            else if (compression_value.value == TAR_GZ_MEDIUM)
                ui_format_gui_menu(item_compress, "压缩", "中");
            else if (compression_value.value == TAR_GZ_HIGH)
                ui_format_gui_menu(item_compress, "压缩", "高");
            else ui_format_gui_menu(item_compress, "压缩", TAR_GZ_DEFAULT_STR); // useless but to not make exceptions
        } else
            ui_format_gui_menu(item_compress, "压缩", "不");
#endif

        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item) {
            case 0: {
                char value[3];
                enable_md5sum.value ^= 1;
                sprintf(value, "%d", enable_md5sum.value);
                write_config_file(PHILZ_SETTINGS_FILE, enable_md5sum.key, value);
                break;
            }
            case 1: {
                char value[3];
                if (volume_for_path("/preload") == NULL)
                    nandroid_add_preload.value = 0;
                else
                    nandroid_add_preload.value ^= 1;
                sprintf(value, "%d", nandroid_add_preload.value);
                write_config_file(PHILZ_SETTINGS_FILE, nandroid_add_preload.key, value);
                break;
            }
            case 2: {
                char value[3];
                twrp_backup_mode.value ^= 1;
                sprintf(value, "%d", twrp_backup_mode.value);
                write_config_file(PHILZ_SETTINGS_FILE, twrp_backup_mode.key, value);
                break;
            }
            case 3: {
                char value[3];
                show_nandroid_size_progress.value ^= 1;
                sprintf(value, "%d", show_nandroid_size_progress.value);
                write_config_file(PHILZ_SETTINGS_FILE, show_nandroid_size_progress.key, value);
                break;
            }
            case 4: {
                char value[3];
                use_nandroid_simple_logging.value ^= 1;
                sprintf(value, "%d", use_nandroid_simple_logging.value);
                write_config_file(PHILZ_SETTINGS_FILE, use_nandroid_simple_logging.key, value);
                break;
            }
            case 5: {
                hidenandprogress ^= 1;
                if (hidenandprogress)
                    write_string_to_file(hidenandprogress_file, "1");
                else delete_a_file(hidenandprogress_file);
                break;
            }
            case 6: {
                char value[3];
                nand_prompt_on_low_space.value ^= 1;
                sprintf(value, "%d", nand_prompt_on_low_space.value);
                write_config_file(PHILZ_SETTINGS_FILE, nand_prompt_on_low_space.key, value);
                break;
            }
            case 7: {
                choose_ors_volume();
                break;
            }
            case 8: {
                if (fmt != NANDROID_BACKUP_FORMAT_TGZ) {
#ifndef USE_CHINESE_FONT
                    ui_print("First set backup format to tar.gz\n");
#else
                    ui_print("把首选备份格式设置为tar.gz\n");
#endif
                } else {
                    // switch pigz -[ fast(1), low(3), medium(5), high(7) ] compression level
                    char value[8];
                    compression_value.value += 2;
                    if (compression_value.value == TAR_GZ_FAST)
                        sprintf(value, "fast");
                    else if (compression_value.value == TAR_GZ_LOW)
                        sprintf(value, "low");
                    else if (compression_value.value == TAR_GZ_MEDIUM)
                        sprintf(value, "medium");
                    else if (compression_value.value == TAR_GZ_HIGH)
                        sprintf(value, "high");
                    else {
                        // loop back the toggle
                        compression_value.value = TAR_GZ_FAST;
                        sprintf(value, "fast");
                    }
                    write_config_file(PHILZ_SETTINGS_FILE, compression_value.key, value);
                }
                break;
            }
            case 9: {
                choose_default_backup_format();
                break;
            }
            case 10: {
                regenerate_md5_sum_menu();
                break;
            }
#ifdef BOARD_RECOVERY_CREATE_SE_CONTAINER
            case 11: {
                create_external_selinux_container();
                break;
            }
#endif
        }
    }
}
//-------- End Misc Nandroid Settings


/****************************************/
/*  Start Install Zip from custom path  */
/*                 and                  */
/*       Free Browse Mode Support       */
/****************************************/
void set_custom_zip_path() {
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Setup Free Browse Mode", NULL };
#else
    static const char* headers[] = { "设置自由浏览模式", NULL };
#endif

    int list_top_items = 2;
#ifndef USE_CHINESE_FONT
    char list_prefix[] = "Start Folder in ";
#else
    char list_prefix[] = "开始目录 ";
#endif
    char* list_main[MAX_NUM_MANAGED_VOLUMES + list_top_items + 1];
    char buf[80];
    memset(list_main, 0, MAX_NUM_MANAGED_VOLUMES + list_top_items + 1);
#ifndef USE_CHINESE_FONT
    list_main[0] = "Disable Free Browse Mode";
#else
    list_main[0] = "关闭自由浏览模式";
#endif
    sprintf(buf, "%s%s", list_prefix, primary_path);
    list_main[1] = strdup(buf);

    int i;
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++) {
            sprintf(buf, "%s%s", list_prefix, extra_paths[i]);
            list_main[i + list_top_items] = strdup(buf);
        }
    }
    list_main[num_extra_volumes + list_top_items] = NULL;

    Volume* v;
    char custom_path[PATH_MAX];
    int chosen_item;
    for (;;) {
        chosen_item = get_menu_selection(headers, list_main, 0, 0);
        if (chosen_item == GO_BACK || chosen_item == REFRESH) {
            goto out;
        } else if (chosen_item == 0) {
            write_config_file(PHILZ_SETTINGS_FILE, user_zip_folder.key, "");
#ifndef USE_CHINESE_FONT
            ui_print("Free browse mode disabled\n");
#else
            ui_print("自由浏览模式已经关闭\n");
#endif
            goto out;
        } else {
            sprintf(custom_path, "%s/", list_main[chosen_item] + strlen(list_prefix));
            if (is_data_media_volume_path(custom_path))
                v = volume_for_path("/data");
            else
                v = volume_for_path(custom_path);
            if (v == NULL || ensure_path_mounted(v->mount_point) != 0)
                continue;
            break;
        }
    }

    // populate fixed headers (display current path while browsing)
    int j = 0;
    while (headers[j]) {
        j++;
    }
    const char** fixed_headers = (const char**)malloc((j + 2) * sizeof(char*));
    j = 0;
    while (headers[j]) {
        fixed_headers[j] = headers[j];
        j++;
    }
    fixed_headers[j] = custom_path;
    fixed_headers[j + 1] = NULL;

    // start browsing for custom path
    int dir_len = strlen(custom_path);
    int numDirs = 0;
    char** dirs = gather_files(custom_path, NULL, &numDirs);
    char** list = (char**) malloc((numDirs + 3) * sizeof(char*));
    list[0] = strdup("../");
#ifndef USE_CHINESE_FONT
    list[1] = strdup(">> Set current folder as default <<");
#else
    list[1] = strdup(">> 将当前目录设为默认 <<");
#endif
    list[numDirs + 2] = NULL; // Go Back Menu

    // populate list with current folders. Reserved list[0] for ../ to browse backward
    for(i = 2; i < numDirs + 2; i++) {
        list[i] = strdup(dirs[i - 2] + dir_len);
    }

/*
 * do not modify custom_path when browsing before we ensure it can be mounted
   else we could write a non mountable path to config file or we could alter fixed_headers path
 * vold_mount_all(): vold managed volumes need to be mounted else we end up in /storage empty folder when browsing ../ while we entered from /sdcard for example
   /storage/sdcard0, /storage/usbdisk... are not created during recovery start in init.rc but when we mount the volume for first time
*/
    char custom_path2[PATH_MAX];
    sprintf(custom_path2, "%s", custom_path);
    vold_mount_all();
    for (;;) {
        chosen_item = get_menu_selection(fixed_headers, list, 0, 0);
        if (chosen_item == GO_BACK || chosen_item == REFRESH)
            break;
        if (chosen_item == 0) {
            // browse up folder: ../
            // check for up_folder == "." for exceptions!
            const char *up_folder = DirName(custom_path);
            if (strcmp(up_folder, "/") == 0 || strcmp(up_folder, ".") == 0)
                sprintf(custom_path2, "/" );
            else
                sprintf(custom_path2, "%s/", up_folder);
        } else if (chosen_item == 1) {
            // save default folder
            // no need to ensure custom_path is mountable as it is always if we reached here
            if (strlen(custom_path) > PROPERTY_VALUE_MAX)
                LOGE("Maximum allowed path length is %d\n", PROPERTY_VALUE_MAX);
            else if (0 == write_config_file(PHILZ_SETTINGS_FILE, user_zip_folder.key, custom_path))
#ifndef USE_CHINESE_FONT
                ui_print("Default install zip folder set to %s\n", custom_path);
#else
                ui_print("默认zip安装文件夹设置到%s\n", custom_path);
#endif
            break;
        } else {
            // continue browsing folders
            sprintf(custom_path2, "%s", dirs[chosen_item - 2]);
        }

        // mount known volumes before browsing folders
        if (is_data_media_volume_path(custom_path2) && ensure_path_mounted("/data") != 0)
            continue;
        else if (volume_for_path(custom_path2) != NULL && ensure_path_mounted(custom_path2) != 0)
            continue;

        // we're now in a mounted path or ramdisk folder: browse selected folder
        sprintf(custom_path, "%s", custom_path2);
        fixed_headers[j] = custom_path;
        dir_len = strlen(custom_path);
        numDirs = 0;
        free_string_array(list);
        free_string_array(dirs);
        dirs = gather_files(custom_path, NULL, &numDirs);
        list = (char**) malloc((numDirs + 3) * sizeof(char*));
        list[0] = strdup("../");
#ifndef USE_CHINESE_FONT
        list[1] = strdup(">> Set current folder as default <<");
#else
        list[1] = strdup(">> 将当前目录设为默认 <<");
#endif
        list[numDirs+2] = NULL;
        for(i=2; i < numDirs+2; i++) {
            list[i] = strdup(dirs[i-2] + dir_len);
        }
    }
    free_string_array(list);
    free_string_array(dirs);
    free(fixed_headers);

out:
    // free(list_main[0]);
    free(list_main[1]);
    if (extra_paths != NULL) {
        for(i = 0; i < num_extra_volumes; i++)
            free(list_main[i + list_top_items]);
    }
}

int show_custom_zip_menu() {
    static const char* headers[] = {
#ifndef USE_CHINESE_FONT
        "Choose a zip to apply",
#else
        "选择一个zip来应用",
#endif
        NULL
    };

    int ret = 0;
    read_config_file(PHILZ_SETTINGS_FILE, user_zip_folder.key, user_zip_folder.value, "");

    // try to mount known volumes, ignore unknown ones to permit using ramdisk and other paths
    if (strcmp(user_zip_folder.value, "") == 0)
        ret = 1;
    else if (is_data_media_volume_path(user_zip_folder.value) && ensure_path_mounted("/data") != 0)
        ret = -1;
    else if (volume_for_path(user_zip_folder.value) != NULL && ensure_path_mounted(user_zip_folder.value) != 0)
        ret = -1;

    if (ret != 0) {
        LOGE("Cannot mount custom path %s\n", user_zip_folder.value);
        LOGE("You must first setup a valid folder\n");
        return ret;
    }

    char custom_path[PATH_MAX];
    sprintf(custom_path, "%s", user_zip_folder.value);
    if (custom_path[strlen(custom_path) - 1] != '/')
        strcat(custom_path, "/");
    //LOGE("Retained user_zip_folder.value to custom_path=%s\n", custom_path);

    // populate fixed headers (display current path while browsing)
    int j = 0;
    while (headers[j]) {
        j++;
    }
    const char** fixed_headers = (const char**)malloc((j + 2) * sizeof(char*));
    j = 0;
    while (headers[j]) {
        fixed_headers[j] = headers[j];
        j++;
    }
    fixed_headers[j] = custom_path;
    fixed_headers[j + 1] = NULL;

    //gather zip files and display ../ to browse backward
    int dir_len = strlen(custom_path);
    int numDirs = 0;
    int numFiles = 0;
    int total;
    char** dirs = gather_files(custom_path, NULL, &numDirs);
    char** files = gather_files(custom_path, ".zip", &numFiles);
    total = numFiles + numDirs;
    char** list = (char**) malloc((total + 2) * sizeof(char*));
    list[0] = strdup("../");
    list[total + 1] = NULL;

    // populate menu list with current folders and zip files. Reserved list[0] for ../ to browse backward
    //LOGE(">> Dirs (num=%d):\n", numDirs);
    int i;
    for(i = 1; i < numDirs + 1; i++) {
        list[i] = strdup(dirs[i - 1] + dir_len);
        //LOGE("list[%d]=%s\n", i, list[i]);
    }
    //LOGE("\n>> Files (num=%d):\n", numFiles);
    for(i = 1; i < numFiles + 1; i++) {
        list[numDirs + i] = strdup(files[i - 1] + dir_len);
        //LOGE("list[%d]=%s\n", numDirs+i, list[numDirs+i]);
    }

    // do not modify custom_path when browsing before we ensure it can be mounted
    // else we could write a non mountable path to config file or we could alter fixed_headers path
    // vold_mount_all(): vold managed volumes need to be mounted else we end up in /storage empty folder
    //  - /storage/sdcard0, /storage/usbdisk... are not created during recovery start in init.rc but when we mount the volume for first time
    int chosen_item;
    char custom_path2[PATH_MAX];
    sprintf(custom_path2, "%s", custom_path);
    vold_mount_all();
    for (;;) {
/*
        LOGE("\n\n>> Total list:\n");
        for(i=0; i < total+1; i++) {
            LOGE("list[%d]=%s\n", i, list[i]);
        }
*/
        chosen_item = get_menu_selection(fixed_headers, list, 0, 0);
        //LOGE("\n\n>> Gathering files for chosen_item=%d:\n", chosen_item);
        if (chosen_item == REFRESH)
            continue;
        if (chosen_item == GO_BACK) {
            if (strcmp(custom_path2, "/") == 0)
                break;
            else chosen_item = 0;
        }
        if (chosen_item < numDirs+1 && chosen_item >= 0) {
            // we selected a folder: browse it
            if (chosen_item == 0) {
                // we selected ../
                const char *up_folder = DirName(custom_path2);
                sprintf(custom_path2, "%s", up_folder);
                if (strcmp(custom_path2, "/") != 0)
                    strcat(custom_path2, "/");
            } else {
                // we selected a folder
                sprintf(custom_path2, "%s", dirs[chosen_item - 1]);
            }
            //LOGE("\n\n Selected chosen_item=%d is: %s\n\n", chosen_item, custom_path2);

            // mount known volumes before browsing folders
            if (is_data_media_volume_path(custom_path2) && ensure_path_mounted("/data") != 0)
                continue;
            else if (volume_for_path(custom_path2) != NULL && ensure_path_mounted(custom_path2) != 0)
                continue;

            // we're now in a mounted path or ramdisk folder: browse selected folder
            sprintf(custom_path, "%s", custom_path2);
            fixed_headers[j] = custom_path;
            dir_len = strlen(custom_path);
            numDirs = 0;
            numFiles = 0;
            free_string_array(list);
            free_string_array(files);
            free_string_array(dirs);
            dirs = gather_files(custom_path, NULL, &numDirs);
            files = gather_files(custom_path, ".zip", &numFiles);
            total = numFiles + numDirs;
            list = (char**) malloc((total + 2) * sizeof(char*));
            list[0] = strdup("../");
            list[total+1] = NULL;
                
            //LOGE(">> Dirs (num=%d):\n", numDirs);
            for(i=1; i < numDirs+1; i++) {
                list[i] = strdup(dirs[i-1] + dir_len);
                //LOGE("list[%d]=%s\n", i, list[i]);
            }
            //LOGE("\n>> Files (num=%d):\n", numFiles);
            for(i=1; i < numFiles+1; i++) {
                list[numDirs+i] = strdup(files[i-1] + dir_len);
                //LOGE("list[%d]=%s\n", numDirs+i, list[numDirs+i]);
            }
        } else if (chosen_item > numDirs && chosen_item < total+1) {
            // we selected a zip file to install
            break;
        }
    }
/*
    LOGE("\n\n>> Selected dir contains:\n");
    for(i=0; i < total+1; i++) {
        LOGE("list[%d]=%s\n", i, list[i]);
    }
*/
    //flashing selected zip file
    if (chosen_item !=  GO_BACK) {
        char tmp[PATH_MAX];
        int confirm;

#ifndef USE_CHINESE_FONT
        sprintf(tmp, "Yes - Install %s", list[chosen_item]);
#else
        sprintf(tmp, "是 - 安装%s", list[chosen_item]);
#endif
        if (install_zip_verify_md5.value) start_md5_verify_thread(files[chosen_item - numDirs - 1]);
        else start_md5_display_thread(files[chosen_item - numDirs - 1]);

#ifndef USE_CHINESE_FONT
        confirm = confirm_selection("Install selected file?", tmp);
#else
        confirm = confirm_selection("安装选择的文件？", tmp);
#endif

        if (install_zip_verify_md5.value) stop_md5_verify_thread();
        else stop_md5_display_thread();

        if (confirm) {
            // when installing from ramdisk paths, do not fail on ensure_path_mounted() commands
            set_ensure_mount_always_true(1);
            install_zip(files[chosen_item - numDirs - 1]);
            set_ensure_mount_always_true(0);
        }
    }
    free_string_array(list);
    free_string_array(files);
    free_string_array(dirs);
    free(fixed_headers);
    return 0;
}
//-------- End Free Browse Mode


/*****************************************/
/*   Custom Backup and Restore Support   */
/*       code written by PhilZ @xda      */
/*        for PhilZ Touch Recovery       */
/*****************************************/

// get mount points for nandroid supported extra partitions
// returns the number of extra partitions we found
// first call must initialize the partitions state, else they can run un-initialized in backup command line calls (nandroid.c)
// always reset backup_state to 0 after use
static int extra_partitions_initialized = 0;
void reset_extra_partitions_state() {
    int i;
    for (i = 0; i < MAX_EXTRA_NANDROID_PARTITIONS; ++i) {
        extra_partition[i].backup_state = 0;
        if (!extra_partitions_initialized)
            extra_partition[i].mount_point[0] = '\0';
    }
    extra_partitions_initialized = 1;
}

int get_extra_partitions_state() {
    if (!extra_partitions_initialized)
        reset_extra_partitions_state();

    int i = 0;
    char *ptr;
    char extra_partitions_prop[PROPERTY_VALUE_MAX];
    property_get("ro.cwm.backup_partitions", extra_partitions_prop, "");

    ptr = strtok(extra_partitions_prop, ", ");
    while (ptr != NULL && i < MAX_EXTRA_NANDROID_PARTITIONS) {
        strcpy(extra_partition[i].mount_point, ptr);
        ptr = strtok(NULL, ", ");
        ++i;
    }

    return i;
}

/*
- set_android_secure_path() should be called each time we want to backup/restore .android_secure
- it will always favour external storage
- get_android_secure_path() always sets it to get_primary_storage_path()
- it will format path to retained android_secure location and set android_secure_ext to 1 or 0
- android_secure_ext = 1, will allow nandroid processing of android_secure partition
- always check android_secure_ext return code before using passed char *and_sec_path as it won't be modified if ignore_android_secure == 1
- to force other storage, user must keep only one .android_secure folder in one of the sdcards
- for /data/media devices, only second storage is allowed, not /sdcard
- custom backup and restore jobs (incl twrp and ors modes) can force .android_secure to be ignored
  this is done by setting ignore_android_secure to 1
- ignore_android_secure is by default 0 and will be reset to 0 by reset_custom_job_settings()
- On restore job: if no android_secure folder is found on any sdcard, restore is skipped.
                  you need to create at least one .android_secure folder on one of the sd cards to restore to
*/
int set_android_secure_path(char *and_sec_path) {
    if (ignore_android_secure)
        return android_secure_ext = 0;

    android_secure_ext = 1;

    struct stat st;
    char buf[80];
    char* path = NULL;
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

    // search second storage path for .android_secure (favour external storage)
    int i = 0;
    if (extra_paths != NULL) {
        while (i < num_extra_volumes && path == NULL) {
            sprintf(buf, "%s/.android_secure", extra_paths[i]);
            if (ensure_path_mounted(buf) == 0 && lstat(buf, &st) == 0)
                path = buf;
            i++;
        }
    }

    // assign primary storage (/sdcard) only if not datamedia and we did not find .android_secure in external storage
    if (path == NULL && !is_data_media()) {
        path = get_android_secure_path();
        if (ensure_path_mounted(path) != 0 || lstat(path, &st) != 0)
            path = NULL;
    }

    if (path == NULL)
        android_secure_ext = 0;
    else strcpy(and_sec_path, path);

    return android_secure_ext;
}

void reset_custom_job_settings(int custom_job) {
    // check if we are setting defaults for custom jobs
    if (custom_job) {
        backup_boot = 1, backup_recovery = 1, backup_system = 1;
        backup_data = 1, backup_cache = 1;
        backup_wimax = 0;
        backup_sdext = 0;
    } else {
        // we are exiting backup jobs, revert to default CWM so that stock Backup / Restore behaves as expected
        backup_boot = 1, backup_recovery = 1, backup_system = 1;
        backup_data = 1, backup_cache = 1;
        backup_wimax = 1;
        backup_sdext = 1;
    }

    // preload: disabled by default to ensure it is never set to 1 on devices without /preload and no need to add extra checks in code
    //          else it will be 1 even for devices without /preload and will block efs backup/restore until we touch the preload menu
    //          or if we add extrac code checks for preload volume
    // modem is disabled from nandroid backups, but can be part of custom backup jobs
    // efs backup is disabled in stock nandroid. In custom Jobs, it must be alone.
    // backup_data_media is always 0. It can be set to 1 only in custom backup and restore menu AND if is_data_media() && !twrp_backup_mode.value
    // in TWRP it is part of backup/restore job
    backup_preload = 0;
    backup_modem = 0;
    backup_radio = 0;
    backup_efs = 0;
    backup_misc = 0;
    backup_data_media = 0;
    reset_extra_partitions_state();
    ignore_android_secure = 0;
    reboot_after_nandroid = 0;
}

static void ui_print_backup_list() {
#ifndef USE_CHINESE_FONT
    ui_print("This will process");
#else
    ui_print("这会操作");
#endif
    if (backup_boot)
        ui_print(" - boot");
    if (backup_recovery)
        ui_print(" - recovery");
    if (backup_system)
        ui_print(" - system");
    if (backup_preload)
        ui_print(" - preload");
    if (backup_data)
        ui_print(" - data");
    if (backup_cache)
        ui_print(" - cache");
    if (backup_sdext)
        ui_print(" - sd-ext");
    if (backup_modem)
        ui_print(" - modem");
    if (backup_radio)
        ui_print(" - radio");
    if (backup_wimax)
        ui_print(" - wimax");
    if (backup_efs)
        ui_print(" - efs");
    if (backup_misc)
        ui_print(" - misc");
    if (backup_data_media)
        ui_print(" - data/media");

    // check extra partitions
    int i;
    int extra_partitions_num = get_extra_partitions_state();
    for (i = 0; i < extra_partitions_num; ++i) {
        if (extra_partition[i].backup_state)
            ui_print(" - %s", extra_partition[i].mount_point);
    }

    ui_print("!\n");
}

void get_cwm_backup_path(const char* backup_volume, char *backup_path) {
    char rom_name[PROPERTY_VALUE_MAX] = "noname";
    get_rom_name(rom_name);

    time_t t = time(NULL);
    struct tm *timeptr = localtime(&t);
    if (timeptr == NULL) {
        struct timeval tp;
        gettimeofday(&tp, NULL);
        if (backup_efs)
            sprintf(backup_path, "%s/%s/%ld", backup_volume, EFS_BACKUP_PATH, tp.tv_sec);
        else
            sprintf(backup_path, "%s/%s/%ld_%s", backup_volume, CWM_BACKUP_PATH, tp.tv_sec, rom_name);
    } else {
        char tmp[PATH_MAX];
        strftime(tmp, sizeof(tmp), "%F.%H.%M.%S", timeptr);
        // this sprintf results in:
        // clockworkmod/custom_backup/%F.%H.%M.%S (time values are populated too)
        if (backup_efs)
            sprintf(backup_path, "%s/%s/%s", backup_volume, EFS_BACKUP_PATH, tmp);
        else
            sprintf(backup_path, "%s/%s/%s_%s", backup_volume, CWM_BACKUP_PATH, tmp, rom_name);
    }
}

void show_twrp_restore_menu(const char* backup_volume) {
    char backup_path[PATH_MAX];
    sprintf(backup_path, "%s/%s/", backup_volume, TWRP_BACKUP_PATH);
    if (ensure_path_mounted(backup_path) != 0) {
        LOGE("Can't mount %s\n", backup_path);
        return;
    }

    static const char* headers[] = {
#ifndef USE_CHINESE_FONT
        "Choose a backup to restore",
#else
        "选择一个备份来恢复",
#endif
        NULL
    };

    char device_id[PROPERTY_VALUE_MAX];
    get_device_id(device_id);
    strcat(backup_path, device_id);

    char* file = choose_file_menu(backup_path, "", headers);
    if (file == NULL) {
        // either no valid files found or we selected no files by pressing back menu
        if (no_files_found)
#ifndef USE_CHINESE_FONT
            ui_print("Nothing to restore in %s !\n", backup_path);
#else
            ui_print("在%s没有可恢复的！\n", backup_path);
#endif
        return;
    }

    char confirm[PATH_MAX];
    char backup_source[PATH_MAX];
    sprintf(backup_source, "%s", DirName(file));
#ifndef USE_CHINESE_FONT
    ui_print("%s will be restored to selected partitions!\n", backup_source);
    sprintf(confirm, "Yes - Restore %s", BaseName(backup_source));
    if (confirm_selection("Restore from this backup ?", confirm))
#else
    ui_print("%s会被恢复到选择的分区！\n", backup_source);
    sprintf(confirm, "是 - 恢复%s", BaseName(backup_source));
    if (confirm_selection("从这个备份恢复？", confirm))
#endif
        twrp_restore(backup_source);

    free(file);
}

static void custom_restore_handler(const char* backup_volume, const char* backup_folder) {
    char backup_path[PATH_MAX];
    char tmp[PATH_MAX];
    char backup_source[PATH_MAX];
    char* file = NULL;
#ifndef USE_CHINESE_FONT
    char* confirm_install = "Restore from this backup?";
    static const char* headers[] = {"Choose a backup to restore", NULL};
#else
    char* confirm_install = "从这个备份恢复？";
    static const char* headers[] = {"选择一个备份来恢复", NULL};
#endif

    sprintf(backup_path, "%s/%s", backup_volume, backup_folder);
    if (ensure_path_mounted(backup_path) != 0) {
        LOGE("Can't mount %s\n", backup_path);
        return;
    }

    if (backup_efs == RESTORE_EFS_IMG) {
        if (volume_for_path("/efs") == NULL) {
            LOGE("No /efs partition to flash\n");
            return;
        }
        file = choose_file_menu(backup_path, ".img", headers);
        if (file == NULL) {
            // either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
#ifndef USE_CHINESE_FONT
                ui_print("Nothing to restore in %s !\n", backup_path);
#else
                ui_print("在%s没有可恢复的！\n", backup_path);
#endif
            return;
        }

        // restore efs raw image
        sprintf(backup_source, "%s", BaseName(file));
#ifndef USE_CHINESE_FONT
        ui_print("%s will be flashed to /efs!\n", backup_source);
        sprintf(tmp, "Yes - Restore %s", backup_source);
#else
        ui_print("%s会被刷入到/efs!\n", backup_source);
        sprintf(tmp, "是 - 恢复%s", backup_source);
#endif
        if (confirm_selection(confirm_install, tmp))
            dd_raw_restore_handler(file, "/efs");
    } else if (backup_efs == RESTORE_EFS_TAR) {
        if (volume_for_path("/efs") == NULL) {
            LOGE("No /efs partition to flash\n");
            return;
        }

        file = choose_file_menu(backup_path, NULL, headers);
        if (file == NULL) {
            // either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
#ifndef USE_CHINESE_FONT
                ui_print("在%s没有可恢复的！\n", backup_path);
#else

#endif
            return;
        }

        // ensure there is no efs.img file in same folder (as nandroid_restore_partition_extended will force it to be restored)
        sprintf(tmp, "%s/efs.img", file);
        if (file_found(tmp)) {
#ifndef USE_CHINESE_FONT
            ui_print("efs.img file detected in %s!\n", file);
            ui_print("Either select efs.img to restore it,\n");
            ui_print("or remove it to restore nandroid source.\n");
#else
            ui_print("在%s发现efs.img文件！\n", file);
            ui_print("选择efs.img来恢复它，\n");
            ui_print("或删除它来恢复nandroid资源\n");
#endif
        } else {
            // restore efs from nandroid tar format
#ifndef USE_CHINESE_FONT
            ui_print("%s会被恢复到/efs！\n", file);
            sprintf(tmp, "是 - 恢复%s", BaseName(file));
#else
            ui_print("%s会被恢复到efs！\n", file);
            sprintf(tmp, "是 - 恢复%s", BaseName(file));
#endif
            if (confirm_selection(confirm_install, tmp))
                nandroid_restore(file, 0, 0, 0, 0, 0, 0);
        }
    } else if (backup_modem == RAW_BIN_FILE) {
        file = choose_file_menu(backup_path, ".bin", headers);
        if (file == NULL) {
            // either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
#ifndef USE_CHINESE_FONT
                ui_print("Nothing to restore in %s !\n", backup_path);
#else
                ui_print("在%s没有可恢复的！\n", backup_path);
#endif
            return;
        }

        // restore modem.bin raw image
        sprintf(backup_source, "%s", BaseName(file));
        Volume *vol = volume_for_path("/modem");
        if (vol != NULL) {
#ifndef USE_CHINESE_FONT
            ui_print("%s will be flashed to /modem!\n", backup_source);
            sprintf(tmp, "Yes - Restore %s", backup_source);
#else
            ui_print("%s会被刷入到/modem!\n", backup_source);
            sprintf(tmp, "是 - 恢复%s", backup_source);
#endif
            if (confirm_selection(confirm_install, tmp))
                dd_raw_restore_handler(file, "/modem");
        } else
            LOGE("no /modem partition to flash\n");
    } else if (backup_radio == RAW_BIN_FILE) {
        file = choose_file_menu(backup_path, ".bin", headers);
        if (file == NULL) {
            // either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
#ifndef USE_CHINESE_FONT
                ui_print("Nothing to restore in %s !\n", backup_path);
#else
                ui_print("在%s没有可恢复的！\n", backup_path);
#endif
            return;
        }

        // restore radio.bin raw image
        sprintf(backup_source, "%s", BaseName(file));
        Volume *vol = volume_for_path("/radio");
        if (vol != NULL) {
#ifndef USE_CHINESE_FONT
            ui_print("%s will be flashed to /radio!\n", backup_source);
            sprintf(tmp, "Yes - Restore %s", backup_source);
#else
            ui_print("%s会被刷入到/radio!\n", backup_source);
            sprintf(tmp, "是 - 恢复%s", backup_source);
#endif
            if (confirm_selection(confirm_install, tmp))
                dd_raw_restore_handler(file, "/radio");
        } else
            LOGE("no /radio partition to flash\n");
    } else {
        // process restore job
        file = choose_file_menu(backup_path, "", headers);
        if (file == NULL) {
            // either no valid files found or we selected no files by pressing back menu
            if (no_files_found)
#ifndef USE_CHINESE_FONT
                ui_print("Nothing to restore in %s !\n", backup_path);
#else
                ui_print("在%s没有可恢复的！\n", backup_path);
#endif
            return;
        }

        sprintf(backup_source, "%s", DirName(file));
#ifndef USE_CHINESE_FONT
        ui_print("%s will be restored to selected partitions!\n", backup_source);
        sprintf(tmp, "Yes - Restore %s", BaseName(backup_source));
#else
        ui_print("%s会被恢复到选择的分区！\n", backup_source);
        sprintf(tmp, "是 - 恢复%s", BaseName(backup_source));
#endif
        if (confirm_selection(confirm_install, tmp)) {
            nandroid_restore(backup_source, backup_boot, backup_system, backup_data, backup_cache, backup_sdext, backup_wimax);
        }
    }

    free(file);
}

/*
* custom backup and restore jobs:
    - At least one partition to restore must be selected
* restore jobs
    - modem.bin and radio.bin file types must be restored alone (available only in custom restore mode)
    - TWRP restore:
        + accepts efs to be restored along other partitions (but modem is never of bin type and preload is always 0)
    - Custom jobs:
        + efs must be restored alone (except for twrp backup jobs)
        + else, all other tasks can be processed
* backup jobs
    - if it is a twrp backup job, we can accept efs with other partitions
    - else, we only accept them separately for custom backup jobs    
*/
static void validate_backup_job(const char* backup_volume, int is_backup) {
    int sum = backup_boot + backup_recovery + backup_system + backup_preload + backup_data +
                backup_cache + backup_sdext + backup_wimax + backup_misc + backup_data_media;

    // add extra partitions to the sum
    int i;
    int extra_partitions_num = get_extra_partitions_state();
    for (i = 0; i < extra_partitions_num; ++i) {
        if (extra_partition[i].backup_state)
            ++sum;
    }

    if (0 == (sum + backup_efs + backup_modem + backup_radio)) {
#ifndef USE_CHINESE_FONT
        ui_print("Select at least one partition to restore!\n");
#else
        ui_print("选择至少一个分区来恢复！\n");
#endif
        return;
    }

    if (is_backup)
    {
        // it is a backup job to validate: ensure default backup handler is not dup before processing
        char backup_path[PATH_MAX] = "";
        ui_print_backup_list();
        int fmt = nandroid_get_default_backup_format();
        if (fmt != NANDROID_BACKUP_FORMAT_TAR && fmt != NANDROID_BACKUP_FORMAT_TGZ) {
            LOGE("Backup format must be tar(.gz)!\n");
        } else if (twrp_backup_mode.value) {
            get_twrp_backup_path(backup_volume, backup_path);
            twrp_backup(backup_path);
        } else if (backup_efs && (sum + backup_modem + backup_radio) != 0) {
#ifndef USE_CHINESE_FONT
            ui_print("efs must be backed up alone!\n");
#else
            ui_print("efs必须被单独备份！\n");
#endif
        } else {
            get_cwm_backup_path(backup_volume, backup_path);
            nandroid_backup(backup_path);
        }
    }
    else {
        // it is a restore job
        if (backup_modem == RAW_BIN_FILE) {
            if (0 != (sum + backup_efs + backup_radio))
#ifndef USE_CHINESE_FONT
                ui_print("modem.bin format must be restored alone!\n");
#else
                ui_print("modem.bin格式必须被单独恢复！\n");
#endif
            else
                custom_restore_handler(backup_volume, MODEM_BIN_PATH);
        }
        else if (backup_radio == RAW_BIN_FILE) {
            if (0 != (sum + backup_efs + backup_modem))
#ifndef USE_CHINESE_FONT
                ui_print("radio.bin format must be restored alone!\n");
#else
                ui_print("radio.bin格式必须被单独恢复！\n");
#endif
            else
                custom_restore_handler(backup_volume, RADIO_BIN_PATH);
        }
        else if (twrp_backup_mode.value)
            show_twrp_restore_menu(backup_volume);
        else if (backup_efs && (sum + backup_modem + backup_radio) != 0)
#ifndef USE_CHINESE_FONT
            ui_print("efs must be restored alone!\n");
#else
            ui_print("efs必须被单独恢复！\n");
#endif
        else if (backup_efs && (sum + backup_modem + backup_radio) == 0)
            custom_restore_handler(backup_volume, EFS_BACKUP_PATH);
        else
            custom_restore_handler(backup_volume, CWM_BACKUP_PATH);
    }
}

#define TOP_CUSTOM_JOB_MENU_ITEMS 16
void custom_restore_menu(const char* backup_volume) {
    const char* headers[] = {
#ifndef USE_CHINESE_FONT
            "Custom restore job from",
#else
            "自定义恢复工作",
#endif
            backup_volume,
            NULL
    };

    int list_items_num = TOP_CUSTOM_JOB_MENU_ITEMS + MAX_EXTRA_NANDROID_PARTITIONS + 1;
    char* list[list_items_num];
    int i;
    for (i = 0; i < list_items_num; ++i) {
        list[i] = NULL;
    }

    char menu_item_tmp[MENU_MAX_COLS];
    char tmp[PATH_MAX];
    int extra_partitions_num = get_extra_partitions_state();

    is_custom_backup = 1;
    reset_custom_job_settings(1);
    for (;;)
    {
        for (i = 0; i < list_items_num; ++i) {
            if (list[i])
                free(list[i]);
                list[i] = NULL;
        }

#ifndef USE_CHINESE_FONT
        list[LIST_ITEM_VALIDATE] = strdup(">> Start Custom Restore Job");

        if (reboot_after_nandroid) ui_format_gui_menu(menu_item_tmp, ">> Reboot once done", "(x)");
        else ui_format_gui_menu(menu_item_tmp, ">> Reboot once done", "( )");
#else
        list[LIST_ITEM_VALIDATE] = strdup(">> 开始自定义恢复工作");

        if (reboot_after_nandroid) ui_format_gui_menu(menu_item_tmp, ">> 完成后重启", "(x)");
        else ui_format_gui_menu(menu_item_tmp, ">> 完成后重启", "( )");
#endif
        list[LIST_ITEM_REBOOT] = strdup(menu_item_tmp);

        if (volume_for_path(BOOT_PARTITION_MOUNT_POINT) != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_boot) ui_format_gui_menu(menu_item_tmp, "Restore boot", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore boot", "( )");
#else
            if (backup_boot) ui_format_gui_menu(menu_item_tmp, "恢复boot", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复boot", "( )");
#endif
            list[LIST_ITEM_BOOT] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_BOOT] = NULL;
        }

        if (volume_for_path("/recovery") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_recovery) ui_format_gui_menu(menu_item_tmp, "Restore recovery", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore recovery", "( )");
#else
            if (backup_recovery) ui_format_gui_menu(menu_item_tmp, "恢复recovery", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复recovery", "( )");
#endif
            list[LIST_ITEM_RECOVERY] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_RECOVERY] = NULL;
        }

#ifndef USE_CHINESE_FONT
        if (backup_system) ui_format_gui_menu(menu_item_tmp, "Restore system", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Restore system", "( )");
#else
        if (backup_system) ui_format_gui_menu(menu_item_tmp, "恢复system", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "恢复system", "( )");
#endif
        list[LIST_ITEM_SYSTEM] = strdup(menu_item_tmp);

        if (volume_for_path("/preload") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_preload) ui_format_gui_menu(menu_item_tmp, "Restore preload", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore preload", "( )");
#else
            if (backup_preload) ui_format_gui_menu(menu_item_tmp, "恢复preload", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复preload", "( )");
#endif
            list[LIST_ITEM_PRELOAD] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_PRELOAD] = NULL;
        }

#ifndef USE_CHINESE_FONT
        if (backup_data) ui_format_gui_menu(menu_item_tmp, "Restore data", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Restore data", "( )");
#else
        if (backup_data) ui_format_gui_menu(menu_item_tmp, "恢复data", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "恢复data", "( )");
#endif
        list[LIST_ITEM_DATA] = strdup(menu_item_tmp);

        set_android_secure_path(tmp);
        if (backup_data && android_secure_ext)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(menu_item_tmp, "Restore and-sec", DirName(tmp));
        else ui_format_gui_menu(menu_item_tmp, "Restore and-sec", "( )");
#else
            ui_format_gui_menu(menu_item_tmp, "恢复and-sec", DirName(tmp));
        else ui_format_gui_menu(menu_item_tmp, "恢复and-sec", "( )");
#endif
        list[LIST_ITEM_ANDSEC] = strdup(menu_item_tmp);

#ifndef USE_CHINESE_FONT
        if (backup_cache) ui_format_gui_menu(menu_item_tmp, "Restore cache", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Restore cache", "( )");
#else
        if (backup_cache) ui_format_gui_menu(menu_item_tmp, "恢复cache", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "恢复cache", "( )");
#endif
        list[LIST_ITEM_CACHE] = strdup(menu_item_tmp);

#ifndef USE_CHINESE_FONT
        if (backup_sdext) ui_format_gui_menu(menu_item_tmp, "Restore sd-ext", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Restore sd-ext", "( )");
#else
        if (backup_sdext) ui_format_gui_menu(menu_item_tmp, "恢复sd-ext", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "恢复sd-ext", "( )");
#endif
        list[LIST_ITEM_SDEXT] = strdup(menu_item_tmp);

        if (volume_for_path("/modem") != NULL) {
            if (backup_modem == RAW_IMG_FILE)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Restore modem [.img]", "(x)");
            else if (backup_modem == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "Restore modem [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore modem", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "恢复modem [.img]", "(x)");
            else if (backup_modem == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "恢复modem [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复modem", "( )");
#endif
            list[LIST_ITEM_MODEM] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_MODEM] = NULL;
        }

        if (volume_for_path("/radio") != NULL) {
            if (backup_radio == RAW_IMG_FILE)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Restore radio [.img]", "(x)");
            else if (backup_radio == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "Restore radio [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore radio", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "恢复radio [.img]", "(x)");
            else if (backup_radio == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "恢复radio [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复radio", "( )");
#endif
            list[LIST_ITEM_RADIO] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_RADIO] = NULL;
        }

        if (volume_for_path("/efs") != NULL) {
            if (backup_efs == RESTORE_EFS_IMG)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Restore efs [.img]", "(x)");
            else if (backup_efs == RESTORE_EFS_TAR)
                ui_format_gui_menu(menu_item_tmp, "Restore efs [.tar]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore efs", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "恢复efs [.img]", "(x)");
            else if (backup_efs == RESTORE_EFS_TAR)
                ui_format_gui_menu(menu_item_tmp, "恢复efs [.tar]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复efs", "( )");
#endif
            list[LIST_ITEM_EFS] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_EFS] = NULL;
        }

        if (volume_for_path("/misc") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_misc) ui_format_gui_menu(menu_item_tmp, "Restore misc", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore misc", "( )");
#else
            if (backup_misc) ui_format_gui_menu(menu_item_tmp, "恢复misc", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复misc", "( )");
#endif
            list[LIST_ITEM_MISC] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_MISC] = NULL;
        }

        if (is_data_media() && !twrp_backup_mode.value) {
            if (backup_data_media)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Restore /data/media", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore /data/media", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "恢复/data/media", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复/data/media", "( )");
#endif
            list[LIST_ITEM_DATAMEDIA] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_DATAMEDIA] = NULL;
        }

        if (volume_for_path("/wimax") != NULL && !twrp_backup_mode.value) {
            if (backup_wimax)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Restore WiMax", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Restore WiMax", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "恢复WiMax", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "恢复WiMax", "( )");
#endif
            list[LIST_ITEM_WIMAX] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_WIMAX] = NULL;
        }

        // show extra partitions menu if available
        for (i = 0; i < extra_partitions_num; ++i)
        {
            if (volume_for_path(extra_partition[i].mount_point) != NULL) {
#ifndef USE_CHINESE_FONT
                sprintf(tmp, "Restore %s", extra_partition[i].mount_point);
#else
                sprintf(tmp, "恢复%s", extra_partition[i].mount_point);
#endif
                if (extra_partition[i].backup_state)
                    ui_format_gui_menu(menu_item_tmp, tmp, "(x)");
                else ui_format_gui_menu(menu_item_tmp, tmp, "( )");
                list[TOP_CUSTOM_JOB_MENU_ITEMS + i] = strdup(menu_item_tmp);
            } else {
                list[TOP_CUSTOM_JOB_MENU_ITEMS + i] = NULL;
            }
        }

        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item < 0)
            break;

        switch (chosen_item)
        {
            case LIST_ITEM_VALIDATE:
                validate_backup_job(backup_volume, 0);
                break;
            case LIST_ITEM_REBOOT:
                reboot_after_nandroid ^= 1;
                break;
            case LIST_ITEM_BOOT:
                backup_boot ^= 1;
                break;
            case LIST_ITEM_RECOVERY:
                backup_recovery ^= 1;
                break;
            case LIST_ITEM_SYSTEM:
                backup_system ^= 1;
                break;
            case LIST_ITEM_PRELOAD:
                backup_preload ^= 1;
                break;
            case LIST_ITEM_DATA:
                backup_data ^= 1;
                break;
            case LIST_ITEM_ANDSEC:
                // if !backup_data, it will not be processed in any-case by nandroid operations
                // if there are extra voldmanaged volumes, warn to force restore .android_secure from one of them
                ignore_android_secure ^= 1;
                if (!ignore_android_secure && get_num_extra_volumes() != 0)
#ifndef USE_CHINESE_FONT
                    ui_print("To force restore to 2nd storage, keep only one .android_secure folder\n");
#else
                    ui_print("强制恢复到第二存储，只保留一个.android_secure文件夹\n");
#endif
                break;
            case LIST_ITEM_CACHE:
                backup_cache ^= 1;
                break;
            case LIST_ITEM_SDEXT:
                backup_sdext ^= 1;
                break;
            case LIST_ITEM_MODEM:
                backup_modem++;
                if (backup_modem > 2)
                    backup_modem = 0;
                if (twrp_backup_mode.value && backup_modem == RAW_BIN_FILE)
                    backup_modem = 0;
                break;
            case LIST_ITEM_RADIO:
                backup_radio++;
                if (backup_radio > 2)
                    backup_radio = 0;
                if (twrp_backup_mode.value && backup_radio == RAW_BIN_FILE)
                    backup_radio = 0;
                break;
            case LIST_ITEM_EFS:
                backup_efs++;
                if (backup_efs > 2)
                    backup_efs = 0;
                if (twrp_backup_mode.value && backup_efs == RESTORE_EFS_IMG)
                    backup_efs = 0;
                break;
            case LIST_ITEM_MISC:
                backup_misc ^= 1;
                break;
            case LIST_ITEM_DATAMEDIA:
                if (is_data_media() && !twrp_backup_mode.value)
                    backup_data_media ^= 1;
                break;
            case LIST_ITEM_WIMAX:
                if (!twrp_backup_mode.value)
                    backup_wimax ^= 1;
                break;
            default: // extra partitions toggle
                extra_partition[chosen_item - TOP_CUSTOM_JOB_MENU_ITEMS].backup_state ^= 1;
                break;
        }
    }

    for (i = 0; i < list_items_num; ++i) {
        if (list[i])
            free(list[i]);
    }
    is_custom_backup = 0;
    reset_custom_job_settings(0);
}

void custom_backup_menu(const char* backup_volume)
{
    const char* headers[] = {
#ifndef USE_CHINESE_FONT
            "Custom backup job to",
#else
            "自定义备份工作",
#endif
            backup_volume,
            NULL
    };

    int list_items_num = TOP_CUSTOM_JOB_MENU_ITEMS + MAX_EXTRA_NANDROID_PARTITIONS + 1;
    char* list[list_items_num];
    int i;
    for (i = 0; i < list_items_num; ++i) {
        list[i] = NULL;
    }

    char menu_item_tmp[MENU_MAX_COLS];
    char tmp[PATH_MAX];
    int extra_partitions_num = get_extra_partitions_state();

    is_custom_backup = 1;
    reset_custom_job_settings(1);
    for (;;)
    {
        for (i = 0; i < list_items_num; ++i) {
            if (list[i])
                free(list[i]);
                list[i] = NULL;
        }

#ifndef USE_CHINESE_FONT
        list[LIST_ITEM_VALIDATE] = strdup(">> Start Custom Backup Job");

        if (reboot_after_nandroid) ui_format_gui_menu(menu_item_tmp, ">> Reboot once done", "(x)");
        else ui_format_gui_menu(menu_item_tmp, ">> Reboot once done", "( )");
#else
        list[LIST_ITEM_VALIDATE] = strdup(">> 开始自定义备份工作");

        if (reboot_after_nandroid) ui_format_gui_menu(menu_item_tmp, ">> 完成后重启", "(x)");
        else ui_format_gui_menu(menu_item_tmp, ">> 完成后重启", "( )");
#endif
        list[LIST_ITEM_REBOOT] = strdup(menu_item_tmp);

        if (volume_for_path(BOOT_PARTITION_MOUNT_POINT) != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_boot) ui_format_gui_menu(menu_item_tmp, "Backup boot", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup boot", "( )");
#else
            if (backup_boot) ui_format_gui_menu(menu_item_tmp, "备份boot", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份boot", "( )");
#endif
            list[LIST_ITEM_BOOT] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_BOOT] = NULL;
        }

        if (volume_for_path("/recovery") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_recovery) ui_format_gui_menu(menu_item_tmp, "Backup recovery", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup recovery", "( )");
#else
            if (backup_recovery) ui_format_gui_menu(menu_item_tmp, "备份recovery", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份recovery", "( )");
#endif
            list[LIST_ITEM_RECOVERY] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_RECOVERY] = NULL;
        }

#ifndef USE_CHINESE_FONT
        if (backup_system) ui_format_gui_menu(menu_item_tmp, "Backup system", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Backup system", "( )");
#else
        if (backup_system) ui_format_gui_menu(menu_item_tmp, "备份system", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "备份system", "( )");
#endif
        list[LIST_ITEM_SYSTEM] = strdup(menu_item_tmp);

        if (volume_for_path("/preload") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_preload) ui_format_gui_menu(menu_item_tmp, "Backup preload", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup preload", "( )");
#else
            if (backup_preload) ui_format_gui_menu(menu_item_tmp, "备份preload", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份preload", "( )");
#endif
            list[LIST_ITEM_PRELOAD] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_PRELOAD] = NULL;
        }

#ifndef USE_CHINESE_FONT
        if (backup_data) ui_format_gui_menu(menu_item_tmp, "Backup data", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Backup data", "( )");
#else
        if (backup_data) ui_format_gui_menu(menu_item_tmp, "备份data", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "备份data", "( )");
#endif
        list[LIST_ITEM_DATA] = strdup(menu_item_tmp);

        set_android_secure_path(tmp);
        if (backup_data && android_secure_ext)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(menu_item_tmp, "Backup and-sec", DirName(tmp));
        else ui_format_gui_menu(menu_item_tmp, "Backup and-sec", "( )");
#else
            ui_format_gui_menu(menu_item_tmp, "备份and-sec", DirName(tmp));
        else ui_format_gui_menu(menu_item_tmp, "备份and-sec", "( )");
#endif
        list[LIST_ITEM_ANDSEC] = strdup(menu_item_tmp);

#ifndef USE_CHINESE_FONT
        if (backup_cache) ui_format_gui_menu(menu_item_tmp, "Backup cache", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Backup cache", "( )");
#else
        if (backup_cache) ui_format_gui_menu(menu_item_tmp, "备份cache", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "备份cache", "( )");
#endif
        list[LIST_ITEM_CACHE] = strdup(menu_item_tmp);

#ifndef USE_CHINESE_FONT
        if (backup_sdext) ui_format_gui_menu(menu_item_tmp, "Backup sd-ext", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "Backup sd-ext", "( )");
#else
        if (backup_sdext) ui_format_gui_menu(menu_item_tmp, "备份sd-ext", "(x)");
        else ui_format_gui_menu(menu_item_tmp, "备份sd-ext", "( )");
#endif
        list[LIST_ITEM_SDEXT] = strdup(menu_item_tmp);

        if (volume_for_path("/modem") != NULL) {
            if (backup_modem == RAW_IMG_FILE)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Backup modem [.img]", "(x)");
            else if (backup_modem == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "Backup modem [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup modem", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "备份modem [.img]", "(x)");
            else if (backup_modem == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "备份modem [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份modem", "( )");
#endif
            list[LIST_ITEM_MODEM] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_MODEM] = NULL;
        }

        if (volume_for_path("/radio") != NULL) {
            if (backup_radio == RAW_IMG_FILE)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Backup radio [.img]", "(x)");
            else if (backup_radio == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "Backup radio [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup radio", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "备份radio [.img]", "(x)");
            else if (backup_radio == RAW_BIN_FILE)
                ui_format_gui_menu(menu_item_tmp, "备份radio [.bin]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份radio", "( )");
#endif
            list[LIST_ITEM_RADIO] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_RADIO] = NULL;
        }

        if (volume_for_path("/efs") != NULL) {
            if (backup_efs == RESTORE_EFS_IMG)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Backup efs [.img]", "(x)");
            else if (backup_efs == RESTORE_EFS_TAR)
                ui_format_gui_menu(menu_item_tmp, "Backup efs [.tar]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup efs", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "备份efs [.img]", "(x)");
            else if (backup_efs == RESTORE_EFS_TAR)
                ui_format_gui_menu(menu_item_tmp, "备份efs [.tar]", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份efs", "( )");
#endif
            list[LIST_ITEM_EFS] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_EFS] = NULL;
        }

        if (volume_for_path("/misc") != NULL) {
#ifndef USE_CHINESE_FONT
            if (backup_misc) ui_format_gui_menu(menu_item_tmp, "Backup misc", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup misc", "( )");
#else
            if (backup_misc) ui_format_gui_menu(menu_item_tmp, "备份misc", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份misc", "( )");
#endif
            list[LIST_ITEM_MISC] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_MISC] = NULL;
        }

        if (is_data_media() && !twrp_backup_mode.value) {
            if (backup_data_media)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Backup /data/media", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup /data/media", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "备份/data/media", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份/data/media", "( )");
#endif
            list[LIST_ITEM_DATAMEDIA] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_DATAMEDIA] = NULL;
        }

        if (volume_for_path("/wimax") != NULL && !twrp_backup_mode.value) {
            if (backup_wimax)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(menu_item_tmp, "Backup WiMax", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "Backup WiMax", "( )");
#else
                ui_format_gui_menu(menu_item_tmp, "备份WiMax", "(x)");
            else ui_format_gui_menu(menu_item_tmp, "备份WiMax", "( )");
#endif
            list[LIST_ITEM_WIMAX] = strdup(menu_item_tmp);
        } else {
            list[LIST_ITEM_WIMAX] = NULL;
        }

        // show extra partitions menu if available
        for (i = 0; i < extra_partitions_num; ++i)
        {
            if (volume_for_path(extra_partition[i].mount_point) != NULL) {
#ifndef USE_CHINESE_FONT
                sprintf(tmp, "Backup %s", extra_partition[i].mount_point);
#else
                sprintf(tmp, "备份%s", extra_partition[i].mount_point);
#endif
                if (extra_partition[i].backup_state)
                    ui_format_gui_menu(menu_item_tmp, tmp, "(x)");
                else ui_format_gui_menu(menu_item_tmp, tmp, "( )");
                list[TOP_CUSTOM_JOB_MENU_ITEMS + i] = strdup(menu_item_tmp);
            } else {
                list[TOP_CUSTOM_JOB_MENU_ITEMS + i] = NULL;
            }
        }

        int chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item < 0)
            break;

        switch (chosen_item)
        {
            case LIST_ITEM_VALIDATE:
                validate_backup_job(backup_volume, 1);
                break;
            case LIST_ITEM_REBOOT:
                reboot_after_nandroid ^= 1;
                break;
            case LIST_ITEM_BOOT:
                backup_boot ^= 1;
                break;
            case LIST_ITEM_RECOVERY:
                backup_recovery ^= 1;
                break;
            case LIST_ITEM_SYSTEM:
                backup_system ^= 1;
                break;
            case LIST_ITEM_PRELOAD:
                backup_preload ^= 1;
                break;
            case LIST_ITEM_DATA:
                backup_data ^= 1;
                break;
            case LIST_ITEM_ANDSEC:
                // if !backup_data, it will not be processed in any-case by nandroid operations
                // if there are extra voldmanaged volumes, warn to force backup .android_secure from one of them
                ignore_android_secure ^= 1;
                if (!ignore_android_secure && get_num_extra_volumes() != 0)
#ifndef USE_CHINESE_FONT
                    ui_print("To force backup from 2nd storage, keep only one .android_secure folder\n");
#else
                    ui_print("强制备份第二存储，只保留一个.android_secure文件夹\n");
#endif
                break;
            case LIST_ITEM_CACHE:
                backup_cache ^= 1;
                break;
            case LIST_ITEM_SDEXT:
                backup_sdext ^= 1;
                break;
            case LIST_ITEM_MODEM:
                backup_modem ^= 1;
                break;
            case LIST_ITEM_RADIO:
                backup_radio ^= 1;
                break;
            case LIST_ITEM_EFS:
                backup_efs ^= 1;
                break;
            case LIST_ITEM_MISC:
                backup_misc ^= 1;
                break;
            case LIST_ITEM_DATAMEDIA:
                if (is_data_media() && !twrp_backup_mode.value)
                    backup_data_media ^= 1;
                break;
            case LIST_ITEM_WIMAX:
                if (!twrp_backup_mode.value)
                    backup_wimax ^= 1;
                break;
            default: // extra partitions toggle
                extra_partition[chosen_item - TOP_CUSTOM_JOB_MENU_ITEMS].backup_state ^= 1;
                break;
        }
    }

    for (i = 0; i < list_items_num; ++i) {
        if (list[i])
            free(list[i]);
    }
    is_custom_backup = 0;
    reset_custom_job_settings(0);
}
//------- end Custom Backup and Restore functions


/*****************************************/
/* Part of TWRP Backup & Restore Support */
/*    Original CWM port by PhilZ @xda    */
/*    Original TWRP code by Dees_Troy    */
/*         (dees_troy at yahoo)          */
/*****************************************/
int check_twrp_md5sum(const char* backup_path) {
    char md5file[PATH_MAX];
    char** files;
    int numFiles = 0;

#ifndef USE_CHINESE_FONT
    ui_print("\n>> Checking MD5 sums...\n");
#else
    ui_print("\n>> 检查MD5...\n");
#endif
    ensure_path_mounted(backup_path);
    files = gather_files(backup_path, "", &numFiles);
    if (numFiles == 0) {
        LOGE("No files found in %s\n", backup_path);
        free_string_array(files);
        return -1;
    }

    int i = 0;
    for(i = 0; i < numFiles; i++) {
        // exclude md5 files
        char *str = strstr(files[i], ".md5");
        if (str != NULL && strcmp(str, ".md5") == 0)
            continue;

        ui_quick_reset_and_show_progress(1, 0);
        ui_print("   - %s\n", BaseName(files[i]));
        sprintf(md5file, "%s.md5", files[i]);
        if (verify_md5digest(files[i], md5file) != 0) {
            LOGE("md5sum error!\n");
            ui_reset_progress();
            free_string_array(files);
            return -1;
        }
    }

#ifndef USE_CHINESE_FONT
    ui_print("MD5 sum ok.\n");
#else
    ui_print("MD5校验正确。\n");
#endif
    ui_reset_progress();
    free_string_array(files);
    return 0;
}

int gen_twrp_md5sum(const char* backup_path) {
    char md5file[PATH_MAX];
    int numFiles = 0;

#ifndef USE_CHINESE_FONT
    ui_print("\n>> Generating md5 sum...\n");
#else
    ui_print("\n>> 正在生成md5校验...\n");
#endif
    ensure_path_mounted(backup_path);

    // this will exclude subfolders!
    char** files = gather_files(backup_path, "", &numFiles);
    if (numFiles == 0) {
        LOGE("No files found in backup path %s\n", backup_path);
        free_string_array(files);
        return -1;
    }

    int i = 0;
    for(i = 0; i < numFiles; i++) {
        ui_quick_reset_and_show_progress(1, 0);
        ui_print("   - %s\n", BaseName(files[i]));
        sprintf(md5file, "%s.md5", files[i]);
        if (write_md5digest(files[i], md5file, 0) < 0) {
            LOGE("Error while generating md5sum!\n");
            ui_reset_progress();
            free_string_array(files);
            return -1;
        }
    }

#ifndef USE_CHINESE_FONT
    ui_print("MD5 sum created.\n");
#else
    ui_print("MD5校验生成结束。\n");
#endif
    ui_reset_progress();
    free_string_array(files);
    return 0;
}

// Device ID functions
static void sanitize_device_id(char *device_id) {
    const char* whitelist ="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890-._";
    char str[PROPERTY_VALUE_MAX];
    char* c = str;

    strcpy(str, device_id);
    char tmp[PROPERTY_VALUE_MAX];
    memset(tmp, 0, sizeof(tmp));
    while (*c) {
        if (strchr(whitelist, *c))
            strncat(tmp, c, 1);
        c++;
    }
    strcpy(device_id, tmp);
    return;
}

#define CMDLINE_SERIALNO        "androidboot.serialno="
#define CMDLINE_SERIALNO_LEN    (strlen(CMDLINE_SERIALNO))
#define CPUINFO_SERIALNO        "Serial"
#define CPUINFO_SERIALNO_LEN    (strlen(CPUINFO_SERIALNO))
#define CPUINFO_HARDWARE        "Hardware"
#define CPUINFO_HARDWARE_LEN    (strlen(CPUINFO_HARDWARE))

void get_device_id(char *device_id) {
#ifdef TW_USE_MODEL_HARDWARE_ID_FOR_DEVICE_ID
    // Now we'll use product_model_hardwareid as device id
    char model_id[PROPERTY_VALUE_MAX];
    property_get("ro.product.model", model_id, "error");
    if (strcmp(model_id, "error") != 0) {
        LOGI("=> product model: '%s'\n", model_id);
        // Replace spaces with underscores
        size_t i;
        for (i = 0; i < strlen(model_id); i++) {
            if (model_id[i] == ' ')
                model_id[i] = '_';
        }
        strcpy(device_id, model_id);
        sanitize_device_id(device_id);
        LOGI("=> using product model for device id: '%s'\n", device_id);
        return;
    }
#endif

    // First try system properties
    property_get("ro.serialno", device_id, "");
    if (strlen(device_id) != 0) {
        sanitize_device_id(device_id);
        LOGI("Using ro.serialno='%s'\n", device_id);
        return;
    }
    property_get("ro.boot.serialno", device_id, "");
    if (strlen(device_id) != 0) {
        sanitize_device_id(device_id);
        LOGI("Using ro.boot.serialno='%s'\n", device_id);
        return;
    }

    // device_id not found, looking elsewhere
    FILE *fp;
    char line[2048];
    char hardware_id[32];
    char* token;

    // Assign a blank device_id to start with
    device_id[0] = 0;

    // Try the cmdline to see if the serial number was supplied
    fp = fopen("/proc/cmdline", "rt");
    if (fp != NULL) {
        // First step, read the line. For cmdline, it's one long line
        LOGI("Checking cmdline for serialno...\n");
        fgets(line, sizeof(line), fp);
        fclose(fp);

        // Now, let's tokenize the string
        token = strtok(line, " ");
        if (strlen(token) > PROPERTY_VALUE_MAX)
            token[PROPERTY_VALUE_MAX] = 0;

        // Let's walk through the line, looking for the CMDLINE_SERIALNO token
        while (token) {
            // We don't need to verify the length of token, because if it's too short, it will mismatch CMDLINE_SERIALNO at the NULL
            if (memcmp(token, CMDLINE_SERIALNO, CMDLINE_SERIALNO_LEN) == 0) {
                // We found the serial number!
                strcpy(device_id, token + CMDLINE_SERIALNO_LEN);
                sanitize_device_id(device_id);
                LOGI("Using serialno='%s'\n", device_id);
                return;
            }
            token = strtok(NULL, " ");
        }
    }

    // Now we'll try cpuinfo for a serial number (we shouldn't reach here as it gives wired output)
    fp = fopen("/proc/cpuinfo", "rt");
    if (fp != NULL) {
        LOGI("Checking cpuinfo...\n");
        // First step, read the line.
        while (fgets(line, sizeof(line), fp) != NULL) {
            if (memcmp(line, CPUINFO_SERIALNO, CPUINFO_SERIALNO_LEN) == 0) {
                // check the beginning of the line for "Serial"
                // We found the serial number!
                token = line + CPUINFO_SERIALNO_LEN; // skip past "Serial"
                while ((*token > 0 && *token <= 32 ) || *token == ':') {
                    // skip over all spaces and the colon
                    token++;
                }

                if (*token != 0) {
                    token[30] = 0;
                    if (token[strlen(token)-1] == 10) {
                        // checking for endline chars and dropping them from the end of the string if needed
                        char tmp[PROPERTY_VALUE_MAX];
                        memset(tmp, 0, sizeof(tmp));
                        strncpy(tmp, token, strlen(token) - 1);
                        strcpy(device_id, tmp);
                    } else {
                        strcpy(device_id, token);
                    }
                    fclose(fp);
                    sanitize_device_id(device_id);
                    LOGI("=> Using cpuinfo serialno: '%s'\n", device_id);
                    return;
                }
            } else if (memcmp(line, CPUINFO_HARDWARE, CPUINFO_HARDWARE_LEN) == 0) {
                // We're also going to look for the hardware line in cpuinfo and save it for later in case we don't find the device ID
                // We found the hardware ID
                token = line + CPUINFO_HARDWARE_LEN; // skip past "Hardware"
                while ((*token > 0 && *token <= 32 ) || *token == ':') {
                    // skip over all spaces and the colon
                    token++;
                }

                if (*token != 0) {
                    token[30] = 0;
                    if (token[strlen(token)-1] == 10) { // checking for endline chars and dropping them from the end of the string if needed
                        memset(hardware_id, 0, sizeof(hardware_id));
                        strncpy(hardware_id, token, strlen(token) - 1);
                    } else {
                        strcpy(hardware_id, token);
                    }
                    LOGI("=> hardware id from cpuinfo: '%s'\n", hardware_id);
                }
            }
        }
        fclose(fp);
    }

    if (hardware_id[0] != 0) {
        LOGW("\nusing hardware id for device id: '%s'\n", hardware_id);
        strcpy(device_id, hardware_id);
        sanitize_device_id(device_id);
        return;
    }

    strcpy(device_id, "serialno");
    LOGE("=> device id not found, using '%s'\n", device_id);
    return;
}
// End of Device ID functions

void get_twrp_backup_path(const char* backup_volume, char *backup_path) {
    char rom_name[PROPERTY_VALUE_MAX] = "noname";
    get_rom_name(rom_name);

    char device_id[PROPERTY_VALUE_MAX];
    get_device_id(device_id);

    time_t t = time(NULL);
    struct tm *timeptr = localtime(&t);
    if (timeptr == NULL) {
        struct timeval tp;
        gettimeofday(&tp, NULL);
        sprintf(backup_path, "%s/%s/%s/%ld_%s", backup_volume, TWRP_BACKUP_PATH, device_id, tp.tv_sec, rom_name);
    } else {
        char tmp[PATH_MAX];
        strftime(tmp, sizeof(tmp), "%F.%H.%M.%S", timeptr);
        // this sprintf results in:
        // clockworkmod/backup/%F.%H.%M.%S (time values are populated too)
        sprintf(backup_path, "%s/%s/%s/%s_%s", backup_volume, TWRP_BACKUP_PATH, device_id, tmp, rom_name);
    }
}
//-------- End TWRP Backup and Restore Options
//-------------- End PhilZ Touch Special Backup and Restore menu and handlers

// launch aromafm.zip from default locations
static int default_aromafm(const char* root) {
    char aroma_file[PATH_MAX];
    sprintf(aroma_file, "%s/%s", root, AROMA_FM_PATH);

    if (file_found(aroma_file)) {
        // will ensure_path_mounted(aroma_file)
#ifdef PHILZ_TOUCH_RECOVERY
        force_wait = -1;
#endif
        install_zip(aroma_file);
        return 0;
    }
    return -1;
}

void run_aroma_browser() {
    // look for AROMA_FM_PATH in storage paths
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();
    int ret = -1;
    int i = 0;

    // vold managed volumes need to be mounted as aromafm cannot mount them (they are not set into /etc/fstab)
    vold_mount_all();
    ret = default_aromafm(get_primary_storage_path());
    if (extra_paths != NULL) {
        i = 0;
        while (ret && i < num_extra_volumes) {
            ret = default_aromafm(extra_paths[i]);
            ++i;
        }
    }
    if (ret != 0)
#ifndef USE_CHINESE_FONT
        ui_print("No %s in storage paths\n", AROMA_FM_PATH);
#else
        ui_print("在存储路径中没有%s\n", AROMA_FM_PATH);
#endif
}
//------ end aromafm launcher functions


//import / export recovery and theme settings
static void load_theme_settings() {
#ifdef PHILZ_TOUCH_RECOVERY
    selective_load_theme_settings();
#else
    static const char* headers[] = {
#ifndef USE_CHINESE_FONT
        "Select a theme to load",
#else
        "选择一个主题来加载",
#endif
        "",
        NULL
    };

    char themes_dir[PATH_MAX];
    char* theme_file;

    sprintf(themes_dir, "%s/%s", get_primary_storage_path(), PHILZ_THEMES_PATH);
    if (0 != ensure_path_mounted(themes_dir))
        return;

    theme_file = choose_file_menu(themes_dir, ".ini", headers);
    if (theme_file == NULL)
        return;

#ifndef USE_CHINESE_FONT
    if (confirm_selection("Overwrite default settings ?", "Yes - Apply New Theme") && copy_a_file(theme_file, PHILZ_SETTINGS_FILE) == 0) {
#else
    if (confirm_selection("覆盖默认设置？", "是 - 应用新主题") && copy_a_file(theme_file, PHILZ_SETTINGS_FILE) == 0) {
#endif
        char settings_copy[PATH_MAX];
        sprintf(settings_copy, "%s/%s", get_primary_storage_path(), PHILZ_SETTINGS_FILE2);
        copy_a_file(theme_file, settings_copy);
        refresh_recovery_settings(0);
#ifndef USE_CHINESE_FONT
        ui_print("loaded default settings from %s\n", BaseName(theme_file));
#else
        ui_print("从%s加载默认设置\n", BaseName(theme_file));
#endif
    }

    free(theme_file);
#endif
}

static void import_export_settings() {
    static const char* headers[] = {
#ifndef USE_CHINESE_FONT
        "Save / Restore Settings",
#else
        "保存 / 恢复设置",
#endif
        "",
        NULL
    };

    static char* list[] = {
#ifndef USE_CHINESE_FONT
        "Backup Recovery Settings to sdcard",
        "Restore Recovery Settings from sdcard",
        "Save Current Theme to sdcard",
        "Load Existing Theme from sdcard",
        "Delete Saved Themes",
#else
        "保存Recovery设置到SD卡",
        "从SD卡恢复Recovery设置",
        "保存当前主题到SD卡",
        "加载SD卡中存在的主题",
        "删除保存的主题",
#endif
        NULL
    };

    char backup_file[PATH_MAX];
    char themes_dir[PATH_MAX];
    sprintf(backup_file, "%s/%s", get_primary_storage_path(), PHILZ_SETTINGS_BAK);
    sprintf(themes_dir, "%s/%s", get_primary_storage_path(), PHILZ_THEMES_PATH);

    for (;;) {
        int chosen_item = get_menu_selection(headers, list, 0, 0);
        if (chosen_item == GO_BACK)
            break;
        switch (chosen_item) {
            case 0: {
                if (copy_a_file(PHILZ_SETTINGS_FILE, backup_file) == 0)
#ifndef USE_CHINESE_FONT
                    ui_print("config file successfully backed up to %s\n", backup_file);
#else
                    ui_print("设置文件成功备份到%s\n", backup_file);
#endif
                break;
            }
            case 1: {
                if (copy_a_file(backup_file, PHILZ_SETTINGS_FILE) == 0) {
                    char settings_copy[PATH_MAX];
                    sprintf(settings_copy, "%s/%s", get_primary_storage_path(), PHILZ_SETTINGS_FILE2);
                    copy_a_file(backup_file, settings_copy);
                    refresh_recovery_settings(0);
#ifndef USE_CHINESE_FONT
                    ui_print("settings loaded from %s\n", backup_file);
#else
                    ui_print("从%s加载设置\n", backup_file);
#endif
                }
                break;
            }
            case 2: {
                int ret = 1;
                int i = 1;
                char path[PATH_MAX];
                while (ret && i < 10) {
                    sprintf(path, "%s/theme_%03i.ini", themes_dir, i);
                    ret = file_found(path);
                    ++i;
                }

                if (ret)
                    LOGE("Can't save more than 10 themes!\n");
                else if (copy_a_file(PHILZ_SETTINGS_FILE, path) == 0)
#ifndef USE_CHINESE_FONT
                    ui_print("Custom settings saved to %s\n", path);
#else
                    ui_print("自定义设置保存到%s\n", path);
#endif
                break;
            }
            case 3: {
                load_theme_settings();
                break;
            }
            case 4: {
                ensure_path_mounted(themes_dir);
                char* theme_file = choose_file_menu(themes_dir, ".ini", headers);
                if (theme_file == NULL)
                    break;
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Delete selected theme ?", "Yes - Delete"))
#else
                if (confirm_selection("删除选中的主题？", "是 - 删除"))
#endif
                    delete_a_file(theme_file);
                free(theme_file);
                break;
            }
        }
    }
}

void show_philz_settings_menu()
{
#ifndef USE_CHINESE_FONT
    static const char* headers[] = {"PhilZ Settings", NULL};
#else
    static const char* headers[] = {"PhilZ设置", NULL};
#endif

    char item_check_root_and_recovery[MENU_MAX_COLS];
    char item_auto_restore[MENU_MAX_COLS];

    char* list[] = {
#ifndef USE_CHINESE_FONT
        "Open Recovery Script",
        "Aroma File Manager",
        "Re-root System (SuperSU)",
        item_check_root_and_recovery,
        item_auto_restore,
        "Save and Restore Settings",
        "Reset All Recovery Settings",
        "Setup Recovery Lock",
        "GUI Preferences",
        "About",
#else
        "Open Recovery脚本",
        "Aroma文件管理器",
        "重新root系统 (SuperSU)",
        item_check_root_and_recovery,
        item_auto_restore,
        "保存和恢复设置",
        "重置所有Recovery设置",
        "设置Recovery锁",
        "GUI设置",
        "关于",
#endif
        NULL
    };

    for (;;) {
        if (check_root_and_recovery.value)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(item_check_root_and_recovery, "Verify Root on Exit", "(x)");
        else ui_format_gui_menu(item_check_root_and_recovery, "Verify Root on Exit", "( )");
#else
            ui_format_gui_menu(item_check_root_and_recovery, "退出时检查Root权限", "(x)");
        else ui_format_gui_menu(item_check_root_and_recovery, "退出时检查Root权限", "( )");
#endif

        if (auto_restore_settings.value)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(item_auto_restore, "Auto Restore Settings", "(x)");
        else ui_format_gui_menu(item_auto_restore, "Auto Restore Settings", "( )");
#else
            ui_format_gui_menu(item_auto_restore, "自动保存设置", "(x)");
        else ui_format_gui_menu(item_auto_restore, "自动保存设置", "( )");
#endif

        int chosen_item = get_menu_selection(headers, list, 0, 0);
        if (chosen_item == GO_BACK)
            break;

        switch (chosen_item) {
            case 0: {
                //search in default ors paths
                char* primary_path = get_primary_storage_path();
                char** extra_paths = get_extra_storage_paths();
                int num_extra_volumes = get_num_extra_volumes();
                int i = 0;

                // choose_default_ors_menu() will set browse_for_file
                // browse_for_file == 0 ---> we found .ors scripts in primary storage default location
                choose_default_ors_menu(primary_path);
                if (extra_paths != NULL) {
                    while (browse_for_file && i < num_extra_volumes) {
                        // while we did not find an ors script in default location, continue searching in other volumes
                        choose_default_ors_menu(extra_paths[i]);
                        i++;
                    }
                }

                if (browse_for_file) {
                    //no files found in default locations, let's search manually for a custom ors
#ifndef USE_CHINESE_FONT
                    ui_print("No .ors files under %s\n", RECOVERY_ORS_PATH);
                    ui_print("Manually search .ors files...\n");
#else
                    ui_print("在%s下面没有.ors文件\n", RECOVERY_ORS_PATH);
                    ui_print("手动搜索.ors文件...\n");
#endif
                    show_custom_ors_menu();
                }
                break;
            }
            case 1: {
                run_aroma_browser();
                break;
            }
            case 2: {
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Remove existing su ?", "Yes - Apply SuperSU")) {
#else
                if (confirm_selection("删除已经存在的su？", "是 - 应用SuperSU")) {
#endif
                    if (0 == __system("/sbin/install-su.sh"))
#ifndef USE_CHINESE_FONT
                        ui_print("Done!\nNow, install SuperSU from market.\n");
                    else
                        ui_print("Failed to apply root!\n");
#else
                        ui_print("完毕！\n现在，从市场安装SuperSU。\n");
                    else
                        ui_print("应用root失败！\n");
#endif
                }
                break;
            }
            case 3: {
                char value[5];
                check_root_and_recovery.value ^= 1;
                sprintf(value, "%d", check_root_and_recovery.value);
                write_config_file(PHILZ_SETTINGS_FILE, check_root_and_recovery.key, value);
                break;
            }
            case 4: {
                char value[5];
                auto_restore_settings.value ^= 1;
                sprintf(value, "%d", auto_restore_settings.value);
                write_config_file(PHILZ_SETTINGS_FILE, auto_restore_settings.key, value);
                break;
            }
            case 5: {
                import_export_settings();
                break;
            }
            case 6: {
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Reset all recovery settings?", "Yes - Reset to Defaults")) {
#else
                if (confirm_selection("重置所有recovery设置？", "是 - 重置到默认")) {
#endif
                    char settings_copy[PATH_MAX];
                    sprintf(settings_copy, "%s/%s", get_primary_storage_path(), PHILZ_SETTINGS_FILE2);
                    delete_a_file(PHILZ_SETTINGS_FILE);
                    delete_a_file(settings_copy);
                    refresh_recovery_settings(0);
#ifndef USE_CHINESE_FONT
                    ui_print("All settings reset to default!\n");
#else
                    ui_print("所有设置重置到默认！\n");
#endif
                }
                break;
            }
#ifdef PHILZ_TOUCH_RECOVERY
            case 7: {
                show_recovery_lock_menu();
                break;
            }
            case 8: {
                show_touch_gui_menu();
                break;
            }
#endif
            case 9: {
                ui_print(EXPAND(RECOVERY_MOD_VERSION) "\n");
#ifndef USE_CHINESE_FONT
                ui_print("Build version: " EXPAND(PHILZ_BUILD) " - " EXPAND(TARGET_COMMON_NAME) "\n");
                ui_print("CWM Base version: " EXPAND(CWM_BASE_VERSION) "\n");
#else
                ui_print("编译版本：" EXPAND(PHILZ_BUILD) " - " EXPAND(TARGET_COMMON_NAME) "\n");
                ui_print("CWM版本" EXPAND(CWM_BASE_VERSION) "\n");
#endif
#ifdef PHILZ_TOUCH_RECOVERY
                print_libtouch_version(1);
#endif
                //ui_print(EXPAND(BUILD_DATE)"\n");
#ifndef USE_CHINESE_FONT
                ui_print("Compiled %s at %s\n", __DATE__, __TIME__);
#else
                ui_print("编译日期：%s %s\n", __DATE__, __TIME__);
#endif
                break;
            }
        }
    }
}
//---------------- End PhilZ Menu settings and functions
