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

#include <signal.h>
#include <sys/wait.h>
#include <libgen.h>

#include "cutils/android_reboot.h"
#include "cutils/properties.h"
#include "make_ext4fs.h"

#include "voldclient/voldclient.h"
#include "bootloader.h"
#include "common.h"
#include "install.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"
#include "recovery_ui.h"

#include "extendedcommands.h"
#include "advanced_functions.h"
#include "recovery_settings.h"
#include "nandroid.h"
#include "mtdutils/mounts.h"
#include "edify/expr.h"


#include "adb_install.h"

#ifdef PHILZ_TOUCH_RECOVERY
#include "libtouch_gui/gui_settings.h"
#endif

extern struct selabel_handle *sehandle;

int get_filtered_menu_selection(const char** headers, char** items, int menu_only, int initial_selection, int items_count) {
    int index;
    int offset = 0;
    int* translate_table = (int*)malloc(sizeof(int) * items_count);
    char* items_new[items_count];

    for (index = 0; index < items_count; index++) {
        items_new[index] = items[index];
    }

    for (index = 0; index < items_count; index++) {
        if (items_new[index] == NULL)
            continue;
        char *item = items_new[index];
        items_new[index] = NULL;
        items_new[offset] = item;
        translate_table[offset] = index;
        offset++;
    }
    items_new[offset] = NULL;

    initial_selection = translate_table[initial_selection];
    int ret = get_menu_selection(headers, items_new, menu_only, initial_selection);
    if (ret < 0 || ret >= offset) {
        free(translate_table);
        return ret;
    }

    ret = translate_table[ret];
    free(translate_table);
    return ret;
}

// returns negative value on failure and total bytes written on success
int write_string_to_file(const char* filename, const char* string) {
    char tmp[PATH_MAX];
    int ret = -1;

    ensure_path_mounted(filename);
    sprintf(tmp, "mkdir -p $(dirname %s)", filename);
    __system(tmp);
    FILE *file = fopen(filename, "w");
    if (file != NULL) {
        ret = fprintf(file, "%s", string);
        fclose(file);
    } else
        LOGE("Cannot write to %s\n", filename);

    return ret;
}

// called on recovery exit
// data will be mounted by call to write_string_to_file() on /data/media devices
// we need to ensure a proper unmount
void write_recovery_version() {
    char path[PATH_MAX];
    sprintf(path, "%s/%s", get_primary_storage_path(), RECOVERY_VERSION_FILE);
    write_string_to_file(path, EXPAND(RECOVERY_VERSION) "\n" EXPAND(TARGET_DEVICE));
    // force unmount /data for /data/media devices as we call this on recovery exit
    preserve_data_media(0);
    ensure_path_unmounted(path);
    preserve_data_media(1);
}

static void write_last_install_path(const char* install_path) {
    char path[PATH_MAX];
    sprintf(path, "%s/%s", get_primary_storage_path(), RECOVERY_LAST_INSTALL_FILE);
    write_string_to_file(path, install_path);
}

const char* read_last_install_path() {
    static char path[PATH_MAX];
    sprintf(path, "%s/%s", get_primary_storage_path(), RECOVERY_LAST_INSTALL_FILE);

    ensure_path_mounted(path);
    FILE *f = fopen(path, "r");
    if (f != NULL) {
        fgets(path, PATH_MAX, f);
        fclose(f);

        return path;
    }
    return NULL;
}

void toggle_signature_check() {
    char value[3];
    signature_check_enabled.value = !signature_check_enabled.value;
    sprintf(value, "%d", signature_check_enabled.value);
    write_config_file(PHILZ_SETTINGS_FILE, signature_check_enabled.key, value);
    // ui_print("Signature Check: %s\n", signature_check_enabled.value ? "Enabled" : "Disabled");
}

static void toggle_install_zip_verify_md5() {
    char value[3];
    install_zip_verify_md5.value ^= 1;
    sprintf(value, "%d", install_zip_verify_md5.value);
    write_config_file(PHILZ_SETTINGS_FILE, install_zip_verify_md5.key, value);
}

#ifdef ENABLE_LOKI
static void toggle_loki_support() {
    char value[3];
    apply_loki_patch.value ^= 1;
    sprintf(value, "%d", apply_loki_patch.value);
    write_config_file(PHILZ_SETTINGS_FILE, apply_loki_patch.key, value);
    // ui_print("Loki Support: %s\n", apply_loki_patch.value ? "Enabled" : "Disabled");
}

// this is called when we load recovery settings and when we istall_package()
// it is needed when after recovery is booted, user wipes /data, then he installs a ROM: we can still return the user setting 
int loki_support_enabled() {
    char no_loki_variant[PROPERTY_VALUE_MAX];
    int ret = -1;

    property_get("ro.loki_disabled", no_loki_variant, "0");
    if (strcmp(no_loki_variant, "0") == 0) {
        // device variant supports loki: check if user enabled it
        // if there is no settings file (read_config_file() < 0), it could be we have wiped /data before installing zip
        // in that case, return current value (we last loaded on start or when user last set it) and not default
        if (read_config_file(PHILZ_SETTINGS_FILE, apply_loki_patch.key, no_loki_variant, "0") >= 0) {
            if (strcmp(no_loki_variant, "true") == 0 || strcmp(no_loki_variant, "1") == 0)
                apply_loki_patch.value = 0;
            else
                apply_loki_patch.value = 1;
        }
        ret = apply_loki_patch.value;
    }
    return ret;
}
#endif

// top fixed menu items, those before extra storage volumes
#define FIXED_TOP_INSTALL_ZIP_MENUS 1
// bottom fixed menu items, those after extra storage volumes
#define FIXED_BOTTOM_INSTALL_ZIP_MENUS 7
#define FIXED_INSTALL_ZIP_MENUS (FIXED_TOP_INSTALL_ZIP_MENUS + FIXED_BOTTOM_INSTALL_ZIP_MENUS)

int show_install_update_menu() {
    char buf[100];
    int i = 0, chosen_item = 0;
    // + 1 for last NULL item
    static char* install_menu_items[MAX_NUM_MANAGED_VOLUMES + FIXED_INSTALL_ZIP_MENUS + 1];

    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

    memset(install_menu_items, 0, MAX_NUM_MANAGED_VOLUMES + FIXED_INSTALL_ZIP_MENUS + 1);

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Install update from zip file", "", NULL };
#else
    static const char* headers[] = { "从zip文件安装更新", "", NULL };
#endif

    // FIXED_TOP_INSTALL_ZIP_MENUS
#ifndef USE_CHINESE_FONT
    sprintf(buf, "Choose zip from %s", primary_path);
#else
    sprintf(buf, "从%s选择zip文件", primary_path);
#endif
    install_menu_items[0] = strdup(buf);

    // extra storage volumes (vold managed)
    for (i = 0; i < num_extra_volumes; i++) {
#ifndef USE_CHINESE_FONT
        sprintf(buf, "Choose zip from %s", extra_paths[i]);
#else
        sprintf(buf, "从%s选择zip文件", extra_paths[i]);
#endif
        install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + i] = strdup(buf);
    }

    // FIXED_BOTTOM_INSTALL_ZIP_MENUS
    char item_toggle_signature_check[MENU_MAX_COLS] = "";
    char item_install_zip_verify_md5[MENU_MAX_COLS] = "";
#ifndef USE_CHINESE_FONT
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes]     = "Choose zip Using Free Browse Mode";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 1] = "Choose zip from Last Install Folder";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 2] = "Install zip from sideload";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 3] = "Install Multiple zip Files";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 4] = item_toggle_signature_check;
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 5] = item_install_zip_verify_md5;
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 6] = "Setup Free Browse Mode";
#else
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes]     = "使用自由浏览模式选择zip文件";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 1] = "从上次安装的目录选择zip文件";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 2] = "从sideload安装zip文件";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 3] = "安装多个zip文件";
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 4] = item_toggle_signature_check;
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 5] = item_install_zip_verify_md5;
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 6] = "设置自由浏览模式";
#endif

    // extra NULL for GO_BACK
    install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + FIXED_BOTTOM_INSTALL_ZIP_MENUS] = NULL;

    for (;;) {
        if (signature_check_enabled.value)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(item_toggle_signature_check, "Signature Verification", "(x)");
        else ui_format_gui_menu(item_toggle_signature_check, "Signature Verification", "( )");
#else
            ui_format_gui_menu(item_toggle_signature_check, "签名验证", "(x)");
        else ui_format_gui_menu(item_toggle_signature_check, "签名验证", "( )");
#endif

        if (install_zip_verify_md5.value)
#ifndef USE_CHINESE_FONT
            ui_format_gui_menu(item_install_zip_verify_md5, "Verify zip md5sum", "(x)");
        else ui_format_gui_menu(item_install_zip_verify_md5, "Verify zip md5sum", "( )");
#else
            ui_format_gui_menu(item_install_zip_verify_md5, "验证zip的md5码", "(x)");
        else ui_format_gui_menu(item_install_zip_verify_md5, "验证zip的md5码", "( )");
#endif

        chosen_item = get_menu_selection(headers, install_menu_items, 0, 0);
        if (chosen_item == 0) {
            show_choose_zip_menu(primary_path);
        } else if (chosen_item >= FIXED_TOP_INSTALL_ZIP_MENUS && chosen_item < FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes) {
            show_choose_zip_menu(extra_paths[chosen_item - FIXED_TOP_INSTALL_ZIP_MENUS]);
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes) {
            // browse for zip files up/backward including root system and have a default user set start folder
            if (show_custom_zip_menu() != 0)
                set_custom_zip_path();
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 1) {
            const char *last_path_used = read_last_install_path();
            if (last_path_used == NULL)
                show_choose_zip_menu(primary_path);
            else
                show_choose_zip_menu(last_path_used);
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 2) {
            enter_sideload_mode(INSTALL_SUCCESS);
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 3) {
            show_multi_flash_menu();
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 4) {
            toggle_signature_check();
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 5) {
            toggle_install_zip_verify_md5();
        } else if (chosen_item == FIXED_TOP_INSTALL_ZIP_MENUS + num_extra_volumes + 6) {
            set_custom_zip_path();
        } else {
            // GO_BACK or REFRESH (chosen_item < 0)
            goto out;
        }
    }
out:
    // free all the dynamic items
    free(install_menu_items[0]);
    if (extra_paths != NULL) {
        for (i = 0; i < num_extra_volumes; i++)
            free(install_menu_items[FIXED_TOP_INSTALL_ZIP_MENUS + i]);
    }
    return chosen_item;
}

void free_string_array(char** array) {
    if (array == NULL)
        return;
    char* cursor = array[0];
    int i = 0;
    while (cursor != NULL) {
        free(cursor);
        cursor = array[++i];
    }
    free(array);
}

// to gather directories you need to pass NULL for fileExtensionOrDirectory
// else, only files are gathered. Pass "" to gather all files
// NO  MORE NEEDED: if it is not called by choose_file_menu(), passed directory MUST end with a trailing /
static int gather_hidden_files = 0;
void set_gather_hidden_files(int enable) {
    gather_hidden_files = enable;
}

char** gather_files(const char* basedir, const char* fileExtensionOrDirectory, int* numFiles) {
    DIR *dir;
    struct dirent *de;
    int total = 0;
    int i;
    char** files = NULL;
    int pass;
    *numFiles = 0;
    int dirLen = strlen(basedir);
    char directory[PATH_MAX];

    // Append a trailing slash if necessary
    strcpy(directory, basedir);
    if (directory[dirLen - 1] != '/') {
        strcat(directory, "/");
        ++dirLen;
    }

    dir = opendir(directory);
    if (dir == NULL) {
#ifndef USE_CHINESE_FONT
        ui_print("Couldn't open directory %s\n", directory);
#else
        ui_print("不能打开目录%s\n", directory);
#endif
        return NULL;
    }

    unsigned int extension_length = 0;
    if (fileExtensionOrDirectory != NULL)
        extension_length = strlen(fileExtensionOrDirectory);

    i = 0;
    // first pass (pass==0) only returns "total" valid file names to initialize files[total] size
    // second pass (pass == 1), rewinddir and initializes files[i] with directory contents
    for (pass = 0; pass < 2; pass++) {
        while ((de = readdir(dir)) != NULL) {
            // skip hidden files
            if (!gather_hidden_files && de->d_name[0] == '.')
                continue;

            // NULL means that we are gathering directories, so skip this
            if (fileExtensionOrDirectory != NULL) {
                if (strcmp("", fileExtensionOrDirectory) == 0) {
                    // we exclude directories since they are gathered on second call to gather_files() by choose_file_menu()
                    // and we keep stock behavior: folders are gathered only by passing NULL
                    // else, we break things at strcat(files[i], "/") in end of while loop
                    struct stat info;
                    char fullFileName[PATH_MAX];
                    strcpy(fullFileName, directory);
                    strcat(fullFileName, de->d_name);
                    lstat(fullFileName, &info);
                    // make sure it is not a directory
                    if (S_ISDIR(info.st_mode))
                        continue;
                } else {
                    // make sure that we can have the desired extension (prevent seg fault)
                    if (strlen(de->d_name) < extension_length)
                        continue;
                    // compare the extension
                    if (strcmp(de->d_name + strlen(de->d_name) - extension_length, fileExtensionOrDirectory) != 0)
                        continue;
                }
            } else {
                struct stat info;
                char fullFileName[PATH_MAX];
                strcpy(fullFileName, directory);
                strcat(fullFileName, de->d_name);
                lstat(fullFileName, &info);
                // make sure it is a directory
                if (!(S_ISDIR(info.st_mode)))
                    continue;
            }

            if (pass == 0) {
                total++;
                continue;
            }

            // only second pass (pass==1) reaches here: initializes files[i] with directory contents
            files[i] = (char*)malloc(dirLen + strlen(de->d_name) + 2);
            strcpy(files[i], directory);
            strcat(files[i], de->d_name);
            if (fileExtensionOrDirectory == NULL)
                strcat(files[i], "/");
            i++;
        }
        if (pass == 1)
            break;
        if (total == 0)
            break;
        // only first pass (pass == 0) reaches here. We rewinddir for second pass
        // initialize "total" with number of valid files to show and initialize files[total]
        rewinddir(dir);
        *numFiles = total;
        files = (char**)malloc((total + 1) * sizeof(char*));
        files[total] = NULL;
    }

    if (closedir(dir) < 0) {
        LOGE("Failed to close directory.\n");
    }

    if (total == 0) {
        return NULL;
    }

    // sort the result
    if (files != NULL) {
        for (i = 0; i < total; i++) {
            int curMax = -1;
            int j;
            for (j = 0; j < total - i; j++) {
                if (curMax == -1 || strcmpi(files[curMax], files[j]) < 0)
                    curMax = j;
            }
            char* temp = files[curMax];
            files[curMax] = files[total - i - 1];
            files[total - i - 1] = temp;
        }
    }

    return files;
}

// pass in NULL for fileExtensionOrDirectory and you will get a directory chooser
// pass in "" to gather all files without filtering extension or filename
// returned directory (when NULL is passed as file extension) has a trailing / causing a wired // return path
// choose_file_menu returns NULL when no file is found or if we choose no file in selection
// no_files_found = 1 when no valid file was found, no_files_found = 0 when we found a valid file
// WARNING : CALLER MUST ALWAYS FREE THE RETURNED POINTER
int no_files_found = 0;
char* choose_file_menu(const char* basedir, const char* fileExtensionOrDirectory, const char* headers[]) {
    const char* fixed_headers[20];
    int numFiles = 0;
    int numDirs = 0;
    int i;
    char* return_value = NULL;
    char directory[PATH_MAX];
    int dir_len = strlen(basedir);

    strcpy(directory, basedir);

    // Append a trailing slash if necessary
    if (directory[dir_len - 1] != '/') {
        strcat(directory, "/");
        dir_len++;
    }

    i = 0;
    while (headers[i]) {
        fixed_headers[i] = headers[i];
        i++;
    }
    fixed_headers[i] = directory;
    // let's spare some header space
    // fixed_headers[i + 1] = "";
    // fixed_headers[i + 2] = NULL;
    fixed_headers[i + 1] = NULL;

    char** files = gather_files(directory, fileExtensionOrDirectory, &numFiles);
    char** dirs = NULL;
    if (fileExtensionOrDirectory != NULL)
        dirs = gather_files(directory, NULL, &numDirs);
    int total = numDirs + numFiles;
    if (total == 0) {
        // we found no valid file to select
        no_files_found = 1;
#ifndef USE_CHINESE_FONT
        ui_print("No files found.\n");
#else
        ui_print("没有发现文件。\n");
#endif
    } else {
        // we found a valid file to select
        no_files_found = 0;
        char** list = (char**)malloc((total + 1) * sizeof(char*));
        list[total] = NULL;


        for (i = 0; i < numDirs; i++) {
            list[i] = strdup(dirs[i] + dir_len);
        }

        for (i = 0; i < numFiles; i++) {
            list[numDirs + i] = strdup(files[i] + dir_len);
        }

        for (;;) {
            int chosen_item = get_menu_selection(fixed_headers, list, 0, 0);
            if (chosen_item == GO_BACK || chosen_item == REFRESH)
                break;
            if (chosen_item < numDirs) {
                char* subret = choose_file_menu(dirs[chosen_item], fileExtensionOrDirectory, headers);
                if (subret != NULL) {
                    // we selected either a folder (or a file from a re-entrant call)
                    return_value = strdup(subret);
                    free(subret);
                    break;
                }
                // the previous re-entrant call did a GO_BACK, REFRESH or no file found in a directory: subret == NULL
                // we drop to up folder
                continue;
            }
            // we selected a file
            return_value = strdup(files[chosen_item - numDirs]);
            break;
        }
        free_string_array(list);
    }

    free_string_array(files);
    free_string_array(dirs);
    return return_value;
}

void show_choose_zip_menu(const char *mount_point) {
    if (ensure_path_mounted(mount_point) != 0) {
        LOGE("Can't mount %s\n", mount_point);
        return;
    }

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Choose a zip to apply", NULL };
#else
    static const char* headers[] = { "选择一个zip来应用", NULL };
#endif

    char* file = choose_file_menu(mount_point, ".zip", headers);
    if (file == NULL)
        return;

    char tmp[PATH_MAX];
    int yes_confirm;

#ifndef USE_CHINESE_FONT
    sprintf(tmp, "Yes - Install %s", BaseName(file));
#else
    sprintf(tmp, "是 - 安装%s", BaseName(file));
#endif
    if (install_zip_verify_md5.value) start_md5_verify_thread(file);
    else start_md5_display_thread(file);

#ifndef USE_CHINESE_FONT
    yes_confirm = confirm_selection("Confirm install?", tmp);
#else
    yes_confirm = confirm_selection("确认安装？", tmp);
#endif

    if (install_zip_verify_md5.value) stop_md5_verify_thread();
    else stop_md5_display_thread();

    if (yes_confirm) {
        install_zip(file);
        sprintf(tmp, "%s", DirName(file));
        write_last_install_path(tmp);
    }

    free(file);
}

void show_nandroid_restore_menu(const char* path) {
    if (ensure_path_mounted(path) != 0) {
        LOGE("Can't mount %s\n", path);
        return;
    }

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Choose an image to restore", NULL };
#else
    static const char* headers[] = { "选择一个镜像来恢复", NULL };
#endif

    char tmp[PATH_MAX];
    sprintf(tmp, "%s/clockworkmod/backup/", path);
    char* file = choose_file_menu(tmp, NULL, headers);
    if (file == NULL)
        return;
#ifndef USE_CHINESE_FONT
    if (confirm_selection("Confirm restore?", "Yes - Restore"))
#else
    if (confirm_selection("确认恢复？", "是 - 恢复"))
#endif
        nandroid_restore(file, 1, 1, 1, 1, 1, 0);

    free(file);
}

void show_nandroid_delete_menu(const char* volume_path) {
    if (ensure_path_mounted(volume_path) != 0) {
        LOGE("Can't mount %s\n", volume_path);
        return;
    }

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Choose a backup to delete", NULL };
#else
    static const char* headers[] = { "删除一个备份", NULL };
#endif
    char path[PATH_MAX];
    char tmp[PATH_MAX];
    char* file;

    if (twrp_backup_mode.value) {
        char device_id[PROPERTY_VALUE_MAX];
        get_device_id(device_id);
        sprintf(path, "%s/%s/%s", volume_path, TWRP_BACKUP_PATH, device_id);
    } else {
        sprintf(path, "%s/%s", volume_path, CWM_BACKUP_PATH);    
    }

    for(;;) {
        file = choose_file_menu(path, NULL, headers);
        if (file == NULL)
            return;

#ifndef USE_CHINESE_FONT
        sprintf(tmp, "Yes - Delete %s", BaseName(file));
        if (confirm_selection("Confirm delete?", tmp)) {
#else
        sprintf(tmp, "是 - 删除%s", BaseName(file));
        if (confirm_selection("确认删除？", tmp)) {
#endif
            sprintf(tmp, "rm -rf '%s'", file);
            __system(tmp);
        }

        free(file);
    }
}

static int control_usb_storage(bool on) {
    int i = 0;
    int num = 0;

    for (i = 0; i < get_num_volumes(); i++) {
        Volume *v = get_device_volumes() + i;
        if (fs_mgr_is_voldmanaged(v) && vold_is_volume_available(v->mount_point)) {
            if (on) {
                vold_share_volume(v->mount_point);
            } else {
                vold_unshare_volume(v->mount_point, 1);
            }
            property_set("sys.storage.ums_enabled", on ? "1" : "0");
            num++;
        }
    }
    return num;
}

void show_mount_usb_storage_menu() {
    // Enable USB storage using vold
    if (!control_usb_storage(true))
        return;

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "USB Mass Storage device",
                                     "Leaving this menu unmounts",
                                     "your SD card from your PC.",
                                     "",
                                     NULL
    };

    static char* list[] = { "Unmount", NULL };
#else
    static const char* headers[] = { "USB大容量存储设备",
                                     "离开这个菜单来从你",
                                     "的电脑取消挂载SD卡",
                                     "",
                                     NULL
    };

    static char* list[] = { "取消挂载", NULL };
#endif

    for (;;) {
        int chosen_item = get_menu_selection(headers, list, 0, 0);
        if (chosen_item == GO_BACK || chosen_item == 0)
            break;
    }

    // Disable USB storage
    control_usb_storage(false);
}

int confirm_selection(const char* title, const char* confirm) {
    struct stat info;
    int ret = 0;

    char path[PATH_MAX];
    sprintf(path, "%s/%s", get_primary_storage_path(), RECOVERY_NO_CONFIRM_FILE);
    ensure_path_mounted(path);
    if (0 == stat(path, &info))
        return 1;

#ifdef BOARD_NATIVE_DUALBOOT
    char buf[PATH_MAX];
    device_build_selection_title(buf, title);
    title = (char*)&buf;
#endif

    int many_confirm;
    char* confirm_str = strdup(confirm);
#ifndef USE_CHINESE_FONT
    const char* confirm_headers[] = { title, "  THIS CAN NOT BE UNDONE.", "", NULL };
#else
    const char* confirm_headers[] = { title, "  这个操作不可恢复。", "", NULL };
#endif
    int old_val = ui_is_showing_back_button();
    ui_set_showing_back_button(0);

    sprintf(path, "%s/%s", get_primary_storage_path(), RECOVERY_MANY_CONFIRM_FILE);
    // ensure_path_mounted(path);
    many_confirm = 0 == stat(path, &info);

    if (many_confirm) {
#ifndef USE_CHINESE_FONT
        char* items[] = { "No",
                          "No",
                          "No",
                          "No",
                          "No",
                          "No",
                          "No",
                          confirm_str, //" Yes -- wipe partition",   // [7]
                          "No",
                          "No",
                          "No",
                          NULL };
#else
        char* items[] = { "不",
                          "不",
                          "不",
                          "不",
                          "不",
                          "不",
                          "不",
                          confirm_str, //" Yes -- wipe partition",   // [7]
                          "不",
                          "不",
                          "不",
                          NULL };
#endif
        int chosen_item = get_menu_selection(confirm_headers, items, 0, 0);
        ret = (chosen_item == 7);
    } else {
#ifndef USE_CHINESE_FONT
        char* items[] = { "No",
                          confirm_str, //" Yes -- wipe partition",   // [1]
                          "No",
                          NULL };
#else
        char* items[] = { "不",
                          confirm_str, //" Yes -- wipe partition",   // [1]
                          "不",
                          NULL };
#endif
        int chosen_item = get_menu_selection(confirm_headers, items, 0, 0);
        ret = (chosen_item == 1);
    }

    free(confirm_str);
    ui_set_showing_back_button(old_val);
    return ret;
}

typedef struct {
    char mount[255];
    char unmount[255];
    char path[PATH_MAX];
} MountMenuEntry;

typedef struct {
    char txt[255];
    char path[PATH_MAX];
    char type[255];
} FormatMenuEntry;

typedef struct {
    char *name;
    int can_mount;
    int can_format;
} MFMatrix;

MFMatrix get_mnt_fmt_capabilities(char *fs_type, char *mount_point) {
    MFMatrix mfm = { mount_point, 1, 1 };

    const int NUM_FS_TYPES = 6;
    MFMatrix *fs_matrix = malloc(NUM_FS_TYPES * sizeof(MFMatrix));
    // Defined capabilities:   fs_type     mnt fmt
    fs_matrix[0] = (MFMatrix){ "bml",       0,  1 };
    fs_matrix[1] = (MFMatrix){ "datamedia", 0,  1 };
    fs_matrix[2] = (MFMatrix){ "emmc",      0,  1 };
    fs_matrix[3] = (MFMatrix){ "mtd",       0,  0 };
    fs_matrix[4] = (MFMatrix){ "ramdisk",   0,  0 };
    fs_matrix[5] = (MFMatrix){ "swap",      0,  0 };

    const int NUM_MNT_PNTS = 6;
    MFMatrix *mp_matrix = malloc(NUM_MNT_PNTS * sizeof(MFMatrix));
    // Defined capabilities:   mount_point   mnt fmt
    mp_matrix[0] = (MFMatrix){ "/misc",       0,  0 };
    mp_matrix[1] = (MFMatrix){ "/radio",      0,  0 };
    mp_matrix[2] = (MFMatrix){ "/bootloader", 0,  0 };
    mp_matrix[3] = (MFMatrix){ "/recovery",   0,  0 };
    mp_matrix[4] = (MFMatrix){ "/efs",        0,  0 };
    mp_matrix[5] = (MFMatrix){ "/wimax",      0,  0 };

    int i;
    for (i = 0; i < NUM_FS_TYPES; i++) {
        if (strcmp(fs_type, fs_matrix[i].name) == 0) {
            mfm.can_mount = fs_matrix[i].can_mount;
            mfm.can_format = fs_matrix[i].can_format;
        }
    }
    for (i = 0; i < NUM_MNT_PNTS; i++) {
        if (strcmp(mount_point, mp_matrix[i].name) == 0) {
            mfm.can_mount = mp_matrix[i].can_mount;
            mfm.can_format = mp_matrix[i].can_format;
        }
    }

    free(fs_matrix);
    free(mp_matrix);

    // User-defined capabilities
    char *custom_mp;
    char custom_forbidden_mount[PROPERTY_VALUE_MAX];
    char custom_forbidden_format[PROPERTY_VALUE_MAX];
    property_get("ro.cwm.forbid_mount", custom_forbidden_mount, "");
    property_get("ro.cwm.forbid_format", custom_forbidden_format, "");

    custom_mp = strtok(custom_forbidden_mount, ",");
    while (custom_mp != NULL) {
        if (strcmp(mount_point, custom_mp) == 0) {
            mfm.can_mount = 0;
        }
        custom_mp = strtok(NULL, ",");
    }

    custom_mp = strtok(custom_forbidden_format, ",");
    while (custom_mp != NULL) {
        if (strcmp(mount_point, custom_mp) == 0) {
            mfm.can_format = 0;
        }
        custom_mp = strtok(NULL, ",");
    }

    return mfm;
}

#ifdef USE_F2FS
static void format_ext4_or_f2fs(const char* volume) {
    if (is_data_media_volume_path(volume))
        return;

    Volume* v = volume_for_path(volume);
    if (v == NULL)
        return;

    const char* headers[] = { "Format device:", v->mount_point, "", NULL };

    char* list[] = {
        "default",
        "ext4",
        "f2fs",
        NULL
    };

    char cmd[PATH_MAX];
    char confirm[128];
    int ret = -1;
    int chosen_item = get_menu_selection(headers, list, 0, 0);

    if (chosen_item < 0) // REFRESH or GO_BACK
        return;

#ifndef USE_CHINESE_FONT
    sprintf(confirm, "Format %s (%s) ?", v->mount_point, list[chosen_item]);
    if (!confirm_selection(confirm, "Yes - Format device"))
#else
    sprintf(confirm, "格式化%s（%s）？", v->mount_point, list[chosen_item]);
    if (!confirm_selection(confirm, "是 - 格式化设备"))
#endif
        return;

    if (ensure_path_unmounted(v->mount_point) != 0)
        return;

    switch (chosen_item) {
        case 0:
            ret = format_volume(v->mount_point);
            break;
        case 1:
        case 2:
            ret = format_device(v->blk_device, v->mount_point, list[chosen_item]);
            break;
    }

    // refresh volume table (Volume*) and recreate the /etc/fstab file for proper system mount command function
    load_volume_table();
    setup_data_media(1);

    if (ret)
        LOGE("Could not format %s (%s)\n", volume, list[chosen_item]);
    else
#ifndef USE_CHINESE_FONT
        ui_print("Done formatting %s (%s)\n", volume, list[chosen_item]);
#else
        ui_print("格式化%s（%s）结束\n", volume, list[chosen_item]);
#endif
}
#endif

int show_partition_menu() {
#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Mounts and Storage Menu", NULL };

    static char* confirm_format = "Confirm format?";
    static char* confirm = "Yes - Format";
#else
    static const char* headers[] = { "挂载和存储菜单", NULL };

    static char* confirm_format = "确认格式化？";
    static char* confirm = "是 - 格式化";
#endif

    char confirm_string[255];

    static MountMenuEntry* mount_menu = NULL;
    static FormatMenuEntry* format_menu = NULL;
    static char* list[256];

    int i, mountable_volumes, formatable_volumes;
    int num_volumes;
    int chosen_item = 0;

    num_volumes = get_num_volumes();

    if (!num_volumes)
        return 0;

    mountable_volumes = 0;
    formatable_volumes = 0;

    mount_menu = malloc(num_volumes * sizeof(MountMenuEntry));
    format_menu = malloc(num_volumes * sizeof(FormatMenuEntry));

    for (i = 0; i < num_volumes; i++) {
        Volume* v = get_device_volumes() + i;

        if (fs_mgr_is_voldmanaged(v) && !vold_is_volume_available(v->mount_point)) {
            continue;
        }

        MFMatrix mfm = get_mnt_fmt_capabilities(v->fs_type, v->mount_point);

        if (mfm.can_mount) {
#ifndef USE_CHINESE_FONT
            sprintf(mount_menu[mountable_volumes].mount, "mount %s", v->mount_point);
            sprintf(mount_menu[mountable_volumes].unmount, "unmount %s", v->mount_point);
#else
            sprintf(mount_menu[mountable_volumes].mount, "挂载%s", v->mount_point);
            sprintf(mount_menu[mountable_volumes].unmount, "取消挂载%s", v->mount_point);
#endif
            sprintf(mount_menu[mountable_volumes].path, "%s", v->mount_point);
            ++mountable_volumes;
        }
        if (mfm.can_format) {
#ifndef USE_CHINESE_FONT
            sprintf(format_menu[formatable_volumes].txt, "format %s", v->mount_point);
#else
            sprintf(format_menu[formatable_volumes].txt, "格式化%s", v->mount_point);
#endif
            sprintf(format_menu[formatable_volumes].path, "%s", v->mount_point);
            sprintf(format_menu[formatable_volumes].type, "%s", v->fs_type);
            ++formatable_volumes;
        }
    }

#ifdef USE_F2FS
    int enable_f2fs_ext4_conversion = 0;
#endif
    for (;;) {
        for (i = 0; i < mountable_volumes; i++) {
            MountMenuEntry* e = &mount_menu[i];
            if (is_path_mounted(e->path))
                list[i] = e->unmount;
            else
                list[i] = e->mount;
        }

        for (i = 0; i < formatable_volumes; i++) {
            FormatMenuEntry* e = &format_menu[i];
            list[mountable_volumes + i] = e->txt;
        }

        if (!is_data_media()) {
#ifndef USE_CHINESE_FONT
            list[mountable_volumes + formatable_volumes] = "mount USB storage";
#else
            list[mountable_volumes + formatable_volumes] = "挂载USB存储";
#endif
            list[mountable_volumes + formatable_volumes + 1] = NULL;
#ifdef USE_F2FS
#ifndef USE_CHINESE_FONT
            list[mountable_volumes + formatable_volumes + 1] = "转换f2fs <-> ext4格式";
#else

#endif
            list[mountable_volumes + formatable_volumes + 2] = NULL;
#endif
        } else {
#ifndef USE_CHINESE_FONT
            list[mountable_volumes + formatable_volumes] = "format /data and /data/media (/sdcard)";
            list[mountable_volumes + formatable_volumes + 1] = "mount USB storage";
#else
            list[mountable_volumes + formatable_volumes] = "格式化/data和/data/media (/sdcard)";
            list[mountable_volumes + formatable_volumes + 1] = "挂载USB存储";
#endif
            list[mountable_volumes + formatable_volumes + 2] = NULL;
#ifdef USE_F2FS
#ifndef USE_CHINESE_FONT
            list[mountable_volumes + formatable_volumes + 2] = "toggle f2fs <-> ext4 migration";
#else
            list[mountable_volumes + formatable_volumes + 2] = "转换f2fs <-> ext4格式";
#endif
            list[mountable_volumes + formatable_volumes + 3] = NULL;
#endif
        }

        chosen_item = get_menu_selection(headers, list, 0, 0);
        if (chosen_item == GO_BACK || chosen_item == REFRESH)
            break;
        if (chosen_item == (mountable_volumes + formatable_volumes)) {
            if (!is_data_media()) {
                show_mount_usb_storage_menu();
            } else {
#ifndef USE_CHINESE_FONT
                if (!confirm_selection("format /data and /data/media (/sdcard)", confirm))
#else
                if (!confirm_selection("格式化/data和/data/media (/sdcard)", confirm))
#endif
                    continue;
                // sets is_data_media_preserved() to 0
                // this will truly format /data as a partition (format_device() and format_volume())
                preserve_data_media(0);
#ifdef USE_F2FS
                if (enable_f2fs_ext4_conversion) {
                    format_ext4_or_f2fs("/data");
                } else
#endif
                {
#ifndef USE_CHINESE_FONT
                    ui_print("Formatting /data...\n");
                    if (0 != format_volume("/data"))
                        ui_print("Error formatting /data!\n");
                    else
                        ui_print("Done.\n");
#else
                    ui_print("格式化/data...\n");
                    if (0 != format_volume("/data"))
                        ui_print("格式化/data出错！\n");
                    else
                        ui_print("完成。\n");
#endif
                }
                preserve_data_media(1);

                // recreate /data/media with proper permissions, mount /data and unmount when done
                setup_data_media(1);
            }
        } else if (is_data_media() && chosen_item == (mountable_volumes + formatable_volumes + 1)) {
            show_mount_usb_storage_menu();
        } else if (chosen_item < mountable_volumes) {
            MountMenuEntry* e = &mount_menu[chosen_item];

            if (is_path_mounted(e->path)) {
                preserve_data_media(0);
                if (0 != ensure_path_unmounted(e->path))
#ifndef USE_CHINESE_FONT
                    ui_print("Error unmounting %s!\n", e->path);
#else
                    ui_print("取消挂载%s出错！\n", e->path);
#endif
                preserve_data_media(1);
            } else {
                if (0 != ensure_path_mounted(e->path))
#ifndef USE_CHINESE_FONT
                    ui_print("Error mounting %s!\n", e->path);
#else
                    ui_print("挂载%s出错！\n", e->path);
#endif
            }
        } else if (chosen_item < (mountable_volumes + formatable_volumes)) {
            chosen_item = chosen_item - mountable_volumes;
            FormatMenuEntry* e = &format_menu[chosen_item];

            sprintf(confirm_string, "%s - %s", e->path, confirm_format);

            // support user choice fstype when formatting external storage
            // ensure fstype==auto because most devices with internal vfat storage cannot be formatted to other types
            if (strcmp(e->type, "auto") == 0) {
                show_format_sdcard_menu(e->path);
                continue;
            }

#ifdef USE_F2FS
            if (enable_f2fs_ext4_conversion && !(is_data_media() && strcmp(e->path, "/data") == 0)) {
                if (strcmp(e->type, "ext4") == 0 || strcmp(e->type, "f2fs") == 0) {
                    format_ext4_or_f2fs(e->path);
                    continue;
                } else {
#ifndef USE_CHINESE_FONT
                    ui_print("unsupported file system (%s)\n", e->type);
#else
                    ui_print("不支持的文件系统（%s）\n", e->type);
#endif
                }
            } else
#endif
            {
                if (!confirm_selection(confirm_string, confirm))
                    continue;
#ifndef USE_CHINESE_FONT
                ui_print("Formatting %s...\n", e->path);
                if (0 != format_volume(e->path))
                    ui_print("Error formatting %s!\n", e->path);
                else
                    ui_print("Done.\n");
#else
                ui_print("正在格式化%s...\n", e->path);
                if (0 != format_volume(e->path))
                    ui_print("格式化%s出错！\n", e->path);
                else
                    ui_print("完成。\n");
#endif
            }
        }
#ifdef USE_F2FS
        else if ((is_data_media() && chosen_item == (mountable_volumes + formatable_volumes + 2)) ||
                    (!is_data_media() && chosen_item == (mountable_volumes + formatable_volumes + 1))) {
            enable_f2fs_ext4_conversion ^= 1;
#ifndef USE_CHINESE_FONT
            ui_print("ext4 <-> f2fs conversion %s\n", enable_f2fs_ext4_conversion ? "enabled" : "disabled");
#else
            ui_print("ext4 <-> f2fs转换%s\n", enable_f2fs_ext4_conversion ? "打开" : "关闭");
#endif
        }
#endif
    }

    free(mount_menu);
    free(format_menu);
    return chosen_item;
}

#if 0
void show_nandroid_advanced_restore_menu(const char* path) {
    if (ensure_path_mounted(path) != 0) {
        LOGE("Can't mount sdcard\n");
        return;
    }

    static const char* advancedheaders[] = { "Choose an image to restore",
                                             "",
                                             "Choose an image to restore",
                                             "first. The next menu will",
                                             "show you more options.",
                                             "",
                                             NULL };

    char tmp[PATH_MAX];
    sprintf(tmp, "%s/clockworkmod/backup/", path);
    char* file = choose_file_menu(tmp, NULL, advancedheaders);
    if (file == NULL)
        return;

    static const char* headers[] = { "Advanced Restore", "", NULL };

    static char* list[] = { "Restore boot",
                            "Restore system (+/- preload)",
                            "Restore data",
                            "Restore cache",
                            "Restore sd-ext",
                            "Restore wimax",
                            NULL };

    if (0 != get_partition_device("wimax", tmp)) {
        // disable wimax restore option
        list[5] = NULL;
    }

    static char* confirm_restore = "Confirm restore?";

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item) {
        case 0: {
            if (confirm_selection(confirm_restore, "Yes - Restore boot"))
                nandroid_restore(file, 1, 0, 0, 0, 0, 0);
            break;
        }
        case 1: {
            if (confirm_selection(confirm_restore, "Yes - Restore system +/- preload"))
                nandroid_restore(file, 0, 1, 0, 0, 0, 0);
            break;
        }
        case 2: {
            if (confirm_selection(confirm_restore, "Yes - Restore data"))
                nandroid_restore(file, 0, 0, 1, 0, 0, 0);
            break;
        }
        case 3: {
            if (confirm_selection(confirm_restore, "Yes - Restore cache"))
                nandroid_restore(file, 0, 0, 0, 1, 0, 0);
            break;
        }
        case 4: {
            if (confirm_selection(confirm_restore, "Yes - Restore sd-ext"))
                nandroid_restore(file, 0, 0, 0, 0, 1, 0);
            break;
        }
        case 5: {
            if (confirm_selection(confirm_restore, "Yes - Restore wimax"))
                nandroid_restore(file, 0, 0, 0, 0, 0, 1);
            break;
        }
    }

    free(file);
}
#endif

static void run_dedupe_gc() {
    char path[PATH_MAX];
    char* fmt = "%s/clockworkmod/blobs";
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int i = 0;

    sprintf(path, fmt, primary_path);
    ensure_path_mounted(primary_path);
    nandroid_dedupe_gc(path);

    if (extra_paths != NULL) {
        for (i = 0; i < get_num_extra_volumes(); i++) {
            ensure_path_mounted(extra_paths[i]);
            sprintf(path, fmt, extra_paths[i]);
            nandroid_dedupe_gc(path);
        }
    }
}

void choose_default_backup_format() {
#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Default Backup Format", "", NULL };
#else
    static const char* headers[] = { "默认备份格式", "", NULL };
#endif

    int fmt = nandroid_get_default_backup_format();

    char **list;
#ifndef USE_CHINESE_FONT
    char* list_tar_default[] = { "tar (default)",
#else
    char* list_tar_default[] = { "tar （默认）",
#endif
                                 "dup",
                                 "tar + gzip",
                                 NULL };
    char* list_dup_default[] = { "tar",
#ifndef USE_CHINESE_FONT
                                 "dup (default)",
#else
                                 "dup （默认）",
#endif
                                 "tar + gzip",
                                 NULL };
    char* list_tgz_default[] = { "tar",
                                 "dup",
#ifndef USE_CHINESE_FONT
                                 "tar + gzip (default)",
#else
                                 "tar + gzip （默认）",
#endif
                                 NULL };

    if (fmt == NANDROID_BACKUP_FORMAT_DUP) {
        list = list_dup_default;
    } else if (fmt == NANDROID_BACKUP_FORMAT_TGZ) {
        list = list_tgz_default;
    } else {
        list = list_tar_default;
    }

    char path[PATH_MAX];
    sprintf(path, "%s/%s", get_primary_storage_path(), NANDROID_BACKUP_FORMAT_FILE);
    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item) {
        case 0: {
            write_string_to_file(path, "tar");
#ifndef USE_CHINESE_FONT
            ui_print("Default backup format set to tar.\n");
#else
            ui_print("默认备份格式设置为tar。\n");
#endif
            break;
        }
        case 1: {
            write_string_to_file(path, "dup");
#ifndef USE_CHINESE_FONT
            ui_print("Default backup format set to dedupe.\n");
#else
            ui_print("默认备份格式设置为dedupe。\n");
#endif
            break;
        }
        case 2: {
            write_string_to_file(path, "tgz");
#ifndef USE_CHINESE_FONT
            ui_print("Default backup format set to tar + gzip.\n");
#else
            ui_print("默认备份格式设置为tar + gzip。\n");
#endif
            break;
        }
    }
}

static void add_nandroid_options_for_volume(char** menu, char* path, int offset) {
    char buf[100];

#ifndef USE_CHINESE_FONT
    sprintf(buf, "Backup to %s", path);
#else
    sprintf(buf, "备份到%s", path);
#endif
    menu[offset] = strdup(buf);

#ifndef USE_CHINESE_FONT
    sprintf(buf, "Restore from %s", path);
#else
    sprintf(buf, "恢复到%s", path);
#endif
    menu[offset + 1] = strdup(buf);

#ifndef USE_CHINESE_FONT
    sprintf(buf, "Delete from %s", path);
#else
    sprintf(buf, "从%s删除", path);
#endif
    menu[offset + 2] = strdup(buf);

#ifndef USE_CHINESE_FONT
    sprintf(buf, "Custom Backup to %s", path);
#else
    sprintf(buf, "自定义备份到%s", path);
#endif
    menu[offset + 3] = strdup(buf);

#ifndef USE_CHINESE_FONT
    sprintf(buf, "Custom Restore from %s", path);
#else
    sprintf(buf, "从%s自定义恢复", path);
#endif
    menu[offset + 4] = strdup(buf);
}

// number of actions added for each volume by add_nandroid_options_for_volume()
// these go on top of menu list
#define NANDROID_ACTIONS_NUM 5
// number of fixed bottom entries after volume actions
#define NANDROID_FIXED_ENTRIES 3

int show_nandroid_menu() {
    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();
    int i = 0, offset = 0, chosen_item = 0;
    char* chosen_path = NULL;
    int action_entries_num = (num_extra_volumes + 1) * NANDROID_ACTIONS_NUM;
                                   // +1 for primary_path
#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Backup and Restore", NULL };
#else
    static const char* headers[] = { "备份和恢复", NULL };
#endif

    // (MAX_NUM_MANAGED_VOLUMES + 1) for primary_path (/sdcard)
    // + 1 for extra NULL entry
    static char* list[((MAX_NUM_MANAGED_VOLUMES + 1) * NANDROID_ACTIONS_NUM) + NANDROID_FIXED_ENTRIES + 1];

    // actions for primary_path
    add_nandroid_options_for_volume(list, primary_path, offset);
    offset += NANDROID_ACTIONS_NUM;

    // actions for voldmanaged volumes
    if (extra_paths != NULL) {
        for (i = 0; i < num_extra_volumes; i++) {
            add_nandroid_options_for_volume(list, extra_paths[i], offset);
            offset += NANDROID_ACTIONS_NUM;
        }
    }

    // fixed bottom entries
#ifndef USE_CHINESE_FONT
    list[offset]     = "Clone ROM to update.zip";
    list[offset + 1] = "Free Unused Backup Data";
    list[offset + 2] = "Misc Nandroid Settings";
#else
    list[offset]     = "克隆ROM到update.zip";
    list[offset + 1] = "释放未使用的备份数据";
    list[offset + 2] = "Nandroid杂项设置";
#endif
    offset += NANDROID_FIXED_ENTRIES;

#ifdef RECOVERY_EXTEND_NANDROID_MENU
    extend_nandroid_menu(list, offset, sizeof(list) / sizeof(char*));
    offset++;
#endif

    // extra NULL for GO_BACK
    list[offset] = NULL;
    offset++;

    for (;;) {
        chosen_item = get_filtered_menu_selection(headers, list, 0, 0, offset);
        if (chosen_item == GO_BACK || chosen_item == REFRESH)
            break;

        // fixed bottom entries
        if (chosen_item == action_entries_num) {
#ifdef PHILZ_TOUCH_RECOVERY
            custom_rom_menu();
#else
#ifndef USE_CHINESE_FONT
            ui_print("Unsupported in open source version!\n");
#else
            ui_print("在开源版本中不支持！\n");
#endif
#endif
        } else if (chosen_item == (action_entries_num + 1)) {
            run_dedupe_gc();
        } else if (chosen_item == (action_entries_num + 2)) {
            misc_nandroid_menu();
        } else if (chosen_item < action_entries_num) {
            // get nandroid volume actions path
            if (chosen_item < NANDROID_ACTIONS_NUM) {
                chosen_path = primary_path;
            } else if (extra_paths != NULL) {
                chosen_path = extra_paths[(chosen_item / NANDROID_ACTIONS_NUM) - 1];
            }

            // process selected nandroid action
            int chosen_subitem = chosen_item % NANDROID_ACTIONS_NUM;
            switch (chosen_subitem) {
                case 0: {
                    char backup_path[PATH_MAX];
                    if (twrp_backup_mode.value) {
                        int fmt = nandroid_get_default_backup_format();
                        if (fmt != NANDROID_BACKUP_FORMAT_TAR && fmt != NANDROID_BACKUP_FORMAT_TGZ) {
                            LOGE("TWRP backup format must be tar(.gz)!\n");
                        } else {
                            get_twrp_backup_path(chosen_path, backup_path);
                            twrp_backup(backup_path);
                        }
                    } else {
                        get_cwm_backup_path(chosen_path, backup_path);
                        nandroid_backup(backup_path);
                    }
                    break;
                }
                case 1: {
                    if (twrp_backup_mode.value)
                        show_twrp_restore_menu(chosen_path);
                    else
                        show_nandroid_restore_menu(chosen_path);
                    break;
                }
                case 2:
                    show_nandroid_delete_menu(chosen_path);
                    break;
                case 3:
                    custom_backup_menu(chosen_path);
                    break;
                case 4:
                    custom_restore_menu(chosen_path);
                    break;
                default:
                    break;
            }
        } else {
#ifdef RECOVERY_EXTEND_NANDROID_MENU
            handle_nandroid_menu(action_entries_num + NANDROID_FIXED_ENTRIES, chosen_item);
#endif
            goto out;
        }
    }
out:
    for (i = 0; i < action_entries_num; i++)
        free(list[i]);
    return chosen_item;
}

static int can_partition(const char* volume) {
    if (is_data_media_volume_path(volume))
        return 0;

    Volume *vol = volume_for_path(volume);
    if (vol == NULL) {
        LOGI("Can't format unknown volume: %s\n", volume);
        return 0;
    }
    if (strcmp(vol->fs_type, "auto") != 0) {
        LOGI("Can't partition non-vfat: %s (%s)\n", volume, vol->fs_type);
        return 0;
    }

    // do not allow partitioning of a device that isn't mmcblkX or mmcblkXp1
    // needed with new vold managed volumes and virtual device path links
    int vol_len;
    char *device = NULL;
    if (strstr(vol->blk_device, "/dev/block/mmcblk") != NULL) {
        device = vol->blk_device;
    } else if (vol->blk_device2 != NULL && strstr(vol->blk_device2, "/dev/block/mmcblk") != NULL) {
        device = vol->blk_device2;
    } else {
        LOGI("Can't partition non mmcblk device: %s\n", vol->blk_device);
        return 0;
    }

    vol_len = strlen(device);
    if (device[vol_len - 2] == 'p' && device[vol_len - 1] != '1') {
        LOGI("Can't partition unsafe device: %s\n", device);
        return 0;
    }

    return 1;
}

// pass in mount point as argument
void show_format_sdcard_menu(const char* volume) {
    if (is_data_media_volume_path(volume))
        return;

    Volume *v = volume_for_path(volume);
    if (v == NULL || strcmp(v->fs_type, "auto") != 0)
        return;
    if (!fs_mgr_is_voldmanaged(v) && !can_partition(volume))
        return;

#ifndef USE_CHINESE_FONT
    const char* headers[] = { "Format device:", volume, "", NULL };
#else
    const char* headers[] = { "格式化设备：", volume, "", NULL };
#endif

    static char* list[] = {
#ifndef USE_CHINESE_FONT
        "default",
#else
        "默认",
#endif
        "ext2",
        "ext3",
        "ext4",
        "vfat",
        "exfat",
        "ntfs",
#ifdef USE_F2FS
        "f2fs",
#endif
        NULL
    };

    int ret = -1;
    char cmd[PATH_MAX];
    int chosen_item = get_menu_selection(headers, list, 0, 0);
    if (chosen_item < 0) // REFRESH or GO_BACK
        return;
#ifndef USE_CHINESE_FONT
    if (!confirm_selection("Confirm formatting?", "Yes - Format device"))
#else
    if (!confirm_selection("确认格式化？", "是 - 格式化设备"))
#endif
        return;

    if (ensure_path_unmounted(v->mount_point) != 0)
        return;

    switch (chosen_item) {
        case 0: {
            ret = format_volume(v->mount_point);
            break;
        }
        case 1:
        case 2: {
            // workaround for new vold managed volumes that cannot be recognized by pre-built ext2/ext3 bins
            const char *device = v->blk_device2;
            if (device == NULL)
                device = v->blk_device;
            ret = format_unknown_device(device, v->mount_point, list[chosen_item]);
            break;
        }
        default: {
            if (fs_mgr_is_voldmanaged(v)) {
                ret = vold_custom_format_volume(v->mount_point, list[chosen_item], 1) == CommandOkay ? 0 : -1;
            } else if (strcmp(list[chosen_item], "vfat") == 0) {
                sprintf(cmd, "/sbin/newfs_msdos -F 32 -O android -c 8 %s", v->blk_device);
                ret = __system(cmd);
            } else if (strcmp(list[chosen_item], "exfat") == 0) {
                sprintf(cmd, "/sbin/mkfs.exfat %s", v->blk_device);
                ret = __system(cmd);
            } else if (strcmp(list[chosen_item], "ntfs") == 0) {
                sprintf(cmd, "/sbin/mkntfs -f %s", v->blk_device);
                ret = __system(cmd);
            } else if (strcmp(list[chosen_item], "ext4") == 0) {
                char *secontext = NULL;
                if (selabel_lookup(sehandle, &secontext, v->mount_point, S_IFDIR) < 0) {
                    LOGE("cannot lookup security context for %s\n", v->mount_point);
                    ret = make_ext4fs(v->blk_device, v->length, volume, NULL);
                } else {
                    ret = make_ext4fs(v->blk_device, v->length, volume, sehandle);
                    freecon(secontext);
                }
            }
#ifdef USE_F2FS
            else if (strcmp(list[chosen_item], "f2fs") == 0) {
                char* args[] = { "mkfs.f2fs", v->blk_device };
                ret = make_f2fs_main(2, args);
            }
#endif
            break;
        }
    }

#ifndef USE_CHINESE_FONT
    if (ret)
        ui_print("Could not format %s (%s)\n", volume, list[chosen_item]);
    else
        ui_print("Done formatting %s (%s)\n", volume, list[chosen_item]);
#else
    if (ret)
        ui_print("无法格式化%s（%s）\n", volume, list[chosen_item]);
    else
        ui_print("格式化%s（%s）完毕\n", volume, list[chosen_item]);
#endif
}

static void show_partition_sdcard_menu(const char* volume) {
    if (!can_partition(volume)) {
#ifndef USE_CHINESE_FONT
        ui_print("Can't partition device: %s\n", volume);
#else
        ui_print("无法分区设备：%s\n", volume);
#endif
        return;
    }

    char* ext_sizes[] = {
        "128M",
        "256M",
        "512M",
        "1024M",
        "2048M",
        "4096M",
        NULL
    };

    char* swap_sizes[] = {
        "0M",
        "32M",
        "64M",
        "128M",
        "256M",
        NULL
    };

    char* partition_types[] = {
        "ext3",
        "ext4",
        NULL
    };

#ifndef USE_CHINESE_FONT
    const char* ext_headers[] = { "Ext Size", "", NULL };
    const char* swap_headers[] = { "Swap Size", "", NULL };
    const char* fstype_headers[] = { "Partition Type", "", NULL };
#else
    const char* ext_headers[] = { "Ext大小", "", NULL };
    const char* swap_headers[] = { "Swap大小", "", NULL };
    const char* fstype_headers[] = { "分区类型", "", NULL };
#endif

    int ext_size = get_menu_selection(ext_headers, ext_sizes, 0, 0);
    if (ext_size < 0)
        return;

    int swap_size = get_menu_selection(swap_headers, swap_sizes, 0, 0);
    if (swap_size < 0)
        return;

    int partition_type = get_menu_selection(fstype_headers, partition_types, 0, 0);
    if (partition_type < 0)
        return;

    char cmd[PATH_MAX];
    char sddevice[256];
    Volume *vol = volume_for_path(volume);

    // can_partition() ensured either blk_device or blk_device2 has /dev/block/mmcblk format
    if (strstr(vol->blk_device, "/dev/block/mmcblk") != NULL)
        strcpy(sddevice, vol->blk_device);
    else
        strcpy(sddevice, vol->blk_device2);

    // we only want the mmcblk, not the partition
    sddevice[strlen("/dev/block/mmcblkX")] = '\0';
    setenv("SDPATH", sddevice, 1);
    sprintf(cmd, "sdparted -es %s -ss %s -efs %s -s", ext_sizes[ext_size], swap_sizes[swap_size], partition_types[partition_type]);
#ifndef USE_CHINESE_FONT
    ui_print("Partitioning SD Card... please wait...\n");
#else
    ui_print("正在格式化SD卡... 请等待...\n");
#endif
    if (0 == __system(cmd))
#ifndef USE_CHINESE_FONT
        ui_print("Done!\n");
#else
        ui_print("完毕！\n");
#endif
    else
#ifndef USE_CHINESE_FONT
        ui_print("An error occured while partitioning your SD Card. Please see /tmp/recovery.log for more details.\n");
#else
        ui_print("在分区你的SD卡时发生了一个错误。更多细节请检查/tmp/recovery.log。\n");
#endif
}

void show_advanced_power_menu() {
#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Advanced power options", "", NULL };

    char* list[] = { "Reboot Recovery",
                     "Reboot to Bootloader",
                     "Power Off",
                     NULL };
#else
    static const char* headers[] = { "高级重启选项", "", NULL };

    char* list[] = { "重启到Recovery",
                     "重启到Bootloader",
                     "关机",
                     NULL };
#endif

    char bootloader_mode[PROPERTY_VALUE_MAX];
#ifdef BOOTLOADER_CMD_ARG
    // force this extra way to use BoardConfig.mk flags
    sprintf(bootloader_mode, BOOTLOADER_CMD_ARG);
#else
    property_get("ro.bootloader.mode", bootloader_mode, "bootloader");
#endif
    if (strcmp(bootloader_mode, "download") == 0)
#ifndef USE_CHINESE_FONT
        list[1] = "Reboot to Download Mode";
#else
        list[1] = "重启到下载模式";
#endif

    int chosen_item = get_menu_selection(headers, list, 0, 0);
    switch (chosen_item) {
        case 0:
#ifndef USE_CHINESE_FONT
            ui_print("Rebooting recovery...\n");
#else
            ui_print("正在重启到recovery...\n");
#endif
            reboot_main_system(ANDROID_RB_RESTART2, 0, "recovery");
            break;
        case 1:
#ifndef USE_CHINESE_FONT
            ui_print("Rebooting to %s mode...\n", bootloader_mode);
#else
            ui_print("正在重启到%s模式...\n", bootloader_mode);
#endif
            reboot_main_system(ANDROID_RB_RESTART2, 0, bootloader_mode);
            break;
        case 2:
#ifndef USE_CHINESE_FONT
            ui_print("Shutting down...\n");
#else
            ui_print("正在关机...\n");
#endif
            reboot_main_system(ANDROID_RB_POWEROFF, 0, 0);
            break;
    }
}

#ifdef ENABLE_LOKI

#ifdef BOARD_NATIVE_DUALBOOT_SINGLEDATA
#define FIXED_ADVANCED_ENTRIES 8
#else
#define FIXED_ADVANCED_ENTRIES 6
#endif

#else

#ifdef BOARD_NATIVE_DUALBOOT_SINGLEDATA
#define FIXED_ADVANCED_ENTRIES 7
#else
#define FIXED_ADVANCED_ENTRIES 5
#endif

#endif

int show_advanced_menu() {
    char buf[80];
    int i = 0, j = 0, chosen_item = 0, list_index = 0;
    /* Default number of entries if no compile-time extras are added */
    static char* list[MAX_NUM_MANAGED_VOLUMES + FIXED_ADVANCED_ENTRIES + 1];

    char* primary_path = get_primary_storage_path();
    char** extra_paths = get_extra_storage_paths();
    int num_extra_volumes = get_num_extra_volumes();

#ifndef USE_CHINESE_FONT
    static const char* headers[] = { "Advanced Menu", NULL };
#else
    static const char* headers[] = { "高级菜单", NULL };
#endif

    memset(list, 0, MAX_NUM_MANAGED_VOLUMES + FIXED_ADVANCED_ENTRIES + 1);

#ifndef USE_CHINESE_FONT
    list[list_index++] = "Wipe Dalvik Cache";   // 0
    list[list_index++] = "Report Error";        // 1
    list[list_index++] = "Key Test";            // 2
    list[list_index++] = "Show log";            // 3
#else
    list[list_index++] = "清除Dalvik缓存";   // 0
    list[list_index++] = "报告错误";        // 1
    list[list_index++] = "按键测试";            // 2
    list[list_index++] = "查看日志";            // 3
#endif
    list[list_index++] = NULL;                  // 4 (/data/media/0 toggle)

#ifdef BOARD_NATIVE_DUALBOOT_SINGLEDATA
    int index_tdb = list_index++;
    int index_bootmode = list_index++;
#endif

#ifdef ENABLE_LOKI
    int index_loki = list_index++;
    list[index_loki] = NULL;
#endif

#ifndef USE_CHINESE_FONT
    char list_prefix[] = "Partition ";
#else
    char list_prefix[] = "分区 ";
#endif
    if (can_partition(primary_path)) {
        sprintf(buf, "%s%s", list_prefix, primary_path);
        list[FIXED_ADVANCED_ENTRIES] = strdup(buf);
        j++;
    }

    if (extra_paths != NULL) {
        for (i = 0; i < num_extra_volumes; i++) {
            if (can_partition(extra_paths[i])) {
                sprintf(buf, "%s%s", list_prefix, extra_paths[i]);
                list[FIXED_ADVANCED_ENTRIES + j] = strdup(buf);
                j++;
            }
        }
    }
    list[FIXED_ADVANCED_ENTRIES + j] = NULL;

    for (;;) {
        if (is_data_media()) {
            ensure_path_mounted("/data");
            if (use_migrated_storage())
#ifndef USE_CHINESE_FONT
                list[4] = "Sdcard target: /data/media/0";
            else list[4] = "Sdcard target: /data/media";
#else
                list[4] = "SD卡目标：/data/media/0";
            else list[4] = "SD卡目标：/data/media";
#endif
        }

#ifdef BOARD_NATIVE_DUALBOOT_SINGLEDATA
        char tdb_name[PATH_MAX];
        device_get_truedualboot_entry(tdb_name);
        list[index_tdb] = &tdb_name;

        char bootmode_name[PATH_MAX];
        device_get_bootmode(bootmode_name);
        list[index_bootmode] = &bootmode_name;
#endif

#ifdef ENABLE_LOKI
        char item_loki_toggle_menu[MENU_MAX_COLS];
        int enabled = loki_support_enabled();
        if (enabled < 0) {
            list[index_loki] = NULL;
        } else {
            if (enabled)
#ifndef USE_CHINESE_FONT
                ui_format_gui_menu(item_loki_toggle_menu, "Apply Loki Patch", "(x)");
            else
                ui_format_gui_menu(item_loki_toggle_menu, "Apply Loki Patch", "( )");
#else
                ui_format_gui_menu(item_loki_toggle_menu, "应用Loki补丁", "(x)");
            else
                ui_format_gui_menu(item_loki_toggle_menu, "应用Loki补丁", "( )");
#endif
            list[index_loki] = item_loki_toggle_menu;
        }
#endif

        chosen_item = get_filtered_menu_selection(headers, list, 0, 0, sizeof(list) / sizeof(char*));
        if (chosen_item == GO_BACK || chosen_item == REFRESH)
            break;
        switch (chosen_item) {
            case 0: {
                if (0 != ensure_path_mounted("/data"))
                    break;
                if (volume_for_path("/sd-ext") != NULL)
                    ensure_path_mounted("/sd-ext");
                ensure_path_mounted("/cache");
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Confirm wipe?", "Yes - Wipe Dalvik Cache")) {
#else
                if (confirm_selection("确认清除？", "是 - 清除Dalvik缓存")) {
#endif
                    __system("rm -r /data/dalvik-cache");
                    __system("rm -r /cache/dalvik-cache");
                    __system("rm -r /sd-ext/dalvik-cache");
#ifndef USE_CHINESE_FONT
                    ui_print("Dalvik Cache wiped.\n");
#else
                    ui_print("Dalvik缓存清除完毕。\n");
#endif
                }
                ensure_path_unmounted("/data");
                break;
            }
            case 1:
                handle_failure();
                break;
            case 2: {
#ifndef USE_CHINESE_FONT
                ui_print("Outputting key codes.\n");
                ui_print("Go back to end debugging.\n");
#else
                ui_print("正在输出键值。\n");
                ui_print("按返回键来结束调试。\n");
#endif
                int key;
                int action;
                do {
                    key = ui_wait_key();
                    action = device_handle_key(key, 1);
#ifndef USE_CHINESE_FONT
                    ui_print("Key: %d\n", key);
#else
                    ui_print("键值：%d\n", key);
#endif
                } while (action != GO_BACK);
                break;
            }
            case 3:
#ifdef PHILZ_TOUCH_RECOVERY
                show_log_menu();
#else
                ui_printlogtail(24);
                ui_wait_key();
                ui_clear_key_queue();
#endif
                break;
            case 4: {
                if (is_data_media()) {
                    // /data is mounted above in the for() loop: we can directly call use_migrated_storage()
                    if (use_migrated_storage()) {
                        write_string_to_file("/data/media/.cwm_force_data_media", "1");
#ifndef USE_CHINESE_FONT
                        ui_print("storage set to /data/media\n");
#else
                        ui_print("存储设置到/data/media\n");
#endif
                    } else {
                        mkdir("/data/media/0", S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IXOTH); 
                        delete_a_file("/data/media/.cwm_force_data_media");
#ifndef USE_CHINESE_FONT
                        ui_print("storage set to /data/media/0\n");
#else
                        ui_print("存储设置到/data/media/0\n");
#endif
                    }
                    setup_data_media(0); // /data is mounted above in the for() loop. No need to mount/unmount on call
#ifndef USE_CHINESE_FONT
                    ui_print("Reboot to apply settings!\n");
#else
                    ui_print("重启来应用设置！\n");
#endif
                }
                break;
            }
            default:
#ifdef BOARD_NATIVE_DUALBOOT_SINGLEDATA
            if (chosen_item == index_tdb) {
                device_toggle_truedualboot();
                break;
            }
            if (chosen_item == index_bootmode) {
                device_choose_bootmode();
                break;
            }
#endif

#ifdef ENABLE_LOKI
            if (chosen_item == index_loki) {
                toggle_loki_support();
                break;
            }
#endif
            show_partition_sdcard_menu(list[chosen_item] + strlen(list_prefix));
            break;
        }
    }

    for (; j > 0; --j) {
        free(list[FIXED_ADVANCED_ENTRIES + j - 1]);
    }
    return chosen_item;
}

void handle_failure() {
    if (0 != ensure_path_mounted(get_primary_storage_path()))
        return;
    mkdir("/sdcard/clockworkmod", S_IRWXU | S_IRWXG | S_IRWXO);
    __system("cp /tmp/recovery.log /sdcard/clockworkmod/philz_recovery.log");
#ifndef USE_CHINESE_FONT
    ui_print("/tmp/recovery.log copied to /sdcard/clockworkmod/philz_recovery.log\n");
    ui_print("Send file to Phil3759 @xda\n");
#else
    ui_print("/tmp/recovery.log已经复制到/sdcard/clockworkmod/philz_recovery.log\n");
    ui_print("发送文件给Phil3759 @xda\n");
#endif
}

int is_path_mounted(const char* path) {
    Volume* v = volume_for_path(path);
    if (v == NULL) {
        return 0;
    }
    if (strcmp(v->fs_type, "ramdisk") == 0) {
        // the ramdisk is always mounted.
        return 1;
    }

    if (scan_mounted_volumes() < 0)
        return 0;

    const MountedVolume* mv = find_mounted_volume_by_mount_point(v->mount_point);
    if (mv) {
        // volume is already mounted
        return 1;
    }
    return 0;
}

int has_datadata() {
    Volume *vol = volume_for_path("/datadata");
    return vol != NULL;
}

// recovery command helper to create /etc/fstab and link /data/media path
int volume_main(int argc, char **argv) {
    load_volume_table();
    setup_data_media(1);
    return 0;
}

int verify_root_and_recovery() {
    if (!check_root_and_recovery.value)
        return 0;

    if (ensure_path_mounted("/system") != 0)
        return 0;

    int ret = 0;
    struct stat st;
    // check to see if install-recovery.sh is going to clobber recovery
    // install-recovery.sh is also used to run the su daemon on stock rom for 4.3+
    // so verify that doesn't exist...
    if (0 != lstat("/system/etc/.installed_su_daemon", &st)) {
        // check install-recovery.sh exists and is executable
        if (0 == lstat("/system/etc/install-recovery.sh", &st)) {
            if (st.st_mode & (S_IXUSR | S_IXGRP | S_IXOTH)) {
                ui_SetShowText(true);
#ifndef USE_CHINESE_FONT
                if (confirm_selection("ROM may flash stock recovery on boot. Fix?", "Yes - Disable recovery flash")) {
#else
                if (confirm_selection("ROM可能会在开机时将recovery还原为官方版本。是否修正？", "是 - 禁用自动还原")) {
#endif
                    __system("chmod -x /system/etc/install-recovery.sh");
                    ret = 1;
                }
            }
        }
    }

    // do not check permissions if system android version is 4.3+
    // in that case, no need to chmod 06755 as it could break root on +4.3 ROMs
    // for 4.3+, su daemon will set proper 755 permissions before app requests root
    // if no su file is found, recovery will just install su daemon on 4.3 ROMs to gain root
    // credits @Chainfire
    char value[PROPERTY_VALUE_MAX];
    int needs_suid = 1;
    read_config_file("/system/build.prop", "ro.build.version.sdk", value, "0");
    if (atoi(value) >= 18)
        needs_suid = 0;

    int exists = 0; // su exists, regular file or symlink
    int su_nums = 0; // su bin as regular file, not symlink
    if (0 == lstat("/system/bin/su", &st)) {
        exists = 1;
        if (S_ISREG(st.st_mode)) {
            su_nums += 1;
            if (needs_suid && (st.st_mode & (S_ISUID | S_ISGID)) != (S_ISUID | S_ISGID)) {
                ui_SetShowText(true);
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Root access possibly lost. Fix?", "Yes - Fix root (/system/bin/su)")) {
#else
                if (confirm_selection("Root权限可能设置不当。是否修复？", "是 - 修复root（/system/bin/su）")) {
#endif
                    __system("chmod 6755 /system/bin/su");
                    ret = 1;
                }
            }
        }
    }

    if (0 == lstat("/system/xbin/su", &st)) {
        exists = 1;
        if (S_ISREG(st.st_mode)) {
            su_nums += 1;
            if (needs_suid && (st.st_mode & (S_ISUID | S_ISGID)) != (S_ISUID | S_ISGID)) {
                ui_SetShowText(true);
#ifndef USE_CHINESE_FONT
                if (confirm_selection("Root access possibly lost. Fix?", "Yes - Fix root (/system/xbin/su)")) {
#else
                if (confirm_selection("Root权限可能设置不当。是否修复？", "是 - 修复root（/system/xbin/su）")) {
#endif
                    __system("chmod 6755 /system/xbin/su");
                    ret = 1;
                }
            }
        }
    }

    // If we have no root (exists == 0) or we have two su instances (exists == 2), prompt to properly root the device
    if (!exists || su_nums != 1) {
        ui_SetShowText(true);
#ifndef USE_CHINESE_FONT
        if (confirm_selection("Root access is missing/broken. Root device?", "Yes - Apply root (/system/xbin/su)")) {
#else
        if (confirm_selection("Root已经丢失或损坏。Root设备？", "是 - 应用root（/system/xbin/su）")) {
#endif
            __system("/sbin/install-su.sh");
            ret = 2;
        }
    }

    ensure_path_unmounted("/system");
    return ret;
}
