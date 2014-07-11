/*
 * Copyright (C) 2012 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <unistd.h>
#include <dirent.h>
#include <errno.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <signal.h>
#include <fcntl.h>

#include "minui/minui.h"
#include "cutils/properties.h"
#include "install.h"
#include "common.h"
#include "recovery_ui.h"
#include "adb_install.h"
#include "minadbd/adb.h"

static pthread_t sideload_thread;

static void
set_usb_driver(bool enabled) {
    int fd = open("/sys/class/android_usb/android0/enable", O_WRONLY);
    if (fd < 0) {
#ifndef USE_CHINESE_FONT
        ui_print("failed to open driver control: %s\n", strerror(errno));
#else
        ui_print("打开硬件控制失败：%s\n", strerror(errno));
#endif
        return;
    }
    if (write(fd, enabled ? "1" : "0", 1) < 0) {
#ifndef USE_CHINESE_FONT
        ui_print("failed to set driver control: %s\n", strerror(errno));
#else
        ui_print("设置硬件控制失败：%s\n", strerror(errno));
#endif
    }
    if (close(fd) < 0) {
#ifndef USE_CHINESE_FONT
        ui_print("failed to close driver control: %s\n", strerror(errno));
#else
        ui_print("关闭硬件控制失败：%s\n", strerror(errno));
#endif
    }
}

static void
stop_adbd() {
    property_set("ctl.stop", "adbd");
    set_usb_driver(false);
}


static void
maybe_restart_adbd() {
    char value[PROPERTY_VALUE_MAX+1];
    int len = property_get("ro.debuggable", value, NULL);
    if (len == 1 && value[0] == '1') {
#ifndef USE_CHINESE_FONT
        ui_print("Restarting adbd...\n");
#else
        ui_print("重新启动adbd...\n");
#endif
        set_usb_driver(true);
        property_set("ctl.start", "adbd");
    }
}

struct sideload_waiter_data {
    pid_t child;
};

static struct sideload_waiter_data waiter;

void *adb_sideload_thread(void* v) {
    struct sideload_waiter_data* data = (struct sideload_waiter_data*)v;

    int status;
    waitpid(data->child, &status, 0);
    LOGI("sideload process finished\n");

    ui_cancel_wait_key();

    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        ui_print("status %d\n", WEXITSTATUS(status));
    }

    LOGI("sideload thread finished\n");
    return NULL;
}

void
start_sideload() {
    stop_adbd();
    set_usb_driver(true);

#ifndef USE_CHINESE_FONT
    ui_print("\n\nNow send the package you want to apply\n"
              "to the device with \"adb sideload <filename>\"...\n");
#else
    ui_print("\n\n现在发送你想使用的刷机包到设备上。\n"
              "命令 \"adb sideload <文件名>\"...\n");
#endif

    if ((waiter.child = fork()) == 0) {
        execl("/sbin/recovery", "recovery", "--adbd", NULL);
        _exit(-1);
    }

    pthread_create(&sideload_thread, NULL, &adb_sideload_thread, &waiter);
}

int
apply_from_adb() {

    set_usb_driver(false);
    maybe_restart_adbd();

    // kill the child
    kill(waiter.child, SIGTERM);
    pthread_join(sideload_thread, NULL);
    ui_clear_key_queue();

    struct stat st;
    if (stat(ADB_SIDELOAD_FILENAME, &st) != 0) {
        if (errno == ENOENT) {
#ifndef USE_CHINESE_FONT
            ui_print("No package received.\n");
#else
            ui_print("没有收到刷机包。\n");
#endif
            return INSTALL_NONE; // Go Back / Cancel
        }
#ifndef USE_CHINESE_FONT
        ui_print("Error reading package:\n  %s\n", strerror(errno));
#else
        ui_print("读取刷机包出错：\n  %s\n", strerror(errno));
#endif
        return INSTALL_ERROR;
    }

    int status = install_package(ADB_SIDELOAD_FILENAME);
    ui_reset_progress(); // install_package will set indeterminate progress

    remove(ADB_SIDELOAD_FILENAME);

    return status;
}
