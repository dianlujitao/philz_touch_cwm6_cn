#ifndef __EXTENDEDCOMMANDS_H
#define __EXTENDEDCOMMANDS_H

void
toggle_signature_check();

void
show_choose_zip_menu();

void
set_gather_hidden_files(int enable);

char**
gather_files(const char* basedir, const char* fileExtensionOrDirectory, int* numFiles);

char*
choose_file_menu(const char* basedir, const char* fileExtensionOrDirectory, const char* headers[]);

int
get_filtered_menu_selection(const char** headers, char** items, int menu_only, int initial_selection, int items_count);

int
write_string_to_file(const char* filename, const char* string);

void
show_nandroid_restore_menu(const char* path);

void
choose_default_backup_format();

int
show_nandroid_menu();

int
show_partition_menu();

int
__system(const char *command);

int
show_advanced_menu();

void show_format_sdcard_menu(const char* volume);

int has_datadata();

void handle_failure();

int show_install_update_menu();

int confirm_selection(const char* title, const char* confirm);

int run_and_remove_extendedcommand();

int verify_root_and_recovery();

void write_recovery_version();

void free_string_array(char** array);

int is_path_mounted(const char* path);

int volume_main(int argc, char **argv);

void show_advanced_power_menu();

#ifdef USE_F2FS
extern int make_f2fs_main(int argc, char **argv);
extern int fsck_f2fs_main(int argc, char **argv);
extern int fibmap_main(int argc, char **argv);
#endif

#ifdef ENABLE_LOKI
int loki_support_enabled();
#endif

#ifdef RECOVERY_EXTEND_NANDROID_MENU
void extend_nandroid_menu(char** items, int item_count, int max_items);
void handle_nandroid_menu(int item_count, int selected);
#endif

#endif  // __EXTENDEDCOMMANDS_H
