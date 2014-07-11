__<center><big>PhilZ Touch Recovery 6 (ClockworkMod 6 based / Advanced Edition)</big></center>__

.

__Home page__
http://forum.xda-developers.com/showthread.php?t=2201860

汉化作者：dianlujitao xiaolu

<br /><br /><br />当BoardConfig.mk中定义了recovery的字体且为中文字体时，自动编译为中文版，否则编译为英文版<br />
例如：

    BOARD_USE_CUSTOM_RECOVERY_FONT := \"fontcn20_12x34.h\"  
此时编译将使用graphics_cn.c，且recovery界面显示为中文。

    BOARD_USE_CUSTOM_RECOVERY_FONT := \"roboto_15x24.h\"
此时编译将使用原版graphics.c，且recovery界面显示为英文。

<br /><br />制作中参考使用了几位大神/团队提供的代码，特此感谢：
<br />xiaolu : https://github.com/xiaolu/philz_touch_cwm6_cn
<br />PhilZ-cwm6 : https://github.com/PhilZ-cwm6/philz_touch_cwm6
<br />xuefy : https://code.csdn.net/ATX/cwm_bootable_recovery_cn

![汉化](https://gist.github.com/dianlujitao/683376d2ae25aa9de458/raw/e11af4636ced4857762bf2e4b333a616acb037d2/1.png)

#### Building

If you haven't build recovery ever before, please look up the thread linked above.
If you regularly build ROMs/Recoveries for your device, and have a working CWM setup
on your build machine, then you can quickly set up and build Philz Touch recovery as well

Check these two patches are present in your build/ directory
   1. https://github.com/CyanogenMod/android_build/commit/c1b0bb6
   2. https://github.com/CyanogenMod/android_build/commit/6b21727

Clone philz recovery to bootable/recovery-philz folder

    git clone https://github.com/PhilZ-cwm6/philz_touch_cwm6 bootable/recovery-philz -b cm-11.0

Now build with RECOVERY_VARIANT flag set to philz.

    . build/envsetup.sh && lunch && make -j8 recoveryimage RECOVERY_VARIANT=philz

or

    export RECOVERY_VARIANT=philz
    . build/envsetup.sh && lunch && make -j8 recoveryimage
