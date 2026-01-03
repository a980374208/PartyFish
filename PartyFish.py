import time
import os
import webbrowser
import warnings
import cv2
import numpy as np
from PIL import Image, ImageDraw, ImageFont
import threading  # For running the script in a separate thread
import ctypes
from pynput import keyboard, mouse  # 用于监听键盘和鼠标事件，支持热键和鼠标侧键操作 
import datetime
import re
import queue  # 用于线程安全通信
import random  # 用于添加随机延迟

# Windows API常量
WS_CAPTION = 0x00C00000  # 标题栏样式
WS_THICKFRAME = 0x00040000  # 可调整边框样式
GWL_STYLE = -16  # 窗口样式属性
# Windows API常量 - DPI相关
LOGPIXELSX = 88  # 水平DPI
LOGPIXELSY = 90  # 垂直DPI
# 默认DPI值
DEFAULT_DPI = 96

# 获取user32库
user32 = ctypes.windll.user32

# 定义MONITORINFO结构体
class MONITORINFO(ctypes.Structure):
    _fields_ = [
        ("cbSize", ctypes.wintypes.DWORD),
        ("rcMonitor", ctypes.wintypes.RECT),
        ("rcWork", ctypes.wintypes.RECT),
        ("dwFlags", ctypes.wintypes.DWORD)
    ]

# 定义RECT结构体
class RECT(ctypes.Structure):
    _fields_ = [
        ("left", ctypes.wintypes.LONG),
        ("top", ctypes.wintypes.LONG),
        ("right", ctypes.wintypes.LONG),
        ("bottom", ctypes.wintypes.LONG)
    ]

# =========================
# 管理员权限检测
# =========================
def is_admin():
    """检测当前程序是否以管理员权限运行"""
    try:
        return ctypes.windll.shell32.IsUserAnAdmin() != 0
    except:
        return False

# 过滤libpng的iCCP警告（图片ICC配置文件问题）
warnings.filterwarnings("ignore", message=".*iCCP.*")
# 设置OpenCV不显示libpng警告
os.environ["OPENCV_IO_ENABLE_JASPER"] = "0"

import tkinter as tk  # 保留用于兼容性
from tkinter import ttk  # 保留用于兼容性
from tkinter import messagebox
import ttkbootstrap as ttkb
from ttkbootstrap.constants import *
import json  # 用于保存和加载参数
import mss

# =========================
# OCR引擎初始化（使用rapidocr，速度快）
# =========================
try:
    from rapidocr_onnxruntime import RapidOCR
    ocr_engine = RapidOCR()
    OCR_AVAILABLE = True
    print("✅ [OCR] RapidOCR 引擎加载成功")
except ImportError:
    OCR_AVAILABLE = False
    ocr_engine = None
    print("⚠️  [OCR] RapidOCR 未安装，钓鱼记录功能将不可用")

# =========================
# 调试信息管理函数
# =========================
def add_debug_info(info):
    """添加调试信息到队列和历史记录"""
    if not debug_mode:
        return
    
    # 添加到队列（用于实时通知）
    try:
        debug_info_queue.put_nowait(info)
    except queue.Full:
        try:
            debug_info_queue.get_nowait()
            debug_info_queue.put_nowait(info)
        except:
            pass
    
    # 添加到历史记录（用于保留历史信息）
    with debug_history_lock:
        debug_info_history.append(info)
        # 保持历史记录不超过200条
        if len(debug_info_history) > 200:
            debug_info_history.pop(0)  # 移除最旧的记录

# =========================
# 线程锁 - 保护共享变量
# =========================
param_lock = threading.Lock()  # 参数读写锁

# =========================
# 钓鱼记录开关
# =========================
record_fish_enabled = True  # 默认启用钓鱼记录
legendary_screenshot_enabled = True # 默认关闭传说/传奇鱼自动截屏

# =========================
# 钓鱼参数配置管理
# =========================
current_fish_config = 0  # 当前钓鱼配置索引（0-3对应4个配置）
fish_configs = []  # 保存4个钓鱼配置

# =========================
# 字体大小设置
# =========================
font_size = 100  # 默认字体大小为100%
preset_btns = []  # 保存预设按钮引用，用于后续字体更新
input_entries = []  # 保存所有输入框引用，用于后续字体更新
combo_boxes = []  # 保存所有组合框引用，用于后续字体更新
fish_tree_ref = None  # 保存钓鱼记录Treeview引用，用于动态调整列宽

# =========================
# 调试功能设置
debug_mode = True  # 调试模式开关，默认开启
debug_info_queue = queue.Queue(maxsize=200)  # 调试信息队列，用于线程间通信
debug_info_history = []  # 调试信息历史记录，最多保存200条
debug_history_lock = threading.Lock()  # 保护调试历史记录的线程锁
debug_window = None  # 调试窗口引用
debug_auto_refresh = True  # 是否自动刷新调试信息

# 应用窗口检测设置
is_selected_window_active = False  # 当前是否为选中的应用窗口
selected_window_check_interval = 1.0  # 检测间隔时间（秒）
last_selected_window_check = 0  # 上次检测的时间戳
selected_window_check = True  # 是否启用应用窗口检测
selected_window_first_check_done = False  # 启动检测标志，确保只在软件启动时检测一次
selected_window_hwnd = None  # 选中的窗口句柄
selected_window_title = ""  # 选中的窗口标题
is_monster_party_active = False  # 当前是否为猛兽派对窗口

selected_qualitys = ["标准","非凡"]  # 选中的颜色类型

# =========================
# 参数文件路径
# =========================
PARAMETER_FILE = "./parameters.json"
# =========================
# 初始化字体样式
# =========================
def init_font_styles(style, font_size_percent):
    """初始化所有字体样式
    
    Args:
        style: ttkbootstrap.Style对象
        font_size_percent: 字体大小百分比（50-200）
    """
    # 缩放因子
    scale_factor = font_size_percent / 100.0
    
    # 基础字体设置
    base_font = "Segoe UI"
    
    # 定义不同控件的字体大小
    font_sizes = {
        "Title": int(14 * scale_factor),  # 标题字体大小
        "Subtitle": int(8 * scale_factor),  # 副标题字体大小
        "Label": int(9 * scale_factor),  # 普通标签字体大小
        "Entry": int(9 * scale_factor),  # 输入框字体大小
        "Button": int(9 * scale_factor),  # 按钮字体大小
        "Treeview": int(9 * scale_factor),  # 树视图字体大小
        "Combobox": int(9 * scale_factor),  # 组合框字体大小
        "Small": int(7 * scale_factor),  # 小号字体大小
        "Stats": int(10 * scale_factor),  # 统计信息字体大小
        "StatsTotal": int(11 * scale_factor),  # 总计统计字体大小
    }
    
    # 确保字体大小在合理范围内
    for key in font_sizes:
        font_sizes[key] = max(5, min(30, font_sizes[key]))
    
    # 更新各种控件的字体样式
    try:
        # 1. 更新标签样式
        label_font = (base_font, font_sizes["Label"])
        label_styles = [
            "TLabel",
            "TLabelframe.Label",
            "Status.TLabel",
            "Stats.TLabel"
        ]
        for style_name in label_styles:
            style.configure(style_name, font=label_font)
        
        # 2. 更新输入框样式
        entry_font = (base_font, font_sizes["Entry"])
        entry_styles = ["TEntry", "Entry"]
        for style_name in entry_styles:
            style.configure(style_name, font=entry_font)
        
        # 3. 更新组合框样式（包括下拉列表）
        combobox_font = (base_font, font_sizes["Combobox"])
        combobox_styles = [
            "TCombobox",
            "Combobox",
            "TCombobox.Listbox",
            "Combobox.Listbox"
        ]
        for style_name in combobox_styles:
            style.configure(style_name, font=combobox_font)
        
        # 4. 更新复选框样式
        style.configure("TCheckbutton", font=label_font)
        
        # 5. 更新树视图样式
        treeview_font = (base_font, font_sizes["Treeview"])
        treeview_rowheight = int(font_sizes["Treeview"] * 2.2)
        treeview_styles = [
            ("Treeview", treeview_font, treeview_rowheight),
            ("CustomTreeview.Treeview", treeview_font, treeview_rowheight)
        ]
        for style_name, font, rowheight in treeview_styles:
            style.configure(style_name, font=font, rowheight=rowheight)
            style.configure(f"{style_name}.Heading", font=(base_font, font_sizes["Label"], "bold"))
        
        # 6. 更新滑块样式
        scale_styles = ["Horizontal.TScale", "Vertical.TScale"]
        for style_name in scale_styles:
            style.configure(style_name, font=label_font)
        
        # 7. 更新单选按钮样式
        radiobutton_styles = {
            "TRadiobutton": label_font,
            "Toolbutton.TRadiobutton": label_font,
            "InfoOutline.TRadiobutton": label_font,
            "SuccessOutline.TRadiobutton": label_font,
            "DangerOutline.TRadiobutton": label_font,
            "InfoOutline.Toolbutton.TRadiobutton": label_font,
            "SuccessOutline.Toolbutton.TRadiobutton": label_font,
            "DangerOutline.Toolbutton.TRadiobutton": label_font,
            "WarningOutline.Toolbutton.TRadiobutton": label_font,
            "SecondaryOutline.Toolbutton.TRadiobutton": label_font
        }
        for style_name, font in radiobutton_styles.items():
            style.configure(style_name, font=font)
        
        # 8. 更新按钮样式
        button_font = (base_font, font_sizes["Button"])
        
        # 基础按钮样式
        base_button_styles = [
            "TButton",
            "Button",
            "Toolbutton",
            "Outline.TButton",
            "Toolbutton.TButton",
            "Outline.Toolbutton.TButton"
        ]
        for style_name in base_button_styles:
            style.configure(style_name, font=button_font)
        
        # 特定按钮样式变体
        specific_button_styles = [
            "InfoOutline.TButton",
            "SuccessOutline.TButton",
            "DangerOutline.TButton",
            "WarningOutline.TButton",
            "SecondaryOutline.TButton",
            "InfoOutline.Toolbutton.TButton",
            "SuccessOutline.Toolbutton.TButton",
            "DangerOutline.Toolbutton.TButton",
            "WarningOutline.Toolbutton.TButton",
            "SecondaryOutline.Toolbutton.TButton",
            "SuccessOutline.Toolbutton",
            "DangerOutline.Toolbutton",
            "InfoOutline.Toolbutton",
            "WarningOutline.Toolbutton",
            "SecondaryOutline.Toolbutton"
        ]
        for style_name in specific_button_styles:
            style.configure(style_name, font=button_font)
        
        # 颜色变体按钮样式
        color_variants = ["Primary", "Secondary", "Success", "Info", "Warning", "Danger", "Light", "Dark"]
        color_button_templates = [
            f"{{}}.TButton",
            f"{{}}Outline.TButton",
            f"{{}}.Toolbutton.TButton",
            f"{{}}Outline.Toolbutton.TButton"
        ]
        bootstyle_templates = [
            f"{{}}-toolbutton",
            f"{{}}-outline-toolbutton"
        ]
        
        for color in color_variants:
            # 颜色按钮样式
            for template in color_button_templates:
                style_name = template.format(color)
                style.configure(style_name, font=button_font)
            
            # 直接使用bootstyle名称作为样式
            for template in bootstyle_templates:
                style_name = template.format(color.lower())
                style.configure(style_name, font=button_font)
    except Exception as e:
        print(f"Error initializing font styles: {e}")

# =========================
# 更新所有控件的字体
# =========================
def update_all_widget_fonts(widget, style, font_size_percent):
    """更新所有控件的字体大小
    
    Args:
        widget: 根控件
        style: ttkbootstrap.Style对象
        font_size_percent: 字体大小百分比（50-200）
    """
    # 初始化字体样式 - 这会更新所有控件的样式字体
    init_font_styles(style, font_size_percent)
    
    # 缩放因子
    scale_factor = font_size_percent / 100.0
    base_font = "Segoe UI"
    
    # 定义默认字体大小
    default_sizes = {
        "Label": 9,
        "Button": 9,
        "Entry": 9,
        "Combobox": 9,
        "Radiobutton": 9,
        "Checkbutton": 9,
        "Treeview": 9,
    }
    
    # 递归更新所有控件的字体
    def update_widget_font(w):
        try:
            widget_type = type(w).__name__
            
            # 确定默认字体大小
            if widget_type in ["Label", "TLabel", "TTKLabel"] or "Label" in widget_type:
                default_size = default_sizes["Label"]
            elif widget_type in ["Button", "TButton", "TTKButton"] or "Button" in widget_type:
                default_size = default_sizes["Button"]
            elif widget_type in ["Entry", "TEntry", "TTKEntry"] or "Entry" in widget_type:
                default_size = default_sizes["Entry"]
            elif widget_type in ["Combobox", "TCombobox", "TTKCombobox"] or "Combobox" in widget_type:
                default_size = default_sizes["Combobox"]
            elif widget_type in ["Radiobutton", "TRadiobutton", "TTKRadiobutton"] or "Radiobutton" in widget_type:
                default_size = default_sizes["Radiobutton"]
            elif widget_type in ["Checkbutton", "TCheckbutton", "TTKCheckbutton"] or "Checkbutton" in widget_type:
                default_size = default_sizes["Checkbutton"]
            elif widget_type in ["Treeview", "TTKTreeview"] or "Treeview" in widget_type:
                default_size = default_sizes["Treeview"]
            elif widget_type in ["Frame", "TFrame", "TTKFrame"] or "Frame" in widget_type:
                # 跳过框架，只处理其内部控件
                pass
            else:
                # 对于其他控件类型，尝试将其作为按钮处理，特别是ttkbootstrap按钮
                # 检查控件是否有configure方法，尝试获取其样式
                try:
                    style_name = w.cget("style")
                    if "Button" in style_name or "Toolbutton" in style_name:
                        default_size = default_sizes["Button"]
                    else:
                        return  # 跳过不支持字体的控件
                except:
                    return  # 跳过不支持字体的控件
            
            # 计算新字体大小
            new_size = int(default_size * scale_factor)
            
            # 构建新字体
            new_font = (base_font, new_size)
            
            # 特殊处理标题和粗体文本
            try:
                if widget_type == "Label" and ("PartyFish" in str(w.cget("text")) or "标题" in str(w.cget("text"))):
                    title_size = int(14 * scale_factor)
                    title_size = max(5, min(24, title_size))  # 限制标题最大24px
                    new_font = (base_font, title_size, "bold")
                elif widget_type == "Label" and "统计" in str(w.cget("text")):
                    stat_size = int(10 * scale_factor)
                    stat_size = max(5, min(18, stat_size))  # 限制统计标签最大18px
                    new_font = (base_font, stat_size, "bold")
                elif widget_type == "Label":
                    # 对所有标签文本设置字体大小限制，确保150%字体下不会过大
                    label_size = int(default_size * scale_factor)
                    label_size = max(5, min(13, label_size))  # 限制普通标签最大13px
                    new_font = (base_font, label_size)
            except:
                pass
            
            # 对其他控件类型也设置合理的字体大小限制
            new_size = max(5, min(14, new_size))
            
            # 尝试直接更新控件字体，如果失败则跳过
            try:
                w.configure(font=new_font)
            except Exception as e:
                # 对于ttkbootstrap按钮，可能无法直接设置字体，需要通过样式更新
                # 这已经在init_font_styles中处理了，所以这里可以安全跳过
                pass
            
        except Exception as e:
            # 跳过不支持字体的控件
            pass
        
        # 递归处理子控件
        for child in w.winfo_children():
            update_widget_font(child)
    
    # 开始递归更新
    update_widget_font(widget)
    
    # 重新配置所有已创建的控件，应用新的样式设置
    widget.update_idletasks()

# =========================
# 加载和保存参数
# =========================
def save_parameters():
    global fish_configs
    
    # 确保fish_configs有4个配置，每个配置都有name字段
    while len(fish_configs) < 4:
        fish_configs.append({
            "name": f"配置 {len(fish_configs) + 1}",
            "t": t,
            "leftclickdown": leftclickdown,
            "leftclickup": leftclickup,
            "times": times,
            "paogantime": paogantime,
            "jiashi_var": jiashi_var,
            "random_delay": random_delay  # 添加随机延迟参数
        })
    
    # 确保每个配置都有name字段和random_delay字段
    for i in range(4):
        if "name" not in fish_configs[i]:
            fish_configs[i]["name"] = f"配置 {i + 1}"
        if "random_delay" not in fish_configs[i]:
            fish_configs[i]["random_delay"] = random_delay
    
    # 更新当前配置
    # 保留当前配置的name字段
    current_name = fish_configs[current_fish_config].get("name", f"配置 {current_fish_config + 1}")
    fish_configs[current_fish_config] = {
        "name": current_name,
        "t": t,
        "leftclickdown": leftclickdown,
        "leftclickup": leftclickup,
        "times": times,
        "paogantime": paogantime,
        "jiashi_var": jiashi_var,
        "random_delay": random_delay  # 添加随机延迟参数
    }
    
    params = {
        "t": t,
        "leftclickdown": leftclickdown,
        "leftclickup": leftclickup,
        "times": times,
        "paogantime": paogantime,
        "jiashi_var": jiashi_var,  # 保存加时参数
        "random_delay": random_delay,  # 保存随机延迟参数
        "resolution": resolution_choice,  # 保存分辨率选择
        "custom_width": TARGET_WIDTH,  # 保存自定义宽度
        "custom_height": TARGET_HEIGHT,  # 保存自定义高度
        "hotkey": hotkey_name,  # 保存热键设置（如 "Ctrl+Shift+A" 或 "F2"）
        "release_hotkey": release_hotkey_name,  # 保存放生热键设置（如 "F4"）
        "record_fish_enabled": record_fish_enabled,  # 保存钓鱼记录开关状态
        "legendary_screenshot_enabled": legendary_screenshot_enabled,  # 保存传说/传奇鱼自动截屏开关状态
        "font_size": font_size,  # 保存字体大小设置
        "fish_configs": fish_configs,  # 保存4个钓鱼配置
        "current_fish_config": current_fish_config,  # 保存当前配置索引
        "random_delay_enabled": random_delay_enabled,  # 保存随机延迟开关状态
        "selected_window_check": selected_window_check,  # 保存应用窗口检测开关状态
        "selected_window_check_interval": selected_window_check_interval,  # 保存应用窗口检测间隔
        "selected_window_title": selected_window_title  # 保存选中的窗口标题
    }
    try:
        with open(PARAMETER_FILE, "w") as f:
            json.dump(params, f)
        print("💾 [保存] 参数已成功保存到文件")
    except Exception as e:
        print(f"❌ [错误] 保存参数失败: {e}")

def load_parameters():
    global t, leftclickdown, leftclickup, times, paogantime, jiashi_var, random_delay
    global resolution_choice, TARGET_WIDTH, TARGET_HEIGHT, SCALE_X, SCALE_Y
    global hotkey_name, hotkey_modifiers, hotkey_main_key, release_hotkey_name, release_hotkey_modifiers, release_hotkey_main_key
    global font_size, fish_configs, current_fish_config
    try:
            with open(PARAMETER_FILE, "r") as f:
                params = json.load(f)
                # 加载基本参数
                t = params.get("t", t)
                leftclickdown = params.get("leftclickdown", leftclickdown)
                leftclickup = params.get("leftclickup", leftclickup)
                times = params.get("times", times)
                paogantime = params.get("paogantime", paogantime)
                jiashi_var = params.get("jiashi_var", jiashi_var)
                # 加载随机延迟参数
                random_delay = params.get("random_delay", random_delay)
                resolution_choice = params.get("resolution", "2K")
                # 加载钓鱼记录开关状态
                global record_fish_enabled
                record_fish_enabled = params.get("record_fish_enabled", True)
                # 加载传说/传奇鱼自动截屏开关状态
                global legendary_screenshot_enabled
                legendary_screenshot_enabled = params.get("legendary_screenshot_enabled", True)
                # 加载随机延迟开关状态
                global random_delay_enabled
                random_delay_enabled = params.get("random_delay_enabled", True)  # 默认启用
                # 加载应用窗口检测参数
                global selected_window_check, selected_window_check_interval, selected_window_title
                selected_window_check = params.get("selected_window_check", True)  # 默认启用
                selected_window_check_interval = params.get("selected_window_check_interval", 1.0)  # 默认1秒
                selected_window_title = params.get("selected_window_title", "")  # 默认空标题
                # 加载字体大小设置
                font_size = params.get("font_size", 100)  # 默认100%
                # 加载热键设置（新格式支持组合键）
                saved_hotkey = params.get("hotkey", "F2")
                try:
                    modifiers, main_key, main_key_name = parse_hotkey_string(saved_hotkey)
                    if main_key is not None:
                        hotkey_name = saved_hotkey
                        hotkey_modifiers = modifiers
                        hotkey_main_key = main_key
                except Exception:
                    # 解析失败，使用默认值
                    hotkey_name = "F2"
                    hotkey_modifiers = set()
                    hotkey_main_key = keyboard.Key.f2

                 # 加载放生热键设置
                saved_release_hotkey = params.get("release_hotkey", "F4")
                try:
                    modifiers, main_key, main_key_name = parse_hotkey_string(saved_release_hotkey)
                    if main_key is not None:
                        release_hotkey_name = saved_release_hotkey
                        release_hotkey_modifiers = modifiers
                        release_hotkey_main_key = main_key
                except Exception:
                    # 解析失败，使用默认值
                    release_hotkey_name = "F4"
                    release_hotkey_modifiers = set()
                    release_hotkey_main_key = keyboard.Key.f4

                # 加载钓鱼配置
                loaded_configs = params.get("fish_configs", [])
                if loaded_configs:
                    fish_configs = loaded_configs
                    # 确保有4个配置
                    while len(fish_configs) < 4:
                        fish_configs.append({
                            "name": f"配置 {len(fish_configs) + 1}",
                            "t": t,
                            "leftclickdown": leftclickdown,
                            "leftclickup": leftclickup,
                            "times": times,
                            "paogantime": paogantime,
                            "jiashi_var": jiashi_var,
                            "random_delay": random_delay
                        })
                    # 确保每个配置都有name字段和random_delay字段
                    for i in range(4):
                        if "name" not in fish_configs[i]:
                            fish_configs[i]["name"] = f"配置 {i + 1}"
                        if "random_delay" not in fish_configs[i]:
                            fish_configs[i]["random_delay"] = random_delay
                    # 加载当前配置索引
                    current_fish_config = params.get("current_fish_config", 0)
                    # 应用当前配置
                    config = fish_configs[current_fish_config]
                    t = config["t"]
                    leftclickdown = config["leftclickdown"]
                    leftclickup = config["leftclickup"]
                    times = config["times"]
                    paogantime = config["paogantime"]
                    jiashi_var = config["jiashi_var"]
                    random_delay = config.get("random_delay", random_delay)
                else:
                    # 旧格式，初始化4个配置
                    fish_configs = []
                    for i in range(4):
                        fish_configs.append({
                            "name": f"配置 {i + 1}",
                            "t": t,
                            "leftclickdown": leftclickdown,
                            "leftclickup": leftclickup,
                            "times": times,
                            "paogantime": paogantime,
                            "jiashi_var": jiashi_var,
                            "random_delay": random_delay
                        })
                    current_fish_config = 0
            # 获取系统缩放比例
            system_scaling = get_system_scaling()
            
            # 根据分辨率选择设置目标分辨率
            if resolution_choice == "1080P":
                TARGET_WIDTH, TARGET_HEIGHT = 1920, 1080
            elif resolution_choice == "2K":
                TARGET_WIDTH, TARGET_HEIGHT = 2560, 1440
            elif resolution_choice == "4K":
                TARGET_WIDTH, TARGET_HEIGHT = 3840, 2160
            elif resolution_choice == "current":
                # 使用当前系统分辨率（已返回真实物理分辨率）
                TARGET_WIDTH, TARGET_HEIGHT = get_current_screen_resolution()
                print(f"📋 [信息] 检测到系统缩放: {system_scaling}%，使用真实分辨率: {TARGET_WIDTH}×{TARGET_HEIGHT}")
            elif resolution_choice == "自定义":
                TARGET_WIDTH = params.get("custom_width", 2560)
                TARGET_HEIGHT = params.get("custom_height", 1440)
            # 重新计算缩放比例
            SCALE_X = TARGET_WIDTH / BASE_WIDTH
            SCALE_Y = TARGET_HEIGHT / BASE_HEIGHT
            calculate_scale_factors()  # 计算所有缩放比例（包括SCALE_UNIFORM）
            update_region_coords()  # 更新区域坐标
            #print(f"已加载参数: 循环间隔 = {t}, 收线时间 = {leftclickdown}, 放线时间 = {leftclickup}, 最大拉杆次数 = {times}，抛竿时间 = {paogantime}, 加时 = {jiashi_var}")
    except FileNotFoundError:
        print("📄 [信息] 未找到参数文件，使用默认值")
        # 初始化4个默认配置
        fish_configs = []
        for i in range(4):
            fish_configs.append({
                "name": f"配置 {i + 1}",
                "t": t,
                "leftclickdown": leftclickdown,
                "leftclickup": leftclickup,
                "times": times,
                "paogantime": paogantime,
                "jiashi_var": jiashi_var
            })
        current_fish_config = 0
    except Exception as e:
        print(f"❌ [错误] 加载参数失败: {e}")
        # 初始化4个默认配置
        fish_configs = []
        for i in range(4):
            fish_configs.append({
                "name": f"配置 {i + 1}",
                "t": t,
                "leftclickdown": leftclickdown,
                "leftclickup": leftclickup,
                "times": times,
                "paogantime": paogantime,
                "jiashi_var": jiashi_var
            })
        current_fish_config = 0

# =========================
# 更新参数
# =========================
def update_parameters(t_var, leftclickdown_var, leftclickup_var, times_var, paogantime_var, jiashi_var_option, random_delay_percent_var,
                      resolution_var, custom_width_var, custom_height_var, hotkey_var=None,release_hotkey_var=None, record_fish_var=None,
                      legendary_screenshot_var=None, random_delay_enabled_var=None):
    global t, leftclickdown, leftclickup, times, paogantime, jiashi_var, random_delay
    global resolution_choice, TARGET_WIDTH, TARGET_HEIGHT, SCALE_X, SCALE_Y
    global hotkey_name, hotkey_modifiers, hotkey_main_key, release_hotkey_name, release_hotkey_modifiers, release_hotkey_main_key
    global record_fish_enabled, legendary_screenshot_enabled, random_delay_enabled

    with param_lock:  # 使用锁保护参数更新
        try:
            t = float(t_var.get())
            leftclickdown = float(leftclickdown_var.get())
            leftclickup = float(leftclickup_var.get())
            times = int(times_var.get())
            paogantime = float(paogantime_var.get())
            jiashi_var = jiashi_var_option.get()
            random_delay = int(random_delay_percent_var.get())  # 获取随机延迟百分比
            
            # 更新钓鱼记录开关状态
            if record_fish_var is not None:
                record_fish_enabled = bool(record_fish_var.get())
            
            # 更新传说/传奇鱼自动截屏开关状态
            if legendary_screenshot_var is not None:
                legendary_screenshot_enabled = bool(legendary_screenshot_var.get())
            
            # 更新随机延迟开关状态
            if random_delay_enabled_var is not None:
                random_delay_enabled = bool(random_delay_enabled_var.get())

            # 更新热键设置（新格式支持组合键）
            if hotkey_var is not None:
                new_hotkey = hotkey_var.get()
                if new_hotkey:
                    try:
                        modifiers, main_key, main_key_name = parse_hotkey_string(new_hotkey)
                        if main_key is not None:
                            hotkey_name = new_hotkey
                            hotkey_modifiers = modifiers
                            hotkey_main_key = main_key
                    except Exception:
                        pass  # 保持原有热键设置

            #更新放生热键设置（新格式支持组合键）
            if release_hotkey_var is not None:
                new_release_hotkey = release_hotkey_var.get()
                if new_release_hotkey:
                    try:
                        modifiers, main_key, main_key_name = parse_hotkey_string(new_release_hotkey)
                        if main_key is not None:
                            release_hotkey_name = new_release_hotkey
                            release_hotkey_modifiers = modifiers
                            release_hotkey_main_key = main_key
                    except Exception:
                        pass  # 保持原有放生热键设置

            # 更新分辨率设置
            resolution_choice = resolution_var.get()
            
            # 获取系统缩放比例
            system_scaling = get_system_scaling()
            
            if resolution_choice == "1080P":
                TARGET_WIDTH, TARGET_HEIGHT = 1920, 1080
            elif resolution_choice == "2K":
                TARGET_WIDTH, TARGET_HEIGHT = 2560, 1440
            elif resolution_choice == "4K":
                TARGET_WIDTH, TARGET_HEIGHT = 3840, 2160
            elif resolution_choice == "current":
                # 使用当前系统分辨率（已返回真实物理分辨率）
                TARGET_WIDTH, TARGET_HEIGHT = get_current_screen_resolution()
                print(f"📋 [信息] 检测到系统缩放: {system_scaling}%，使用真实分辨率: {TARGET_WIDTH}×{TARGET_HEIGHT}")
                # 更新输入框显示，确保用户看到实际应用的值
                custom_width_var.set(str(TARGET_WIDTH))
                custom_height_var.set(str(TARGET_HEIGHT))
            elif resolution_choice == "自定义":
                # 自定义分辨率限制
                min_width, max_width = 800, 7680
                min_height, max_height = 600, 4320
                
                # 获取输入值
                width = int(custom_width_var.get())
                height = int(custom_height_var.get())
                
                # 应用限制
                TARGET_WIDTH = max(min_width, min(max_width, width))
                TARGET_HEIGHT = max(min_height, min(max_height, height))
                
                # 更新输入框显示，确保用户看到实际应用的值
                custom_width_var.set(str(TARGET_WIDTH))
                custom_height_var.set(str(TARGET_HEIGHT))

            # 重新计算缩放比例
            SCALE_X = TARGET_WIDTH / BASE_WIDTH
            SCALE_Y = TARGET_HEIGHT / BASE_HEIGHT
            calculate_scale_factors()  # 计算所有缩放比例（包括SCALE_UNIFORM）
            update_region_coords()  # 更新区域坐标

            print("┌" + "─" * 56 + "┐")
            print("│  ⚙️  参数更新成功                                  │")
            print("├" + "─" * 56 + "┤")
            print(f"│  ⏱️  循环间隔: {t:.1f}s    📍 收线: {leftclickdown:.1f}s    📍 放线: {leftclickup:.1f}s")
            print(f"│  🎣 最大拉杆: {times}次     ⏳ 抛竿: {paogantime:.1f}s    {'✅' if jiashi_var else '❌'} 加时: {'是' if jiashi_var else '否'}")
            print(f"│  🖥️  分辨率: {resolution_choice} ({TARGET_WIDTH}×{TARGET_HEIGHT})")
            print(f"│  🎲 随机延迟: {'✅' if random_delay_enabled else '❌'} {random_delay}%    📐 缩放比例: X={SCALE_X:.2f}  Y={SCALE_Y:.2f}")
            print(f"│  ⌨️  热键: {hotkey_name}")
            print(f"│  ⌨️  放生热键: {release_hotkey_name}")
            print("└" + "─" * 56 + "┘")
            # 保存到文件
            save_parameters()
        except ValueError as e:
            print(f"⚠️  [警告] 请输入有效的数值！错误: {e}")
        except Exception as e:
            print(f"❌ [错误] 更新参数失败: {e}")

# =========================
# 调试功能
# =========================
def show_debug_window():
    """显示调试窗口，展示OCR识别的详细信息"""
    global debug_window, debug_auto_refresh
    
    if debug_window is not None and debug_window.winfo_exists():
        # 如果调试窗口已存在，先销毁它
        debug_window.destroy()
    
    # 创建调试窗口
    debug_window = ttkb.Toplevel()
    debug_window.title("🐛 调试信息")
    debug_window.geometry("800x600")
    debug_window.minsize(600, 400)
    debug_window.resizable(True, True)
    
    # 设置窗口图标（与主窗口相同）
    try:
        import sys
        import os
        if hasattr(sys, '_MEIPASS'):
            icon_path = os.path.join(sys._MEIPASS, "666.ico")
        else:
            icon_path = "666.ico"
        debug_window.iconbitmap(icon_path)
    except:
        pass
    
    # 主框架
    main_frame = ttkb.Frame(debug_window, padding=12)
    main_frame.pack(fill=BOTH, expand=YES)
    
    # 标题
    title_label = ttkb.Label(main_frame, text="OCR 调试信息", font=("Segoe UI", 14, "bold"), bootstyle="primary")
    title_label.pack(pady=(0, 10))
    
    # 控制框架
    control_frame = ttkb.Frame(main_frame)
    control_frame.pack(fill=X, pady=(0, 10))
    
    # 自动刷新开关
    auto_refresh_var = ttkb.BooleanVar(value=debug_auto_refresh)
    auto_refresh_check = ttkb.Checkbutton(
        control_frame, 
        text="自动刷新", 
        variable=auto_refresh_var, 
        bootstyle="info"
    )
    auto_refresh_check.pack(side=LEFT)
    
    def toggle_auto_refresh():
        """切换自动刷新状态"""
        global debug_auto_refresh
        debug_auto_refresh = auto_refresh_var.get()
    
    auto_refresh_check.configure(command=toggle_auto_refresh)
    
    # 屏幕分辨率信息标签，显示在自动刷新右边
    def update_resolution_label():
        """更新分辨率信息标签"""
        max_width, max_height = get_max_screen_resolution()
        current_width, current_height = get_current_screen_resolution()  # 使用实际系统分辨率
        actual_width, actual_height = get_actual_screen_resolution()  # 真实物理分辨率
        system_scaling = get_system_scaling()  # 系统缩放比例
        
        resolution_text = f"🖥️  当前分辨率: {current_width}×{current_height} | 真实分辨率: {actual_width}×{actual_height}\n" + \
                          f"📏 系统缩放: {system_scaling}% | 最大分辨率: {max_width}×{max_height}\n" + \
                          f"📐 缩放比例: X={SCALE_X:.2f} Y={SCALE_Y:.2f} 统一={SCALE_UNIFORM:.2f}"
        resolution_label.configure(text=resolution_text)
    
    resolution_label = ttkb.Label(
        control_frame, 
        font=("Consolas", 10),  # 增大字体大小，提高可读性
        bootstyle="info"
    )
    resolution_label.pack(side=TOP, fill=X, pady=(5, 0))  # 调整为顶部填充，增加垂直间距
    
    # 初始更新分辨率标签
    update_resolution_label()
    
    # 手动触发OCR按钮
    def manual_ocr_trigger():
        """手动触发OCR识别，用于测试调试功能"""
        temp_scr = None
        try:
            # 临时初始化scr对象
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "manual_ocr_start",
                "message": "开始手动触发OCR识别，正在初始化截图对象..."
            }
            add_debug_info(debug_info)
            update_debug_info()
            
            # 初始化mss截图对象
            temp_scr = mss.mss()
            
            # 添加调试信息，记录截图对象初始化成功
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "manual_ocr_scr_init",
                "message": "截图对象初始化成功，正在执行OCR识别...",
                "scr_type": type(temp_scr).__name__
            }
            add_debug_info(debug_info)
            update_debug_info()
            
            # 调用OCR识别相关函数，传入临时初始化的scr对象
            img = capture_fish_info_region(temp_scr)
            if img is not None:
                fish_name, fish_quality, fish_weight = recognize_fish_info_ocr(img)
                # 添加调试信息，通知用户手动触发成功
                debug_info = {
                    "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                    "action": "manual_ocr_complete",
                    "parsed_info": {
                        "鱼名": fish_name if fish_name else "未识别",
                        "品质": fish_quality if fish_quality else "未识别",
                        "重量": fish_weight if fish_weight else "未识别"
                    },
                    "message": "手动触发OCR识别完成",
                    "image_shape": img.shape,
                    "scr_type": type(temp_scr).__name__
                }
                add_debug_info(debug_info)
            else:
                # 添加调试信息，通知用户OCR识别失败
                debug_info = {
                    "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                    "action": "manual_ocr_failed",
                    "message": "OCR识别失败，无法截取鱼信息区域",
                    "scr_type": type(temp_scr).__name__
                }
                add_debug_info(debug_info)
            
            # 立即更新调试信息显示
            update_debug_info()
        except Exception as e:
            # 添加错误调试信息
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "manual_ocr_error",
                "error": f"手动触发OCR识别失败: {str(e)}",
                "exception_type": type(e).__name__
            }
            add_debug_info(debug_info)
            # 立即更新调试信息显示
            update_debug_info()
        finally:
            # 确保scr对象正确关闭
            if temp_scr is not None:
                try:
                    temp_scr.close()
                    # 添加调试信息，记录截图对象关闭
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "manual_ocr_scr_close",
                        "message": "截图对象已关闭",
                        "scr_type": type(temp_scr).__name__ if temp_scr is not None else "未知"
                    }
                    add_debug_info(debug_info)
                    update_debug_info()
                except Exception as close_error:
                    # 添加错误调试信息
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "manual_ocr_scr_close_error",
                        "error": f"关闭截图对象失败: {str(close_error)}",
                        "exception_type": type(close_error).__name__
                    }
                    add_debug_info(debug_info)
                    update_debug_info()
    
    manual_ocr_btn = ttkb.Button(
        control_frame, 
        text="🔍 手动触发OCR", 
        command=manual_ocr_trigger, 
        bootstyle="primary-outline"
    )
    manual_ocr_btn.pack(side=RIGHT, padx=(10, 0))
    
    # 应用窗口检测功能
    window_detection_frame = ttkb.Frame(control_frame, bootstyle="info")
    window_detection_frame.pack(fill=X, pady=(10, 0))
    

    
    # 窗口选择下拉框
    window_list_var = ttkb.StringVar(value="选择窗口...")
    window_list_combobox = ttkb.Combobox(
        window_detection_frame,
        textvariable=window_list_var,
        width=35,
        bootstyle="info",
        state="readonly"
    )
    window_list_combobox.pack(side=LEFT, padx=5, pady=5, fill=X, expand=True)
    
    # 刷新窗口列表按钮
    def refresh_window_list():
        """刷新窗口列表"""
        windows = get_all_windows()
        window_titles = [title for _, title in windows]
        window_list_combobox['values'] = window_titles
        if window_titles:
            window_list_var.set(window_titles[0])
        else:
            window_list_var.set("无可用窗口")
    
    window_refresh_btn = ttkb.Button(
        window_detection_frame,
        text="刷新",
        command=refresh_window_list,
        bootstyle="info",
        width=6
    )
    window_refresh_btn.pack(side=LEFT, padx=5, pady=5)
    
    # 窗口选择变化时更新全局变量
    def on_window_selection_change(event):
        """窗口选择变化时更新全局变量"""
        global selected_window_hwnd, selected_window_title
        selected_title = window_list_var.get()
        windows = get_all_windows()
        for hwnd, title in windows:
            if title == selected_title:
                selected_window_hwnd = hwnd
                selected_window_title = title
                break
    
    window_list_combobox.bind("<<ComboboxSelected>>", on_window_selection_change)
    
    # 初始刷新窗口列表
    refresh_window_list()
    
    # 检测选定窗口按钮
    def on_check_selected_window():
        """检测选定窗口样式并显示结果"""
        result = check_window_style(selected_window_hwnd)
        # 添加调试信息到队列
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "selected_window_detection",
            "message": "应用窗口检测结果",
            "ocr_result": [],
            "parsed_info": {
                "是否为选中窗口": "是" if result["is_selected_window"] else "否",
                "窗口标题": result["window_title"],
                "窗口类名": result["window_class"],
                "窗口尺寸": f"{result['window_width']}x{result['window_height']}",
                "显示器分辨率": f"{result['screen_width']}x{result['screen_height']}",
                "是否无窗口边框样式": "是" if result["has_no_border"] else "否",
                "是否尺寸匹配": "是" if result["size_match"] else "否",
                "是否为全屏无边框窗口": "是" if result["is_fullscreen_borderless"] else "否"
            }
        }
        add_debug_info(debug_info)
        # 更新调试信息显示
        update_debug_info()
    
    selected_window_btn = ttkb.Button(
        window_detection_frame, 
        text="检测选定窗口", 
        command=on_check_selected_window, 
        bootstyle="success"
    )
    selected_window_btn.pack(side=LEFT, padx=5, pady=5)
    
    # 刷新按钮
    refresh_btn = ttkb.Button(
        control_frame, 
        text="🔄 刷新", 
        command=lambda: update_debug_info(), 
        bootstyle="info-outline"
    )
    refresh_btn.pack(side=RIGHT, padx=(10, 0))
    
    # 调试模式开关
    debug_mode_var = ttkb.BooleanVar(value=debug_mode)
    debug_mode_check = ttkb.Checkbutton(
        control_frame, 
        text="启用调试模式", 
        variable=debug_mode_var, 
        bootstyle="warning"
    )
    debug_mode_check.pack(side=RIGHT)
    
    def toggle_debug_mode():
        """切换调试模式"""
        global debug_mode
        debug_mode = debug_mode_var.get()
    
    debug_mode_check.configure(command=toggle_debug_mode)
    
    # 信息显示区域
    info_frame = ttkb.Frame(main_frame)
    info_frame.pack(fill=BOTH, expand=YES)
    
    # 滚动条
    scrollbar = ttkb.Scrollbar(info_frame, orient="vertical")
    scrollbar.pack(side=RIGHT, fill=Y)
    
    # 文本框
    debug_text = tk.Text(
        info_frame,
        wrap="word",
        font=("Consolas", 10),
        bg="#1e1e1e",
        fg="#d4d4d4",
        insertbackground="white",
        yscrollcommand=scrollbar.set
    )
    debug_text.pack(fill=BOTH, expand=YES)
    scrollbar.configure(command=debug_text.yview)
    
    # 添加行号
    debug_text.tag_configure("line_number", foreground="#606060")
    debug_text.tag_configure("timestamp", foreground="#569cd6")
    debug_text.tag_configure("region", foreground="#4ec9b0")
    debug_text.tag_configure("ocr_result", foreground="#ce9178")
    debug_text.tag_configure("parsed_info", foreground="#dcdcaa")
    debug_text.tag_configure("error", foreground="#f48771")
    
    def update_debug_info():
        """更新调试信息显示"""
        debug_text.delete(1.0, END)
        
        # 显示调试模式状态
        if not debug_mode:
            debug_text.insert(END, "🔴 调试模式已关闭\n", "error")
            debug_text.insert(END, "请勾选'启用调试模式'以查看OCR调试信息\n")
            return
        
        # 获取屏幕分辨率信息
        max_width, max_height = get_max_screen_resolution()
        current_width, current_height = TARGET_WIDTH, TARGET_HEIGHT
        
        # 获取历史记录（线程安全）
        with debug_history_lock:
            # 复制当前历史记录，避免在迭代时被修改
            debug_info_list = list(debug_info_history)
        
        # 显示调试模式状态和历史记录信息
        debug_text.insert(END, "🟢 调试模式已启用\n", "timestamp")
        debug_text.insert(END, f"📊 历史记录: 当前共有 {len(debug_info_list)} 条调试信息\n")
        debug_text.insert(END, f"🔄 自动刷新: {'开启' if debug_auto_refresh else '关闭'}\n")
        debug_text.insert(END, "-" * 60 + "\n")
        
        # 显示信息统计
        debug_text.insert(END, f"📋 共显示 {len(debug_info_list)} 条调试信息\n", "timestamp")
        debug_text.insert(END, "显示所有日志：\n")
        debug_text.insert(END, "-" * 60 + "\n")
        
        if not debug_info_list:
            debug_text.insert(END, "📭 暂无调试信息\n")
            debug_text.insert(END, "等待OCR识别...\n")
            debug_text.insert(END, "💡 提示: 点击'手动触发OCR'按钮可立即测试OCR识别\n")
            return
        
        # 显示所有信息
        for info in debug_info_list:
            timestamp = info.get("timestamp", "未知时间")
            region = info.get("region", {})
            ocr_result = info.get("ocr_result", [])
            parsed_info = info.get("parsed_info", {})
            error = info.get("error", None)
            action = info.get("action", "未知操作")
            message = info.get("message", None)
            elapse = info.get("elapse", None)
            image_shape = info.get("image_shape", None)
            result_count = info.get("result_count", None)
            has_text = info.get("has_text", None)
            exception_type = info.get("exception_type", None)
            full_text = info.get("full_text", None)
            
            # 显示时间戳和操作类型
            debug_text.insert(END, f"📅 {timestamp} | 🔧 {action}\n", "timestamp")
            
            # 显示自定义消息
            if message:
                debug_text.insert(END, f"💬 {message}\n")
            
            # 显示识别区域
            if region:
                x1, y1, x2, y2 = region.get("x1", 0), region.get("y1", 0), region.get("x2", 0), region.get("y2", 0)
                width, height = x2 - x1, y2 - y1
                debug_text.insert(END, f"📍 识别区域: ({x1}, {y1}) - ({x2}, {y2}) | 宽: {width}, 高: {height}\n", "region")
            
            # 显示图像信息
            if image_shape:
                debug_text.insert(END, f"🖼️ 图像尺寸: {image_shape}\n")
            
            # 显示识别耗时
            if elapse is not None and isinstance(elapse, (int, float)):
                debug_text.insert(END, f"⏱️ 识别耗时: {elapse:.3f}秒\n")
            
            # 显示识别结果统计
            if result_count is not None:
                debug_text.insert(END, f"📊 识别结果: {result_count} 行文本 | 包含有效文本: {'是' if has_text else '否'}\n")
            
            # 显示完整识别文本
            if full_text:
                debug_text.insert(END, f"📝 完整识别文本: {full_text}\n")
            
            # 显示OCR原始结果
            if ocr_result:
                debug_text.insert(END, "📋 OCR原始结果 (包含置信度):\n", "ocr_result")
                for i, line in enumerate(ocr_result):
                    if isinstance(line, list) and len(line) >= 2:
                        text = line[1]
                        confidence = line[2] if len(line) > 2 else 0
                        # 确保置信度是数字类型
                        if isinstance(confidence, (int, float)):
                            debug_text.insert(END, f"   [{i+1}] {text} (置信度: {confidence:.2f})\n")
                        else:
                            debug_text.insert(END, f"   [{i+1}] {text} (置信度: {confidence})\n")
                    else:
                        debug_text.insert(END, f"   [{i+1}] {line}\n")
            else:
                debug_text.insert(END, "📋 OCR原始结果: 无\n", "ocr_result")
            
            # 显示解析后的信息
            if parsed_info:
                debug_text.insert(END, "🔍 解析结果:\n", "parsed_info")
                for key, value in parsed_info.items():
                    debug_text.insert(END, f"   {key}: {value}\n")
            
            # 显示错误信息
            if error:
                error_line = f"❌ 错误: {error}\n"
                if exception_type:
                    error_line += f"   异常类型: {exception_type}\n"
                debug_text.insert(END, error_line, "error")
            
            debug_text.insert(END, "-" * 60 + "\n")
        
        # 滚动到底部
        debug_text.see(END)
    
    # 定时更新
    after_id = None
    
    def schedule_update():
        """定时更新调试信息"""
        global after_id
        if debug_auto_refresh and debug_window is not None and debug_window.winfo_exists():
            update_debug_info()
            after_id = debug_window.after(1000, schedule_update)  # 每秒更新一次，保存after ID
    
    schedule_update()
    
    # 窗口关闭时的清理
    def on_close():
        """窗口关闭事件处理"""
        global debug_window, after_id
        if debug_window is not None:
            # 先停止定时更新
            if after_id is not None:
                debug_window.after_cancel(after_id)
                after_id = None
            # 销毁窗口
            debug_window.destroy()
            debug_window = None
    
    debug_window.protocol("WM_DELETE_WINDOW", on_close)
    
    # 初始更新
    update_debug_info()
    
    return debug_window

# =========================
# 创建 Tkinter 窗口（现代化UI设计 - 左右分栏布局）
# =========================
def create_gui():
    # 加载保存的参数
    load_parameters()

    # 创建现代化主题窗口
    root = ttkb.Window(themename="darkly")  # 使用深色主题
    root.title("🎣 PartyFish 自动钓鱼助手")
    root.geometry("1110x855")  # 增大初始高度，确保所有信息完整显示
    root.minsize(840, 500)    # 调整最小尺寸，提供更好的初始体验
    root.maxsize(2560, 1440)   # 调整最大尺寸，支持更大的显示器
    root.resizable(True, True)  # 允许调整大小

    # 设置窗口图标（如果有的话）
    try:
        import sys
        import os
        # 处理PyInstaller打包后的资源路径
        if hasattr(sys, '_MEIPASS'):
            # 打包后使用_internal目录
            icon_path = os.path.join(sys._MEIPASS, "666.ico")
        else:
            # 开发环境使用当前目录
            icon_path = "666.ico"
        root.iconbitmap(icon_path)
    except:
        pass
    
    # 响应式布局：窗口大小变化时调整钓鱼记录表格列宽
    def on_window_resize(event):
        """窗口大小变化时调整钓鱼记录表格列宽"""
        if not fish_tree_ref:
            return
            
        # 获取当前主窗口宽度
        window_width = root.winfo_width()
        
        # 计算右侧面板的可用宽度（假设左侧面板宽度为280px，加上间距8px）
        available_width = max(window_width - 288, 400)  # 最小400px
        
        # 调整比例，时间列与名称/重量列相同（时间:名称:品质:重量 = 63:63:36:63）
        time_ratio = 63   # 时间列比例改为63，与名称/重量列一致
        name_ratio = 63
        quality_ratio = 36
        weight_ratio = 63
        total_ratio = time_ratio + name_ratio + quality_ratio + weight_ratio
        
        # 计算Treeview容器的可用宽度，完全跟随窗口变化
        tree_container_width = available_width - 30  # 减去滚动条和边距
        
        # 严格按照比例计算各列宽度，真正实现响应式
        time_width = int(tree_container_width * (time_ratio / total_ratio))
        name_width = int(tree_container_width * (name_ratio / total_ratio))
        quality_width = int(tree_container_width * (quality_ratio / total_ratio))
        weight_width = int(tree_container_width - time_width - name_width - quality_width - 4)  # 减去4个像素的边框间距
        
        # 设置合理的最小宽度，确保内容能正常显示
        time_width = max(time_width, 100)   # 时间列最小宽度
        name_width = max(name_width, 60)    # 名称列最小宽度
        quality_width = max(quality_width, 35)  # 品质列最小宽度
        weight_width = max(weight_width, 60)   # 重量列最小宽度
        
        # 应用新列宽
        fish_tree_ref.column("时间", width=time_width, anchor="center")
        fish_tree_ref.column("名称", width=name_width, anchor="center")
        fish_tree_ref.column("品质", width=quality_width, anchor="center")
        fish_tree_ref.column("重量", width=weight_width, anchor="center")
    
    # 绑定窗口大小变化事件
    root.bind("<Configure>", on_window_resize)

    # ==================== 主容器（固定布局，左右分栏） ====================
    main_frame = ttkb.Frame(root, padding=12)
    main_frame.pack(fill=BOTH, expand=YES)

    # 配置主框架的行列权重
    main_frame.columnconfigure(0, weight=0, minsize=240)  # 左侧面板权重调整为0，使用固定宽度
    main_frame.columnconfigure(1, weight=2, minsize=400)  # 右侧面板权重保持2，更好地自适应扩展
    main_frame.rowconfigure(0, weight=1)  # 内容区域自适应高度

    # ==================== 左侧面板（设置区域） ====================
    left_panel = ttkb.Frame(main_frame)
    left_panel.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
    
    # ==================== 垂直滚动条 ====================
    # 先添加垂直滚动条，确保它从顶部到底部，和左侧面板一样长
    left_scrollbar = ttkb.Scrollbar(
        left_panel,
        orient="vertical",
        bootstyle="primary"
    )
    left_scrollbar.pack(side=RIGHT, fill=Y)
    
    # ==================== 固定标题区域 ====================
    # 标题区域固定，不随滚动条滚动
    title_frame = ttkb.Frame(left_panel)
    title_frame.pack(fill=X, pady=(0, 5))

    title_label = ttkb.Label(
        title_frame,
        text="🎣 PartyFish",
        bootstyle="light"
    )
    title_label.pack()

    subtitle_label = ttkb.Label(
        title_frame,
        text="自动钓鱼参数配置",
        bootstyle="light"
    )
    subtitle_label.pack()
    
    # 添加分隔线
    separator = ttkb.Separator(left_panel, bootstyle="secondary")
    separator.pack(fill=X, pady=(0, 5))
    
    # ==================== 可滚动内容区域 ====================
    # 创建滚动容器，用于放置可滚动的内容
    scrollable_content_frame = ttkb.Frame(left_panel)
    scrollable_content_frame.pack(fill=BOTH, expand=YES, pady=(0, 0))
    
    # 创建Canvas作为滚动区域
    left_canvas = tk.Canvas(
        scrollable_content_frame,
        yscrollcommand=left_scrollbar.set,
        background="#212529",  # 深色主题背景色，与ttkbootstrap darkly主题匹配
        highlightthickness=0,  # 去除Canvas的高亮边框
        relief="flat"  # 平边框样式
    )
    left_canvas.pack(side=LEFT, fill=BOTH, expand=YES)
    
    # 配置滚动条与Canvas关联，使用标准的yview方法，它可以正确处理所有滚动条事件
    left_scrollbar.config(command=left_canvas.yview)
    
    # 创建内部框架，用于放置所有可滚动的左侧面板内容
    # 设置与Canvas相同的背景色，避免滚动时出现拖影
    left_content_frame = ttkb.Frame(left_canvas, bootstyle="dark")
    
    # 保存canvas window的ID，用于后续调整宽度
    canvas_window = left_canvas.create_window((0, 0), window=left_content_frame, anchor="nw", tags="content_window")
    
    # 优化滚动性能，减少拖影
    def smooth_scroll(event):
        # 使用更平滑的滚动增量
        left_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        # 强制Canvas重绘，避免拖影
        left_canvas.update_idletasks()
    
    # 修复鼠标滚轮绑定，确保所有组件都能响应鼠标滚轮
    # 先解绑所有现有的鼠标滚轮绑定，避免冲突
    left_canvas.unbind("<MouseWheel>")
    left_content_frame.unbind("<MouseWheel>")
    
    # 绑定鼠标滚轮事件到Canvas和内容框架
    left_canvas.bind("<MouseWheel>", smooth_scroll)
    left_content_frame.bind("<MouseWheel>", smooth_scroll)
    
    # 为内容框架中的所有子组件绑定鼠标滚轮事件
    # 定义一个递归函数，为所有子组件绑定事件
    def bind_mousewheel_recursively(widget):
        # 跳过已经绑定过的组件，避免重复绑定
        if hasattr(widget, '_mousewheel_bound') and widget._mousewheel_bound:
            return
        
        # 绑定鼠标滚轮事件
        widget.bind("<MouseWheel>", smooth_scroll)
        widget._mousewheel_bound = True
        
        # 递归绑定所有子组件
        for child in widget.winfo_children():
            bind_mousewheel_recursively(child)
    
    # 绑定内容框架的子组件
    bind_mousewheel_recursively(left_content_frame)
    
    # 为新添加的组件自动绑定鼠标滚轮事件
    def on_content_frame_child_added(event):
        bind_mousewheel_recursively(event.widget)
    
    left_content_frame.bind("<Map>", on_content_frame_child_added)
    
    # 绑定canvas的Configure事件，确保内容框架宽度与canvas一致
    def on_canvas_configure(event):
        # 调整canvas的宽度，确保内容框架与canvas宽度一致
        left_canvas.itemconfig(canvas_window, width=event.width)
    
    left_canvas.bind("<Configure>", on_canvas_configure)
    
    # 更新滚动区域大小
    def update_scroll_region(event):
        # 强制更新布局
        left_content_frame.update_idletasks()
        # 设置滚动区域，确保包含整个内容
        left_canvas.config(scrollregion=left_canvas.bbox("all"))
    
    # 绑定内容框架的Configure事件，更新滚动区域
    left_content_frame.bind("<Configure>", update_scroll_region)

    # ==================== 钓鱼配置选择 ====================
    config_frame = ttkb.Labelframe(
        left_content_frame,
        text=" 📋 配置选择 ",
        padding=10,
        bootstyle="secondary"
    )
    config_frame.pack(fill=X, pady=(0, 6), padx=2)
    
    # 配置容器列表，保存每个配置的控件
    config_containers = []
    
    # 配置切换函数
    def switch_config(config_index):
        global current_fish_config, t, leftclickdown, leftclickup, times, paogantime, jiashi_var, random_delay
        if 0 <= config_index < 4:
            current_fish_config = config_index
            # 应用配置
            config = fish_configs[current_fish_config]
            t = config["t"]
            leftclickdown = config["leftclickdown"]
            leftclickup = config["leftclickup"]
            times = config["times"]
            paogantime = config["paogantime"]
            jiashi_var = config["jiashi_var"]
            random_delay = config.get("random_delay", 30)
            
            # 更新输入框
            t_var.set(str(t))
            leftclickdown_var.set(str(leftclickdown))
            leftclickup_var.set(str(leftclickup))
            times_var.set(str(times))
            paogantime_var.set(str(paogantime))
            jiashi_var_option.set(jiashi_var)
            random_delay_percent_var.set(str(random_delay))
            # 更新滑块
            random_delay_slider_var.set(random_delay)
            
            # 更新所有配置按钮样式
            for i in range(4):
                container = config_containers[i]
                btn = container["btn"]
                if i == current_fish_config:
                    btn.configure(bootstyle="success")
                else:
                    btn.configure(bootstyle="primary-outline")
            
            # 更新状态提示
            status_label.config(text=f"✅ 已切换到{fish_configs[current_fish_config]['name']}", bootstyle="success")
            root.after(2000, lambda: status_label.config(text=f"按 {hotkey_name} 启动/暂停", bootstyle="light"))
            root.after(2000, lambda: status_label.config(text=f"按 {release_hotkey_name} 放生", bootstyle="light"))
    
    # 更新配置名称函数
    def update_config_name(config_index, new_name):
        """更新配置名称"""
        if 0 <= config_index < 4:
            # 确保名称不为空
            if not new_name.strip():
                new_name = f"配置 {config_index + 1}"
            # 更新配置名称
            fish_configs[config_index]["name"] = new_name
            # 保存配置
            save_parameters()
            # 更新按钮文本
            container = config_containers[config_index]
            btn = container["btn"]
            btn.configure(text=new_name)
    
    # 创建可编辑配置按钮
    for i in range(4):
        # 获取配置名称
        config_name = fish_configs[i].get("name", f"配置 {i + 1}")
        
        # 创建配置容器
        config_container = ttkb.Frame(config_frame)
        config_container.pack(side=LEFT, padx=2, fill=X, expand=True)
        
        # 创建配置按钮
        config_btn = ttkb.Button(
            config_container,
            text=config_name,
            command=lambda i=i: switch_config(i),
            bootstyle="success" if i == current_fish_config else "primary-outline",
            width=8
        )
        config_btn.pack(fill=X)
        
        # 创建编辑框（默认隐藏）
        edit_var = ttkb.StringVar(value=config_name)
        edit_entry = ttkb.Entry(
            config_container,
            textvariable=edit_var,
            bootstyle="info",
            justify="center"
        )
        
        # 使用嵌套函数创建事件处理函数，解决闭包变量作用域问题
        def create_event_handlers(idx, btn, entry, var):
            # 编辑框失去焦点时保存
            def on_edit_lost_focus(event):
                new_name = var.get().strip()
                update_config_name(idx, new_name)
                # 隐藏编辑框，显示按钮
                btn.pack(fill=X)
                entry.pack_forget()
            
            # 编辑框按Enter键保存
            def on_edit_enter(event):
                new_name = var.get().strip()
                update_config_name(idx, new_name)
                # 隐藏编辑框，显示按钮
                btn.pack(fill=X)
                entry.pack_forget()
            
            # 点击按钮进入编辑模式
            def on_btn_click(event):
                # 如果是点击当前配置按钮，进入编辑模式
                if idx == current_fish_config:
                    # 更新编辑框内容
                    var.set(fish_configs[idx]["name"])
                    # 隐藏按钮，显示编辑框
                    btn.pack_forget()
                    entry.pack(fill=X)
                    entry.focus_set()
                else:
                    # 切换配置
                    switch_config(idx)
            
            return on_edit_lost_focus, on_edit_enter, on_btn_click
        
        # 创建事件处理函数
        on_edit_lost_focus, on_edit_enter, on_btn_click = create_event_handlers(i, config_btn, edit_entry, edit_var)
        
        # 绑定事件处理函数
        edit_entry.bind("<FocusOut>", on_edit_lost_focus)
        edit_entry.bind("<Return>", on_edit_enter)
        edit_entry.bind("<Escape>", lambda e, btn=config_btn, entry=edit_entry: (btn.pack(fill=X), entry.pack_forget()))
        config_btn.bind("<Button-1>", on_btn_click)
        
        # 保存容器引用
        config_containers.append({
            "btn": config_btn,
            "entry": edit_entry,
            "var": edit_var
        })
    
    # ==================== 钓鱼参数卡片 ====================
    params_card = ttkb.Labelframe(
        left_content_frame,
        text=" ⚙️ 钓鱼参数 ",
        padding=10,
        bootstyle="primary"
    )
    params_card.pack(fill=X, pady=(0, 6), padx=2)

    # 参数输入样式
    def create_param_row(parent, label_text, var, row, tooltip=""):
        label = ttkb.Label(parent, text=label_text, bootstyle="light")
        label.grid(row=row, column=0, sticky=W, pady=4, padx=(0, 10))

        entry = ttkb.Entry(parent, textvariable=var, width=8, bootstyle="info")
        entry.grid(row=row, column=1, sticky=E, pady=4)
        
        # 保存输入框引用到全局列表
        input_entries.append(entry)
        
        return entry

    # 循环间隔
    t_var = ttkb.StringVar(value=str(t))
    create_param_row(params_card, "循环间隔 (秒)", t_var, 0)

    # 收线时间
    leftclickdown_var = ttkb.StringVar(value=str(leftclickdown))
    create_param_row(params_card, "收线时间 (秒)", leftclickdown_var, 1)

    # 放线时间
    leftclickup_var = ttkb.StringVar(value=str(leftclickup))
    create_param_row(params_card, "放线时间 (秒)", leftclickup_var, 2)

    # 最大拉线次数
    times_var = ttkb.StringVar(value=str(times))
    create_param_row(params_card, "最大拉杆次数", times_var, 3)

    # 抛竿时间
    paogantime_var = ttkb.StringVar(value=str(paogantime))
    create_param_row(params_card, "抛竿时间 (秒)", paogantime_var, 4)

    # 配置列宽
    params_card.columnconfigure(0, weight=1)
    params_card.columnconfigure(1, weight=0)

    # ==================== 加时选项卡片 ====================
    jiashi_card = ttkb.Labelframe(
        left_content_frame,
        text=" ⏱️ 加时选项 ",
        padding=10,
        bootstyle="warning"
    )
    jiashi_card.pack(fill=X, pady=(0, 6), padx=2)

    jiashi_var_option = ttkb.IntVar(value=jiashi_var)

    jiashi_frame = ttkb.Frame(jiashi_card)
    jiashi_frame.pack(fill=X)

    jiashi_label = ttkb.Label(jiashi_frame, text="是否自动加时")
    jiashi_label.pack(side=LEFT)

    jiashi_btn_frame = ttkb.Frame(jiashi_frame)
    jiashi_btn_frame.pack(side=RIGHT)

    jiashi_yes = ttkb.Radiobutton(
        jiashi_btn_frame,
        text="是",
        variable=jiashi_var_option,
        value=1,
        bootstyle="success-outline-toolbutton"
    )
    jiashi_yes.pack(side=LEFT, padx=5)

    jiashi_no = ttkb.Radiobutton(
        jiashi_btn_frame,
        text="否",
        variable=jiashi_var_option,
        value=0,
        bootstyle="danger-outline-toolbutton"
    )
    jiashi_no.pack(side=LEFT, padx=5)

    # ==================== 随机延迟选项 ====================
    random_delay_card = ttkb.Labelframe(
        left_content_frame,
        text=" 🎲 随机延迟 ",
        padding=10,
        bootstyle="info"
    )
    random_delay_card.pack(fill=X, pady=(0, 6), padx=2)

    # 启用/禁用开关
    random_delay_var = ttkb.BooleanVar(value=random_delay_enabled)
    random_delay_enabled_frame = ttkb.Frame(random_delay_card)
    random_delay_enabled_frame.pack(fill=X, pady=(0, 8))

    random_delay_enabled_label = ttkb.Label(random_delay_enabled_frame, text="是否启用随机延迟")
    random_delay_enabled_label.pack(side=LEFT)

    random_delay_enabled_btn_frame = ttkb.Frame(random_delay_enabled_frame)
    random_delay_enabled_btn_frame.pack(side=RIGHT)

    random_delay_enabled_yes = ttkb.Radiobutton(
        random_delay_enabled_btn_frame,
        text="是",
        variable=random_delay_var,
        value=True,
        bootstyle="success-outline-toolbutton"
    )
    random_delay_enabled_yes.pack(side=LEFT, padx=5)

    random_delay_enabled_no = ttkb.Radiobutton(
        random_delay_enabled_btn_frame,
        text="否",
        variable=random_delay_var,
        value=False,
        bootstyle="danger-outline-toolbutton"
    )
    random_delay_enabled_no.pack(side=LEFT, padx=5)

    # 随机延迟百分比设置
    random_delay_value_frame = ttkb.Frame(random_delay_card)
    random_delay_value_frame.pack(fill=X)

    # 滑块和输入框容器
    random_delay_slider_frame = ttkb.Frame(random_delay_value_frame)
    random_delay_slider_frame.pack(fill=X)

    # 滑块标签
    random_delay_slider_label = ttkb.Label(random_delay_slider_frame, text="随机延迟 (%):")
    random_delay_slider_label.pack(side=LEFT, padx=(0, 5), pady=5, anchor="center")

    # 滑块
    random_delay_slider_var = ttkb.IntVar(value=random_delay)
    random_delay_slider = ttkb.Scale(
        random_delay_slider_frame,
        from_=0,
        to=30,
        orient="horizontal",
        variable=random_delay_slider_var,
        bootstyle="info",
        length=150,
        cursor="hand2"
    )
    random_delay_slider.pack(side=LEFT, padx=5, expand=True, fill=X, pady=5)

    # 数字输入框
    random_delay_percent_var = ttkb.StringVar(value=str(random_delay))
    random_delay_entry = ttkb.Entry(
        random_delay_slider_frame,
        textvariable=random_delay_percent_var,
        width=5,
        bootstyle="info",
        justify="center"
    )
    random_delay_entry.pack(side=LEFT, padx=5, pady=5)
    input_entries.append(random_delay_entry)

    # ==================== 双向联动逻辑 ====================
    # 滑块变化时更新输入框
    def on_slider_change(*args):
        slider_value = random_delay_slider_var.get()
        random_delay_percent_var.set(str(slider_value))
        # 保存参数
        update_parameters(t_var, leftclickdown_var, leftclickup_var, times_var, 
                        paogantime_var, jiashi_var_option, random_delay_percent_var, 
                        resolution_var, custom_width_var, custom_height_var, 
                        hotkey_var, record_fish_var, legendary_screenshot_var, 
                        random_delay_var)
    
    # 输入框变化时更新滑块和验证范围
    def on_entry_change(*args):
        try:
            entry_value = int(random_delay_percent_var.get())
            # 限制范围在0-30之间
            if entry_value < 0:
                entry_value = 0
            elif entry_value > 30:
                entry_value = 30
            # 更新滑块和输入框
            random_delay_slider_var.set(entry_value)
            random_delay_percent_var.set(str(entry_value))
            # 保存参数
            update_parameters(t_var, leftclickdown_var, leftclickup_var, times_var, 
                            paogantime_var, jiashi_var_option, random_delay_percent_var, 
                            resolution_var, custom_width_var, custom_height_var, 
                            hotkey_var, record_fish_var, legendary_screenshot_var, 
                            random_delay_var)
        except ValueError:
            # 如果输入不是数字，不做处理
            pass
    
    # 输入框失去焦点时验证和修正值
    def on_entry_focus_out(event):
        try:
            entry_value = int(random_delay_percent_var.get())
            # 限制范围在0-30之间
            if entry_value < 0:
                entry_value = 0
            elif entry_value > 30:
                entry_value = 30
            # 更新滑块和输入框
            random_delay_slider_var.set(entry_value)
            random_delay_percent_var.set(str(entry_value))
        except ValueError:
            # 如果输入不是数字，设为默认值0
            random_delay_slider_var.set(0)
            random_delay_percent_var.set("0")
    
    # 绑定事件
    random_delay_slider_var.trace_add("write", on_slider_change)
    random_delay_percent_var.trace_add("write", on_entry_change)
    random_delay_entry.bind("<FocusOut>", on_entry_focus_out)
    random_delay_entry.bind("<Return>", on_entry_focus_out)


     # ==================== 放生按钮和多选框 ====================
    # 放在左侧面板合适位置，比如在params_card之后
    filter_card = ttkb.Labelframe(
        left_content_frame,
        text=" 🏷️放生品质 ",
        padding=10,
        bootstyle="info"
    )
    filter_card.pack(fill=X, pady=(0, 6), padx=2)

    # 筛选按钮
    def on_filter_btn_click():
        # 这里可以根据实际需求处理筛选逻辑
        global selected_qualitys
        selected_qualitys = [q for q, var in filter_vars.items() if var.get()]
        print("已选品质：", selected_qualitys)
        # 你可以在这里调用刷新钓鱼记录的函数，并传递selected

    filter_btn = ttkb.Button(
        filter_card,
        text="确认筛选放生品质",
        command=on_filter_btn_click,
        bootstyle="primary"
    )
    filter_btn.pack(fill=X, pady=(0, 8))

    # 多选框变量
    filter_vars = {
        "标准": ttkb.BooleanVar(value=True),
        "非凡": ttkb.BooleanVar(value=True),
        "稀有": ttkb.BooleanVar(value=False),
        "史诗": ttkb.BooleanVar(value=False),
        "传说": ttkb.BooleanVar(value=False),
    }

    # 多选框布局
    for q in ["标准", "非凡", "稀有", "史诗", "传说"]:
        cb = ttkb.Checkbutton(
            filter_card,
            text=q,
            variable=filter_vars[q],
            bootstyle="info"
        )
        if q == "标准":
            cb.config(state="disabled")
        cb.pack(anchor="w", padx=10)

    # ==================== 热键设置卡片 ====================
    hotkey_card = ttkb.Labelframe(
        left_content_frame,
        text=" ⌨️ 热键设置 ",
        padding=10,
        bootstyle="secondary"
    )
    hotkey_card.pack(fill=X, pady=(0, 6), padx=2)

    # 热键显示变量
    hotkey_var = ttkb.StringVar(value=hotkey_name)
    release_hotkey_var = ttkb.StringVar(value=release_hotkey_name)

    # 热键捕获状态
    is_capturing_hotkey = [False]  # 使用列表以便在闭包中修改
    captured_modifiers = [set()]
    captured_main_key = [None]
    captured_main_key_name = [""]
    capture_listener = [None]

    hotkey_frame = ttkb.Frame(hotkey_card)
    hotkey_frame.pack(fill=X)


    hotkey_label = ttkb.Label(hotkey_frame, text="启动/暂停热键")
    hotkey_label.pack(side=LEFT)

    release_hotkey_frame = ttkb.Frame(hotkey_card)
    release_hotkey_frame.pack(fill=X)


    release_hotkey_label = ttkb.Label(release_hotkey_frame, text="放生热键")
    release_hotkey_label.pack(side=LEFT)

    # 热键显示按钮（点击后进入捕获模式）
    hotkey_btn = ttkb.Button(
        hotkey_frame,
        text=hotkey_name,
        bootstyle="primary-outline",
        width=12
    )
    hotkey_btn.pack(side=RIGHT)
    # 放生热键显示按钮
    release_hotkey_btn = ttkb.Button(
        release_hotkey_frame,
        text=release_hotkey_name,
        bootstyle="primary-outline",
        width=12
    )
    release_hotkey_btn.pack(side=RIGHT)

    # 热键信息提示（合并显示，点击按钮时会变化）
    hotkey_info_label = ttkb.Label(
        hotkey_card,
        text=f"按 {hotkey_name} 启动/暂停|{release_hotkey_name}放生|点击按钮修改",
        bootstyle="info"
    )
    hotkey_info_label.pack(pady=(3, 0))

    # 提示标签（用于捕获模式显示）
    hotkey_tip_label = ttkb.Label(
        hotkey_card,
        text="",
        bootstyle="secondary"
    )

    def stop_hotkey_capture():
        """停止热键捕获"""
        is_capturing_hotkey[0] = False
        # 停止键盘监听器
        if capture_listener[0] is not None:
            try:
                capture_listener[0].stop()
            except:
                pass
            capture_listener[0] = None
        # 停止鼠标监听器
        if 'mouse_capture_listener' in globals():
            mouse_listener = globals()['mouse_capture_listener']
            if mouse_listener is not None:
                try:
                    mouse_listener.stop()
                except:
                    pass
            globals()['mouse_capture_listener'] = None
        hotkey_btn.configure(bootstyle="info-outline")
        release_hotkey_btn.configure(bootstyle="info-outline")
        hotkey_tip_label.pack_forget()  # 隐藏提示
        hotkey_info_label.configure(text=f"点击按钮修改热键")

    def on_capture_key_press(key):
        """捕获按键按下事件"""
        if not is_capturing_hotkey[0]:
            return False  # 停止监听

         # 添加一个全局变量来跟踪当前捕获的按钮
        if not hasattr(on_capture_key_press, 'current_button_name'):
            on_capture_key_press.current_button_name = None

        # 检查是否是修饰键
        if key in MODIFIER_KEYS:
            captured_modifiers[0].add(MODIFIER_KEYS[key])
            # 更新按钮显示
            display_parts = []
            if 'ctrl' in captured_modifiers[0]:
                display_parts.append('Ctrl')
            if 'alt' in captured_modifiers[0]:
                display_parts.append('Alt')
            if 'shift' in captured_modifiers[0]:
                display_parts.append('Shift')
            display_parts.append('...')
            def update_button_display():
                if on_capture_key_press.current_button_name == "hotkey":
                    hotkey_btn.configure(text='+'.join(display_parts))
                elif on_capture_key_press.current_button_name == "release_hotkey":
                    release_hotkey_btn.configure(text='+'.join(display_parts))
            root.after(0, update_button_display)
            return True

        # 这是主按键
        captured_main_key[0] = key
        captured_main_key_name[0] = key_to_name(key)

        # 生成热键字符串
        new_hotkey = format_hotkey_display(captured_modifiers[0], captured_main_key_name[0])

        # 更新GUI
        def update_gui():
            if on_capture_key_press.current_button_name == "hotkey":
                hotkey_var.set(new_hotkey)
                hotkey_btn.configure(text=new_hotkey)
            elif on_capture_key_press.current_button_name == "release_hotkey":
                release_hotkey_var.set(new_hotkey)
                release_hotkey_btn.configure(text=new_hotkey)
        
            hotkey_info_label.configure(text=f"新热键: {new_hotkey} | 点击保存生效")
            stop_hotkey_capture()

        root.after(0, update_gui)
        return False  # 停止监听

    def on_capture_key_release(key):
        """捕获按键释放事件"""
        if not is_capturing_hotkey[0]:
            return False
        # 释放修饰键时移除
        if key in MODIFIER_KEYS:
            captured_modifiers[0].discard(MODIFIER_KEYS[key])
        return True

    def on_capture_mouse_click(x, y, button, pressed):
        """捕获鼠标点击事件"""
        if not is_capturing_hotkey[0] or not pressed:
            return
        
        # 只允许鼠标侧键（x1, x2），禁用左右中键
        if button not in [mouse.Button.x1, mouse.Button.x2]:
            return
        
        # 鼠标侧键作为主按键
        captured_main_key[0] = button
        captured_main_key_name[0] = key_to_name(button)
        
        # 生成热键字符串
        new_hotkey = format_hotkey_display(captured_modifiers[0], captured_main_key_name[0])
        
        # 更新GUI
        def update_gui():
            if on_capture_key_press.current_button_name == "hotkey":
                hotkey_var.set(new_hotkey)
                hotkey_btn.configure(text=new_hotkey)
            elif on_capture_key_press.current_button_name == "release_hotkey":
                release_hotkey_var.set(new_hotkey)
                release_hotkey_btn.configure(text=new_hotkey)
            hotkey_info_label.configure(text=f"新热键: {new_hotkey} | 点击保存生效")
            stop_hotkey_capture()

        root.after(0, update_gui)

    def start_hotkey_capture(source_btn_name):
        """开始热键捕获"""
        if is_capturing_hotkey[0]:
            stop_hotkey_capture()
            return

        is_capturing_hotkey[0] = True
        captured_modifiers[0] = set()
        captured_main_key[0] = None
        captured_main_key_name[0] = ""

          # 设置当前捕获的按钮名称
        on_capture_key_press.current_button_name = source_btn_name

        if source_btn_name == "hotkey":
            hotkey_btn.configure(text="请按键...", bootstyle="warning")
            hotkey_info_label.configure(text="按下组合键（如Ctrl+F2）或单键/鼠标侧键")
        elif source_btn_name == "release_hotkey":
            release_hotkey_btn.configure(text="请按键...", bootstyle="warning")
            hotkey_info_label.configure(text="按下释放热键（如Ctrl+F3）或单键/鼠标侧键")

        hotkey_tip_label.configure(text="5秒内按键，或再次点击取消")
        hotkey_tip_label.pack(pady=(2, 0))

        # 启动键盘监听器
        capture_listener[0] = keyboard.Listener(
            on_press=on_capture_key_press,
            on_release=on_capture_key_release
        )
        capture_listener[0].start()
        
        # 启动鼠标监听器
        global mouse_capture_listener
        mouse_capture_listener = mouse.Listener(on_click=on_capture_mouse_click)
        mouse_capture_listener.daemon = True
        mouse_capture_listener.start()

        # 5秒后自动取消
        def auto_cancel():
            if is_capturing_hotkey[0]:
                 if source_btn_name == "hotkey":
                    current_value = hotkey_var.get()
                    if not current_value or current_value == "未设置":
                        current_value = "未设置"
                    root.after(0, lambda: hotkey_btn.configure(text=current_value))
                 elif source_btn_name == "release_hotkey":
                    current_value = release_hotkey_var.get()
                    if not current_value or current_value == "未设置":
                        current_value = "未设置"
                    root.after(0, lambda: release_hotkey_btn.configure(text=current_value))
                 stop_hotkey_capture()
        
        root.after(5000, auto_cancel)

    hotkey_btn.configure(command=lambda: start_hotkey_capture("hotkey"))
    release_hotkey_btn.configure(command=lambda: start_hotkey_capture("release_hotkey"))

    # ==================== 分辨率设置卡片 ====================
    resolution_card = ttkb.Labelframe(
        left_content_frame,
        text=" 🖥️ 分辨率设置 ",
        padding=10,
        bootstyle="success"
    )
    resolution_card.pack(fill=X, pady=(0, 6), padx=2)

    resolution_var = ttkb.StringVar(value=resolution_choice)
    custom_width_var = ttkb.StringVar(value=str(TARGET_WIDTH))
    custom_height_var = ttkb.StringVar(value=str(TARGET_HEIGHT))

    # 分辨率选择按钮组（使用2x2网格布局）
    res_btn_frame = ttkb.Frame(resolution_card)
    res_btn_frame.pack(fill=X, pady=(0, 6))
# 分辨率选择（2x2网格布局）
    resolutions = [("1080P", "1080P"), ("2K", "2K"), ("4K", "4K"), ("当前", "current"), ("自定义", "自定义")]

    # 自定义分辨率输入框容器
    custom_frame = ttkb.Frame(resolution_card)

    custom_width_label = ttkb.Label(custom_frame, text="宽:")
    custom_width_label.pack(side=LEFT, padx=(0, 3))

    custom_width_entry = ttkb.Entry(custom_frame, textvariable=custom_width_var, width=6)
    custom_width_entry.pack(side=LEFT, padx=(0, 10))

    custom_height_label = ttkb.Label(custom_frame, text="高:")
    custom_height_label.pack(side=LEFT, padx=(0, 3))

    custom_height_entry = ttkb.Entry(custom_frame, textvariable=custom_height_var, width=6)
    custom_height_entry.pack(side=LEFT)

    # 当前分辨率信息标签
    resolution_info_var = ttkb.StringVar(
        value=f"当前: {TARGET_WIDTH}×{TARGET_HEIGHT} | 系统缩放: {get_system_scaling()}%"
    )
    info_label = ttkb.Label(
        resolution_card,
        textvariable=resolution_info_var,
        bootstyle="info"
    )

    def update_resolution_info():
        res = resolution_var.get()
        # 获取系统缩放比例
        system_scaling = get_system_scaling()
        
        if res == "1080P":
            resolution_info_var.set(f"当前: 1920×1080 | 系统缩放: {system_scaling}%")
        elif res == "2K":
            resolution_info_var.set(f"当前: 2560×1440 | 系统缩放: {system_scaling}%")
        elif res == "4K":
            resolution_info_var.set(f"当前: 3840×2160 | 系统缩放: {system_scaling}%")
        elif res == "current":
            # 显示当前系统分辨率
            current_width, current_height = get_current_screen_resolution()
            resolution_info_var.set(f"当前: {current_width}×{current_height} | 系统缩放: {system_scaling}%")
        else:
            resolution_info_var.set(f"当前: {custom_width_var.get()}×{custom_height_var.get()} | 系统缩放: {system_scaling}%")

    def on_resolution_change():
        """当分辨率选择改变时，更新自定义输入框状态"""
        # 更新分辨率信息
        update_resolution_info()
        
        # 根据选择更新显示值
        if resolution_var.get() == "current":
            # 使用当前系统分辨率
            current_width, current_height = get_current_screen_resolution()
            custom_width_var.set(str(current_width))
            custom_height_var.set(str(current_height))
        elif resolution_var.get() == "1080P":
            custom_width_var.set("1920")
            custom_height_var.set("1080")
        elif resolution_var.get() == "2K":
            custom_width_var.set("2560")
            custom_height_var.set("1440")
        elif resolution_var.get() == "4K":
            custom_width_var.set("3840")
            custom_height_var.set("2160")


    # 创建分辨率选择按钮（3行2列布局）
    res_btn_frame.columnconfigure(0, weight=1)
    res_btn_frame.columnconfigure(1, weight=1)
    
    # 3行2列布局排列：
    # 第1行: 1080P, 2K
    # 第2行: 4K, 当前
    # 第3行: 自定义, [自定义输入框]
    
    # 创建第1行按钮
    rb_1080p = ttkb.Radiobutton(
        res_btn_frame,
        text="1080P",
        variable=resolution_var,
        value="1080P",
        bootstyle="primary-outline-toolbutton",
        width=8,
        command=on_resolution_change
    )
    rb_1080p.grid(row=0, column=0, padx=2, pady=2, sticky="ew")
    
    rb_2k = ttkb.Radiobutton(
        res_btn_frame,
        text="2K",
        variable=resolution_var,
        value="2K",
        bootstyle="primary-outline-toolbutton",
        width=8,
        command=on_resolution_change
    )
    rb_2k.grid(row=0, column=1, padx=2, pady=2, sticky="ew")
    
    # 创建第2行按钮
    rb_4k = ttkb.Radiobutton(
        res_btn_frame,
        text="4K",
        variable=resolution_var,
        value="4K",
        bootstyle="primary-outline-toolbutton",
        width=8,
        command=on_resolution_change
    )
    rb_4k.grid(row=1, column=0, padx=2, pady=2, sticky="ew")
    
    rb_current = ttkb.Radiobutton(
        res_btn_frame,
        text="当前",
        variable=resolution_var,
        value="current",
        bootstyle="primary-outline-toolbutton",
        width=8,
        command=on_resolution_change
    )
    rb_current.grid(row=1, column=1, padx=2, pady=2, sticky="ew")
    
    # 创建第3行左侧的自定义按钮
    rb_custom = ttkb.Radiobutton(
        res_btn_frame,
        text="自定义",
        variable=resolution_var,
        value="自定义",
        bootstyle="primary-outline-toolbutton",
        width=8,
        command=on_resolution_change
    )
    rb_custom.grid(row=2, column=0, padx=2, pady=2, sticky="ew")
    
    # 创建第3行右侧的自定义输入框
    custom_input_frame = ttkb.Frame(res_btn_frame)
    custom_input_frame.grid(row=2, column=1, padx=2, pady=2, sticky="ew")
    
    custom_width_label = ttkb.Label(custom_input_frame, text="宽:", width=2)
    custom_width_label.pack(side=LEFT, padx=(0, 2))

    custom_width_entry = ttkb.Entry(custom_input_frame, textvariable=custom_width_var, width=5)
    custom_width_entry.pack(side=LEFT, padx=(0, 8))

    custom_height_label = ttkb.Label(custom_input_frame, text="高:", width=2)
    custom_height_label.pack(side=LEFT, padx=(0, 2))

    custom_height_entry = ttkb.Entry(custom_input_frame, textvariable=custom_height_var, width=5)
    custom_height_entry.pack(side=LEFT)
    
    # 始终显示分辨率信息标签
    info_label.pack(pady=(8, 0))

    # ==================== 钓鱼记录开关卡片 ====================
    record_card = ttkb.Labelframe(
        left_content_frame,
        text=" 📝 钓鱼记录设置 ",
        padding=10,
        bootstyle="info"
    )
    record_card.pack(fill=X, pady=(0, 6), padx=2)

    # 钓鱼记录开关
    record_fish_var = ttkb.IntVar(value=1 if record_fish_enabled else 0)

    record_frame = ttkb.Frame(record_card)
    record_frame.pack(fill=X)

    record_label = ttkb.Label(record_frame, text="是否启用钓鱼记录")
    record_label.pack(side=LEFT)

    record_btn_frame = ttkb.Frame(record_frame)
    record_btn_frame.pack(side=RIGHT)

    record_yes = ttkb.Radiobutton(
        record_btn_frame,
        text="是",
        variable=record_fish_var,
        value=1,
        bootstyle="success-outline-toolbutton"
    )
    record_yes.pack(side=LEFT, padx=5)

    record_no = ttkb.Radiobutton(
        record_btn_frame,
        text="否",
        variable=record_fish_var,
        value=0,
        bootstyle="danger-outline-toolbutton"
    )
    record_no.pack(side=LEFT, padx=5)

    # 传说/传奇鱼自动截屏开关
    legendary_screenshot_var = ttkb.IntVar(value=1 if legendary_screenshot_enabled else 0)
    
    legendary_frame = ttkb.Frame(record_card)
    legendary_frame.pack(fill=X, pady=(5, 0))
    
    legendary_label = ttkb.Label(legendary_frame, text="传说/传奇鱼自动截屏")
    legendary_label.pack(side=LEFT)
    
    legendary_btn_frame = ttkb.Frame(legendary_frame)
    legendary_btn_frame.pack(side=RIGHT)
    
    legendary_yes = ttkb.Radiobutton(
        legendary_btn_frame,
        text="是",
        variable=legendary_screenshot_var,
        value=1,
        bootstyle="success-outline-toolbutton"
    )
    legendary_yes.pack(side=LEFT, padx=5)
    
    legendary_no = ttkb.Radiobutton(
        legendary_btn_frame,
        text="否",
        variable=legendary_screenshot_var,
        value=0,
        bootstyle="danger-outline-toolbutton"
    )
    legendary_no.pack(side=LEFT, padx=5)

    # ==================== 字体大小设置卡片 ====================
    font_size_card = ttkb.Labelframe(
        left_content_frame,
        text=" 📝 字体大小设置 ",
        padding=10,
        bootstyle="info"
    )
    font_size_card.pack(fill=X, pady=(0, 6), padx=2)

    # 字体大小变量
    font_size_var = ttkb.IntVar(value=font_size)

    # 字体大小滑块 - 优化样式
    font_slider = ttkb.Scale(
        font_size_card,
        from_=50,
        to=200,
        orient="horizontal",
        variable=font_size_var,
        bootstyle="info",  # 使用标准样式
        length=220,  # 增加滑块长度
        cursor="hand2"  # 鼠标悬停时显示手型光标
    )
    font_slider.pack(pady=(8, 5))

    # 字体大小显示标签 - 美化显示
    font_size_display = ttkb.Label(
        font_size_card,
        text=f"当前字体大小: {font_size}%",
        bootstyle="primary",  # 使用更醒目的样式
        font=("Segoe UI", 10, "bold")  # 加粗字体
    )
    font_size_display.pack(pady=(0, 8))

    # 预设按钮框架 - 使用两行布局
    preset_frame = ttkb.Frame(font_size_card)
    preset_frame.pack(fill=X, pady=(0, 4))
    
    # 第一行预设按钮框架
    preset_row1 = ttkb.Frame(preset_frame)
    preset_row1.pack(fill=X)
    
    # 第二行预设按钮框架
    preset_row2 = ttkb.Frame(preset_frame)
    preset_row2.pack(fill=X)

    # 字体大小预设配置 - 简化文本，适合大字体显示
    font_presets = [
        ("小 (50%)", 50),    # 50% 字体大小
        ("中 (100%)", 100),   # 100% 字体大小
        ("大 (150%)", 150),   # 150% 字体大小
        ("特大 (200%)", 200)   # 200% 字体大小
    ]
    
    # 保存预设按钮引用的字典，用于更新选中状态
    preset_button_dict = {}
    
    # 预设按钮点击处理
    def set_font_size(value):
        font_size_var.set(value)
        update_font_size()
        # 更新预设按钮的选中状态
        update_preset_button_state()
    
    # 更新预设按钮状态
    def update_preset_button_state():
        current_size = font_size_var.get()
        for text, size in font_presets:
            btn = preset_button_dict[size]
            if size == current_size:
                # 当前选中的预设，使用填充样式
                btn.configure(bootstyle="info")
            else:
                # 未选中的预设，使用轮廓样式
                btn.configure(bootstyle="info-outline")
    
    # 创建预设按钮，两行布局
    for i, (text, size) in enumerate(font_presets):
        # 选择按钮所在的行
        current_row = preset_row1 if i < 2 else preset_row2
        
        preset_btn = ttkb.Button(
            current_row,
            text=text,
            command=lambda v=size: set_font_size(v),
            bootstyle="info-outline",  # 默认轮廓样式
            width=10,  # 减小按钮宽度，适应大字体
            padding=(3, 2),  # 优化内边距，更紧凑
            cursor="hand2"  # 鼠标悬停时显示手型光标
        )
        # 每行两个按钮，各占50%宽度
        preset_btn.pack(side=LEFT, padx=2, pady=2, expand=True, fill=X)
        
        # 保存按钮引用
        preset_button_dict[size] = preset_btn
        preset_btns.append(preset_btn)
    
    # 初始化预设按钮状态
    update_preset_button_state()

    # 字体大小应用按钮
    apply_font_btn = ttkb.Button(
        font_size_card,
        text="应用",
        command=lambda: update_font_size(),
        bootstyle="primary"
    )
    apply_font_btn.pack(fill=X, pady=(8, 0))

    # 定义字体大小更新函数
    def update_font_size():
        global font_size
        font_size = font_size_var.get()
        font_size_display.config(text=f"当前字体大小: {font_size}%")
        # 保存字体大小到参数文件
        save_parameters()
        
        # 更新预设按钮状态，确保滑块和按钮状态一致
        update_preset_button_state()
        
        # 计算新字体大小和缩放因子
        scale_factor = font_size / 100.0
        base_font = "Segoe UI"
        entry_font_size = max(5, min(30, int(9 * scale_factor)))
        new_font = (base_font, entry_font_size)
        
        # 直接更新所有输入框的字体
        for entry in input_entries:
            try:
                # 尝试直接更新字体
                entry.configure(font=new_font)
            except Exception as e:
                # 如果直接更新失败，确保样式已经更新
                # 通过修改样式对象来更新所有输入框
                style.configure("TEntry", font=new_font)
                style.configure("Entry", font=new_font)
        
        # 直接更新所有组合框的字体和宽度（包括品质筛选组合框）
        for i, combo in enumerate(combo_boxes):
            try:
                # 尝试直接更新字体
                combo.configure(font=new_font)
                
                # 计算新的组合框宽度，根据字体大小动态调整
                # 基础宽度为8，根据缩放因子调整
                base_combo_width = 8
                new_combo_width = max(6, int(base_combo_width * scale_factor))
                combo.configure(width=new_combo_width)
            except Exception as e:
                # 如果直接更新失败，确保样式已经更新
                # 通过修改样式对象来更新所有组合框
                style.configure("TCombobox", font=new_font)
                style.configure("Combobox", font=new_font)
                # 更新组合框下拉列表的字体（同时支持标准TTK和TTKBootstrap）
                style.configure("TCombobox.Listbox", font=new_font)
                style.configure("Combobox.Listbox", font=new_font)
        
        # 应用字体大小到所有界面元素
        update_all_widget_fonts(root, style, font_size)
        
        # 动态调整Treeview列宽，根据字体大小缩放
        if fish_tree_ref:
            try:
                # 计算新的字体大小（像素单位）
                # 确保字体大小按照要求计算：
                # - 100% 时为 12px
                # - 150% 时为 18px
                # - 200% 时为 24px
                base_font_size = 12  # 基础字体大小为12px（100%时）
                new_font_size = int(base_font_size * scale_factor)
                
                # 精确调整字体大小，确保符合要求
                if font_size == 100:
                    new_font_size = 12
                elif font_size == 150:
                    new_font_size = 16
                elif font_size == 200:
                    new_font_size = 20  # 调整为20px，比原来的24px小，避免字体过大
                
                #print(f"字体大小设置: {font_size}%, 使用的字体大小: {new_font_size}px")
                
                # 根据具体的字体大小值精确计算列宽
                # 确保在不影响外扩的情况下，调整列宽
                # 不同字体大小对应不同的列宽
                # 调整比例，减小时间列宽度（时间:名称:品质:重量 = 90:63:36:63）
                # 动态计算列宽，跟随页面行宽变化
                time_ratio = 63   # 减小时间列比例，让它更紧凑
                name_ratio = 63
                quality_ratio = 36
                weight_ratio = 63
                total_ratio = time_ratio + name_ratio + quality_ratio + weight_ratio
                
                # 获取当前Treeview容器宽度
                current_container_width = fish_tree_ref.winfo_width() if fish_tree_ref else 500
                
                # 计算各列宽度
                column_widths = {
                    "时间": int(current_container_width * (time_ratio / total_ratio)),
                    "名称": int(current_container_width * (name_ratio / total_ratio)),
                    "品质": int(current_container_width * (quality_ratio / total_ratio)),
                    "重量": int(current_container_width * (weight_ratio / total_ratio))
                }
                
                # print(f"根据字体大小 {new_font_size}px 计算得到的列宽: {column_widths}")
                
                # 应用新列宽到Treeview
                for col, width in column_widths.items():
                    fish_tree_ref.column(col, width=width, anchor="center")
                
                # 动态调整行高，通过样式设置
                # 计算合适的行高
                new_rowheight = int(new_font_size * 2.2)  # 行高为字体大小的2.2倍，确保垂直间距合适
                
                # 直接通过样式修改Treeview行高
                # 尝试修改多种Treeview样式，确保覆盖所有可能的样式名称
                style.configure("Treeview", rowheight=new_rowheight)
                style.configure("Info.Treeview", rowheight=new_rowheight)  # 对应bootstyle="info"
                style.configure("Table.Treeview", rowheight=new_rowheight)  # ttkbootstrap默认Treeview样式
                style.configure("CustomTreeview.Treeview", rowheight=new_rowheight)  # 自定义样式
                
                # 强制更新Treeview布局，确保列宽和行高调整立即生效
                fish_tree_ref.update_idletasks()
                
                # 不调整外面的布局，只调整Treeview内部列宽和行高
                # 确保父容器的大小不会受到影响
            except Exception as e:
                print(f"调整Treeview列宽时出错: {e}")
                # 处理可能的错误
                pass

    # ==================== 右侧面板（钓鱼记录区域） ====================
    right_panel = ttkb.Frame(main_frame)
    right_panel.grid(row=0, column=1, sticky="nsew")
    
    # 配置右侧面板的行列权重，确保内部组件能正确扩展
    right_panel.columnconfigure(0, weight=1)  # 唯一列自适应宽度
    right_panel.rowconfigure(0, weight=1)  # 唯一行自适应高度

    # ==================== 钓鱼记录卡片 ====================
    # 先创建style对象
    style = ttk.Style()
    
    # 设置自定义海洋蓝边框
    style.configure("OceanBlue.TLabelframe", bordercolor="#1E90FF")
    style.configure("OceanBlue.TLabelframe.Label", foreground="#1E90FF")
    
    fish_record_card = ttkb.Labelframe(
        right_panel,
        text=" 🐟 钓鱼记录 ",
        padding=12,
        bootstyle="primary"
    )
    fish_record_card.pack(fill=BOTH, expand=YES)
    fish_record_card.configure(style="OceanBlue.TLabelframe")

    # 切换按钮（本次/总览）
    record_view_frame = ttkb.Frame(fish_record_card)
    record_view_frame.pack(fill=X, pady=(0, 10))

    view_mode = ttkb.StringVar(value="current")

    current_btn = ttkb.Radiobutton(
        record_view_frame,
        text="本次钓鱼",
        variable=view_mode,
        value="current",
        bootstyle="info-outline-toolbutton",
        command=lambda: update_fish_display()
    )
    current_btn.pack(side=LEFT, padx=5)

    all_btn = ttkb.Radiobutton(
        record_view_frame,
        text="历史总览",
        variable=view_mode,
        value="all",
        bootstyle="info-outline-toolbutton",
        command=lambda: update_fish_display()
    )
    all_btn.pack(side=LEFT, padx=5)

    # 刷新按钮
    refresh_btn = ttkb.Button(
        record_view_frame,
        text="🔄",
        command=lambda: update_fish_display(),
        bootstyle="info-outline",
        width=3
    )
    refresh_btn.pack(side=RIGHT, padx=5)

    # 搜索和筛选框
    search_frame = ttkb.Frame(fish_record_card)
    search_frame.pack(fill=X, pady=(0, 10))

    search_var = ttkb.StringVar()
    search_entry = ttkb.Entry(search_frame, textvariable=search_var, width=15)
    search_entry.pack(side=LEFT, padx=(0, 5))
    search_entry.insert(0, "搜索鱼名...")
    
    # 保存搜索输入框到全局列表
    input_entries.append(search_entry)

    def on_search_focus_in(event):
        if search_entry.get() == "搜索鱼名...":
            search_entry.delete(0, "end")

    def on_search_focus_out(event):
        if not search_entry.get():
            search_entry.insert(0, "搜索鱼名...")

    search_entry.bind("<FocusIn>", on_search_focus_in)
    search_entry.bind("<FocusOut>", on_search_focus_out)
    search_entry.bind("<Return>", lambda e: update_fish_display())

    search_btn = ttkb.Button(
        search_frame,
        text="🔍",
        command=lambda: update_fish_display(),
        bootstyle="info-outline",
        width=3
    )
    search_btn.pack(side=LEFT, padx=(0, 10))

    # 品质筛选
    quality_var = ttkb.StringVar(value="全部")
    quality_label = ttkb.Label(search_frame, text="品质:")
    quality_label.pack(side=LEFT)
    quality_combo = ttkb.Combobox(
        search_frame,
        textvariable=quality_var,
        values=["全部"] + GUI_QUALITY_LEVELS,
        width=8,
        state="readonly"
    )
    quality_combo.pack(side=LEFT, padx=5)
    quality_combo.bind("<<ComboboxSelected>>", lambda e: update_fish_display())
    
    # 保存品质筛选组合框到全局列表
    combo_boxes.append(quality_combo)

    # 统计信息卡片
    # 设置自定义紫色边框
    style.configure("Purple.TLabelframe", bordercolor="#9B59B6")
    style.configure("Purple.TLabelframe.Label", foreground="#9B59B6")
    
    stats_card = ttkb.Labelframe(
        fish_record_card,
        text=" 📊 钓鱼统计 ",
        padding=15,
        bootstyle="primary"
    )
    stats_card.pack(fill=X, pady=(0, 10))
    stats_card.configure(relief="solid", borderwidth=1)
    stats_card.configure(style="Purple.TLabelframe")
    
    # 品质统计框架 - 网格布局
    stats_grid = ttkb.Frame(stats_card)
    stats_grid.pack(fill=X, expand=True)
    
    # 创建统计标签变量
    standard_var = ttkb.StringVar(value="⚪ 标准: 0 (0.00%)")
    uncommon_var = ttkb.StringVar(value="🟢 非凡: 0 (0.00%)")
    rare_var = ttkb.StringVar(value="🔵 稀有: 0 (0.00%)")
    epic_var = ttkb.StringVar(value="🟣 史诗: 0 (0.00%)")
    legendary_var = ttkb.StringVar(value="🟡 传说: 0 (0.00%)")
    total_var = ttkb.StringVar(value="📝 总计: 0 条")
    
    # 品质统计标签 - 网格布局
    standard_label = ttkb.Label(stats_grid, textvariable=standard_var, foreground="#FFFFFF")
    standard_label.pack(side=LEFT, padx=10, pady=8, expand=True, fill=X)
    
    uncommon_label = ttkb.Label(stats_grid, textvariable=uncommon_var, foreground="#2ECC71")
    uncommon_label.pack(side=LEFT, padx=10, pady=8, expand=True, fill=X)
    
    rare_label = ttkb.Label(stats_grid, textvariable=rare_var, foreground="#1E90FF")
    rare_label.pack(side=LEFT, padx=10, pady=8, expand=True, fill=X)
    
    epic_label = ttkb.Label(stats_grid, textvariable=epic_var, foreground="#9B59B6")
    epic_label.pack(side=LEFT, padx=10, pady=8, expand=True, fill=X)
    
    legendary_label = ttkb.Label(stats_grid, textvariable=legendary_var, foreground="#F1C40F")
    legendary_label.pack(side=LEFT, padx=10, pady=8, expand=True, fill=X)
    
    # 总计和清空按钮框架
    total_frame = ttkb.Frame(stats_card)
    total_frame.pack(fill=X, expand=True)
    
    total_label = ttkb.Label(total_frame, textvariable=total_var, bootstyle="success")
    total_label.pack(side=LEFT, padx=10, pady=8)
    
    # 清空按钮
    clear_btn = ttkb.Button(
        total_frame,
        text="🗑️ 清空记录",
        command=lambda: clear_fish_records(),
        bootstyle="danger-outline"
    )
    clear_btn.pack(side=RIGHT, padx=10, pady=8)
    
    # 记录列表容器（包含Treeview和滚动条）
    tree_container = ttkb.Frame(fish_record_card)
    tree_container.pack(fill=BOTH, expand=YES, pady=(0, 8))

    # 记录列表（使用Treeview）
    columns = ("时间", "名称", "品质", "重量")
    fish_tree = ttkb.Treeview(
        tree_container,
        columns=columns,
        show="headings",
        style="CustomTreeview.Treeview"  # 使用自定义样式名称，避免bootstyle冲突
    )
    
    # 保存Treeview引用到全局变量
    global fish_tree_ref
    fish_tree_ref = fish_tree

    # 添加垂直滚动条（放在Treeview右侧）
    tree_scroll = ttkb.Scrollbar(tree_container, orient="vertical", command=fish_tree.yview, bootstyle="rounded")
    fish_tree.configure(yscrollcommand=tree_scroll.set)

    # 设置列标题
    fish_tree.heading("时间", text="时间")
    fish_tree.heading("名称", text="鱼名")
    fish_tree.heading("品质", text="品质")
    fish_tree.heading("重量", text="重量")

    # 不设置固定列宽，而是在程序初始化后调用动态调整列宽的函数
    # 初始化列宽为0，稍后会根据字体大小动态调整
    fish_tree.column("时间", width=0, anchor="center", stretch=YES)  # 启用自动拉伸
    fish_tree.column("名称", width=0, anchor="center", stretch=YES)      # 启用自动拉伸
    fish_tree.column("品质", width=0, anchor="center", stretch=YES) # 启用自动拉伸
    fish_tree.column("重量", width=0, anchor="center", stretch=YES) # 启用自动拉伸

    # 布局Treeview和滚动条
    fish_tree.pack(side=LEFT, fill=BOTH, expand=YES)
    tree_scroll.pack(side=RIGHT, fill=Y)

    # 配置品质颜色标签（背景色和前景色）
    # 标准-白色背景黑色字体, 非凡-绿色, 稀有-海洋蓝色, 史诗-紫色, 传说/传奇-金色
    fish_tree.tag_configure("标准", background="#FFFFFF", foreground="#000000")
    fish_tree.tag_configure("非凡", background="#2ECC71", foreground="#000000")
    fish_tree.tag_configure("稀有", background="#1E90FF", foreground="#FFFFFF")
    fish_tree.tag_configure("史诗", background="#9B59B6", foreground="#FFFFFF")
    fish_tree.tag_configure("传说", background="#F1C40F", foreground="#000000")
    fish_tree.tag_configure("传奇", background="#F1C40F", foreground="#000000")  # 传奇与传说同色

    # 绑定鼠标滚轮到Treeview
    def on_tree_mousewheel(event):
        fish_tree.yview_scroll(int(-1*(event.delta/120)), "units")

    fish_tree.bind("<MouseWheel>", on_tree_mousewheel)

    # 统计信息
    stats_var = ttkb.StringVar(value="共 0 条记录")
    stats_label = ttkb.Label(
        fish_record_card,
        textvariable=stats_var,
        bootstyle="info"
    )
    stats_label.pack()

    def update_fish_display():
        """更新钓鱼记录显示"""
        # 清空列表
        for item in fish_tree.get_children():
            fish_tree.delete(item)

        # 获取搜索关键词
        keyword = search_var.get()
        if keyword == "搜索鱼名...":
            keyword = ""

        # 根据视图模式选择数据源
        use_session = (view_mode.get() == "current")
        quality_filter = quality_var.get()

        # 获取筛选后的记录
        filtered = search_fish_records(keyword, quality_filter, use_session)
        
        # 获取所有记录用于统计（不考虑搜索和筛选）
        all_records = current_session_fish if use_session else all_fish_records
        
        # 计算品质统计
        total = len(all_records)
        quality_counts = {
            "标准": 0,
            "非凡": 0,
            "稀有": 0,
            "史诗": 0,
            "传说": 0,
            "传奇": 0
        }
        
        for record in all_records:
            if record.quality in quality_counts:
                quality_counts[record.quality] += 1
        
        # 合并传说和传奇的计数（因为它们是同一品质的不同名称）
        total_legendary = quality_counts["传说"] + quality_counts["传奇"]
        
        # 计算概率并更新标签
        def calc_percentage(count):
            return (count / total * 100) if total > 0 else 0
        
        # 品质图标映射
        quality_icons = {
            "标准": "⚪",
            "非凡": "🟢",
            "稀有": "🔵",
            "史诗": "🟣",
            "传说": "🟡"
        }
        
        # 格式化显示，添加图标和更美观的样式
        standard_var.set(f"{quality_icons['标准']} 标准: {quality_counts['标准']} ({calc_percentage(quality_counts['标准']):.2f}%)")
        uncommon_var.set(f"{quality_icons['非凡']} 非凡: {quality_counts['非凡']} ({calc_percentage(quality_counts['非凡']):.2f}%)")
        rare_var.set(f"{quality_icons['稀有']} 稀有: {quality_counts['稀有']} ({calc_percentage(quality_counts['稀有']):.2f}%)")
        epic_var.set(f"{quality_icons['史诗']} 史诗: {quality_counts['史诗']} ({calc_percentage(quality_counts['史诗']):.2f}%)")
        legendary_var.set(f"{quality_icons['传说']} 传说: {total_legendary} ({calc_percentage(total_legendary):.2f}%)")
        total_var.set(f"📊 总计: {total} 条")

        # 显示记录（倒序，最新的在前面）
        for record in reversed(filtered[-100:]):  # 最多显示100条
            # 直接使用完整时间戳（格式：YYYY-MM-DD HH:MM:SS）
            time_display = record.timestamp if record.timestamp else "未知时间"

            # 根据品质确定标签（用于显示颜色）
            quality_tag = record.quality if record.quality in ["标准", "非凡", "稀有", "史诗", "传说", "传奇"] else "标准"

            fish_tree.insert("", "end", values=(
                time_display,
                record.name,
                record.quality,
                record.weight
            ), tags=(quality_tag,))

        # 更新统计
        total_display = len(filtered)
        if use_session:
            stats_var.set(f"本次: {total_display} 条")
        else:
            stats_var.set(f"总计: {total_display} 条")

    # 设置GUI更新回调
    global gui_fish_update_callback
    def safe_update():
        try:
            root.after(0, update_fish_display)
        except:
            pass
    gui_fish_update_callback = safe_update

    def clear_fish_records():
        """清空钓鱼记录"""
        # 询问用户确认
        use_session = (view_mode.get() == "current")
        if use_session:
            confirm_text = "确定要清空本次钓鱼记录吗？"
        else:
            confirm_text = "确定要清空所有历史钓鱼记录吗？此操作不可恢复！"
        
        result = messagebox.askyesno("确认清空", confirm_text, parent=root)
        if not result:
            return
        
        with fish_record_lock:
            if use_session:
                # 清空当前会话记录
                global current_session_fish
                current_session_fish.clear()
            else:
                # 清空所有记录
                global all_fish_records
                all_fish_records.clear()
                # 清空记录文件
                try:
                    with open(FISH_RECORD_FILE, "w", encoding="utf-8") as f:
                        f.write("")
                except Exception as e:
                    print(f"❌ [错误] 清空记录文件失败: {e}")
        
        # 更新显示
        update_fish_display()
    
    # 初始加载
    update_fish_display()


    # ==================== 操作按钮区域（左侧面板底部） ====================
    btn_frame = ttkb.Frame(left_content_frame)
    btn_frame.pack(fill=X, pady=(8, 0))


    
    def update_and_refresh():
        """更新参数并刷新显示"""
        update_parameters(
            t_var, leftclickdown_var, leftclickup_var, times_var,
            paogantime_var, jiashi_var_option, random_delay_percent_var, resolution_var,
            custom_width_var, custom_height_var, hotkey_var, record_fish_var,
            legendary_screenshot_var, random_delay_var
        )
        resolution_info_var.set(f"当前: {TARGET_WIDTH}×{TARGET_HEIGHT}")
        hotkey_info_label.config(text=f"按 {hotkey_name} 启动/暂停 | 点击按钮修改")
        hotkey_btn.configure(text=hotkey_name)  # 更新热键按钮显示
        # 显示保存成功提示
        status_label.config(text="✅ 参数已保存", bootstyle="success")
        root.after(2000, lambda: status_label.config(text=f"按 {hotkey_name} 启动/暂停", bootstyle="light"))

    update_button = ttkb.Button(
        btn_frame,
        text="💾 保存设置",
        command=update_and_refresh,
        bootstyle="success",
        width=16
    )
    update_button.pack(pady=3, fill=X)

    # 调试按钮
    debug_button = ttkb.Button(
        btn_frame,
        text="🐛 调试",
        command=show_debug_window,
        bootstyle="warning-outline",
        width=16
    )
    debug_button.pack(pady=3, fill=X)

    # ==================== 状态栏（左侧面板底部） ====================
    status_frame = ttkb.Frame(left_panel)
    status_frame.pack(fill=X, pady=(8, 0))

    separator = ttkb.Separator(status_frame, bootstyle="secondary")
    separator.pack(fill=X, pady=(0, 5))

    status_label = ttkb.Label(
        status_frame,
        text=f"按 {hotkey_name} 启动/暂停",
        bootstyle="light"
    )
    status_label.pack()

    version_label = ttkb.Label(
        status_frame,
        text="v2.8 | PartyFish",
        bootstyle="light"
    )
    version_label.pack(pady=(2, 0))

    # ==================== 开发者信息 ====================
    def open_github(event=None):
        """打开GitHub主页"""
        webbrowser.open("https://github.com/FADEDTUMI/PartyFish/")

    dev_frame = ttkb.Frame(status_frame)
    dev_frame.pack(pady=(3, 0))

    dev_label = ttkb.Label(
        dev_frame,
        text="by ",
        bootstyle="light"
    )
    dev_label.pack(side=LEFT)

    # 可点击的开发者链接
    dev_link = ttkb.Label(
        dev_frame,
        text="FadedTUMI/PeiXiaoXiao",
        bootstyle="info",
        cursor="hand2"
    )
    dev_link.pack(side=LEFT)
    dev_link.bind("<Button-1>", open_github)

    # 鼠标悬停效果
    def on_enter(event):
        dev_link.configure(bootstyle="primary")

    def on_leave(event):
        dev_link.configure(bootstyle="info")

    dev_link.bind("<Enter>", on_enter)
    dev_link.bind("<Leave>", on_leave)

    # 应用保存的字体大小设置
    update_all_widget_fonts(root, style, font_size)
    
    # 在GUI初始化完成后，根据当前字体大小动态调整Treeview列宽
    # 确保程序启动时就能显示正确的列宽
    print(f"初始化后应用字体大小: {font_size}%")
    
    # 计算新的字体大小（像素单位）
    # 确保字体大小按照要求计算：
    # - 100% 时为 12px
    # - 150% 时为 18px
    # - 200% 时为 24px
    base_font_size = 12  # 基础字体大小为12px（100%时）
    new_font_size = int(base_font_size * (font_size / 100.0))
    
    # 精确调整字体大小，确保符合要求
    if font_size == 100:
        new_font_size = 12
    elif font_size == 150:
        new_font_size = 18
    elif font_size == 200:
        new_font_size = 24
    
    print(f"初始化时使用的字体大小: {new_font_size}px")
    
    # 调整比例，时间列与名称/重量列相同（时间:名称:品质:重量 = 63:63:36:63）
    # 动态计算初始列宽
    time_ratio = 63   # 时间列比例改为63，与名称/重量列一致
    name_ratio = 63
    quality_ratio = 36
    weight_ratio = 63
    total_ratio = time_ratio + name_ratio + quality_ratio + weight_ratio
    
    # 初始Treeview容器宽度，使用更小的估算值，让列宽更紧凑
    initial_container_width = 300  # 更小的初始估算宽度
    
    # 计算初始列宽
    column_widths = {
        "时间": int(initial_container_width * (time_ratio / total_ratio)),
        "名称": int(initial_container_width * (name_ratio / total_ratio)),
        "品质": int(initial_container_width * (quality_ratio / total_ratio)),
        "重量": int(initial_container_width * (weight_ratio / total_ratio))
    }
    
    print(f"初始化时计算得到的列宽: {column_widths}")
    
    # 应用新列宽到Treeview
    if fish_tree_ref:
        for col, width in column_widths.items():
            fish_tree_ref.column(col, width=width, anchor="center")
        
        # 初始化设置行高
        new_rowheight = int(new_font_size * 2.2)  # 行高为字体大小的2.2倍
        # 尝试修改多种Treeview样式，确保覆盖所有可能的样式名称
        style.configure("Treeview", rowheight=new_rowheight)
        style.configure("Info.Treeview", rowheight=new_rowheight)  # 对应bootstyle="info"
        style.configure("Table.Treeview", rowheight=new_rowheight)  # ttkbootstrap默认Treeview样式
        style.configure("CustomTreeview.Treeview", rowheight=new_rowheight)  # 自定义样式
        
        # 强制更新Treeview布局，确保列宽和行高调整立即生效
        fish_tree_ref.update_idletasks()
    
    # 主动触发一次窗口大小变化事件，确保初始列宽正确设置
    # 创建一个虚拟事件对象来传递
    class DummyEvent:
        def __init__(self, width):
            self.width = width
    
    # 调用窗口大小变化处理函数，确保初始列宽设置正确
    on_window_resize(DummyEvent(root.winfo_width()))
    
    # 软件启动时的一次应用窗口检测
    def perform_startup_window_check():
        global is_selected_window_active, selected_window_first_check_done
        if not selected_window_first_check_done:
            # 使用当前活动窗口进行检测
            result = check_window_style()
            is_selected_window_active = result['is_fullscreen_borderless']
            selected_window_first_check_done = True
            # 添加调试信息
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "selected_window_detection",
                "message": "应用窗口检测结果",
                "ocr_result": [],
                "parsed_info": {
                    "是否为选中窗口": "是" if result["is_selected_window"] else "否",
                    "窗口标题": result["window_title"],
                    "窗口类名": result["window_class"],
                    "窗口尺寸": f"{result['window_width']}x{result['window_height']}",
                    "显示器分辨率": f"{result['screen_width']}x{result['screen_height']}",
                    "是否无窗口边框样式": "是" if result["has_no_border"] else "否",
                    "是否尺寸匹配": "是" if result["size_match"] else "否",
                    "是否为全屏无边框窗口": "是" if result["is_fullscreen_borderless"] else "否"
                }
            }
            add_debug_info(debug_info)
    
    # 执行启动检测
    perform_startup_window_check()
    
    # 运行 GUI
    root.mainloop()
# =========================
# =========================
# 常数 t 定义：定义时间间隔为 0.3 秒（可以根据需要调整）
t = 0.3  # 将时间间隔缩短，提高响应速度
# 常数 leftclickup 和 leftclickdown，用于调整按下去和抬起的时间
leftclickdown = 2.5  # 鼠标左键按下去的时间（秒）
leftclickup = 2  # 鼠标左键抬起的时间（秒）
times = 15 #最大钓鱼拉杆次数
paogantime = 0.5
random_delay = 30  # 随机延迟百分比，0-30%，用户可自定义
random_delay_enabled = True  # 默认启用随机延迟
# =========================
# 分辨率设置（修改此处适配不同分辨率）
# =========================
# 基准分辨率：2560x1440 (2K)
BASE_WIDTH = 2560
BASE_HEIGHT = 1440
# 目标分辨率（修改为您的屏幕分辨率）
# 初始默认值，后续会更新为当前系统分辨率
TARGET_WIDTH = 2560
TARGET_HEIGHT = 1440

# 分辨率选择（用于GUI和保存）
resolution_choice = "current"

# 计算缩放比例
SCALE_X = TARGET_WIDTH / BASE_WIDTH
SCALE_Y = TARGET_HEIGHT / BASE_HEIGHT

def calculate_scale_factors():
    """
    计算缩放比例，考虑不同宽高比的情况
    游戏UI通常基于16:9设计，非16:9分辨率需要特殊处理
    """
    global SCALE_X, SCALE_Y, SCALE_UNIFORM

    # 基准宽高比 (16:9)
    base_aspect = BASE_WIDTH / BASE_HEIGHT  # 约1.78
    # 目标宽高比
    target_aspect = TARGET_WIDTH / TARGET_HEIGHT

    # 计算基础缩放
    SCALE_X = TARGET_WIDTH / BASE_WIDTH
    SCALE_Y = TARGET_HEIGHT / BASE_HEIGHT

    # 对于模板匹配和UI元素定位，使用基于宽高比的统一缩放
    # 16:10等非16:9分辨率需要特殊处理，确保UI元素正确定位
    # 16:10的宽高比(1.6)比16:9(1.78)小，所以需要特殊处理
    # 游戏UI通常会保持水平居中，垂直方向调整位置
    
    # 使用基于高度的缩放，确保垂直方向元素正确显示
    SCALE_UNIFORM = SCALE_Y

    return SCALE_X, SCALE_Y, SCALE_UNIFORM

# 初始化统一缩放比例
# 与calculate_scale_factors函数逻辑保持一致
# 使用基于高度的缩放，确保垂直方向元素正确显示
SCALE_UNIFORM = SCALE_Y

def scale_coords(x, y, w, h):
    """根据分辨率缩放坐标"""
    return (int(x * SCALE_X), int(y * SCALE_Y), int(w * SCALE_X), int(h * SCALE_Y))

def scale_coords_uniform(x, y, w, h):
    """使用统一缩放比例缩放坐标（避免变形）"""
    return (int(x * SCALE_UNIFORM), int(y * SCALE_UNIFORM), int(w * SCALE_UNIFORM), int(h * SCALE_UNIFORM))

def scale_point(x, y):
    """根据分辨率缩放单点坐标"""
    return (int(x * SCALE_X), int(y * SCALE_Y))

def scale_point_center_anchored(x, y):
    """使用中心锚定方式缩放单点坐标（适用于居中UI元素如加时按钮）"""
    scale = SCALE_UNIFORM
    center_offset_x = x - BASE_WIDTH / 2
    center_offset_y = y - BASE_HEIGHT / 2
    return (int(TARGET_WIDTH / 2 + center_offset_x * scale),
            int(TARGET_HEIGHT / 2 + center_offset_y * scale))

def scale_corner_anchored(base_x, base_y, base_w, base_h, anchor="bottom_right"):
    """
    缩放锚定在角落的UI元素坐标
    游戏UI（如鱼饵数量）通常锚定在屏幕角落而不是按比例缩放

    anchor: "bottom_right", "top_left", "center" 等
    """
    if anchor == "bottom_right":
        # 计算距离右下角的偏移（基于2K分辨率）
        offset_from_right = BASE_WIDTH - base_x
        offset_from_bottom = BASE_HEIGHT - base_y
        # 在目标分辨率中，从右下角计算实际位置
        # 使用基于高度的缩放比例，确保16:10等非16:9分辨率下元素正确定位
        scale = SCALE_UNIFORM
        new_x = TARGET_WIDTH - int(offset_from_right * scale)
        new_y = TARGET_HEIGHT - int(offset_from_bottom * scale)
        new_w = int(base_w * scale)
        new_h = int(base_h * scale)
        return (new_x, new_y, new_w, new_h)
    elif anchor == "center":
        # 居中的元素按比例缩放
        return scale_coords_uniform(base_x, base_y, base_w, base_h)
    else:
        # 默认使用普通缩放
        return scale_coords(base_x, base_y, base_w, base_h)

def scale_coords_bottom_anchored(base_x, base_y, base_w, base_h):
    """
    缩放锚定在底部中央的UI元素坐标
    游戏UI（如F1/F2按钮）通常锚定在屏幕底部中央
    """
    scale = SCALE_UNIFORM
    # X坐标：居中元素按中心点缩放
    center_offset_x = base_x - BASE_WIDTH / 2
    new_x = int(TARGET_WIDTH / 2 + center_offset_x * scale)
    # Y坐标：锚定在底部
    offset_from_bottom = BASE_HEIGHT - base_y
    new_y = TARGET_HEIGHT - int(offset_from_bottom * scale)
    new_w = int(base_w * scale)
    new_h = int(base_h * scale)
    return (new_x, new_y, new_w, new_h)

def scale_coords_top_center(base_x, base_y, base_w, base_h):
    """
    缩放锚定在顶部中央的UI元素坐标（如钓鱼星星）
    """
    scale = SCALE_UNIFORM
    # X坐标：居中元素按中心点缩放
    center_offset_x = base_x - BASE_WIDTH / 2
    new_x = int(TARGET_WIDTH / 2 + center_offset_x * scale)
    # Y坐标：锚定在顶部
    new_y = int(base_y * scale)
    new_w = int(base_w * scale)
    new_h = int(base_h * scale)
    return (new_x, new_y, new_w, new_h)

def update_region_coords():
    """根据当前缩放比例更新所有区域坐标"""
    global region3_coords, region4_coords, region5_coords, region6_coords
    # 上鱼星星 - 顶部中央区域
    region3_coords = scale_coords_top_center(1172, 165, 34, 34)
    # F1位置 - 底部中央区域
    region4_coords = scale_coords_bottom_anchored(1100, 1329, 10, 19)
    # F2位置 - 底部中央区域
    region5_coords = scale_coords_bottom_anchored(1212, 1329, 10, 19)
    # 上鱼右键 - 底部中央区域
    region6_coords = scale_coords_bottom_anchored(1146, 1316, 17, 21)
    # 当坐标更新时，检查是否需要重新加载模板
    reload_templates_if_scale_changed()

# =========================
# 参数设置
# =========================
template_folder_path = os.path.join(os.path.dirname(__file__), 'resources')

# =========================
# 钓鱼记录系统
# =========================
FISH_RECORD_FILE = "./fish_records.txt"

# 鱼信息识别区域（2K分辨率基准值）
FISH_INFO_REGION_BASE = (915, 75, 1640, 225)  # 左上角x, y, 右下角x, y

# 品质等级定义（包含"传奇"作为"传说"的别名，部分游戏版本可能使用不同名称）
QUALITY_LEVELS = ["标准", "非凡", "稀有", "史诗", "传说", "传奇"]
# GUI专用品质列表，不包含"传奇"选项，避免在GUI筛选中显示
GUI_QUALITY_LEVELS = ["标准", "非凡", "稀有", "史诗", "传说"]
QUALITY_COLORS = {
    "标准": "⚪",
    "非凡": "🟢",
    "稀有": "🔵",
    "史诗": "🟣",
    "传说": "🟡",
    "传奇": "🟡"  # 传奇与传说同级，使用相同颜色（用于兼容旧记录）
}

# 当前会话数据
current_session_id = None
current_session_fish = []  # 当前会话钓到的鱼
all_fish_records = []      # 所有钓鱼记录（从文件加载）
fish_record_lock = threading.Lock()  # 钓鱼记录锁

# GUI更新回调（将在create_gui中设置）
gui_fish_update_callback = None

class FishRecord:
    """单条鱼的记录"""
    def __init__(self, name, quality, weight):
        self.name = name if name else "未知"
        self.quality = quality if quality in QUALITY_LEVELS else "标准"
        self.weight = weight if weight else "0"
        self.timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.session_id = current_session_id

    def to_dict(self):
        return {
            "name": self.name,
            "quality": self.quality,
            "weight": self.weight,
            "timestamp": self.timestamp,
            "session_id": self.session_id
        }

    def to_line(self):
        """转换为文件存储格式"""
        return f"{self.session_id}|{self.timestamp}|{self.name}|{self.quality}|{self.weight}\n"

    @staticmethod
    def from_line(line):
        """从文件行解析"""
        try:
            parts = line.strip().split("|")
            if len(parts) >= 5:
                record = FishRecord.__new__(FishRecord)
                record.session_id = parts[0]
                record.timestamp = parts[1]
                record.name = parts[2]
                record.quality = parts[3]
                record.weight = parts[4]
                return record
        except:
            pass
        return None

def save_fish_record(fish_record):
    """保存单条钓鱼记录到文件"""
    try:
        with open(FISH_RECORD_FILE, "a", encoding="utf-8") as f:
            f.write(fish_record.to_line())
    except Exception as e:
        print(f"❌ [错误] 保存钓鱼记录失败: {e}")

def load_all_fish_records():
    """加载所有历史钓鱼记录"""
    global all_fish_records
    all_fish_records = []
    try:
        if os.path.exists(FISH_RECORD_FILE):
            with open(FISH_RECORD_FILE, "r", encoding="utf-8") as f:
                for line in f:
                    if line.strip():
                        record = FishRecord.from_line(line)
                        if record:
                            all_fish_records.append(record)
            print(f"📊 [信息] 已加载 {len(all_fish_records)} 条历史钓鱼记录")
    except Exception as e:
        print(f"❌ [错误] 加载钓鱼记录失败: {e}")

def start_new_session():
    """开始新的钓鱼会话"""
    global current_session_id, current_session_fish
    current_session_id = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    current_session_fish = []
    print(f"🎣 [会话] 新钓鱼会话开始: {current_session_id}")

def end_current_session():
    """结束当前钓鱼会话"""
    global current_session_id, current_session_fish
    if current_session_fish:
        print(f"📊 [会话] 本次钓鱼结束，共钓到 {len(current_session_fish)} 条鱼")
        # 统计品质
        quality_count = {}
        for fish in current_session_fish:
            quality_count[fish.quality] = quality_count.get(fish.quality, 0) + 1
        for q, count in quality_count.items():
            emoji = QUALITY_COLORS.get(q, "⚪")
            print(f"   {emoji} {q}: {count} 条")
    current_session_id = None

def capture_fish_info_region(scr_param=None):
    """截取鱼信息区域的图像
    
    Args:
        scr_param: 截图对象，如果为None则使用全局scr对象
    
    Returns:
        img_rgb: RGB格式的鱼信息区域图像，如果截取失败则返回None
    """
    global scr
    # 优先使用传入的scr_param，如果为None则使用全局scr
    current_scr = scr_param if scr_param is not None else scr
    
    if current_scr is None:
        # 调试信息：记录错误
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "capture_error",
                "error": "截图对象未初始化",
                "scr_source": "传入参数" if scr_param is not None else "全局对象"
            }
            add_debug_info(debug_info)
        return None

    # 获取主显示器信息，确保只在主显示器上截图
    monitor = current_scr.monitors[1]  # 1 表示主显示器
    
    # 根据分辨率缩放坐标
    x1, y1, x2, y2 = FISH_INFO_REGION_BASE
    scaled_x1 = int(x1 * SCALE_X)
    scaled_y1 = int(y1 * SCALE_Y)
    scaled_x2 = int(x2 * SCALE_X)
    scaled_y2 = int(y2 * SCALE_Y)
    
    # 确保区域在主显示器范围内
    actual_x1 = max(monitor['left'], scaled_x1)
    actual_y1 = max(monitor['top'], scaled_y1)
    actual_x2 = min(monitor['left'] + monitor['width'], scaled_x2)
    actual_y2 = min(monitor['top'] + monitor['height'], scaled_y2)
    
    # 重新计算宽度和高度，确保有效
    actual_w = max(1, actual_x2 - actual_x1)
    actual_h = max(1, actual_y2 - actual_y1)
    
    region = (actual_x1, actual_y1, actual_x2, actual_y2)

    try:
        frame = current_scr.grab(region)
        if frame is None:
            # 调试信息：记录错误
            if debug_mode:
                debug_info = {
                    "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                    "region": {
                        "x1": region[0],
                        "y1": region[1],
                        "x2": region[2],
                        "y2": region[3],
                        "width": region[2] - region[0],
                        "height": region[3] - region[1]
                    },
                    "action": "capture_error",
                    "error": "截取图像失败",
                    "scr_source": "传入参数" if scr_param is not None else "全局对象"
                }
                add_debug_info(debug_info)
            return None
        img = np.array(frame)
        # 转换为RGB格式（OCR需要）
        img_rgb = cv2.cvtColor(img, cv2.COLOR_BGRA2RGB)
        
        # 调试信息：记录截取区域
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "region": {
                    "x1": region[0],
                    "y1": region[1],
                    "x2": region[2],
                    "y2": region[3],
                    "width": region[2] - region[0],
                    "height": region[3] - region[1]
                },
                "action": "capture_region",
                "message": "成功截取鱼信息区域",
                "scr_source": "传入参数" if scr_param is not None else "全局对象"
            }
            add_debug_info(debug_info)
        
        return img_rgb
    except Exception as e:
        print(f"❌ [错误] 截取鱼信息区域失败: {e}")
        # 调试信息：记录错误
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "region": {
                    "x1": region[0],
                    "y1": region[1],
                    "x2": region[2],
                    "y2": region[3],
                    "width": region[2] - region[0],
                    "height": region[3] - region[1]
                },
                "action": "capture_error",
                "error": str(e),
                "scr_source": "传入参数" if scr_param is not None else "全局对象"
            }
            add_debug_info(debug_info)
        return None

def recognize_fish_info_ocr(img):
    """使用OCR识别鱼的信息"""
    if not OCR_AVAILABLE or ocr_engine is None:
        # 调试信息：记录错误
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "ocr_error",
                "error": "OCR引擎不可用"
            }
            add_debug_info(debug_info)
        return None, None, None

    if img is None:
        # 调试信息：记录错误
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "ocr_error",
                "error": "输入图像为空"
            }
            add_debug_info(debug_info)
        return None, None, None

    try:
        # 执行OCR识别
        result, elapse = ocr_engine(img)
        
        # 确保result是列表类型
        if result is None:
            result = []
        
        # 合并所有识别到的文本
        full_text = ""
        for line in result:
            if isinstance(line, list) and len(line) >= 2:
                full_text += line[1] + " "

        full_text = full_text.strip()

        # 解析鱼的信息
        fish_name = None
        fish_quality = None
        fish_weight = None

        if len(result) > 0 and full_text:
            # 识别品质
            for quality in QUALITY_LEVELS:
                if quality in full_text:
                    fish_quality = quality
                    break

            # 识别重量（匹配数字+kg或g的模式）
            weight_pattern = r'(\d+\.?\d*)\s*(kg|g|千克|克)?'
            weight_matches = re.findall(weight_pattern, full_text, re.IGNORECASE)
            if weight_matches:
                # 取最后一个匹配的数字作为重量
                for match in weight_matches:
                    if match[0]:
                        fish_weight = match[0]
                        unit = match[1].lower() if match[1] else "kg"
                        if unit in ['g', '克']:
                            fish_weight = str(float(fish_weight) / 1000)
                        fish_weight = f"{float(fish_weight):.2f}kg"

            # 识别鱼名 - 优先匹配"你钓到了XXX"或"首次捕获XXX"格式
            # 使用正则表达式提取鱼名
            fish_name_patterns = [
                r'你钓到了\s*[「【\[]?\s*(.+?)\s*[」】\]]?\s*(?:标准|非凡|稀有|史诗|传说|传奇|$)',  # 你钓到了XXX
                r'首次捕获\s*[「【\[]?\s*(.+?)\s*[」】\]]?\s*(?:标准|非凡|稀有|史诗|传说|传奇|$)',  # 首次捕获XXX
                r'钓到了\s*[「【\[]?\s*(.+?)\s*[」】\]]?\s*(?:标准|非凡|稀有|史诗|传说|传奇|$)',   # 钓到了XXX
                r'捕获\s*[「【\[]?\s*(.+?)\s*[」】\]]?\s*(?:标准|非凡|稀有|史诗|传说|传奇|$)',     # 捕获XXX
            ]

            for pattern in fish_name_patterns:
                match = re.search(pattern, full_text)
                if match:
                    extracted_name = match.group(1).strip()
                    # 清理鱼名中的数字、单位和特殊字符
                    extracted_name = re.sub(r'\d+\.?\d*\s*(kg|g|千克|克)?', '', extracted_name, flags=re.IGNORECASE)
                    extracted_name = re.sub(r'[^\u4e00-\u9fa5a-zA-Z\s]', '', extracted_name)
                    extracted_name = extracted_name.strip()
                    if extracted_name and len(extracted_name) >= 2:
                        fish_name = extracted_name
                        break

            # 如果上述模式都没匹配到，尝试备用方案
            if not fish_name:
                name_text = full_text
                # 移除常见前缀
                prefixes_to_remove = ['你钓到了', '首次捕获', '钓到了', '捕获', '你钓到', '钓到']
                for prefix in prefixes_to_remove:
                    name_text = name_text.replace(prefix, ' ')
                # 移除品质词
                if fish_quality:
                    name_text = name_text.replace(fish_quality, ' ')
                # 移除数字和单位
                name_text = re.sub(r'\d+\.?\d*\s*(kg|g|千克|克)?', '', name_text, flags=re.IGNORECASE)
                # 清理特殊字符，保留中文和英文
                name_text = re.sub(r'[^\u4e00-\u9fa5a-zA-Z]', ' ', name_text)
                # 取最长的连续中文词作为鱼名
                chinese_words = re.findall(r'[\u4e00-\u9fa5]{2,}', name_text)
                if chinese_words:
                    # 选择最长的词作为鱼名
                    fish_name = max(chinese_words, key=len)
        
        # 调试信息：记录OCR识别结果和详细的鱼信息识别
        if debug_mode:
            # 基本OCR识别结果日志
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "ocr_recognize",
                "message": "鱼信息OCR识别完成",
                "ocr_result": result,
                "full_text": full_text,
                "elapse": elapse,
                "image_shape": img.shape if img is not None else "无图像",
                "result_count": len(result),
                "has_text": bool(full_text)
            }
            add_debug_info(debug_info)
            
            # 详细的鱼信息识别日志
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_info_recognition_complete",
                "message": "鱼信息识别完整流程完成",
                "parsed_info": {
                    "鱼名": fish_name if fish_name else "未识别",
                    "品质": fish_quality if fish_quality else "未识别",
                    "重量": fish_weight if fish_weight else "未识别"
                },
                "full_text": full_text
            }
            add_debug_info(debug_info)

        if len(result) == 0 or not full_text:
            return None, None, None

        return fish_name, fish_quality, fish_weight

    except Exception as e:
        print(f"❌ [错误] OCR识别失败: {e}")
        # 调试信息：记录OCR错误
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "ocr_error",
                "error": str(e),
                "exception_type": type(e).__name__
            }
            add_debug_info(debug_info)
        return None, None, None

def record_caught_fish():
    """识别并记录钓到的鱼"""
    global current_session_fish, all_fish_records
    global record_fish_enabled

    # 调试信息：记录函数开始执行
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_start",
            "message": "开始记录钓到的鱼",
            "ocr_available": OCR_AVAILABLE,
            "record_fish_enabled": record_fish_enabled
        }
        add_debug_info(debug_info)

    if not OCR_AVAILABLE or not record_fish_enabled:
        # 调试信息：记录钓鱼记录开关状态
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_record_check",
                "message": "钓鱼记录未执行",
                "reason": "OCR不可用" if not OCR_AVAILABLE else "钓鱼记录开关已关闭",
                "ocr_available": OCR_AVAILABLE,
                "record_fish_enabled": record_fish_enabled
            }
            add_debug_info(debug_info)
        return None

    # 等待鱼信息显示
    time.sleep(0.3)

    # 调试信息：记录准备截取鱼信息区域
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_capture_start",
            "message": "准备截取鱼信息区域"
        }
        add_debug_info(debug_info)

    # 截取鱼信息区域
    img = capture_fish_info_region()
    if img is None:
        # 调试信息：记录鱼信息区域截取失败
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_record_capture_failed",
                "message": "鱼信息区域截取失败"
            }
            add_debug_info(debug_info)
        return None

    # 调试信息：记录鱼信息区域截取成功
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_capture_success",
            "message": "鱼信息区域截取成功",
            "image_shape": img.shape if img is not None else "无图像"
        }
        add_debug_info(debug_info)
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_ocr_start",
            "message": "开始OCR识别鱼信息"
        }
        add_debug_info(debug_info)

    # OCR识别
    fish_name, fish_quality, fish_weight = recognize_fish_info_ocr(img)

    # 调试信息：记录OCR识别结果
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_ocr_result",
            "message": "OCR识别完成",
            "fish_name": fish_name,
            "fish_quality": fish_quality,
            "fish_weight": fish_weight,
            "has_valid_data": fish_name is not None or fish_quality is not None or fish_weight is not None
        }
        add_debug_info(debug_info)

    if fish_name is None and fish_quality is None and fish_weight is None:
        # 调试信息：记录OCR识别无有效数据
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_record_ocr_no_data",
                "message": "OCR识别未获取到有效鱼信息"
            }
            add_debug_info(debug_info)
        return None

    # 调试信息：记录开始保存记录
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "fish_record_save_start",
            "message": "准备保存钓鱼记录",
            "raw_fish_quality": fish_quality
        }
        add_debug_info(debug_info)

    try:
        # 创建记录
        with fish_record_lock:
            # 合并"传奇"和"传说"品质，统一使用"传说"
            if fish_quality == "传奇":
                fish_quality = "传说"
            fish = FishRecord(fish_name, fish_quality, fish_weight)
            current_session_fish.append(fish)
            all_fish_records.append(fish)
            save_fish_record(fish)
        
        # 调试信息：记录保存成功
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_record_save_success",
                "message": "钓鱼记录保存成功",
                "record": {
                    "name": fish.name,
                    "quality": fish.quality,
                    "weight": fish.weight,
                    "timestamp": fish.timestamp
                },
                "parsed_info": {
                    "鱼名": fish.name,
                    "品质": fish.quality,
                    "重量": fish.weight
                }
            }
            add_debug_info(debug_info)
        
        # 终端输出
        quality_emoji = QUALITY_COLORS.get(fish.quality, "⚪")
        print(f"🐟 [钓到] {quality_emoji} {fish.name} | 品质: {fish.quality} | 重量: {fish.weight}")

        # 传说/传奇鱼自动截屏
        if legendary_screenshot_enabled and fish.quality == "传说":
            try:
                # 调试信息：记录开始传说鱼截屏
                if debug_mode:
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "fish_record_screenshot_start",
                        "message": "开始传说鱼自动截屏"
                    }
                    add_debug_info(debug_info)
                
                # 使用mss截取全屏
                with mss.mss() as sct:
                    # 获取主显示器的尺寸
                    monitor = sct.monitors[1]  # 1 表示主显示器
                    screenshot = sct.grab(monitor)
                    
                    # 创建截图保存目录
                    screenshot_dir = os.path.join('.', 'screenshots')
                    os.makedirs(screenshot_dir, exist_ok=True)
                    
                    # 生成截图文件名（包含时间戳和鱼名）
                    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                    fish_name_clean = re.sub(r'[^\w\s]', '', fish.name)
                    screenshot_path = os.path.join(screenshot_dir, f"{timestamp}_{fish_name_clean}_{fish.quality}.png")
                    
                    # 保存截图
                    mss.tools.to_png(screenshot.rgb, screenshot.size, output=screenshot_path)
                    print(f"📸 [截屏] 传说鱼已自动保存: {screenshot_path}")
                    
                    # 调试信息：记录传说鱼截屏成功
                    if debug_mode:
                        debug_info = {
                            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                            "action": "fish_record_screenshot_success",
                            "message": "传说鱼自动截屏成功",
                            "screenshot_path": screenshot_path
                        }
                        add_debug_info(debug_info)
            except Exception as e:
                print(f"❌ [错误] 截图失败: {e}")
                # 调试信息：记录传说鱼截屏失败
                if debug_mode:
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "fish_record_screenshot_failed",
                        "message": "传说鱼自动截屏失败",
                        "error": str(e),
                        "exception_type": type(e).__name__
                    }
                    add_debug_info(debug_info)

        # 通知GUI更新
        if gui_fish_update_callback:
            try:
                gui_fish_update_callback()
                # 调试信息：记录GUI更新成功
                if debug_mode:
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "fish_record_gui_update",
                        "message": "钓鱼记录GUI更新成功"
                    }
                    add_debug_info(debug_info)
            except Exception as e:
                # 调试信息：记录GUI更新失败
                if debug_mode:
                    debug_info = {
                        "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                        "action": "fish_record_gui_update_failed",
                        "message": "钓鱼记录GUI更新失败",
                        "error": str(e),
                        "exception_type": type(e).__name__
                    }
                    add_debug_info(debug_info)
        
        return fish
    except Exception as e:
        # 调试信息：记录记录保存失败
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "fish_record_save_failed",
                "message": "钓鱼记录保存失败",
                "error": str(e),
                "exception_type": type(e).__name__,
                "fish_name": fish_name,
                "fish_quality": fish_quality,
                "fish_weight": fish_weight
            }
            add_debug_info(debug_info)
        return None

def get_session_fish_list():
    """获取当前会话的钓鱼记录"""
    with fish_record_lock:
        return list(current_session_fish)

def get_all_fish_list():
    """获取所有钓鱼记录"""
    with fish_record_lock:
        return list(all_fish_records)

def search_fish_records(keyword="", quality_filter="全部", use_session=True):
    """搜索钓鱼记录"""
    with fish_record_lock:
        records = current_session_fish if use_session else all_fish_records

        filtered = []
        for record in records:
            # 品质筛选 - 合并"传说"和"传奇"
            if quality_filter != "全部":
                if quality_filter == "传说":
                    # 筛选传说时也包含传奇
                    if record.quality not in ["传说", "传奇"]:
                        continue
                else:
                    # 其他品质正常筛选
                    if record.quality != quality_filter:
                        continue
            # 关键词搜索
            if keyword and keyword.lower() not in record.name.lower():
                continue
            filtered.append(record)

        return filtered
# 定义区域的坐标 (x, y, w, h) - 基于2K分辨率的基准值
# 使用 scale_coords 函数自动缩放
region3_coords = scale_coords(1172, 165, 34, 34)    #上鱼星星
region4_coords = scale_coords(1100, 1329, 10, 19)   #F1位置
region5_coords = scale_coords(1212, 1329, 10, 19)   #F2位置
region6_coords = scale_coords(1146, 1316, 17, 21)   #上鱼右键

# 鱼饵数量区域（基准值）
BAIT_REGION_BASE = (2318, 1296, 2348, 1318)
# 加时界面检测区域（基准值）
JIASHI_REGION_BASE = (1245, 675, 26, 27)
# 点击按钮位置（基准值）
BTN_NO_JIASHI_BASE = (1182, 776)   # 不加时按钮
BTN_YES_JIASHI_BASE = (1398, 776)  # 加时按钮
#鱼桶区域（基准值）
FISH_BUCKET_REGION_BASE = (1865, 510, 590, 700)   #鱼桶区域
FISH_BUCKET_LABEL_REGION_BASE = (2143, 410, 106, 49)   #鱼桶标签区域

previous_result = None  # 上次识别的结果
current_result = 0  # 当前识别的数字
# 模板加载一次
templates = None
star_template = None
f1 = None
f2 = None
shangyule = None
jiashi = None
jiashi_var = 0
# 模板缩放后的缓存（用于分辨率切换时重新加载）
_cached_scale_x = None
_cached_scale_y = None
run_event = threading.Event()
begin_event = threading.Event()
fish_bucket_run_event = threading.Event()
user32 = ctypes.WinDLL("user32")
listener = None #监听
hotkey_name = "F2"  # 默认热键显示名称
hotkey_modifiers = set()  # 修饰键集合 (ctrl, alt, shift)
hotkey_main_key = keyboard.Key.f4  # 主按键对象
release_hotkey_name = "F4"  # 默认热键显示名称
release_hotkey_modifiers = set()  # 修饰键集合 (ctrl, alt, shift)
release_hotkey_main_key = keyboard.Key.f4  # 主按键对象

#定义放生模板
# release_biaozun = None
release_feifan = None
release_xiyou = None
release_shishi = None
release_chuanshuo = None
release_bucket_label = None



# 获取当前系统分辨率（考虑系统缩放）
def get_current_screen_resolution():
    """
    获取当前系统的屏幕分辨率（不考虑系统缩放，返回真实物理分辨率）
    返回: (width, height) 元组
    """
    try:
        # 直接返回真实物理分辨率，不考虑系统缩放
        actual_width, actual_height = get_actual_screen_resolution()
        return actual_width, actual_height
    except Exception as e:
        print(f"❌ [错误] 获取屏幕分辨率失败: {e}")
        return TARGET_WIDTH, TARGET_HEIGHT

# 获取系统缩放比例（百分比）
def get_system_scaling():
    """
    获取系统缩放比例（百分比）
    返回: 缩放百分比，如100, 125, 150等
    """
    try:
        # 获取设备上下文
        dc = user32.GetDC(0)
        if dc is None:
            return 100
        
        # 获取水平DPI
        dpi_x = ctypes.windll.gdi32.GetDeviceCaps(dc, LOGPIXELSX)
        
        # 释放设备上下文
        user32.ReleaseDC(0, dc)
        
        # 默认DPI是96，计算缩放百分比
        scaling = int(dpi_x / DEFAULT_DPI * 100)
        return scaling
    except Exception as e:
        print(f"❌ [错误] 获取系统缩放失败: {e}")
        return 100

# 获取真实屏幕分辨率（不考虑系统缩放）
def get_actual_screen_resolution():
    """
    获取真实物理屏幕分辨率（不考虑系统缩放）
    返回: (width, height) 元组
    """
    try:
        # 使用EnumDisplaySettings获取真实分辨率
        class DEVMODE(ctypes.Structure):
            _fields_ = [
                ("dmDeviceName", ctypes.c_wchar * 32),
                ("dmSpecVersion", ctypes.wintypes.WORD),
                ("dmDriverVersion", ctypes.wintypes.WORD),
                ("dmSize", ctypes.wintypes.WORD),
                ("dmDriverExtra", ctypes.wintypes.WORD),
                ("dmFields", ctypes.wintypes.DWORD),
                ("dmPositionX", ctypes.wintypes.LONG),
                ("dmPositionY", ctypes.wintypes.LONG),
                ("dmDisplayOrientation", ctypes.wintypes.DWORD),
                ("dmDisplayFixedOutput", ctypes.wintypes.DWORD),
                ("dmColor", ctypes.wintypes.WORD),
                ("dmDuplex", ctypes.wintypes.WORD),
                ("dmYResolution", ctypes.wintypes.WORD),
                ("dmTTOption", ctypes.wintypes.WORD),
                ("dmCollate", ctypes.wintypes.WORD),
                ("dmFormName", ctypes.c_wchar * 32),
                ("dmLogPixels", ctypes.wintypes.WORD),
                ("dmBitsPerPel", ctypes.wintypes.DWORD),
                ("dmPelsWidth", ctypes.wintypes.DWORD),
                ("dmPelsHeight", ctypes.wintypes.DWORD),
                ("dmDisplayFlags", ctypes.wintypes.DWORD),
                ("dmDisplayFrequency", ctypes.wintypes.DWORD),
                ("dmICMMethod", ctypes.wintypes.DWORD),
                ("dmICMIntent", ctypes.wintypes.DWORD),
                ("dmMediaType", ctypes.wintypes.DWORD),
                ("dmDitherType", ctypes.wintypes.DWORD),
                ("dmReserved1", ctypes.wintypes.DWORD),
                ("dmReserved2", ctypes.wintypes.DWORD),
                ("dmPanningWidth", ctypes.wintypes.DWORD),
                ("dmPanningHeight", ctypes.wintypes.DWORD),
            ]
        
        devmode = DEVMODE()
        devmode.dmSize = ctypes.sizeof(DEVMODE)
        
        # 获取当前显示设置
        if ctypes.windll.user32.EnumDisplaySettingsW(None, -1, ctypes.byref(devmode)):
            # 注意：dmPelsWidth是宽度，dmPelsHeight是高度
            actual_width = devmode.dmPelsWidth
            actual_height = devmode.dmPelsHeight
            
            # 添加合理性检查，确保分辨率有效
            if actual_width >= 800 and actual_height >= 600:
                return actual_width, actual_height
            else:
                print(f"⚠️  [警告] 检测到无效分辨率: {actual_width}×{actual_height}，尝试使用备选方案")
        
        # 如果获取失败或分辨率无效，使用默认分辨率或直接调用Windows API获取
        try:
            # 使用GetSystemMetrics获取当前分辨率
            width = user32.GetSystemMetrics(0)  # SM_CXSCREEN = 0
            height = user32.GetSystemMetrics(1)  # SM_CYSCREEN = 1
            
            # 再次检查合理性
            if width >= 800 and height >= 600:
                return width, height
            else:
                print(f"⚠️  [警告] 备选方案返回无效分辨率: {width}×{height}，使用默认分辨率")
        except Exception as e:
            print(f"❌ [错误] 获取分辨率失败: {e}，使用默认分辨率")
        
        # 如果所有方法都失败，返回默认分辨率
        return BASE_WIDTH, BASE_HEIGHT
    except Exception as e:
        print(f"❌ [错误] 获取真实分辨率失败: {e}")
        try:
            # 使用GetSystemMetrics作为备选方案
            width = user32.GetSystemMetrics(0)
            height = user32.GetSystemMetrics(1)
            
            if width >= 800 and height >= 600:
                return width, height
            else:
                print(f"⚠️  [警告] 错误处理中返回无效分辨率: {width}×{height}，使用默认分辨率")
        except Exception as e2:
            print(f"❌ [错误] 错误处理中获取分辨率失败: {e2}，使用默认分辨率")
        
        # 所有方法都失败，返回默认分辨率
        return BASE_WIDTH, BASE_HEIGHT

# 获取当前系统分辨率（真实物理分辨率）
CURRENT_SCREEN_WIDTH, CURRENT_SCREEN_HEIGHT = get_current_screen_resolution()

# 获取系统缩放比例
initial_system_scaling = get_system_scaling()

# 如果分辨率选择为"current"，则更新目标分辨率为当前系统分辨率
if resolution_choice == "current":
    # 直接使用真实物理分辨率，无需额外处理
    TARGET_WIDTH, TARGET_HEIGHT = CURRENT_SCREEN_WIDTH, CURRENT_SCREEN_HEIGHT
    # 重新计算缩放比例
    SCALE_X = TARGET_WIDTH / BASE_WIDTH
    SCALE_Y = TARGET_HEIGHT / BASE_HEIGHT
    # 计算统一缩放比例
    calculate_scale_factors()

def get_monitor_info(hwnd):
    """
    获取窗口所在显示器的分辨率
    
    Args:
        hwnd: 窗口句柄
        
    Returns:
        (width, height): 显示器分辨率
    """
    try:
        # 获取窗口所在的显示器句柄
        monitor_hwnd = user32.MonitorFromWindow(hwnd, 0)
        
        # 初始化MONITORINFO结构体
        monitor_info = MONITORINFO()
        monitor_info.cbSize = ctypes.sizeof(MONITORINFO)
        
        # 获取显示器信息
        if user32.GetMonitorInfoW(monitor_hwnd, ctypes.byref(monitor_info)):
            # 计算显示器分辨率
            width = monitor_info.rcMonitor.right - monitor_info.rcMonitor.left
            height = monitor_info.rcMonitor.bottom - monitor_info.rcMonitor.top
            return width, height
        else:
            # 获取失败，返回当前系统分辨率
            return get_current_screen_resolution()
    except Exception as e:
        print(f"❌ [错误] 获取显示器信息失败: {e}")
        # 获取失败，返回当前系统分辨率
        return get_current_screen_resolution()

def is_fullscreen_borderless_window(hwnd):
    """
    判断窗口是否为全屏无边框窗口
    
    Args:
        hwnd: 窗口句柄
        
    Returns:
        bool: True表示是全屏无边框窗口，False表示不是
    """
    # 步骤3：获取显示器分辨率和窗口尺寸
    screen_width, screen_height = get_monitor_info(hwnd)
    if screen_width == 0 or screen_height == 0:
        return False
    
    # 获取窗口边界矩形（含边框、标题栏，屏幕坐标）
    window_rect = RECT()
    if not user32.GetWindowRect(hwnd, ctypes.byref(window_rect)):
        return False
    
    window_width = window_rect.right - window_rect.left
    window_height = window_rect.bottom - window_rect.top
    
    # 步骤4：验证窗口样式（无标题栏、无边框，排除手动拉满窗口的情况）
    window_style = user32.GetWindowLongW(hwnd, GWL_STYLE)
    if window_style == 0:
        return False
    
    # 无WS_CAPTION（标题栏）且无WS_THICKFRAME（可调整边框）
    has_no_border = (window_style & (WS_CAPTION | WS_THICKFRAME)) == 0
    
    # 步骤5：尺寸对比（允许±2像素容差，适配部分游戏的微小偏差）
    TOLERANCE = 2
    size_match = (abs(window_width - screen_width) <= TOLERANCE) and \
                 (abs(window_height - screen_height) <= TOLERANCE)
    
    # 最终判断：尺寸匹配 + 无窗口边框样式
    return size_match and has_no_border

def get_foreground_window():
    """
    获取当前活动窗口句柄
    
    Returns:
        hwnd: 当前活动窗口句柄
    """
    try:
        return user32.GetForegroundWindow()
    except Exception as e:
        print(f"❌ [错误] 获取当前活动窗口失败: {e}")
        return None

def find_window(title):
    """
    根据窗口标题查找特定窗口句柄
    
    Args:
        title: 窗口标题
        
    Returns:
        hwnd: 窗口句柄，如果未找到则返回None
    """
    try:
        return user32.FindWindowW(None, title)
    except Exception as e:
        print(f"❌ [错误] 查找窗口失败: {e}")
        return None

def get_window_title(hwnd):
    """
    获取窗口标题
    
    Args:
        hwnd: 窗口句柄
        
    Returns:
        str: 窗口标题
    """
    try:
        # 先获取窗口标题的长度
        length = user32.GetWindowTextLengthW(hwnd)
        if length == 0:
            return ""
        
        # 创建缓冲区并获取窗口标题
        buffer = ctypes.create_unicode_buffer(length + 1)
        user32.GetWindowTextW(hwnd, buffer, length + 1)
        return buffer.value
    except Exception as e:
        print(f"❌ [错误] 获取窗口标题失败: {e}")
        return ""

def get_window_class(hwnd):
    """
    获取窗口类名
    
    Args:
        hwnd: 窗口句柄
        
    Returns:
        str: 窗口类名
    """
    try:
        # 创建缓冲区并获取窗口类名
        buffer = ctypes.create_unicode_buffer(256)
        user32.GetClassNameW(hwnd, buffer, 256)
        return buffer.value
    except Exception as e:
        print(f"❌ [错误] 获取窗口类名失败: {e}")
        return ""

def get_all_windows():
    """
    获取当前所有打开的可见窗口，返回窗口句柄和标题的列表
    
    Returns:
        list: 包含元组(hwnd, window_title)的列表
    """
    windows = []
    
    def enum_windows_proc(hwnd, lParam):
        if user32.IsWindowVisible(hwnd):
            window_title = get_window_title(hwnd)
            if window_title:
                windows.append((hwnd, window_title))
        return True
    
    # 定义回调函数类型
    enum_windows_proc_type = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
    # 调用EnumWindows获取所有窗口
    user32.EnumWindows(enum_windows_proc_type(enum_windows_proc), 0)
    return windows

def check_window_style(hwnd=None):
    """
    检测指定窗口样式和尺寸，如果没有指定窗口句柄，则使用当前活动窗口
    
    Args:
        hwnd: 窗口句柄，默认为None（当前活动窗口）
        
    Returns:
        dict: 检测结果，包含以下字段：
            - is_selected_window: 是否为选中的窗口
            - window_title: 窗口标题
            - window_class: 窗口类名
            - is_fullscreen_borderless: 是否为全屏无边框窗口
            - has_no_border: 是否无窗口边框样式
            - size_match: 是否尺寸匹配
            - window_width: 窗口宽度
            - window_height: 窗口高度
            - screen_width: 显示器宽度
            - screen_height: 显示器高度
    """
    try:
        # 如果没有指定窗口句柄，使用当前活动窗口
        if hwnd is None:
            hwnd = get_foreground_window()
        
        if hwnd is None:
            return {
                "is_selected_window": False,
                "window_title": "",
                "window_class": "",
                "is_fullscreen_borderless": False,
                "has_no_border": False,
                "size_match": False,
                "window_width": 0,
                "window_height": 0,
                "screen_width": 0,
                "screen_height": 0
            }
        
        # 获取窗口标题和类名
        window_title = get_window_title(hwnd)
        window_class = get_window_class(hwnd)
        
        # 获取显示器分辨率
        screen_width, screen_height = get_monitor_info(hwnd)
        
        # 获取窗口边界矩形
        window_rect = RECT()
        if not user32.GetWindowRect(hwnd, ctypes.byref(window_rect)):
            return {
                "is_selected_window": False,
                "window_title": window_title,
                "window_class": window_class,
                "is_fullscreen_borderless": False,
                "has_no_border": False,
                "size_match": False,
                "window_width": 0,
                "window_height": 0,
                "screen_width": screen_width,
                "screen_height": screen_height
            }
        
        # 计算窗口尺寸
        window_width = window_rect.right - window_rect.left
        window_height = window_rect.bottom - window_rect.top
        
        # 判断窗口样式
        window_style = user32.GetWindowLongW(hwnd, GWL_STYLE)
        has_no_border = (window_style & (WS_CAPTION | WS_THICKFRAME)) == 0
        
        # 判断尺寸匹配
        TOLERANCE = 2
        size_match = (abs(window_width - screen_width) <= TOLERANCE) and \
                     (abs(window_height - screen_height) <= TOLERANCE)
        
        # 判断是否为全屏无边框窗口
        is_fullscreen_borderless = size_match and has_no_border
        
        return {
            "is_selected_window": True,
            "window_title": window_title,
            "window_class": window_class,
            "is_fullscreen_borderless": is_fullscreen_borderless,
            "has_no_border": has_no_border,
            "size_match": size_match,
            "window_width": window_width,
            "window_height": window_height,
            "screen_width": screen_width,
            "screen_height": screen_height
        }
    except Exception as e:
        print(f"❌ [错误] 检测窗口样式失败: {e}")
        return {
            "is_selected_window": False,
            "window_title": "",
            "window_class": "",
            "is_fullscreen_borderless": False,
            "has_no_border": False,
            "size_match": False,
            "window_width": 0,
            "window_height": 0,
            "screen_width": 0,
            "screen_height": 0
        }

def test_monster_party_detection():
    """
    测试猛兽派对窗口检测功能
    """
    global is_monster_party_active
    
    print("=== 测试猛兽派对窗口检测功能 ===")
    
    # 检测当前窗口
    result = check_window_style()
    
    # 模拟猛兽派对窗口检测（实际应该根据窗口标题或其他特征判断）
    # 这里简单地假设全屏无边框窗口就是猛兽派对窗口
    is_monster_party = result['is_fullscreen_borderless']
    result['is_monster_party'] = is_monster_party
    
    # 更新全局变量
    is_monster_party_active = is_monster_party
    
    print(f"\n📋 检测结果:")
    print(f"🎮 是否为猛兽派对窗口: {'✅' if is_monster_party else '❌'}")
    print(f"🪟 窗口标题: {result['window_title']}")
    print(f"🏷️  窗口类名: {result['window_class']}")
    print(f"📏 窗口尺寸: {result['window_width']}x{result['window_height']}")
    print(f"🖥️  显示器分辨率: {result['screen_width']}x{result['screen_height']}")
    print(f"🔲 是否无窗口边框样式: {'✅' if result['has_no_border'] else '❌'}")
    print(f"📐 尺寸是否匹配: {'✅' if result['size_match'] else '❌'}")
    print(f"🎯 是否为全屏无边框窗口: {'✅' if result['is_fullscreen_borderless'] else '❌'}")
    
    # 如果是猛兽派对窗口，输出更详细的信息
    if is_monster_party:
        print(f"\n🎉 当前窗口是猛兽派对游戏窗口！")
        if result['is_fullscreen_borderless']:
            print("✨ 窗口为全屏无边框模式，符合要求！")
        else:
            if result['has_no_border']:
                print("⚠️  窗口无边框，但尺寸不匹配")
            elif result['size_match']:
                print("⚠️  窗口尺寸匹配，但有边框")
            else:
                print("❌ 窗口既不是无边框也不是尺寸匹配")
    else:
        print(f"\n⏭️ 当前窗口不是猛兽派对游戏窗口")
    
    return result

def auto_check_monster_party():
    """
    返回当前是否为猛兽派对窗口
    
    Returns:
        bool: 当前是否为猛兽派对窗口
    """
    global is_monster_party_active
    
    # 不再执行自动检测，只返回当前状态
    # 检测逻辑将只在软件启动和调试窗口点击时执行
    return is_monster_party_active

# 当前按下的修饰键状态
current_modifiers = set()

# 修饰键映射
MODIFIER_KEYS = {
    keyboard.Key.ctrl_l: 'ctrl',
    keyboard.Key.ctrl_r: 'ctrl',
    keyboard.Key.alt_l: 'alt',
    keyboard.Key.alt_r: 'alt',
    keyboard.Key.alt_gr: 'alt',
    keyboard.Key.shift_l: 'shift',
    keyboard.Key.shift_r: 'shift',
}

# 特殊键名称映射（用于显示和解析）
SPECIAL_KEY_NAMES = {
    keyboard.Key.f1: "F1", keyboard.Key.f2: "F2", keyboard.Key.f3: "F3",
    keyboard.Key.f4: "F4", keyboard.Key.f5: "F5", keyboard.Key.f6: "F6",
    keyboard.Key.f7: "F7", keyboard.Key.f8: "F8", keyboard.Key.f9: "F9",
    keyboard.Key.f10: "F10", keyboard.Key.f11: "F11", keyboard.Key.f12: "F12",
    keyboard.Key.space: "Space", keyboard.Key.enter: "Enter",
    keyboard.Key.tab: "Tab", keyboard.Key.backspace: "Backspace",
    keyboard.Key.delete: "Delete", keyboard.Key.insert: "Insert",
    keyboard.Key.home: "Home", keyboard.Key.end: "End",
    keyboard.Key.page_up: "PageUp", keyboard.Key.page_down: "PageDown",
    keyboard.Key.up: "↑", keyboard.Key.down: "↓",
    keyboard.Key.left: "←", keyboard.Key.right: "→",
    keyboard.Key.esc: "Esc", keyboard.Key.pause: "Pause",
    keyboard.Key.print_screen: "PrintScreen",
    keyboard.Key.scroll_lock: "ScrollLock", keyboard.Key.caps_lock: "CapsLock",
    keyboard.Key.num_lock: "NumLock",
    # 鼠标侧键支持
    mouse.Button.x1: "Mouse4",  # 鼠标前进键
    mouse.Button.x2: "Mouse5",  # 鼠标后退键
}

# 反向映射：名称 -> 按键对象
NAME_TO_KEY = {v: k for k, v in SPECIAL_KEY_NAMES.items()}

def parse_hotkey_string(hotkey_str):
    """
    解析热键字符串，返回 (修饰键集合, 主按键对象, 主按键名称)
    例如: "Ctrl+Shift+A" -> ({'ctrl', 'shift'}, KeyCode(char='a'), 'A')
    支持鼠标侧键: "Mouse4" -> (set(), mouse.Button.x1, "Mouse4")
    """
    parts = [p.strip() for p in hotkey_str.split('+')]
    modifiers = set()
    main_key = None
    main_key_name = ""

    for part in parts:
        part_lower = part.lower()
        if part_lower == 'ctrl':
            modifiers.add('ctrl')
        elif part_lower == 'alt':
            modifiers.add('alt')
        elif part_lower == 'shift':
            modifiers.add('shift')
        else:
            # 这是主按键
            main_key_name = part
            # 检查是否是特殊键
            if part in NAME_TO_KEY:
                main_key = NAME_TO_KEY[part]
            elif len(part) == 1:
                # 单个字符键
                main_key = keyboard.KeyCode.from_char(part.lower())
            else:
                # 尝试作为特殊键名称
                try:
                    main_key = getattr(keyboard.Key, part.lower())
                except AttributeError:
                    # 检查是否是鼠标侧键
                    if part == "Mouse4":
                        main_key = mouse.Button.x1
                    elif part == "Mouse5":
                        main_key = mouse.Button.x2
                    else:
                        main_key = keyboard.KeyCode.from_char(part[0].lower())

    return modifiers, main_key, main_key_name

def format_hotkey_display(modifiers, main_key_name):
    """格式化热键显示字符串"""
    parts = []
    if 'ctrl' in modifiers:
        parts.append('Ctrl')
    if 'alt' in modifiers:
        parts.append('Alt')
    if 'shift' in modifiers:
        parts.append('Shift')
    parts.append(main_key_name)
    return '+'.join(parts)

def key_to_name(key):
    """将按键对象转换为显示名称"""
    # 检查是否为鼠标按键
    if key in SPECIAL_KEY_NAMES:
        return SPECIAL_KEY_NAMES[key]
    # 处理键盘按键
    elif hasattr(key, 'vk') and key.vk is not None:
        # 通过虚拟键码识别按键（解决Ctrl+字母时char为控制字符的问题）
        vk = key.vk
        # 字母键 A-Z (vk: 65-90)
        if 65 <= vk <= 90:
            return chr(vk)  # 返回大写字母
        # 数字键 0-9 (vk: 48-57)
        elif 48 <= vk <= 57:
            return chr(vk)
        # 数字小键盘 0-9 (vk: 96-105)
        elif 96 <= vk <= 105:
            return f"Num{vk - 96}"
        # 其他有vk但没有可打印char的键
        elif hasattr(key, 'char') and key.char and key.char.isprintable():
            return key.char.upper()
        else:
            return f"Key{vk}"
    elif hasattr(key, 'char') and key.char and key.char.isprintable():
        return key.char.upper()
    return str(key)

a = 0
region1 = 0
region2 = 0
result_val_is = None
scr = None
# =========================
# 模板加载
# =========================
def scale_template(template, scale_x, scale_y):
    """根据缩放比例缩放模板图片"""
    if scale_x == 1.0 and scale_y == 1.0:
        return template
    h, w = template.shape[:2]
    new_w = max(1, int(w * scale_x))
    new_h = max(1, int(h * scale_y))
    return cv2.resize(template, (new_w, new_h), interpolation=cv2.INTER_LINEAR)

def reload_templates_if_scale_changed():
    """如果缩放比例变化，重新加载所有模板"""
    global templates, star_template, f1, f2, shangyule, jiashi
    global _cached_scale_x, _cached_scale_y

    if _cached_scale_x != SCALE_X or _cached_scale_y != SCALE_Y:
        # 缩放比例变化，需要重新加载所有模板
        _cached_scale_x = SCALE_X
        _cached_scale_y = SCALE_Y
        print(f"🔄 [模板] 分辨率变化，重新加载模板 (缩放: X={SCALE_X:.2f}, Y={SCALE_Y:.2f})")

        # 重新加载所有模板（强制重新加载）
        try:
            # 使用统一缩放比例避免模板变形
            scale = SCALE_UNIFORM

            # 数字模板
            templates = []
            for i in range(10):
                template_path = os.path.join(template_folder_path, f"{i}_grayscale.png")
                img = Image.open(template_path)
                template = np.array(img)
                template = scale_template(template, scale, scale)
                templates.append(template)

            # 星星模板
            star_template_path = os.path.join(template_folder_path, "star_grayscale.png")
            img = Image.open(star_template_path)
            star_template = scale_template(np.array(img), scale, scale)

            # F1模板
            f1_path = os.path.join(template_folder_path, "F1_grayscale.png")
            img = Image.open(f1_path)
            f1 = scale_template(np.array(img), scale, scale)

            # F2模板
            f2_path = os.path.join(template_folder_path, "F2_grayscale.png")
            img = Image.open(f2_path)
            f2 = scale_template(np.array(img), scale, scale)

            # 上鱼模板
            shangyule_path = os.path.join(template_folder_path, "shangyu_grayscale.png")
            img = Image.open(shangyule_path)
            shangyule = scale_template(np.array(img), scale, scale)

            # 加时模板
            jiashi_path = os.path.join(template_folder_path, "chang_grayscale.png")
            img = Image.open(jiashi_path)
            jiashi = scale_template(np.array(img), scale, scale)

            # 放生稀有模板
            release_xiyou_path = os.path.join(template_folder_path, "xiyou.png")
            img = Image.open(release_xiyou_path)
            # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
            release_xiyou = scale_template(cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR), scale, scale)

            release_feifan_path = os.path.join(template_folder_path, "feifan.png")
            img = Image.open(release_feifan_path)
            # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
            release_feifan = scale_template(cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR), scale, scale)

            release_shishi_path = os.path.join(template_folder_path, "shishi.png")
            img = Image.open(release_shishi_path)
            # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
            release_shishi = scale_template(cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR), scale, scale)

            release_chuanshuo_path = os.path.join(template_folder_path, "chuanshuo.png")
            img = Image.open(release_chuanshuo_path)
            # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
            release_chuanshuo = scale_template(cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR), scale, scale)


            # 放生鱼桶标签模板
            release_bucket_label_path = os.path.join(template_folder_path, "bucket_label.png")
            img = Image.open(release_bucket_label_path)
            release_bucket_label = scale_template(np.array(img), scale, scale)

            print(f"✅ [模板] 所有模板重新加载完成，共 {len(templates)} 个数字模板 (统一缩放: {scale:.2f})")
        except Exception as e:
            print(f"❌ [错误] 重新加载模板失败: {e}")

# 加载模板（0.png到9.png）
def load_templates():
    global templates, template_folder_path
    if templates is None:
        templates = []
        scale = SCALE_UNIFORM  # 使用统一缩放比例
        for i in range(10):
            template_path = os.path.join(template_folder_path, f"{i}_grayscale.png")
            img = Image.open(template_path)
            template = np.array(img)
            # 根据当前缩放比例缩放模板
            template = scale_template(template, scale, scale)
            templates.append(template)
    return templates

# 加载模板
def load_star_template():
    global star_template, template_folder_path
    if star_template is None:
        star_template_path = os.path.join(template_folder_path, "star_grayscale.png")
        img = Image.open(star_template_path)
        template = np.array(img)
        scale = SCALE_UNIFORM  # 使用统一缩放比例
        star_template = scale_template(template, scale, scale)
    return star_template

def load_f1():
    global f1
    if f1 is None:
        f1_path = os.path.join(template_folder_path, "F1_grayscale.png")
        img = Image.open(f1_path)
        template = np.array(img)
        scale = SCALE_UNIFORM
        f1 = scale_template(template, scale, scale)
    return f1

def load_f2():
    global f2
    if f2 is None:
        f2_path = os.path.join(template_folder_path, "F2_grayscale.png")
        img = Image.open(f2_path)
        template = np.array(img)
        scale = SCALE_UNIFORM
        f2 = scale_template(template, scale, scale)
    return f2
def load_shangyule():
    global shangyule
    shangyule_path = os.path.join(template_folder_path, "shangyu_grayscale.png")
    img = Image.open(shangyule_path)
    template = np.array(img)
    scale = SCALE_UNIFORM
    shangyule = scale_template(template, scale, scale)
    return shangyule
def load_jiashi():
    global jiashi
    jiashi_path = os.path.join(template_folder_path, "chang_grayscale.png")
    img = Image.open(jiashi_path)
    template = np.array(img)
    scale = SCALE_UNIFORM
    jiashi = scale_template(template, scale, scale)
    return jiashi

def load_release_xiyou():
    global release_xiyou
    if release_xiyou is None:
        release_xiyou_path = os.path.join(template_folder_path, "xiyou.png")
        img = Image.open(release_xiyou_path)
        template = np.array(img)
        # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
        template = cv2.cvtColor(template, cv2.COLOR_RGB2BGR)
        scale = SCALE_UNIFORM
        release_xiyou = scale_template(template, scale, scale)
    return release_xiyou

def load_release_feifan():
    global release_feifan
    if release_feifan is None:
        release_feifan_path = os.path.join(template_folder_path, "feifan.png")
        img = Image.open(release_feifan_path)
        template = np.array(img)
        # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
        template = cv2.cvtColor(template, cv2.COLOR_RGB2BGR)
        scale = SCALE_UNIFORM
        release_feifan = scale_template(template, scale, scale)
    return release_feifan

def load_release_shishi():
    global release_shishi
    if release_shishi is None:
        release_shishi_path = os.path.join(template_folder_path, "shishi.png")
        img = Image.open(release_shishi_path)
        template = np.array(img)
        # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
        template = cv2.cvtColor(template, cv2.COLOR_RGB2BGR)
        scale = SCALE_UNIFORM
        release_shishi = scale_template(template, scale, scale)
    return release_shishi

def load_release_chuanshuo():
    global release_chuanshuo
    if release_chuanshuo is None:
        release_chuanshuo_path = os.path.join(template_folder_path, "chuanshuo.png")
        img = Image.open(release_chuanshuo_path)
        template = np.array(img)
        # PIL 返回 RGB 格式，需要转换为 BGR 格式（OpenCV 默认格式）
        template = cv2.cvtColor(template, cv2.COLOR_RGB2BGR)
        scale = SCALE_UNIFORM
        release_chuanshuo = scale_template(template, scale, scale)
    return release_chuanshuo

# =========================
# 鼠标操作（使用 win32api 实现）
# =========================
mouse_lock = threading.Lock()
mouse_is_down = False
def pressandreleasemousebutton():
    # 根据开关状态决定是否应用随机延迟
    if random_delay_enabled:
        # 根据设置的百分比添加随机延迟
        max_factor = 1.0 + random_delay / 100.0
        random_factor_down = random.uniform(1.0, max_factor)
        random_factor_up = random.uniform(1.0, max_factor)
        
        user32.mouse_event(0x02, 0, 0, 0, 0)
        time.sleep(leftclickdown * random_factor_down)
        user32.mouse_event(0x04, 0, 0, 0, 0)
        time.sleep(leftclickup * random_factor_up)
    else:
        # 不使用随机延迟
        user32.mouse_event(0x02, 0, 0, 0, 0)
        time.sleep(leftclickdown)
        user32.mouse_event(0x04, 0, 0, 0, 0)
        time.sleep(leftclickup)

def ensure_mouse_down():
    global mouse_is_down
    with mouse_lock:
        if not mouse_is_down:
            user32.mouse_event(0x02, 0, 0, 0, 0)  # 左键按下
            mouse_is_down = True

def ensure_mouse_up():
    global mouse_is_down
    with mouse_lock:
        if mouse_is_down:
            user32.mouse_event(0x04, 0, 0, 0, 0)  # 左键释放
            mouse_is_down = False
# =========================
# 比较数字大小
# =========================
def compare_results():
    global current_result, previous_result
    if current_result is None or previous_result is None:
        return 0  # 无法比较，返回 0 作为标识
    if current_result > previous_result:
        return 1  # 当前结果较大
    elif current_result < previous_result:
        return -1  # 上次结果较大
    else:
        return 0  # 当前结果与上次相同
# =========================
# 截取屏幕区域
# =========================
# 基准裁切尺寸（2K分辨率下的像素值）
BAIT_CROP_HEIGHT_BASE = 22
BAIT_CROP_WIDTH1_BASE = 15  # 单个数字宽度

# 获取电脑屏幕最大分辨率
def get_max_screen_resolution():
    """获取电脑屏幕的最大分辨率"""
    try:
        # 定义结构体
        class DEVMODEW(ctypes.Structure):
            _fields_ = [
                ("dmDeviceName", ctypes.c_wchar * 32),
                ("dmSpecVersion", ctypes.wintypes.WORD),
                ("dmDriverVersion", ctypes.wintypes.WORD),
                ("dmSize", ctypes.wintypes.WORD),
                ("dmDriverExtra", ctypes.wintypes.WORD),
                ("dmFields", ctypes.wintypes.DWORD),
                ("dmPositionX", ctypes.wintypes.LONG),
                ("dmPositionY", ctypes.wintypes.LONG),
                ("dmDisplayOrientation", ctypes.wintypes.DWORD),
                ("dmDisplayFixedOutput", ctypes.wintypes.DWORD),
                ("dmColor", ctypes.wintypes.SHORT),
                ("dmDuplex", ctypes.wintypes.SHORT),
                ("dmYResolution", ctypes.wintypes.SHORT),
                ("dmTTOption", ctypes.wintypes.SHORT),
                ("dmCollate", ctypes.wintypes.SHORT),
                ("dmFormName", ctypes.c_wchar * 32),
                ("dmLogPixels", ctypes.wintypes.WORD),
                ("dmBitsPerPel", ctypes.wintypes.DWORD),
                ("dmPelsWidth", ctypes.wintypes.DWORD),
                ("dmPelsHeight", ctypes.wintypes.DWORD),
                ("dmDisplayFlags", ctypes.wintypes.DWORD),
                ("dmDisplayFrequency", ctypes.wintypes.DWORD),
                ("dmICMMethod", ctypes.wintypes.DWORD),
                ("dmICMIntent", ctypes.wintypes.DWORD),
                ("dmMediaType", ctypes.wintypes.DWORD),
                ("dmDitherType", ctypes.wintypes.DWORD),
                ("dmReserved1", ctypes.wintypes.DWORD),
                ("dmReserved2", ctypes.wintypes.DWORD),
                ("dmPanningWidth", ctypes.wintypes.DWORD),
                ("dmPanningHeight", ctypes.wintypes.DWORD)
            ]
        
        user32 = ctypes.windll.user32
        devmode = DEVMODEW()
        devmode.dmSize = ctypes.sizeof(DEVMODEW)
        
        # 尝试获取显示器的最大分辨率
        max_width, max_height = 0, 0
        i = 0
        while user32.EnumDisplaySettingsW(None, i, ctypes.byref(devmode)):
            if devmode.dmPelsWidth > max_width:
                max_width = devmode.dmPelsWidth
                max_height = devmode.dmPelsHeight
            i += 1
        
        # 如果没有获取到，回退到当前分辨率
        if max_width == 0 or max_height == 0:
            max_width = user32.GetSystemMetrics(0)
            max_height = user32.GetSystemMetrics(1)
        
        return max_width, max_height
    except:
        # 出错时回退到当前分辨率
        try:
            user32 = ctypes.windll.user32
            current_width = user32.GetSystemMetrics(0)
            current_height = user32.GetSystemMetrics(1)
            return current_width, current_height
        except:
            return None, None

def bait_math_val(scr):
    global  region1, region2, result_val_is
    # 记录日志：开始鱼饵识别
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "bait_recognition_start",
            "message": "开始识别鱼饵数量"
        }
        add_debug_info(debug_info)
    
    # 鱼饵数量显示在屏幕右下角，使用锚定方式计算坐标
    x1, y1, x2, y2 = BAIT_REGION_BASE
    base_w = x2 - x1
    base_h = y2 - y1
    
    # 使用现有的scale_corner_anchored函数计算坐标，确保与其他UI元素使用相同的缩放逻辑
    actual_x1, actual_y1, actual_w, actual_h = scale_corner_anchored(x1, y1, base_w, base_h, anchor="bottom_right")
    actual_x2 = actual_x1 + actual_w
    actual_y2 = actual_y1 + actual_h

    region = (actual_x1, actual_y1, actual_x2, actual_y2)
    
    # 记录日志：识别区域
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "bait_recognition_region",
            "message": "鱼饵识别区域",
            "region": {
                "x1": actual_x1,
                "y1": actual_y1,
                "x2": actual_x2,
                "y2": actual_y2
            }
        }
        add_debug_info(debug_info)
    
    math_frame = scr.grab(region)
    # 将 mss 截取的图像转换为 NumPy 数组 (height, width, 4)，即 RGBA 图像
    if math_frame is None:
        result_val_is = None
        # 记录日志：识别失败
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "bait_recognition_failed",
                "message": "无法获取鱼饵区域图像"
            }
            add_debug_info(debug_info)
        return None
    else:
        img = np.array(math_frame)  # screenshot 是 ScreenShot 类型，转换为 NumPy 数组
        gray_img = cv2.cvtColor(img, cv2.COLOR_RGBA2GRAY)

        # 根据统一缩放比例动态计算裁切尺寸
        scale = SCALE_UNIFORM
        crop_h = max(1, int(BAIT_CROP_HEIGHT_BASE * scale))
        crop_w = max(1, int(BAIT_CROP_WIDTH1_BASE * scale))

        # 确保不超出图像边界
        img_h, img_w = gray_img.shape[:2]
        crop_h = min(crop_h, img_h)
        crop_w = min(crop_w, img_w // 2)  # 确保单个数字宽度不超过一半

        # 初始化匹配结果
        best_match1 = None
        best_match2 = None
        best_match3 = None

        # 截取并处理区域1（第一个数字）
        if crop_w <= img_w:
            region1 = gray_img[0:crop_h, 0:crop_w]
            best_match1 = match_digit_template(region1)
        
        # 截取并处理区域2（第二个数字）
        if crop_w*2 <= img_w:
            region2 = gray_img[0:crop_h, crop_w:crop_w*2]
            best_match2 = match_digit_template(region2)
        
        # 单个数字居中区域 - 动态计算起始位置，适应各种分辨率
        mid_start = max(0, (img_w - crop_w) // 2)
        mid_end = min(mid_start + crop_w, img_w)
        region3 = gray_img[0:crop_h, mid_start:mid_end]
        best_match3 = match_digit_template(region3)
        if best_match1 and best_match2:
            # 从best_match中提取数字索引（i），并拼接成整数
            best_match1_val = best_match1[0]  # 提取区域1的数字索引
            best_match2_val = best_match2[0]  # 提取区域2的数字索引
            # 拼接两个匹配的数字，转换为整数
            result_val_is = int(f"{best_match1_val}{best_match2_val}")
        elif best_match3:
            result_val_is = int(f'{best_match3[0]}')
        else:
            result_val_is = None
        
        # 记录日志：识别结果
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "bait_recognition_result",
                "message": "鱼饵识别完成",
                "result": result_val_is,
                "parsed_info": {
                    "鱼饵数量": result_val_is if result_val_is is not None else "未识别"
                }
            }
            add_debug_info(debug_info)
        return result_val_is

def match_digit_template(image):
    global templates
    # 确保模板已加载
    if templates is None or len(templates) == 0:
        load_templates()
    if templates is None or len(templates) == 0:
        return None
    best_match = None  # 最佳匹配信息
    best_val = 0  # 存储最佳匹配度
    for i, template in enumerate(templates):
        res = cv2.matchTemplate(image, template, cv2.TM_CCOEFF_NORMED)
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(res)
        if max_val> 0.8 and max_val > best_val:  # 找到最佳匹配
            best_val = max_val
            best_match = (i, max_loc)  # 记录最佳匹配的数字和位置
    return best_match

def capture_region(x, y, w, h, scr):
    # 获取主显示器信息，确保只在主显示器上截图
    monitor = scr.monitors[1]  # 1 表示主显示器
    
    # 计算实际截图区域，确保在主显示器范围内
    actual_x = x
    actual_y = y
    actual_w = w
    actual_h = h
    
    # 确保区域在主显示器范围内
    actual_x = max(monitor['left'], actual_x)
    actual_y = max(monitor['top'], actual_y)
    actual_x2 = min(monitor['left'] + monitor['width'], actual_x + actual_w)
    actual_y2 = min(monitor['top'] + monitor['height'], actual_y + actual_h)
    
    # 重新计算宽度和高度，确保有效
    actual_w = max(1, actual_x2 - actual_x)
    actual_h = max(1, actual_y2 - actual_y)
    
    region = (actual_x, actual_y, actual_x2, actual_y2)
    frame = scr.grab(region)
    if frame is None:
        return None
    img = np.array(frame)  # screenshot 是 ScreenShot 类型，转换为 NumPy 数组
    gray_img = cv2.cvtColor(img, cv2.COLOR_RGBA2GRAY)
    return gray_img

#识别钓上鱼
def fished(scr):
    global region3_coords, star_template
    # 确保模板已加载
    if star_template is None:
        load_star_template()
    # 获取区域坐标并捕获灰度图
    region_gray = capture_region(*region3_coords, scr)  # 直接传递解包后的参数和scr
    if region_gray is None:
        return None
    # 执行模板匹配并检查最大匹配度是否大于 0.8
    return cv2.minMaxLoc(cv2.matchTemplate(region_gray, star_template, cv2.TM_CCOEFF_NORMED))[1] > 0.8
def f1_mached(scr):
    global region4_coords, f1
    # 确保模板已加载
    if f1 is None:
        load_f1()
    region_gray = capture_region(*region4_coords, scr)
    if region_gray is None:
        return None
    return cv2.minMaxLoc(cv2.matchTemplate(region_gray, f1, cv2.TM_CCOEFF_NORMED))[1] > 0.8
def f2_mached(scr):
    global region5_coords, f2
    # 确保模板已加载
    if f2 is None:
        load_f2()
    region_gray = capture_region(*region5_coords, scr)
    if region_gray is None:
        return None
    return cv2.minMaxLoc(cv2.matchTemplate(region_gray, f2, cv2.TM_CCOEFF_NORMED))[1] > 0.8
def shangyu_mached(scr):
    global region6_coords, shangyule
    # 确保模板已加载
    if shangyule is None:
        load_shangyule()
    region_gray = capture_region(*region6_coords, scr)
    if region_gray is None:
        return None
    return cv2.minMaxLoc(cv2.matchTemplate(region_gray, shangyule, cv2.TM_CCOEFF_NORMED))[1] > 0.8
def fangzhu_jiashi(scr):
    global jiashi
    # 记录日志：开始加时识别
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "jiashi_recognition_start",
            "message": "开始识别加时界面"
        }
        add_debug_info(debug_info)
    
    # 确保模板已加载
    if jiashi is None:
        load_jiashi()
    x, y, w, h = JIASHI_REGION_BASE
    # 加时界面在屏幕中央，使用中心锚定方式
    scale = SCALE_UNIFORM
    center_offset_x = x - BASE_WIDTH / 2
    center_offset_y = y - BASE_HEIGHT / 2
    actual_x = int(TARGET_WIDTH / 2 + center_offset_x * scale)
    actual_y = int(TARGET_HEIGHT / 2 + center_offset_y * scale)
    actual_w = int(w * scale)
    actual_h = int(h * scale)
    
    # 记录日志：识别区域
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "jiashi_recognition_region",
            "message": "加时识别区域",
            "region": {
                "x1": actual_x,
                "y1": actual_y,
                "x2": actual_x + actual_w,
                "y2": actual_y + actual_h
            }
        }
        add_debug_info(debug_info)
    
    region_gray = capture_region(actual_x, actual_y, actual_w, actual_h, scr)
    if region_gray is None:
        # 记录日志：识别失败
        if debug_mode:
            debug_info = {
                "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
                "action": "jiashi_recognition_failed",
                "message": "无法获取加时区域图像"
            }
            add_debug_info(debug_info)
        return None
    
    result = cv2.minMaxLoc(cv2.matchTemplate(region_gray, jiashi, cv2.TM_CCOEFF_NORMED))[1] > 0.8
    
    # 记录日志：识别结果
    if debug_mode:
        debug_info = {
            "timestamp": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "action": "jiashi_recognition_result",
            "message": "加时识别完成",
            "result": "是" if result else "否",
            "parsed_info": {
                "加时界面": "已识别" if result else "未识别"
            }
        }
        add_debug_info(debug_info)
    
    return result
# =========================
# 程序主循环与热键监听
# =========================
def toggle_run():
    global a, previous_result, scr
    if run_event.is_set():
        run_event.clear()  # 暂停
        a = 0
        previous_result = None
        ensure_mouse_up()  # 确保鼠标没有按下
        end_current_session()  # 结束钓鱼会话
        print("⏸️  [状态] 脚本已暂停")
    else:
        start_new_session()  # 开始新的钓鱼会话
        if previous_result is None:
            temp_scr = None
            try:
                temp_scr = mss.mss()
                bait_result = bait_math_val(temp_scr)
                if bait_result is not None:
                    previous_result = result_val_is
                    run_event.set()  # 恢复运行
                    print("▶️  [状态] 脚本开始运行")
                else:
                    time.sleep(0.1)
                    print("⚠️  [警告] 未识别到鱼饵，请确保游戏界面正确")
            except Exception as e:
                print(f"❌ [错误] 初始化失败: {e}")
            finally:
                if temp_scr is not None:
                    try:
                        temp_scr.close()
                    except:
                        pass
                scr = None
        else:
            run_event.set()
            print("▶️  [状态] 脚本继续运行")

def on_press(key):
    global current_modifiers
    time.sleep(0.02)

    # 检查是否是修饰键
    if key in MODIFIER_KEYS:
        current_modifiers.add(MODIFIER_KEYS[key])
        return

    # 检查是否匹配热键
    check_hotkey_match(key)
    check_release_hotkey_match(key)

def on_release(key):
    global current_modifiers
    # 释放修饰键时移除
    if key in MODIFIER_KEYS:
        current_modifiers.discard(MODIFIER_KEYS[key])

def on_mouse_press(x, y, button, pressed):
    """鼠标按下事件处理"""
    if not pressed:
        return
    
    # 检查是否匹配热键
    check_hotkey_match(button)

def check_hotkey_match(key):
    """检查按键是否匹配热键"""
    # 比较主按键
    main_key_match = False
    
    # 直接比较按键对象
    if key == hotkey_main_key:
        main_key_match = True
    # 字符键比较（忽略大小写）
    elif hasattr(key, 'char') and hasattr(hotkey_main_key, 'char'):
        if key.char and hotkey_main_key.char:
            main_key_match = (key.char.lower() == hotkey_main_key.char.lower())
    # 鼠标按键比较
    elif isinstance(key, mouse.Button) and isinstance(hotkey_main_key, mouse.Button):
        main_key_match = (key == hotkey_main_key)

    if main_key_match:
        # 检查修饰键是否匹配
        if current_modifiers == hotkey_modifiers:
            toggle_run()  # 暂停或恢复程序
            return

def check_release_hotkey_match(key):
    """检查按键是否匹配放生热键"""
    # 比较主按键
    main_key_match = False
    
    # 直接比较按键对象
    if key == release_hotkey_main_key:
        main_key_match = True
    # 字符键比较（忽略大小写）
    elif hasattr(key, 'char') and hasattr(release_hotkey_main_key, 'char'):
        if key.char and release_hotkey_main_key.char:
            main_key_match = (key.char.lower() == release_hotkey_main_key.char.lower())
    # 鼠标按键比较
    elif isinstance(key, mouse.Button) and isinstance(release_hotkey_main_key, mouse.Button):
        main_key_match = (key == release_hotkey_main_key)

    if main_key_match:
        # 检查修饰键是否匹配
        if current_modifiers == release_hotkey_modifiers:
            # 切换鱼桶识别线程的运行状态
            if fish_bucket_run_event.is_set():
                fish_bucket_run_event.clear()
                print("🐟 [鱼桶] 识别线程已停止")
            else:
                fish_bucket_run_event.set()
                print("🐟 [鱼桶] 识别线程已启动")
            return
            
def detect_and_classify_templates(target_image, templates_dict, threshold=0.8):
    """
    在目标图像中检测并区分多个颜色变体的模板。
    
    参数：
    - target_image: 目标图像（彩色 numpy 数组）
    - templates_dict: 字典，键为颜色标签（e.g., 'red'），值为模板图像（彩色 numpy 数组）
    - threshold: 相似度阈值 (0.0-1.0)
    
    返回：
    - results: 字典，键为颜色标签，值为 {'count': int, 'locations': [(x, y, w, h), ...]}
    """
    results = {color: {'count': 0, 'locations': []} for color in templates_dict}
    
    # 转换为 HSV 用于颜色区分
    target_hsv = cv2.cvtColor(target_image, cv2.COLOR_BGR2HSV)
    
    for color, template in templates_dict.items():
        # 模板也转换为 HSV
        template_hsv = cv2.cvtColor(template, cv2.COLOR_BGR2HSV)
        
        # 方法1: 灰度匹配位置（形状检测）
        target_gray = cv2.cvtColor(target_image, cv2.COLOR_BGR2GRAY)
        template_gray = cv2.cvtColor(template, cv2.COLOR_BGR2GRAY)
        result = cv2.matchTemplate(target_gray, template_gray, cv2.TM_CCOEFF_NORMED)
        
        # 获取潜在位置
        loc = np.where(result >= threshold)
        template_h, template_w = template_gray.shape[:2]
        
        # 方法2: 颜色验证（区分变体）
        for pt in zip(*loc[::-1]):
            x, y = pt
            
            # 提取目标区域的 HSV
            roi_hsv = target_hsv[y:y + template_h, x:x + template_w]
            
            # 计算颜色相似度（e.g., 平均色调差异）
            template_hue = np.mean(template_hsv[:, :, 0])  # 色调通道
            roi_hue = np.mean(roi_hsv[:, :, 0])
            hue_diff = abs(template_hue - roi_hue)
            
            # 如果色调差异小（<30），认为是匹配的颜色变体
            if hue_diff < 15:  # 阈值可调
                # 去重：检查重叠
                overlap = any(abs(x - lx) < template_w // 2 and abs(y - ly) < template_h // 2 
                             for lx, ly, _, _ in results[color]['locations'])
                if not overlap:
                    results[color]['locations'].append((x, y, template_w, template_h))
        
        results[color]['count'] = len(results[color]['locations'])
    
    return results

def start_hotkey_listener():
    global listener, mouse_listener
    # 启动键盘监听器
    if listener is None or not listener.running:
        listener = keyboard.Listener(on_press=on_press, on_release=on_release)
        listener.daemon = True
        listener.start()
    
    # 启动鼠标监听器
    if 'mouse_listener' not in globals() or mouse_listener is None or not mouse_listener.running:
        mouse_listener = mouse.Listener(on_click=on_mouse_press)
        mouse_listener.daemon = True
        mouse_listener.start()
# =========================
# 主函数
# =========================
# 主函数：定时识别并比较数字
def handle_jiashi_thread():
    global run_event, begin_event, previous_result, result_val_is
    while not begin_event.is_set():
        if run_event.is_set():
            # 自动检测猛兽派对窗口
            auto_check_monster_party()
            
            try:
                # 为每个线程创建独立的mss对象
                scr = mss.mss()
                
                # 确保scr对象和_handles属性正确初始化
                if hasattr(scr, '_handles') and hasattr(scr._handles, 'srcdc') and scr._handles.srcdc is not None:
                    # 处理加时选择（使用锁保护读取jiashi_var）
                    with param_lock:
                        current_jiashi = jiashi_var

                    if current_jiashi == 0:
                        if fangzhu_jiashi(scr):
                            btn_x, btn_y = scale_point_center_anchored(*BTN_NO_JIASHI_BASE)
                            user32.SetCursorPos(btn_x, btn_y)
                            if random_delay_enabled:
                                # 根据设置的百分比添加随机延迟
                                max_factor = 1.0 + random_delay / 100.0
                                random_factor_short = random.uniform(1.0, max_factor)
                                random_factor_medium = random.uniform(1.0, max_factor)
                                time.sleep(0.05 * random_factor_short)
                                user32.mouse_event(0x02, 0, 0, 0, 0)
                                time.sleep(0.1 * random_factor_medium)
                                user32.mouse_event(0x04, 0, 0, 0, 0)
                                time.sleep(0.05 * random_factor_short)
                            else:
                                # 不使用随机延迟
                                time.sleep(0.05)
                                user32.mouse_event(0x02, 0, 0, 0, 0)
                                time.sleep(0.1)
                                user32.mouse_event(0x04, 0, 0, 0, 0)
                                time.sleep(0.05)
                            if bait_math_val(scr):
                                with param_lock:
                                    previous_result = result_val_is
                    elif current_jiashi == 1:
                        if fangzhu_jiashi(scr):
                            btn_x, btn_y = scale_point_center_anchored(*BTN_YES_JIASHI_BASE)
                            user32.SetCursorPos(btn_x, btn_y)
                            if random_delay_enabled:
                                # 根据设置的百分比添加随机延迟
                                max_factor = 1.0 + random_delay / 100.0
                                random_factor_short = random.uniform(1.0, max_factor)
                                random_factor_medium = random.uniform(1.0, max_factor)
                                time.sleep(0.05 * random_factor_short)
                                user32.mouse_event(0x02, 0, 0, 0, 0)
                                time.sleep(0.1 * random_factor_medium)
                                user32.mouse_event(0x04, 0, 0, 0, 0)
                                time.sleep(0.05 * random_factor_short)
                            else:
                                # 不使用随机延迟
                                time.sleep(0.05)
                                user32.mouse_event(0x02, 0, 0, 0, 0)
                                time.sleep(0.1)
                                user32.mouse_event(0x04, 0, 0, 0, 0)
                                time.sleep(0.05)
                            if bait_math_val(scr):
                                with param_lock:
                                    previous_result = result_val_is
                
                # 确保资源被正确释放
                scr.close()
            except Exception as e:
                print(f"❌ [错误] 加时线程异常: {e}")
                # 确保即使发生异常也能释放资源
                try:
                    if 'scr' in locals() and scr is not None:
                        scr.close()
                except:
                    pass
        time.sleep(0.05)

def handle_fish_bucket_thread():
    """鱼桶区域识别线程 - F4触发时执行一次识别并显示结果"""
    global fish_bucket_run_event, begin_event, release_xiyou
    last_f4_state = False
    
    # 定义颜色类型和对应的HSV范围（基于色相和饱和度）
    color_ranges = {
        '传说': {'hue_range': (15, 25), 'saturation_range': (110, 125), 'color': (128, 128, 128), 'label': '传说'},  # 灰白色
        '标准': {'hue_range': (55, 65), 'saturation_range': (20, 40), 'color': (0, 165, 255), 'label': '标准'},  # 金白色
        '稀有': {'hue_range': (65, 75), 'saturation_range': (80, 95), 'color': (255, 0, 0), 'label': '稀有'},   # 蓝白色
        '非凡': {'hue_range': (30, 40), 'saturation_range': (90, 100), 'color': (0, 255, 0), 'label': '非凡'},   # 绿白色
        '史诗': {'hue_range': (80, 95), 'saturation_range': (90, 100), 'color': (255, 0, 255), 'label': '史诗'},  # 紫白色
    }
    
    while not begin_event.is_set():
        current_f4_state = fish_bucket_run_event.is_set()
        
        # 检测 F4 按下的上升沿（从未按下变为按下）
        if current_f4_state and not last_f4_state:
            break_all_loops = False  # 设置跳出循环的标志
            try:
                scr = mss.mss()
                
                if hasattr(scr, '_handles') and hasattr(scr._handles, 'srcdc') and scr._handles.srcdc is not None:
                    
                    if release_xiyou is not None:
                        # FISH_BUCKET_REGION_BASE 格式是 (left, top, width, height)
                        # 使用统一缩放比例缩放坐标
                        scaled_x, scaled_y, scaled_w, scaled_h = scale_coords_uniform(*FISH_BUCKET_REGION_BASE)
                        
                        # 调试信息：打印坐标
                        print(f"🐟 [鱼桶] 原始区域: {FISH_BUCKET_REGION_BASE}")
                        print(f"🐟 [鱼桶] 缩放比例: {SCALE_UNIFORM:.2f}")
                        print(f"🐟 [鱼桶] 缩放后区域: ({scaled_x}, {scaled_y}, {scaled_w}, {scaled_h})")
                        print(f"🐟 [鱼桶] 屏幕尺寸: {user32.GetSystemMetrics(0)}x{user32.GetSystemMetrics(1)}")
                        
                        # 检查缩放后的坐标是否有效
                        if scaled_w <= 0 or scaled_h <= 0:
                            print(f"❌ [鱼桶] 缩放后的区域宽度或高度无效: ({scaled_x}, {scaled_y}, {scaled_w}, {scaled_h})")
                        elif scaled_x < 0 or scaled_y < 0:
                            print(f"❌ [鱼桶] 缩放后的区域坐标为负: ({scaled_x}, {scaled_y}, {scaled_w}, {scaled_h})")
                        elif (scaled_x + scaled_w > user32.GetSystemMetrics(0) or 
                              scaled_y + scaled_h > user32.GetSystemMetrics(1)):
                            print(f"❌ [鱼桶] 缩放后的区域超出屏幕范围: ({scaled_x}, {scaled_y}, {scaled_w}, {scaled_h})")
                        else:
                            # 使用字典格式捕获鱼桶区域
                            bucket_frame = scr.grab({
                                "left": scaled_x,
                                "top": scaled_y,
                                "width": scaled_w,
                                "height": scaled_h
                            })
                            
                            if bucket_frame is not None:
                                # 弹窗显示截取的图片，1秒后自动关闭
                                try:
                                    # 将mss截取的图像转换为NumPy数组 (BGRA格式）
                                    preview_img = np.array(bucket_frame)
                                    # 转换为BGR格式用于显示
                                    preview_img_bgr = cv2.cvtColor(preview_img, cv2.COLOR_BGRA2BGR)
                                    # 显示图片
                                    cv2.imshow("截取的鱼桶区域", preview_img_bgr)
                                    # 等待1秒后自动关闭
                                    cv2.waitKey(1000)
                                    # 销毁窗口
                                    cv2.destroyWindow("截取的鱼桶区域")
                                except Exception as e:
                                    print(f"⚠️  [鱼桶] 图片预览出错: {e}")
                            
                            if bucket_frame is not None:
                                # 将mss截取的图像转换为NumPy数组 (BGRA格式）
                                bucket_img = np.array(bucket_frame)
                                
                                # 检查图像是否有效
                                if bucket_img.size > 0:
                                    # 转换为BGR格式（mss返回BGRA，不是RGBA）
                                    bucket_img_bgr = cv2.cvtColor(bucket_img, cv2.COLOR_BGRA2BGR)
                                    
                                    # 转换为灰度图像用于形状匹配
                                    bucket_img_gray = cv2.cvtColor(bucket_img_bgr, cv2.COLOR_BGR2GRAY)
                                    template_gray = cv2.cvtColor(release_xiyou, cv2.COLOR_BGR2GRAY)
                                    
                                    # 使用灰度模板匹配找到所有形状
                                    result = cv2.matchTemplate(bucket_img_gray, template_gray, cv2.TM_CCOEFF_NORMED)
                                    loc = np.where(result >= 0.9)  # 阈值
                                    
                                    template_h, template_w = template_gray.shape[:2]
                                    
                                    # 转换为HSV用于颜色分析
                                    bucket_img_hsv = cv2.cvtColor(bucket_img_bgr, cv2.COLOR_BGR2HSV)
                                    
                                    # 存储所有检测到的结果
                                    all_results = {color_type: {'count': 0, 'locations': []} for color_type in color_ranges}
                                    
                                    # 遍历所有检测到的位置
                                    for pt in zip(*loc[::-1]):
                                        if break_all_loops:
                                            break
                                        
                                        x, y = pt
                                        
                                        # 提取目标区域的HSV
                                        roi_hsv = bucket_img_hsv[y:y + template_h, x:x + template_w]
                                        
                                        # 计算平均色相和饱和度
                                        avg_hue = np.mean(roi_hsv[:, :, 0])
                                        avg_saturation = np.mean(roi_hsv[:, :, 1])
                                        
                                        # 调试：打印前几个位置的HSV值
                                        try:
                                            total_count = (all_results.get('稀有', {}).get('count', 0) + 
                                                         all_results.get('标准', {}).get('count', 0) + 
                                                         all_results.get('非凡', {}).get('count', 0) + 
                                                         all_results.get('史诗', {}).get('count', 0) + 
                                                         all_results.get('传说', {}).get('count', 0))
                                            if total_count < 5:
                                                print(f"   位置({x}, {y}) - 色相: {avg_hue:.1f}, 饱和度: {avg_saturation:.1f}")
                                        except Exception as e:
                                            print(f"   调试信息打印错误: {e}")
                                        
                                        # 根据色相和饱和度判断颜色类型
                                        detected_type = None
                                        for color_type, color_info in color_ranges.items():
                                            if break_all_loops:
                                                break
                                            hue_min, hue_max = color_info['hue_range']
                                            sat_min, sat_max = color_info['saturation_range']
                                            
                                            # 检查色相和饱和度是否在范围内
                                            if hue_min <= avg_hue <= hue_max and sat_min <= avg_saturation <= sat_max:
                                                detected_type = color_type
                                                break
                                        
                                        # 如果没有匹配到颜色，默认为标准
                                        if detected_type is None:
                                            detected_type = '标准'
                                        
                                        # 检查是否在选中的品质列表中
                                        global selected_qualitys
                                        if detected_type in selected_qualitys:
                                            screen_x = scaled_x + x
                                            screen_y = scaled_y + y
                                            
                                            # 鼠标移动到目标位置（确保坐标为整数）
                                            user32.SetCursorPos(int(screen_x), int(screen_y))
                                            
                                            # 鼠标单击操作（考虑随机延迟）
                                            if random_delay_enabled:
                                                time.sleep(0.05 * 1.5)
                                                user32.mouse_event(0x02, 0, 0, 0, 0)  # 左键按下
                                                time.sleep(0.1 * 1.5)
                                                user32.mouse_event(0x04, 0, 0, 0, 0)  # 左键释放
                                                time.sleep(0.05 * 1.5)
                                            else:
                                                # 不使用随机延迟
                                                time.sleep(0.05)
                                                user32.mouse_event(0x02, 0, 0, 0, 0)  # 左键按下
                                                time.sleep(0.1)
                                                user32.mouse_event(0x04, 0, 0, 0, 0)  # 左键释放
                                                time.sleep(0.05)
                                            
                                            if screen_x >= 2290:
                                                screen_x = screen_x - 160
                                            else:
                                                screen_x = screen_x + 160
                                            if screen_y >= 960:
                                                screen_y = screen_y - 120
                                            else:
                                                screen_y = screen_y + 140
                                            # 鼠标移动到目标位置（确保坐标为整数）
                                            user32.SetCursorPos(int(screen_x), int(screen_y))
                                            time.sleep(0.1)
                                            # 鼠标单击操作（考虑随机延迟）
                                            if random_delay_enabled:
                                                time.sleep(0.05 * 1.5)
                                                user32.mouse_event(0x02, 0, 0, 0, 0)  # 左键按下
                                                time.sleep(0.1 * 1.5)
                                                user32.mouse_event(0x04, 0, 0, 0, 0)  # 左键释放
                                                time.sleep(0.05 * 1.5)
                                            else:
                                                # 不使用随机延迟
                                                time.sleep(0.05)
                                                user32.mouse_event(0x02, 0, 0, 0, 0)  # 左键按下
                                                time.sleep(0.1)
                                                user32.mouse_event(0x04, 0, 0, 0, 0)  # 左键释放
                                                time.sleep(0.05)
                                            
                                            # 执行完成后设置标志并跳出当前循环
                                            user32.SetCursorPos(1986, 450)
                                            time.sleep(0.5)
                                            break_all_loops = True
                                            break
                                    
                                    # 如果已经找到并处理了目标鱼，直接跳回到F4状态检查
                                    if break_all_loops:
                                        continue


                                    # # 遍历所有识别结果
                                    # for color_type, result in all_results.items():
                                    #     if result['count'] > 0:
                                    #         color = color_ranges[color_type]['color']
                                    #         label = color_ranges[color_type]['label']
                                    #         print(f"🐟 [鱼桶] 检测到 {result['count']} 个{label}")
                                            
                                    #         # 计算屏幕上的绝对位置并更新到 result 中
                                    #         updated_locations = []
                                    #         for x, y, w, h in result['locations']:
                                    #             # 计算屏幕上的绝对位置
                                    #             screen_x = scaled_x + x
                                    #             screen_y = scaled_y + y
                                                
                                    #             # 打印相对位置和绝对位置
                                    #             print(f"   相对位置: ({x}, {y}, {w}, {h})")
                                    #             print(f"   绝对位置: ({screen_x}, {screen_y}, {w}, {h})")
                                                
                                    #             # 使用对应的颜色绘制矩形框
                                    #             cv2.rectangle(display_img, (x, y), (x + w, y + h), color, 2)
                                                
                                    #             # 在框内添加品质标签
                                    #             # 使用PIL绘制中文文字（OpenCV默认字体不支持中文）
                                                
                                    #             # 将OpenCV图像转换为PIL图像
                                    #             display_img_pil = Image.fromarray(cv2.cvtColor(display_img, cv2.COLOR_BGR2RGB))
                                    #             draw = ImageDraw.Draw(display_img_pil)
                                                
                                    #             # 设置字体
                                    #             font_path = "C:\\Windows\\Fonts\\simsun.ttc"
                                    #             font_size = 12
                                    #             font = ImageFont.truetype(font_path, font_size)
                                                
                                    #             text = label
                                    #             text_color = (255, 255, 255)  # 白色文字
                                                
                                    #             # 计算文字位置（左上角）
                                    #             text_x = x + 3
                                    #             text_y = y + 3  # 向下偏移3像素
                                                
                                    #             # 在框内绘制文字
                                    #             draw.text((text_x, text_y), text, font=font, fill=text_color)
                                                
                                    #             # 将PIL图像转换回OpenCV图像
                                    #             display_img = cv2.cvtColor(np.array(display_img_pil), cv2.COLOR_RGB2BGR)
                                                
                                    #             # 保存绝对位置到列表中
                                    #             updated_locations.append((screen_x, screen_y, w, h))
                                            
                                    #         # 更新 result 中的 locations 为屏幕绝对位置
                                    #         result['locations'] = updated_locations
                                    
                                    # # 弹窗显示带标记框的图像
                                    # cv2.imshow("鱼桶识别结果", display_img)
                                    # cv2.waitKey(0)
                                    # cv2.destroyAllWindows()
                                else:
                                    print("⚠️  [鱼桶] 捕获的图像无效")
                    else:
                        print("⚠️  [鱼桶] release_xiyou 模板加载失败")
                
                scr.close()
            except Exception as e:
                print(f"❌ [错误] 鱼桶线程异常: {e}")
                import traceback
                traceback.print_exc()
                try:
                    if 'scr' in locals() and scr is not None:
                        scr.close()
                except:
                    pass
        
        last_f4_state = current_f4_state
        time.sleep(0.1)

def main():
    global templates, template_folder_path, current_result, previous_result, times, a, region1, region2, result_val_is, scr, jiashi_var

    # 启动加时处理线程
    jiashi_thread = threading.Thread(target=handle_jiashi_thread, daemon=True)
    jiashi_thread.start()
    
    # 加载 release_xiyou 模板
    load_release_xiyou()
    # load_release_chuanshuo()
    # load_release_feifan()
    # load_release_shishi()
    # 启动鱼桶区域识别线程
    fish_bucket_thread = threading.Thread(target=handle_fish_bucket_thread, daemon=True)
    fish_bucket_thread.start()

    while not begin_event.is_set():
        if run_event.is_set():
            # 自动检测猛兽派对窗口
            auto_check_monster_party()
            
            scr = None
            try:
                scr = mss.mss()

                # 检测F1/F2抛竿
                if f1_mached(scr):
                    user32.mouse_event(0x02, 0, 0, 0, 0)
                    if random_delay_enabled:
                        # 根据设置的百分比添加随机延迟
                        max_factor = 1.0 + random_delay / 100.0
                        random_factor_paogantime = random.uniform(1.0, max_factor)
                        time.sleep(paogantime * random_factor_paogantime)
                    else:
                        time.sleep(paogantime)
                    user32.mouse_event(0x04, 0, 0, 0, 0)
                    time.sleep(0.15)
                elif f2_mached(scr):
                    user32.mouse_event(0x02, 0, 0, 0, 0)
                    if random_delay_enabled:
                        # 根据设置的百分比添加随机延迟
                        max_factor = 1.0 + random_delay / 100.0
                        random_factor_paogantime = random.uniform(1.0, max_factor)
                        time.sleep(paogantime * random_factor_paogantime)
                    else:
                        time.sleep(paogantime)
                    user32.mouse_event(0x04, 0, 0, 0, 0)
                    time.sleep(0.15)
                elif shangyu_mached(scr):
                    user32.mouse_event(0x02, 0, 0, 0, 0)
                    time.sleep(0.1)
                    user32.mouse_event(0x04, 0, 0, 0, 0)

                time.sleep(0.05)

                # 获取当前结果
                bait_result = bait_math_val(scr)
                if bait_result is not None:
                    current_result = result_val_is
                else:
                    current_result = previous_result  # 将当前数字设为上次的数字
                    time.sleep(0.1)
                    continue  # 会在finally中关闭scr

                # 比较并执行操作
                comparison_result = compare_results()
                time.sleep(0.01)

                if comparison_result == -1:  # 当前结果小于上次结果
                    previous_result = current_result  # 更新上次识别的结果
                    while not fished(scr) and run_event.is_set():
                        # 使用锁保护读取times
                        with param_lock:
                            current_times = times
                        if a <= current_times:
                            a += 1
                            pressandreleasemousebutton()  # 执行点击循环直到识别到 star.png
                        else:
                            a = 0
                            print("🎣 [提示] 达到最大拉杆次数，本轮结束")
                            break
                    ensure_mouse_up()
                    a = 0

                    # 钓到鱼后，识别并记录鱼的信息
                    if OCR_AVAILABLE and record_fish_enabled:
                        try:
                            record_caught_fish()
                        except Exception as e:
                            print(f"⚠️  [警告] 记录鱼信息失败: {e}")
                elif comparison_result == 1:
                    previous_result = current_result
                    # continue会在finally中关闭scr
            except Exception as e:
                print(f"❌ [错误] 主循环异常: {e}")
            finally:
                # 确保mss资源被正确释放
                if scr is not None:
                    try:
                        scr.close()
                    except:
                        pass
                    scr = None
        time.sleep(0.1)

# =========================
# 程序入口
# =========================
if __name__ == "__main__":
    # 管理员权限检测
    print("🔒 [初始化] 正在检测管理员权限...")
    if not is_admin():
        print("⚠️  [警告] 当前程序未以管理员权限运行")
        print("📋 [提示] 请右键点击程序图标，选择'以管理员身份运行'，以确保所有功能正常工作")
        print("💡 [说明] 管理员权限对于键盘鼠标模拟、截图等功能至关重要")
        print()
    else:
        print("✅ [初始化] 管理员权限检测通过")
        print()
    
    # 先加载参数以获取热键设置
    load_parameters()

    print("╔" + "═" * 50 + "╗")
    print("║" + " " * 50 + "║")
    print("║     🎣  PartyFish 自动钓鱼助手  v2.8             ║")
    print("║" + " " * 50 + "║")
    print("╠" + "═" * 50 + "╣")
    print(f"║  📺 当前分辨率: {CURRENT_SCREEN_WIDTH}×{CURRENT_SCREEN_HEIGHT}".ljust(45)+"║")
    print(f"║  ⌨️ 快捷键: {hotkey_name}启动/暂停脚本".ljust(42)+"║")
    print("║  🔧 开发者: FadedTUMI/PeiXiaoXiao                ║")
    print("╚" + "═" * 50 + "╝")
    print()

    # 加载参数和模板
    print("📦 [初始化] 配置加载完成")

    # 加载历史钓鱼记录
    print("📊 [初始化] 正在加载钓鱼记录...")
    load_all_fish_records()

    print("🖼️  [初始化] 正在加载图像模板...")
    load_templates()
    load_star_template()
    load_f1()
    load_f2()
    load_shangyule()
    load_jiashi()
    print("✅ [初始化] 模板加载完成")

    # 启动热键监听
    print("🎮 [初始化] 正在启动热键监听...")
    start_hotkey_listener()
    print("✅ [初始化] 热键监听已启动")

    print()
    print("┌" + "─" * 48 + "┐")
    print(f"│  🚀 程序已就绪，按 {hotkey_name} 开始自动钓鱼！".ljust(34) + "│")
    print("└" + "─" * 48 + "┘")
    print()

    # 将main()放在后台线程运行（daemon=True确保主线程退出时自动结束）
    main_thread = threading.Thread(target=main, daemon=True)
    main_thread.start()

    # GUI必须在主线程运行（Tkinter要求）
    # 这样可以确保GUI正常工作且不会崩溃
    try:
        create_gui()
    except KeyboardInterrupt:
        # 优雅处理Ctrl+C中断，确保程序能够正常退出
        print("\n\n┌" + "─" * 48 + "┐")
        print("│  🛑  程序已通过Ctrl+C中断                      │")
        print("└" + "─" * 48 + "┘")
        # 确保所有资源都能正确释放
        pass