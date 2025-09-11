#!/usr/bin/env python3
# coding: utf-8
import socket
import psutil
import subprocess
import time
import os
import shutil
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import logging
import tkinter as tk
from tkinter import ttk, scrolledtext
from queue import Queue
import re

# 配置日志 - 每次运行清空之前的日志
log_file = "adb_install.log"
if os.path.exists(log_file):
    try:
        os.remove(log_file)
    except Exception as e:
        print(f"清除旧日志文件失败: {str(e)}")

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(log_file),  # 日志保存到当前目录
        logging.StreamHandler()
    ]
)

# 配置参数 - 优化连接和超时设置（重点优化项）
PORT = 5555           
TIMEOUT = 0.5         # 减少超时时间，加速扫描
MAX_THREADS = 100     # 增加线程数，加速网段扫描
SCAN_INTERVAL = 10    # 扫描间隔（秒）
INSTALL_RETRY = 2     # 减少重试次数
POST_INSTALL_WAIT = 1 # 减少安装后等待时间
REBOOT_WAIT = 20      # 减少重启等待时间
REBOOT_RETRY = 1      # 减少重启重试次数
ADB_TIMEOUT = 90      # 调整ADB超时时间
ADB_BUFFER_SIZE = 1048576  
TARGET_VOLUME_PERCENT = 80  # 目标音量百分比

# 实时监控配置
REAL_TIME_MONITOR = True  # 启用实时监控
SHOW_SCAN_DETAILS = False  # 关闭详细扫描日志，减少IO操作

# 新增：扫描优化配置
SCAN_BLOCK_SIZE = 20      # 分块扫描大小
SCAN_BATCH_DELAY = 0.1    # 批次扫描延迟
SKIP_RECENTLY_SCANNED = True  # 跳过最近扫描过的IP
RECENT_SCAN_WINDOW = 60   # 最近扫描窗口（秒）

# 版本配置（国内版/全球版文件夹）
VERSION_CONFIG = {
    "国内版": "国内版",    # 按钮文本: 对应文件夹名称
    "全球版": "全球版"     # 按钮文本: 对应文件夹名称
}
CURRENT_VERSION = None  # 记录当前运行的版本（国内版/全球版）

# 安装统计数据
installation_stats = {
    "国内版": {
        "total": 0,       # 总安装设备数
        "success": 0,     # 成功安装数
        "failed": 0       # 安装失败数
    },
    "全球版": {
        "total": 0,
        "success": 0,
        "failed": 0
    }
}

# 设备状态跟踪
device_status = {}  # 格式: {ip: {"status": "", "progress": 0, "last_updated": "", "in_progress": False, "version": ""}}
status_queue = Queue()  # 用于UI更新的队列
recently_scanned_ips = {}  # 记录最近扫描过的IP: {ip: timestamp}

# 扩展网络接口识别模式
WIRED_INTERFACE_PATTERNS = {
    # 常见有线网卡前缀
    'eth', 'en', 'em', 'eno', 'ens', 'enp', 
    # 中文系统常见名称
    '本地连接', '以太网', '有线', 
    # 其他可能的模式
    'lan', '有线连接'
}

# 无线网卡模式
WIRELESS_INTERFACE_PATTERNS = {
    'wlan', 'wl', 'wifi', '无线', 'wlp', 'wwan', 'wlan'
}

class DeviceMonitorUI:
    def __init__(self, root):
        self.root = root
        self.root.title("ADB设备管理工具（国内版/全球版）")
        self.root.geometry("1100x650")
        
        # 创建主框架
        main_frame = ttk.Frame(root, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 顶部控制区 - 放置按钮和版本状态
        control_frame = ttk.Frame(main_frame)
        control_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 版本状态标签（突出显示当前版本）
        self.version_label = ttk.Label(
            control_frame, 
            text="当前状态：未开始任何版本安装", 
            foreground="red",  # 红色字体强调
            font=('Helvetica', 11, 'bold')  # 加粗放大
        )
        self.version_label.pack(side=tk.LEFT, padx=(0, 20))
        
        # 拆分后的两个扫描按钮（国内版/全球版）
        style = ttk.Style()
        style.configure('Large.TButton', font=('Helvetica', 10))
        
        # 国内版扫描按钮
        self.start_cn_button = ttk.Button(
            control_frame, 
            text="国内版扫描", 
            command=lambda: self.start_scan("国内版"),  # 绑定国内版参数
            width=15,
            style='Large.TButton'
        )
        self.start_cn_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # 全球版扫描按钮
        self.start_global_button = ttk.Button(
            control_frame, 
            text="全球版扫描", 
            command=lambda: self.start_scan("全球版"),  # 绑定全球版参数
            width=15,
            style='Large.TButton'
        )
        self.start_global_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # 停止所有操作按钮
        self.stop_all_button = ttk.Button(
            control_frame, 
            text="停止所有操作", 
            command=self.stop_all_operations,
            width=15,
            style='Large.TButton',
            state=tk.DISABLED  # 初始禁用
        )
        self.stop_all_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # 新增：强制处理设备按钮
        self.force_process_button = ttk.Button(
            control_frame, 
            text="强制处理所有设备", 
            command=self.force_process_all,
            width=15,
            style='Large.TButton',
            state=tk.DISABLED  # 初始禁用
        )
        self.force_process_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # 网络选择复选框
        self.scan_wired = tk.BooleanVar(value=True)
        self.scan_wireless = tk.BooleanVar(value=True)
        
        ttk.Checkbutton(
            control_frame, 
            text="扫描有线网络", 
            variable=self.scan_wired
        ).pack(side=tk.LEFT, padx=(0, 10))
        
        ttk.Checkbutton(
            control_frame, 
            text="扫描无线网络", 
            variable=self.scan_wireless
        ).pack(side=tk.LEFT, padx=(0, 10))
        
        # 日志过滤复选框
        self.log_filter_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            control_frame, 
            text="仅显示关键日志", 
            variable=self.log_filter_var,
            command=self.filter_logs
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # 扫描状态标签
        self.status_label = ttk.Label(control_frame, text="等待选择版本并开始扫描...")
        self.status_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # 中间区域：左侧设备表格，右侧统计信息
        middle_frame = ttk.Frame(main_frame)
        middle_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # 设备状态表格（新增“版本”列）
        status_frame = ttk.LabelFrame(middle_frame, text="设备状态", padding="10")
        status_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # 创建表格（新增"version"列）
        columns = ("ip", "status", "progress", "last_updated", "network_type", "version")
        self.tree = ttk.Treeview(status_frame, columns=columns, show="headings")
        
        # 设置列标题（新增“版本”列）
        self.tree.heading("ip", text="IP地址")
        self.tree.heading("status", text="状态")
        self.tree.heading("progress", text="进度")
        self.tree.heading("last_updated", text="最后更新时间")
        self.tree.heading("network_type", text="网络类型")
        self.tree.heading("version", text="安装版本")  # 新增列标题
        
        # 设置列宽（调整适配新增列）
        self.tree.column("ip", width=120)
        self.tree.column("status", width=180)
        self.tree.column("progress", width=80)
        self.tree.column("last_updated", width=160)
        self.tree.column("network_type", width=100)
        self.tree.column("version", width=100)  # 新增列宽度
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 添加滚动条
        scrollbar = ttk.Scrollbar(status_frame, orient=tk.VERTICAL, command=self.tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.configure(yscrollcommand=scrollbar.set)
        
        # 统计信息面板
        stats_frame = ttk.LabelFrame(middle_frame, text="安装统计", padding="10")
        stats_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0), pady=(0, 10))
        
        # 国内版统计
        self.cn_stats_frame = ttk.LabelFrame(stats_frame, text="国内版", padding="10")
        self.cn_stats_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.cn_total_label = ttk.Label(self.cn_stats_frame, text="总安装设备: 0")
        self.cn_total_label.pack(anchor=tk.W, pady=2)
        
        self.cn_success_label = ttk.Label(self.cn_stats_frame, text="安装成功: 0", foreground="green")
        self.cn_success_label.pack(anchor=tk.W, pady=2)
        
        self.cn_failed_label = ttk.Label(self.cn_stats_frame, text="安装失败: 0", foreground="red")
        self.cn_failed_label.pack(anchor=tk.W, pady=2)
        
        # 全球版统计
        self.global_stats_frame = ttk.LabelFrame(stats_frame, text="全球版", padding="10")
        self.global_stats_frame.pack(fill=tk.X)
        
        self.global_total_label = ttk.Label(self.global_stats_frame, text="总安装设备: 0")
        self.global_total_label.pack(anchor=tk.W, pady=2)
        
        self.global_success_label = ttk.Label(self.global_stats_frame, text="安装成功: 0", foreground="green")
        self.global_success_label.pack(anchor=tk.W, pady=2)
        
        self.global_failed_label = ttk.Label(self.global_stats_frame, text="安装失败: 0", foreground="red")
        self.global_failed_label.pack(anchor=tk.W, pady=2)
        
        # 日志区域
        log_frame = ttk.LabelFrame(main_frame, text="操作日志", padding="10")
        log_frame.pack(fill=tk.BOTH, expand=True)
        
        self.log_text = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)
        
        self.scanning = False
        self.scan_thread = None
        self.current_running_version = None  # 记录当前运行的版本（用于停止扫描时重置）
        
    def update_log(self, message):
        """更新日志区域，支持过滤"""
        self.log_text.configure(state=tk.NORMAL)
        
        # 根据过滤状态决定是否显示
        show_message = True
        if self.log_filter_var.get():
            # 只显示关键信息
            show_message = any(keyword in message for keyword in ["发现", "连接", "安装", "成功", "失败", "错误", "音量"])
        
        if show_message:
            self.log_text.insert(tk.END, message + "\n")
            self.log_text.see(tk.END)
            
        self.log_text.configure(state=tk.DISABLED)
    
    def filter_logs(self):
        """过滤日志显示，只显示关键信息"""
        if self.log_filter_var.get():
            # 保存当前日志内容
            current_content = self.log_text.get("1.0", tk.END)
            self.log_text.configure(state=tk.NORMAL)
            self.log_text.delete("1.0", tk.END)
            
            # 只保留关键日志
            for line in current_content.split("\n"):
                if any(keyword in line for keyword in ["发现", "连接", "安装", "成功", "失败", "错误", "音量"]):
                    self.log_text.insert(tk.END, line + "\n")
            
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.NORMAL)
        else:
            # 显示所有日志（需要从日志文件重新加载）
            self.log_text.configure(state=tk.NORMAL)
            self.log_text.delete("1.0", tk.END)
            if os.path.exists(log_file):
                with open(log_file, "r", encoding="utf-8") as f:
                    self.log_text.insert(tk.END, f.read())
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.DISABLED)
    
    def update_stats_display(self):
        """更新统计信息显示"""
        # 更新国内版统计
        self.cn_total_label.config(text=f"总安装设备: {installation_stats['国内版']['total']}")
        self.cn_success_label.config(text=f"安装成功: {installation_stats['国内版']['success']}")
        self.cn_failed_label.config(text=f"安装失败: {installation_stats['国内版']['failed']}")
        
        # 更新全球版统计
        self.global_total_label.config(text=f"总安装设备: {installation_stats['全球版']['total']}")
        self.global_success_label.config(text=f"安装成功: {installation_stats['全球版']['success']}")
        self.global_failed_label.config(text=f"安装失败: {installation_stats['全球版']['failed']}")
        
        # 继续更新循环
        self.root.after(1000, self.update_stats_display)
    
    def update_version_status(self, version, is_running):
        """更新版本状态标签（实时显示当前安装版本）"""
        global CURRENT_VERSION
        if is_running:
            CURRENT_VERSION = version
            self.current_running_version = version
            self.version_label.config(
                text=f"当前状态：正在执行【{version}】安装",
                foreground="green"  # 运行中显示绿色
            )
            # 禁用两个版本按钮，启用停止按钮和强制处理按钮
            self.start_cn_button.config(state=tk.DISABLED)
            self.start_global_button.config(state=tk.DISABLED)
            self.stop_all_button.config(state=tk.NORMAL)
            self.force_process_button.config(state=tk.NORMAL)
        else:
            CURRENT_VERSION = None
            self.current_running_version = None
            self.version_label.config(
                text=f"当前状态：【{version}】安装已停止/完成",
                foreground="red"  # 停止后显示红色
            )
            # 启用两个版本按钮，检查是否需要禁用停止按钮
            self.start_cn_button.config(state=tk.NORMAL)
            self.start_global_button.config(state=tk.NORMAL)
            self.force_process_button.config(state=tk.DISABLED)
            
            # 如果没有任何操作在运行，禁用停止按钮
            if not self.scanning:
                self.stop_all_button.config(state=tk.DISABLED)
    
    def update_device_status(self):
        """更新设备状态表格（新增版本列数据）"""
        while not status_queue.empty():
            ip, status, progress, last_updated, in_progress, network_type, version = status_queue.get()
            
            # 更新设备状态字典（新增version字段）
            device_status[ip] = {
                "status": status,
                "progress": progress,
                "last_updated": last_updated,
                "in_progress": in_progress,
                "network_type": network_type,
                "version": version  # 记录该设备对应的安装版本
            }
            
            # 更新表格（新增版本列值）
            found = False
            for item in self.tree.get_children():
                if self.tree.item(item, "values")[0] == ip:
                    self.tree.item(item, values=(ip, status, progress, last_updated, network_type, version))
                    found = True
                    break
            
            if not found:
                self.tree.insert("", tk.END, values=(ip, status, progress, last_updated, network_type, version))
        
        # 继续检查更新
        self.root.after(500, self.update_device_status)  # 更频繁地更新UI
    
    def start_scan(self, version):
        """开始指定版本的扫描（国内版/全球版）"""
        if not self.scanning:
            # 检查版本对应的APK文件夹是否存在
            apk_folder = VERSION_CONFIG[version]
            if not os.path.exists(apk_folder):
                msg = f"错误：【{version}】对应的文件夹「{apk_folder}」不存在，请先创建并放入APK文件！"
                logging.error(msg)
                self.update_log(msg)
                return
            
            self.scanning = True
            self.update_version_status(version, is_running=True)  # 更新版本状态为“运行中”
            self.status_label.config(text=f"正在执行【{version}】扫描设备...")
            # 启动扫描线程（传入当前版本参数）
            self.scan_thread = threading.Thread(
                target=self.run_scanner, 
                args=(version,), 
                daemon=True
            )
            self.scan_thread.start()
        else:
            # 停止扫描时重置状态
            self.scanning = False
            self.update_version_status(self.current_running_version, is_running=False)  # 标记版本“已停止”
            self.status_label.config(text=f"【{self.current_running_version}】扫描已停止")
    
    def stop_all_operations(self):
        """停止所有正在进行的操作"""
        if not self.scanning:
            return
            
        msg = "正在停止所有操作..."
        logging.info(msg)
        self.update_log(msg)
        self.status_label.config(text="正在停止所有操作...")
        
        # 标记扫描为停止状态
        self.scanning = False
        
        # 标记所有设备为不处理状态
        for ip in device_status:
            device_status[ip]["in_progress"] = False
        
        # 更新UI状态
        if self.current_running_version:
            self.update_version_status(self.current_running_version, is_running=False)
            self.status_label.config(text=f"【{self.current_running_version}】所有操作已停止")
        
        msg = "所有操作已停止"
        logging.info(msg)
        self.update_log(msg)
    
    def force_process_all(self):
        """强制处理所有已发现但未处理的设备"""
        if not self.current_running_version or not self.scanning:
            return
            
        version = self.current_running_version
        msg = f"=== 【{version}】开始强制处理所有设备 ==="
        logging.info(msg)
        self.update_log(msg)
        
        # 遍历所有设备，强制处理
        for ip, info in list(device_status.items()):
            if not info["in_progress"]:  # 只处理未在处理中的设备
                network_type = info["network_type"]
                msg = f"【{version}】强制开始处理{network_type}设备 {ip}"
                logging.info(msg)
                self.update_log(msg)
                # 启动处理线程
                threading.Thread(target=process_device, args=(ip, self, network_type, version), daemon=True).start()
                time.sleep(0.2)  # 更短的延迟，加速处理队列
        
        msg = f"=== 【{version}】强制处理命令已发送 ==="
        logging.info(msg)
        self.update_log(msg)
    
    def run_scanner(self, version):
        """运行指定版本的扫描器（核心逻辑，传入版本参数）"""
        try:
            if not shutil.which("adb"):
                msg = "未找到ADB工具，请确保ADB已安装并添加到PATH中"
                logging.error(msg)
                self.root.after(0, lambda: self.update_log(msg))
                self.root.after(0, lambda: self.status_label.config(text="错误: 未找到ADB工具"))
                self.root.after(0, lambda: self.update_version_status(version, is_running=False))
                return
                
            # 启动实时监控线程
            monitor_thread = None
            if REAL_TIME_MONITOR:
                monitor_thread = threading.Thread(
                    target=start_real_time_monitor, 
                    args=(self, version), 
                    daemon=True
                )
                monitor_thread.start()
                
            scan_count = 0  # 计数，每3次扫描清理一次离线设备
            while self.scanning:
                # 每3次扫描执行一次离线设备清理
                scan_count += 1
                if scan_count % 3 == 0:
                    clean_offline_devices(self, version)
                
                # 传递当前的扫描设置和版本参数
                scan_and_process(self, self.scan_wired.get(), self.scan_wireless.get(), version)
                if self.scanning:  # 检查是否已停止
                    msg = f"\n等待 {SCAN_INTERVAL} 秒后进行【{version}】下一次扫描..."
                    logging.info(msg)
                    # 根据配置决定是否显示详细扫描日志
                    if SHOW_SCAN_DETAILS:
                        self.root.after(0, lambda: self.update_log(msg.strip()))
                    else:
                        # 只在日志文件中记录，不在UI显示
                        pass
                        
                    # 倒计时显示
                    for i in range(SCAN_INTERVAL, 0, -1):
                        if not self.scanning:
                            break
                        self.root.after(0, lambda i=i: self.status_label.config(
                            text=f"等待【{version}】下次扫描: {i}秒 | 实时监控中..."
                        ))
                        time.sleep(1)
                    
                    if self.scanning:
                        self.root.after(0, lambda: self.status_label.config(
                            text=f"正在执行【{version}】扫描设备... | 实时监控中..."
                        ))
        except Exception as e:
            logging.error(f"【{version}】扫描线程错误: {str(e)}")
            self.root.after(0, lambda: self.update_log(f"【{version}】扫描线程错误: {str(e)}"))
        
        # 扫描结束后重置状态
        self.scanning = False
        self.root.after(0, lambda: self.start_cn_button.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.start_global_button.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.stop_all_button.config(state=tk.DISABLED))
        self.root.after(0, lambda: self.force_process_button.config(state=tk.DISABLED))
        self.root.after(0, lambda: self.status_label.config(text=f"【{version}】扫描已停止"))
        self.root.after(0, lambda: self.update_version_status(version, is_running=False))

def get_local_ip():
    """获取本机局域网 IP"""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(2)
        try:
            s.connect(("8.8.8.8", 80))
            ip = s.getsockname()[0]
            return ip
        except socket.timeout:
            logging.warning("获取本机IP超时，使用默认IP")
            return "127.0.0.1"
        except Exception as e:
            logging.error(f"获取本机IP失败: {str(e)}")
            return "127.0.0.1"
        finally:
            s.close()
    except Exception as e:
        logging.error(f"创建socket失败: {str(e)}")
        return "127.0.0.1"

def classify_interface(iface_name):
    """
    分类网络接口类型
    返回: 'wired' (有线), 'wireless' (无线), 或 'unknown' (未知)
    """
    if not iface_name:
        return 'unknown'
        
    # 转为小写进行比较
    iface_lower = iface_name.lower()
    
    # 检查是否为无线接口
    for pattern in WIRELESS_INTERFACE_PATTERNS:
        if pattern in iface_lower:
            return 'wireless'
    
    # 检查是否为有线接口
    for pattern in WIRED_INTERFACE_PATTERNS:
        if pattern in iface_lower:
            return 'wired'
    
    # 检查USB有线网卡
    if "usb" in iface_lower:
        return 'wired'
        
    return 'unknown'

def get_network_ips(scan_wired=True, scan_wireless=True):
    """
    获取指定类型网络接口的IPv4地址，排除APIPA地址
    可通过参数控制是否扫描有线和无线网络
    """
    # 按类型存储IP
    network_ips = {
        'wired': [],
        'wireless': [],
        'unknown': []
    }
    
    all_interfaces = []
    
    try:
        addrs = psutil.net_if_addrs()
        interfaces = psutil.net_if_stats()
        
        # 收集所有接口信息
        for iface, addr_list in addrs.items():
            all_interfaces.append(iface)
            is_up = interfaces.get(iface, {}).isup if iface in interfaces else False
            
            # 分类接口类型
            iface_type = classify_interface(iface)
            
            # 记录所有接口信息用于调试
            logging.debug(f"网络接口: {iface} (类型: {iface_type}, 状态: {'启用' if is_up else '禁用'})")
            
            # 跳过禁用的接口
            if not is_up:
                continue
                
            # 根据配置决定是否处理该类型接口
            if (iface_type == 'wired' and not scan_wired) or \
               (iface_type == 'wireless' and not scan_wireless):
                continue
                
            # 处理该接口的IP地址
            for addr in addr_list:
                if addr.family == socket.AF_INET:
                    ip = addr.address
                    # 排除回环地址和APIPA地址(169.254.x.x)
                    if not ip.startswith(("127.", "169.254.")):
                        network_ips[iface_type].append(ip)
                        logging.info(f"检测到{iface_type}网络接口 {iface}: {ip}")
        
        # 记录接口分类情况
        logging.info(f"检测到所有网络接口 ({len(all_interfaces)}个): {', '.join(all_interfaces)}")
        logging.info(f"有线网络接口IPs ({len(network_ips['wired'])}个): {', '.join(network_ips['wired']) if network_ips['wired'] else '无'}")
        logging.info(f"无线网络接口IPs ({len(network_ips['wireless'])}个): {', '.join(network_ips['wireless']) if network_ips['wireless'] else '无'}")
        logging.info(f"未知类型网络接口IPs ({len(network_ips['unknown'])}个): {', '.join(network_ips['unknown']) if network_ips['unknown'] else '无'}")
        
    except Exception as e:
        logging.error(f"获取网络IP失败: {str(e)}")
    
    # 合并结果并去重，保持有线优先
    all_ips = []
    # 先添加有线IP
    if scan_wired:
        all_ips.extend(network_ips['wired'])
    # 再添加无线IP
    if scan_wireless:
        all_ips.extend(network_ips['wireless'])
    # 最后添加未知类型IP
    all_ips.extend(network_ips['unknown'])
    
    # 去重但保持顺序
    seen = set()
    unique_ips = []
    for ip in all_ips:
        if ip not in seen:
            seen.add(ip)
            unique_ips.append(ip)
    
    return unique_ips, network_ips

def get_network_prefix(ip):
    """获取 /24 网段前缀"""
    try:
        parts = ip.split('.')
        if len(parts) != 4:
            raise ValueError(f"无效的IP地址格式: {ip}")
        for part in parts:
            if not part.isdigit() or not (0 <= int(part) <= 255):
                raise ValueError(f"无效的IP地址: {ip}")
        return '.'.join(parts[:3]) + '.'
    except ValueError as e:
        logging.error(f"解析IP地址失败: {str(e)}")
        return "192.168.1."

def is_device_connected(ip):
    """检查设备是否已连接"""
    try:
        # 增加重试机制
        for _ in range(2):
            result = subprocess.run(
                ["adb", "devices"],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=True,
                timeout=5  # 缩短超时时间
            )
            if f"{ip}:{PORT}" in result.stdout:
                return True
            time.sleep(0.5)  # 缩短等待时间
        return False
    except Exception as e:
        logging.error(f"检查设备连接时发生错误: {str(e)}")
        return False

def wait_for_authorization(ip, ui, network_type, version):
    """等待设备授权 - 优化响应速度，减少等待时间"""
    msg = f"开始处理设备 {ip}..."
    logging.info(msg)
    ui.root.after(0, lambda: ui.update_log(msg))
    status_queue.put((ip, "开始处理", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
    
    try:
        # 减少等待循环的间隔时间，加速响应
        last_check_time = time.time()
        
        while True:
            # 检查是否已被用户手动取消处理
            if ip in device_status and not device_status[ip].get("in_progress", True):
                msg = f"设备 {ip} 的处理已被取消"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return False
                
            try:
                # 更频繁地检查设备状态
                current_time = time.time()
                if current_time - last_check_time >= 1:  # 每秒检查一次
                    last_check_time = current_time
                    
                    # 检查设备状态
                    result = subprocess.run(
                        ["adb", "devices"],
                        capture_output=True,
                        text=True,
                        encoding='utf-8',
                        errors='ignore',
                        check=False,
                        timeout=5  # 缩短超时时间
                    )
                    
                    # 一旦检测到设备已授权，立即返回成功并继续执行
                    if f"{ip}:{PORT}\tdevice" in result.stdout:
                        msg = f"设备 {ip} 已授权，开始执行后续操作..."
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        status_queue.put((ip, "已授权", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                        return True
                        
                    # 检测到未授权状态，持续等待并提示用户
                    elif f"{ip}:{PORT}\tunauthorized" in result.stdout:
                        # 主动尝试触发授权窗口
                        subprocess.run(
                            ["adb", "-s", f"{ip}:{PORT}", "shell", "getprop"],
                            capture_output=True, text=True, timeout=3  # 缩短超时时间
                        )
                        
                        msg = f"请在设备 {ip} 上允许ADB调试授权（等待中...）"
                        logging.warning(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        status_queue.put((ip, "等待授权", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                    
                    else:
                        # 尝试重新连接设备
                        reconnect_result = subprocess.run(
                            ["adb", "connect", f"{ip}:{PORT}"],
                            capture_output=True, text=True, timeout=5  # 缩短超时时间
                        )
                        
                        if "connected to" in reconnect_result.stdout:
                            msg = f"重新连接到设备 {ip} 成功，等待授权..."
                            logging.info(msg)
                            ui.root.after(0, lambda: ui.update_log(msg))
                        else:
                            msg = f"与设备 {ip} 的连接已断开，持续尝试重新连接..."
                            logging.warning(msg)
                            ui.root.after(0, lambda: ui.update_log(msg))
                            status_queue.put((ip, "连接断开，重试中", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                
                # 极短的等待时间，提高响应速度
                time.sleep(0.1)
                
            except Exception as e:
                logging.error(f"检查设备授权时发生错误: {str(e)}")
                ui.root.after(0, lambda: ui.update_log(f"检查设备授权时发生错误: {str(e)}"))
                time.sleep(1)
    
    except Exception as e:
        logging.error(f"等待设备授权时发生异常: {str(e)}")
        ui.root.after(0, lambda: ui.update_log(f"等待设备授权时发生异常: {str(e)}"))
        status_queue.put((ip, "授权错误", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
        return False

def install_apk_with_retry(ip, apk_path, ui, total_apks, current_apk, network_type, version):
    """带重试机制安装单个APK，优化速度参数"""
    # 检查是否仍在处理中
    if ip in device_status and not device_status[ip].get("in_progress", True):
        msg = f"【{version}】设备 {ip} 的处理已被取消，终止安装 {apk_path}"
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        return False
        
    if not os.path.isfile(apk_path):
        msg = f"【{version}】APK文件不存在: {apk_path}"
        logging.error(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        return False
        
    progress = int((current_apk / total_apks) * 100)
    file_size = os.path.getsize(apk_path) / (1024 * 1024)
    adb_cmd = [
        "adb", "-s", f"{ip}:{PORT}", 
        "install", "-r", "--user", "0",
        apk_path
    ]
    
    for attempt in range(INSTALL_RETRY):
        # 检查是否仍在处理中
        if ip in device_status and not device_status[ip].get("in_progress", True):
            msg = f"【{version}】设备 {ip} 的处理已被取消，终止安装 {apk_path}"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            return False
            
        msg = f"【{version}】安装 {apk_path} (尝试 {attempt + 1}/{INSTALL_RETRY}) - 大小: {file_size:.2f} MB"
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        status_queue.put((ip, f"安装中: {os.path.basename(apk_path)}", f"{progress}%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        
        try:
            result = subprocess.run(
                adb_cmd,
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=False,
                timeout=ADB_TIMEOUT
            )
            
            # 检查是否是ADB连接错误
            if "error: device offline" in result.stderr or "error: device not found" in result.stderr:
                # 尝试重新连接
                reconnect_result = subprocess.run(
                    ["adb", "connect", f"{ip}:{PORT}"],
                    capture_output=True, text=True, timeout=5  # 缩短超时时间
                )
                
                if "connected to" in reconnect_result.stdout:
                    msg = f"【{version}】重新连接到设备 {ip} 成功，重试安装..."
                    logging.info(msg)
                    ui.root.after(0, lambda: ui.update_log(msg))
                    time.sleep(1)  # 缩短等待时间
                    continue
                
                msg = f"【{version}】ADB连接错误: 设备 {ip} 已离线或未找到"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
                
            if result.returncode == 0 and "Success" in result.stdout:
                time.sleep(POST_INSTALL_WAIT)
                msg = f"【{version}】安装成功：{apk_path}"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return True
            else:
                msg = f"【{version}】安装失败 (返回码 {result.returncode})：{apk_path}"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                error_msg = result.stderr if result.stderr else result.stdout
                logging.error(f"错误信息：{error_msg}")
                ui.root.after(0, lambda: ui.update_log(f"错误信息：{error_msg}"))
        
        except subprocess.TimeoutExpired:
            msg = f"【{version}】安装超时: {apk_path}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
        except Exception as e:
            # 检查是否是连接相关的错误
            if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
                msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
            msg = f"【{version}】安装过程中发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
        
        if attempt < INSTALL_RETRY - 1:
            time.sleep(2)  # 缩短重试等待时间
    
    status_queue.put((ip, f"安装失败: {os.path.basename(apk_path)}", f"{progress}%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
    return False

def reboot_device(ip, ui, network_type, version):
    """重启设备并等待重启完成"""
    # 检查是否仍在处理中
    if ip in device_status and not device_status[ip].get("in_progress", True):
        msg = f"【{version}】设备 {ip} 的处理已被取消，终止重启"
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        return False
        
    msg = f"【{version}】准备重启设备 {ip}..."
    logging.info(msg)
    ui.root.after(0, lambda: ui.update_log(msg))
    status_queue.put((ip, "准备重启", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
    
    for attempt in range(REBOOT_RETRY):
        # 检查是否仍在处理中
        if ip in device_status and not device_status[ip].get("in_progress", True):
            msg = f"【{version}】设备 {ip} 的处理已被取消，终止重启"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            return False
            
        try:
            result = subprocess.run(
                ["adb", "-s", f"{ip}:{PORT}", "reboot"],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=False,
                timeout=20  # 缩短超时时间
            )
            
            # 检查是否是ADB连接错误
            if "error: device offline" in result.stderr or "error: device not found" in result.stderr:
                msg = f"【{version}】ADB连接错误: 设备 {ip} 已离线或未找到"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
            
            if result.returncode == 0:
                msg = f"【{version}】重启命令已发送到设备 {ip}"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                status_queue.put((ip, "重启中", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                
                msg = f"【{version}】等待 {REBOOT_WAIT} 秒让设备完成重启..."
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                
                # 等待过程中检查是否需要取消
                for _ in range(REBOOT_WAIT):
                    if ip in device_status and not device_status[ip].get("in_progress", True):
                        msg = f"【{version}】设备 {ip} 的处理已被取消，终止等待重启"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        return False
                    time.sleep(1)
                    
                return True
            else:
                msg = f"【{version}】重启命令执行失败 (返回码 {result.returncode})"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                error_msg = result.stderr if result.stderr else "无详细错误信息"
                logging.error(f"错误信息：{error_msg}")
                ui.root.after(0, lambda: ui.update_log(f"错误信息：{error_msg}"))
                
        except Exception as e:
            # 检查是否是连接相关的错误
            if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
                msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
            msg = f"【{version}】执行重启命令时发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            
        if attempt < REBOOT_RETRY - 1:
            msg = f"【{version}】重试重启设备 {ip}..."
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            time.sleep(2)  # 缩短重试等待时间
    
    msg = f"【{version}】多次尝试后仍无法重启设备 {ip}"
    logging.error(msg)
    ui.root.after(0, lambda: ui.update_log(msg))
    status_queue.put((ip, "重启失败", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
    return False

def remove_device(ip, ui, reason, version):
    """从设备列表中移除设备并更新UI"""
    msg = f"【{version}】由于{reason}，从设备列表中移除 {ip}"
    logging.info(msg)
    ui.root.after(0, lambda: ui.update_log(msg))
    
    # 从状态字典中移除
    if ip in device_status:
        del device_status[ip]
    
    # 从UI表格中移除
    def remove_from_tree():
        for item in ui.tree.get_children():
            if ui.tree.item(item, "values")[0] == ip:
                ui.tree.delete(item)
                break
    
    ui.root.after(0, remove_from_tree)

def set_device_volume(ip, percent, ui, version):
    """通过模拟遥控器音量+按键，将音量从10调节到80"""
    try:
        # 1. 确认设备连接状态
        if not is_device_connected(ip):
            msg = f"【{version}】设备 {ip} 未连接，尝试重新连接..."
            logging.warning(msg)
            ui.update_log(msg)
            
            # 尝试重新连接设备
            result = subprocess.run(
                ["adb", "connect", f"{ip}:{PORT}"],
                capture_output=True,
                text=True,
                timeout=5  # 缩短超时时间
            )
            
            if "connected to" not in result.stdout:
                msg = f"【{version}】无法连接到设备 {ip}，无法设置音量"
                logging.error(msg)
                ui.update_log(msg)
                return False

        # 2. 计算需要按多少次音量+（从10到80需要70步）
        target_steps = 70  # 80 - 10 = 70
        network_type = device_status[ip]["network_type"] if ip in device_status else "未知"
        status_queue.put((ip, f"正在调节音量至{percent}%", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        msg = f"【{version}】将通过模拟遥控器音量+键，从初始音量10调节到80（需要按{target_steps}次）"
        logging.info(msg)
        ui.update_log(msg)

        # 3. 先将音量设置为10（确保初始状态一致）
        msg = f"【{version}】设置初始音量为10..."
        logging.info(msg)
        ui.update_log(msg)
        
        # 使用settings命令先设置到10
        subprocess.run(
            ["adb", "-s", f"{ip}:{PORT}", "shell", "settings", "put", "system", "volume_music", "10"],
            capture_output=True, text=True, timeout=5  # 缩短超时时间
        )
        time.sleep(0.5)  # 缩短等待时间

        # 4. 模拟遥控器音量+按键（每次按增加1单位音量）
        success_count = 0
        for i in range(target_steps):
            # 检查是否仍在处理中
            if ip in device_status and not device_status[ip].get("in_progress", True):
                msg = f"【{version}】设备 {ip} 的处理已被取消，终止音量调节"
                logging.info(msg)
                ui.update_log(msg)
                return False
                
            # 发送音量+按键事件（KEYCODE_VOLUME_UP = 24）
            result = subprocess.run(
                ["adb", "-s", f"{ip}:{PORT}", "shell", "input", "keyevent", "24"],
                capture_output=True, text=True, timeout=3  # 缩短超时时间
            )
            
            if result.returncode == 0:
                success_count += 1
                # 每10步更新一次状态
                if (i + 1) % 10 == 0:
                    current_vol = 10 + i + 1
                    progress = int((current_vol / 80) * 100)
                    status_queue.put((ip, f"音量调节中: {current_vol}/80", f"{progress}%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                    msg = f"【{version}】已按音量+键 {i + 1}/{target_steps} 次，当前音量约为 {current_vol}"
                    logging.info(msg)
                    ui.update_log(msg)
            else:
                msg = f"【{version}】第 {i + 1} 次音量+键发送失败"
                logging.warning(msg)
                ui.update_log(msg)
            
            # 更短的延迟，加速音量调节
            time.sleep(0.1)

        # 5. 验证最终音量
        result_get = subprocess.run(
            ["adb", "-s", f"{ip}:{PORT}", "shell", "settings", "get", "system", "volume_music"],
            capture_output=True, text=True, timeout=5  # 缩短超时时间
        )
        
        final_volume = result_get.stdout.strip()
        msg = f"【{version}】音量调节完成，实际音量: {final_volume}/80"
        logging.info(msg)
        ui.update_log(msg)
        
        # 检查是否接近目标值（允许±2的误差）
        try:
            if 78 <= int(final_volume) <= 82:
                status_queue.put((ip, f"音量已设为{percent}%", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                return True
            else:
                status_queue.put((ip, f"音量调节不准确({final_volume}/80)", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                return False
        except:
            status_queue.put((ip, "音量验证失败", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
            return False

    except Exception as e:
        msg = f"【{version}】设置设备 {ip} 音量时发生错误: {str(e)}"
        logging.error(msg)
        ui.update_log(msg)
        status_queue.put((ip, "音量设置失败", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        return False

def install_apks(ip, ui, network_type, version):
    """安装指定版本文件夹中的APK文件 - 在安装前自动设置音量"""
    try:
        # 先设置设备音量为80%，然后再安装APK
        msg = f"【{version}】在安装APK前，先设置设备 {ip} 的音量为{TARGET_VOLUME_PERCENT}%"
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        
        # 设置音量，如果失败则记录警告但继续安装流程
        volume_success = set_device_volume(ip, TARGET_VOLUME_PERCENT, ui, version)
        if not volume_success:
            msg = f"【{version}】设备 {ip} 音量设置失败，但将继续执行APK安装"
            logging.warning(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
        
        # 获取当前版本对应的APK文件夹
        apk_folder = VERSION_CONFIG[version]
        
        # 检查是否仍在处理中
        if ip in device_status and not device_status[ip].get("in_progress", True):
            msg = f"【{version}】设备 {ip} 的处理已被取消，终止安装"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            return False
            
        msg = f"【{version}】开始为设备 {ip} 安装APK..."
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        status_queue.put((ip, "准备安装", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        
        try:
            # 读取版本对应文件夹中的APK文件
            apk_files = [
                os.path.join(apk_folder, f) 
                for f in os.listdir(apk_folder) 
                if f.lower().endswith('.apk')
            ]
        except Exception as e:
            msg = f"【{version}】获取文件列表时发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "获取文件列表失败", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
            return False
        
        apk_files.sort(key=lambda x: os.path.getsize(x), reverse=True)
        
        if not apk_files:
            msg = f"【{version}】文件夹中未找到APK文件，跳过安装步骤"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "无APK文件", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
            return True
        
        # 排除特定APK
        apk_files = [apk for apk in apk_files if os.path.basename(apk).upper() != "DBZM.APK"]
        total_apks = len(apk_files)
        
        if total_apks == 0:
            msg = f"【{version}】文件夹中所有APK文件都被排除，跳过安装步骤"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "无可用APK文件", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
            return True
        
        # 区分大小APK
        small_apks = [apk for apk in apk_files if os.path.getsize(apk) < 50 * 1024 * 1024]  
        large_apks = [apk for apk in apk_files if os.path.getsize(apk) >= 50 * 1024 * 1024]  
        
        all_installed_successfully = True
        current_apk = 0
        
        # 安装大型APK
        for apk in large_apks:
            # 检查设备是否已被移除
            if ip not in device_status:
                msg = f"【{version}】设备 {ip} 已被移除，终止安装"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return False
                
            current_apk += 1
            if not install_apk_with_retry(ip, apk, ui, total_apks, current_apk, network_type, version):
                # 检查是否是因为连接错误被移除
                if ip not in device_status:
                    return False
                    
                msg = f"【{version}】大型文件安装失败：{apk}"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                all_installed_successfully = False
        
        # 并行安装小型APK（增加并行数）
        if small_apks:
            msg = f"【{version}】开始并行安装 {len(small_apks)} 个小型APK"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            
            with ThreadPoolExecutor(max_workers=8) as executor:  # 增加并行数
                futures = {}
                for apk in small_apks:
                    current_apk += 1
                    futures[executor.submit(install_apk_with_retry, ip, apk, ui, total_apks, current_apk, network_type, version)] = apk
                    
                for future in as_completed(futures):
                    # 检查设备是否已被移除
                    if ip not in device_status:
                        msg = f"【{version}】设备 {ip} 已被移除，终止安装"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        return False
                        
                    # 检查是否仍在处理中
                    if not device_status[ip].get("in_progress", True):
                        msg = f"【{version}】设备 {ip} 的处理已被取消，终止安装"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        return False
                        
                    apk = futures[future]
                    try:
                        if not future.result():
                            # 检查是否是因为连接错误被移除
                            if ip not in device_status:
                                return False
                                
                            msg = f"【{version}】小型APK安装失败：{apk}"
                            logging.error(msg)
                            ui.root.after(0, lambda: ui.update_log(msg))
                            all_installed_successfully = False
                    except Exception as e:
                        # 检查是否是因为连接错误被移除
                        if ip not in device_status:
                            return False
                            
                        msg = f"【{version}】处理小型APK {apk} 时发生错误: {str(e)}"
                        logging.error(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        all_installed_successfully = False
        
        # 卸载特定应用
        try:
            # 检查设备是否已被移除
            if ip not in device_status:
                msg = f"【{version}】设备 {ip} 已被移除，终止卸载操作"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return False
                
            # 检查是否仍在处理中
            if not device_status[ip].get("in_progress", True):
                msg = f"【{version}】设备 {ip} 的处理已被取消，终止卸载操作"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return False
                
            result = subprocess.run(
                ["adb", "-s", f"{ip}:{PORT}", "shell", "pm", "uninstall", "--user", "0", "com.xiaomi.mitv.upgrade"],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=False,
                timeout=20  # 缩短超时时间
            )
            
            # 检查是否是ADB连接错误
            if "error: device offline" in result.stderr or "error: device not found" in result.stderr:
                msg = f"【{version}】ADB连接错误: 设备 {ip} 已离线或未找到"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
                
        except Exception as e:
            # 检查是否是连接相关的错误
            if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
                msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
                
            msg = f"【{version}】卸载系统升级应用时发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
        
        # 同步数据
        try:
            # 检查设备是否已被移除
            if ip not in device_status:
                msg = f"【{version}】设备 {ip} 已被移除，终止同步操作"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                return False
                
            msg = f"【{version}】强制同步数据到存储..."
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "同步数据", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
            
            result = subprocess.run(
                ["adb", "-s", f"{ip}:{PORT}", "shell", "sync"],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=False,
                timeout=20  # 缩短超时时间
            )
            
            # 检查是否是ADB连接错误
            if "error: device offline" in result.stderr or "error: device not found" in result.stderr:
                msg = f"【{version}】ADB连接错误: 设备 {ip} 已离线或未找到"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
                
            time.sleep(1)  # 缩短等待时间
        except Exception as e:
            # 检查是否是连接相关的错误
            if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
                msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return False
                
            msg = f"【{version}】执行同步命令时发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            
        if all_installed_successfully:
            status_queue.put((ip, "安装完成", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        else:
            status_queue.put((ip, "安装部分失败", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
            
        return all_installed_successfully
            
    except Exception as e:
        # 检查是否是连接相关的错误
        if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
            msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            # 标记为连接错误并从设备列表中移除
            remove_device(ip, ui, "ADB连接错误", version)
            return False
            
        msg = f"【{version}】安装APK过程中发生严重错误: {str(e)}"
        logging.error(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        status_queue.put((ip, "安装错误", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
        return False

def process_device(ip, ui, network_type, version):
    """处理发现的设备（增加版本参数，修复失败后状态残留问题）"""
    try:
        # 增加总安装设备计数
        global installation_stats
        installation_stats[version]["total"] += 1
        
        # 标记设备为正在处理中（初始化状态）
        status_queue.put((ip, "准备处理", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        
        # 处理前强制检查设备是否真的在线，避免残留离线设备
        if not is_device_connected(ip):
            # 尝试重新连接3次，确认设备是否可用
            reconnect_success = False
            for _ in range(3):
                result = subprocess.run(
                    ["adb", "connect", f"{ip}:{PORT}"],
                    capture_output=True, text=True, timeout=3  # 缩短超时时间
                )
                if "connected to" in result.stdout:
                    reconnect_success = True
                    break
                time.sleep(0.5)  # 缩短等待时间
            if not reconnect_success:
                msg = f"【{version}】设备 {ip} 离线且无法重连，跳过处理"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为“未处理”，允许下次扫描重新识别
                status_queue.put((ip, "设备离线", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
                installation_stats[version]["failed"] += 1
                return

        if is_device_connected(ip):
            msg = f"【{version}】设备 {ip} 已连接，跳过连接步骤"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "已连接", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
        else:
            msg = f"【{version}】正在尝试连接到设备：{ip}"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "连接中", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
            
            connect_success = False
            for _ in range(3):
                # 检查是否仍在处理中
                if ip in device_status and not device_status[ip].get("in_progress", True):
                    msg = f"【{version}】设备 {ip} 的处理已被取消，终止连接"
                    logging.info(msg)
                    ui.root.after(0, lambda: ui.update_log(msg))
                    return
                    
                try:
                    result = subprocess.run(
                        ["adb", "connect", f"{ip}:{PORT}"],
                        capture_output=True,
                        text=True,
                        encoding='utf-8',
                        errors='ignore',
                        check=False,
                        timeout=5  # 缩短超时时间
                    )
                    
                    if "connected to" in result.stdout:
                        msg = f"【{version}】设备 {ip} 已连接成功"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        status_queue.put((ip, "连接成功", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), True, network_type, version))
                        connect_success = True
                        break
                    else:
                        msg = f"【{version}】设备 {ip} 连接失败，重试..."
                        logging.warning(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        time.sleep(1)  # 缩短等待时间
                except Exception as e:
                    msg = f"【{version}】连接设备时发生错误: {str(e)}"
                    logging.error(msg)
                    ui.root.after(0, lambda: ui.update_log(msg))
                    time.sleep(1)  # 缩短等待时间
            
            if not connect_success:
                msg = f"【{version}】设备 {ip} 连接失败，放弃处理"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                status_queue.put((ip, "连接失败", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
                # 更新失败计数
                installation_stats[version]["failed"] += 1
                return
        
        # 等待授权（增加版本参数）
        if not wait_for_authorization(ip, ui, network_type, version):
            # 检查设备是否已被移除
            if ip not in device_status:
                # 更新失败计数
                installation_stats[version]["failed"] += 1
                return
                
            # 标记为处理完成
            status_queue.put((ip, device_status[ip]["status"], device_status[ip]["progress"], 
                             time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
            # 更新失败计数
            installation_stats[version]["failed"] += 1
            return
        
        # 执行安装并等待结果反馈（增加版本参数）
        installation_success = install_apks(ip, ui, network_type, version)
        
        # 检查设备是否已被移除
        if ip not in device_status:
            # 根据安装结果更新计数
            if installation_success:
                installation_stats[version]["success"] += 1
            else:
                installation_stats[version]["failed"] += 1
            return
        
        # 只有安装完全成功才执行重启
        if installation_success:
            msg = f"【{version}】所有APK安装成功，准备重启设备..."
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            
            reboot_success = reboot_device(ip, ui, network_type, version)
            
            # 检查设备是否已被移除
            if ip not in device_status:
                # 根据重启结果更新计数
                if reboot_success:
                    installation_stats[version]["success"] += 1
                else:
                    installation_stats[version]["failed"] += 1
                return
                
            if reboot_success:
                msg = f"【{version}】设备 {ip} 重启成功"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                status_queue.put((ip, "重启成功", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
                # 更新成功计数
                installation_stats[version]["success"] += 1
            else:
                msg = f"【{version}】设备 {ip} 重启失败"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 更新失败计数
                installation_stats[version]["failed"] += 1
        else:
            msg = f"【{version}】APK安装未完全成功，不执行重启"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "安装未完成", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
            # 更新失败计数
            installation_stats[version]["failed"] += 1
        
        # 断开连接
        try:
            # 检查设备是否已被移除
            if ip not in device_status:
                return
                
            result = subprocess.run(
                ["adb", "-s", f"{ip}:{PORT}", "disconnect"],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='ignore',
                check=False,
                timeout=5  # 缩短超时时间
            )
            
            # 检查是否是ADB连接错误
            if "error: device offline" in result.stderr or "error: device not found" in result.stderr:
                msg = f"【{version}】ADB连接错误: 设备 {ip} 已离线或未找到"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return
                
            msg = f"【{version}】已断开与设备 {ip} 的连接"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            status_queue.put((ip, "已断开连接", "100%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
        except Exception as e:
            # 检查是否是连接相关的错误
            if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
                msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
                logging.error(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                # 标记为连接错误并从设备列表中移除
                remove_device(ip, ui, "ADB连接错误", version)
                return
                
            msg = f"【{version}】断开设备连接时发生错误: {str(e)}"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            
    except Exception as e:
        # 检查是否是连接相关的错误
        if "Connection reset by peer" in str(e) or "Broken pipe" in str(e):
            msg = f"【{version}】ADB连接错误: 与设备 {ip} 的连接已断开"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            # 标记为连接错误并从设备列表中移除
            remove_device(ip, ui, "ADB连接错误", version)
            # 更新失败计数
            installation_stats[version]["failed"] += 1
            return
            
        msg = f"【{version}】处理设备 {ip} 时发生严重错误: {str(e)}"
        logging.error(msg)
        ui.root.after(0, lambda: ui.update_log(msg))
        status_queue.put((ip, "处理错误", "0%", time.strftime("%Y-%m-%d %H:%M:%S"), False, network_type, version))
        # 异常时强制标记为“未处理”，避免状态残留
        if ip in device_status:
            device_status[ip]["in_progress"] = False
        # 更新失败计数
        installation_stats[version]["failed"] += 1
    finally:
        # 无论成功/失败/异常，最终强制重置为“未处理”状态
        if ip in device_status:
            device_status[ip]["in_progress"] = False
            status_queue.put((
                ip, 
                device_status[ip]["status"], 
                device_status[ip]["progress"], 
                time.strftime("%Y-%m-%d %H:%M:%S"), 
                False,  # 强制设为“未处理”
                network_type, 
                version
            ))

def scan_adb(ip, found_devices, network_type):
    """扫描ADB端口"""
    # 检查是否需要跳过最近扫描过的IP
    global recently_scanned_ips
    current_time = time.time()
    
    # 清理过期的记录
    to_remove = [ip for ip, timestamp in recently_scanned_ips.items() if current_time - timestamp > RECENT_SCAN_WINDOW]
    for ip in to_remove:
        del recently_scanned_ips[ip]
    
    # 如果启用了跳过最近扫描过的IP，且该IP在最近扫描窗口内，则跳过
    if SKIP_RECENTLY_SCANNED and ip in recently_scanned_ips:
        return
        
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.settimeout(TIMEOUT)
        try:
            s.connect((ip, PORT))
            s.close()
            msg = f"[+] 发现{network_type}ADB设备: {ip}"
            logging.info(msg)
            found_devices.append((ip, network_type))
            # 记录扫描时间
            recently_scanned_ips[ip] = current_time
        except (socket.timeout, ConnectionRefusedError):
            # 记录扫描时间，避免短时间内重复扫描
            recently_scanned_ips[ip] = current_time
            pass
        except Exception as e:
            logging.debug(f"扫描 {ip} 时发生错误: {str(e)}")
        finally:
            s.close()
    except Exception as e:
        logging.error(f"创建扫描socket时发生错误: {str(e)}")

def start_real_time_monitor(ui, version):
    """实时监控ADB设备连接状态"""
    try:
        # 使用adb monitor命令监听设备连接事件
        process = subprocess.Popen(
            ["adb", "monitor"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding='utf-8',
            errors='ignore'
        )
        
        # 已处理的设备IP集合，避免重复处理
        processed_ips = set()
        
        for line in process.stdout:
            # 如果扫描已停止，退出监控
            if not ui.scanning:
                process.terminate()
                return
                
            # 检测设备连接事件
            if "Device connected" in line or "New device" in line:
                # 提取IP地址（简化版，实际可能需要更复杂的正则）
                ip_match = re.search(r"\b(?:\d{1,3}\.){3}\d{1,3}\b", line)
                if ip_match:
                    ip = ip_match.group()
                    # 检查是否是新设备
                    if ip not in processed_ips and ip not in device_status:
                        processed_ips.add(ip)
                        msg = f"\n【{version}】实时检测到新设备：{ip}"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                        
                        # 立即处理该设备
                        network_type = "未知"  # 实际应用中可以尝试识别网络类型
                        ui.root.after(0, lambda: threading.Thread(
                            target=process_device, 
                            args=(ip, ui, network_type, version), 
                            daemon=True
                        ).start())
            
            # 限制已处理设备数量，防止内存占用过大
            if len(processed_ips) > 1000:
                processed_ips.clear()
                
    except Exception as e:
        msg = f"【{version}】实时监控线程错误: {str(e)}"
        logging.error(msg)
        ui.root.after(0, lambda: ui.update_log(msg))

def clean_offline_devices(ui, version):
    """定期清理设备状态字典中的离线设备，避免残留"""
    offline_ips = []
    for ip in list(device_status.keys()):
        if not is_device_connected(ip):
            offline_ips.append(ip)
            msg = f"【{version}】清理离线设备: {ip}"
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            # 从UI表格中移除
            def remove_from_tree(ip=ip):
                for item in ui.tree.get_children():
                    if ui.tree.item(item, "values")[0] == ip:
                        ui.tree.delete(item)
                        break
            ui.root.after(0, remove_from_tree)
    # 从状态字典中删除离线设备
    for ip in offline_ips:
        if ip in device_status:
            del device_status[ip]

def scan_and_process(ui, scan_wired=True, scan_wireless=True, version="国内版"):
    """扫描并处理发现的ADB设备（修复失败设备不重新处理问题）"""
    try:
        # 获取有效网络IP，根据设置决定扫描类型
        all_ips, network_ips = get_network_ips(scan_wired, scan_wireless)
        
        if not all_ips:
            msg = f"【{version}】未能获取到任何有效网络IP，无法扫描"
            logging.error(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            return

        all_found_devices = []

        # 先处理有线网络
        if scan_wired and network_ips['wired']:
            for local_ip in network_ips['wired']:
                prefix = get_network_prefix(local_ip)
                msg = f"\n=== 【{version}】开始扫描有线网卡 {local_ip} ==="
                logging.info(msg)
                # 根据配置决定是否显示详细扫描日志
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】扫描网段: {prefix}0/24"
                logging.info(msg)
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))

                found_devices = []
                # 分块扫描，避免一次性创建过多线程
                for i in range(0, 255, SCAN_BLOCK_SIZE):
                    if not ui.scanning:  # 检查是否已停止扫描
                        break
                        
                    end = min(i + SCAN_BLOCK_SIZE, 255)
                    with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
                        futures = {executor.submit(scan_adb, f"{prefix}{j}", found_devices, "有线"): j 
                                  for j in range(i, end)}
                        
                        for future in as_completed(futures):
                            try:
                                future.result()
                            except Exception as e:
                                ip = f"{prefix}{futures[future]}"
                                msg = f"【{version}】扫描 {ip} 时线程发生错误: {str(e)}"
                                logging.error(msg)
                                ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】有线网段 {prefix} 扫描完成，发现 {len(found_devices)} 个ADB设备"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                all_found_devices.extend(found_devices)
                time.sleep(SCAN_BATCH_DELAY)  # 批次间短暂延迟

        # 再处理无线网络
        if scan_wireless and network_ips['wireless']:
            for local_ip in network_ips['wireless']:
                prefix = get_network_prefix(local_ip)
                msg = f"\n=== 【{version}】开始扫描无线网卡 {local_ip} ==="
                logging.info(msg)
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】扫描网段: {prefix}0/24"
                logging.info(msg)
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))

                found_devices = []
                # 分块扫描，避免一次性创建过多线程
                for i in range(0, 255, SCAN_BLOCK_SIZE):
                    if not ui.scanning:  # 检查是否已停止扫描
                        break
                        
                    end = min(i + SCAN_BLOCK_SIZE, 255)
                    with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
                        futures = {executor.submit(scan_adb, f"{prefix}{j}", found_devices, "无线"): j 
                                  for j in range(i, end)}
                        
                        for future in as_completed(futures):
                            try:
                                future.result()
                            except Exception as e:
                                ip = f"{prefix}{futures[future]}"
                                msg = f"【{version}】扫描 {ip} 时线程发生错误: {str(e)}"
                                logging.error(msg)
                                ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】无线网段 {prefix} 扫描完成，发现 {len(found_devices)} 个ADB设备"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                all_found_devices.extend(found_devices)
                time.sleep(SCAN_BATCH_DELAY)  # 批次间短暂延迟

        # 最后处理未知类型网络
        if network_ips['unknown']:
            for local_ip in network_ips['unknown']:
                prefix = get_network_prefix(local_ip)
                msg = f"\n=== 【{version}】开始扫描未知类型网卡 {local_ip} ==="
                logging.info(msg)
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】扫描网段: {prefix}0/24"
                logging.info(msg)
                if SHOW_SCAN_DETAILS:
                    ui.root.after(0, lambda: ui.update_log(msg))

                found_devices = []
                # 分块扫描，避免一次性创建过多线程
                for i in range(0, 255, SCAN_BLOCK_SIZE):
                    if not ui.scanning:  # 检查是否已停止扫描
                        break
                        
                    end = min(i + SCAN_BLOCK_SIZE, 255)
                    with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
                        futures = {executor.submit(scan_adb, f"{prefix}{j}", found_devices, "未知"): j 
                                  for j in range(i, end)}
                        
                        for future in as_completed(futures):
                            try:
                                future.result()
                            except Exception as e:
                                ip = f"{prefix}{futures[future]}"
                                msg = f"【{version}】扫描 {ip} 时线程发生错误: {str(e)}"
                                logging.error(msg)
                                ui.root.after(0, lambda: ui.update_log(msg))
                
                msg = f"【{version}】未知类型网段 {prefix} 扫描完成，发现 {len(found_devices)} 个ADB设备"
                logging.info(msg)
                ui.root.after(0, lambda: ui.update_log(msg))
                all_found_devices.extend(found_devices)
                time.sleep(SCAN_BATCH_DELAY)  # 批次间短暂延迟

        # 去重设备列表（按IP去重）
        unique_devices = {}
        for device in all_found_devices:
            ip, network_type = device
            if ip not in unique_devices:
                unique_devices[ip] = network_type
        
        # 转换回列表形式
        all_unique_devices = [(ip, network_type) for ip, network_type in unique_devices.items()]
        
        # 优化可处理设备检测逻辑
        devices_to_process = []
        for ip, network_type in all_unique_devices:
            # 检查设备是否已在处理中
            is_in_progress = device_status[ip].get("in_progress", False) if ip in device_status else False
            
            # 即使设备标记为处理中，也检查是否真的在线
            if is_in_progress:
                if not is_device_connected(ip):
                    msg = f"【{version}】设备 {ip} 标记为处理中但已离线，重置状态并重新处理"
                    logging.info(msg)
                    ui.root.after(0, lambda: ui.update_log(msg))
                    # 重置状态为“未处理”
                    if ip in device_status:
                        device_status[ip]["in_progress"] = False
                    devices_to_process.append((ip, network_type))
                else:
                    msg = f"【{version}】设备 {ip} 正在处理中，跳过本次扫描处理"
                    logging.info(msg)
                    if SHOW_SCAN_DETAILS:
                        ui.root.after(0, lambda: ui.update_log(msg))
            else:
                # 对于未处理的设备，先尝试重新连接
                connect_success = False
                if not is_device_connected(ip):
                    msg = f"【{version}】设备 {ip} 未连接，尝试重新连接..."
                    logging.info(msg)
                    ui.root.after(0, lambda: ui.update_log(msg))
                    
                    # 尝试重新连接
                    result = subprocess.run(
                        ["adb", "connect", f"{ip}:{PORT}"],
                        capture_output=True, text=True, timeout=5  # 缩短超时时间
                    )
                    
                    if "connected to" in result.stdout:
                        connect_success = True
                        msg = f"【{version}】设备 {ip} 重新连接成功"
                        logging.info(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                    else:
                        msg = f"【{version}】设备 {ip} 重新连接失败"
                        logging.warning(msg)
                        ui.root.after(0, lambda: ui.update_log(msg))
                else:
                    connect_success = True
                
                # 如果连接成功，加入处理列表
                if connect_success:
                    devices_to_process.append((ip, network_type))
                else:
                    msg = f"【{version}】设备 {ip} 连接失败，无法处理"
                    logging.debug(msg)
        
        msg = f"\n【{version}】总共发现 {len(all_unique_devices)} 个ADB设备，其中 {len(devices_to_process)} 个可处理"
        logging.info(msg)
        ui.root.after(0, lambda: ui.update_log(msg))

        # 处理每个发现的设备（增加版本参数）
        for ip, network_type in devices_to_process:
            msg = f"\n=== 【{version}】开始处理{network_type}设备 {ip} ==="
            logging.info(msg)
            ui.root.after(0, lambda: ui.update_log(msg))
            # 为每个设备创建单独的处理线程
            threading.Thread(target=process_device, args=(ip, ui, network_type, version), daemon=True).start()
            time.sleep(0.2)  # 更短的延迟，加速处理队列

    except Exception as e:
        msg = f"【{version}】扫描和处理设备时发生严重错误: {str(e)}"
        logging.error(msg)
        ui.root.after(0, lambda: ui.update_log(msg))

def main():
    # 隐藏控制台窗口的代码（在Windows上有效）
    try:
        import ctypes
        ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(), 0)
    except:
        pass
        
    root = tk.Tk()
    app = DeviceMonitorUI(root)
    
    # 启动设备状态更新线程
    app.update_device_status()
    
    # 启动统计信息更新线程
    app.update_stats_display()
    
    # 显示初始信息
    msg = "ADB设备自动扫描与安装工具（支持国内版/全球版）"
    logging.info(msg)
    app.update_log(msg)
    
    msg = f"将每 {SCAN_INTERVAL} 秒扫描一次局域网，安装前会自动将设备音量设置为{TARGET_VOLUME_PERCENT}%"
    logging.info(msg)
    app.update_log(msg)
    
    msg = "请先在当前目录创建「国内版」和「全球版」文件夹并放入对应APK"
    logging.info(msg)
    app.update_log(msg)
    
    msg = "点击对应版本的扫描按钮开始操作\n"
    logging.info(msg)
    app.update_log(msg)
    
    root.mainloop()

if __name__ == "__main__":
    main()
