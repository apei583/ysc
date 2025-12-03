import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import subprocess
import os
import glob
import threading
import time
import socket
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from threading import Semaphore
import configparser
import json


class ADBInstaller:
    def __init__(self, root):
        self.root = root
        self.root.title("ADB批量安装工具")
        self.root.geometry("1100x700")
        self.root.resizable(True, True)

        # 初始化变量（紧凑化）
        self.cn_install_count = self.global_install_count = self.custom_install_count = 0
        self.volume_press_count = tk.IntVar(value=70)
        self.concurrent_devices = tk.IntVar(value=5)
        self.running = self.scanning = False
        self.processing_devices = set()
        self.completed_devices = set()
        self.devices = {}
        self.current_mode = self.custom_apk_path = None
        self.device_semaphore = Semaphore(self.concurrent_devices.get())
        
        # 配置加载
        self.config = configparser.ConfigParser()
        self.load_config()

        # UI样式配置
        style = ttk.Style()
        for w in ["TButton", "TLabel", "Treeview", "Treeview.Heading"]:
            style.configure(w, font=("SimHei", 10, "bold") if "Heading" in w else ("SimHei", 10))

        self.create_widgets()
        self.check_adb_available()

    def load_config(self):
        if os.path.exists("adb_config.ini"):
            self.config.read("adb_config.ini")
            self.volume_press_count.set(self.config.getint("DEFAULT", "volume_count", fallback=70))
            self.concurrent_devices.set(self.config.getint("DEFAULT", "concurrent", fallback=5))

    def save_config(self):
        self.config["DEFAULT"] = {"volume_count": self.volume_press_count.get(), "concurrent": self.concurrent_devices.get()}
        with open("adb_config.ini", "w") as f:
            self.config.write(f)

    def create_widgets(self):
        # 顶部框架
        btn_frame = ttk.Frame(self.root, padding="10")
        btn_frame.pack(fill=tk.X)

        # 安装模式单选框
        mode_frame = ttk.LabelFrame(btn_frame, text="安装模式", padding="5")
        mode_frame.pack(side=tk.LEFT, padx=5)
        self.install_mode = tk.StringVar(value="国内版")
        for i, mode in enumerate(["国内版", "全球版", "自定义APK"]):
            ttk.Radiobutton(mode_frame, text=mode, variable=self.install_mode, value=mode, command=self.on_mode_change).grid(row=0, column=i, padx=5)

        # 自定义APK选择
        apk_frame = ttk.Frame(btn_frame)
        apk_frame.pack(side=tk.LEFT, padx=10)
        self.select_apk_btn = ttk.Button(apk_frame, text="选择APK文件", command=self.select_custom_apk, state=tk.DISABLED)
        self.select_apk_btn.pack(side=tk.LEFT)
        self.apk_path_var = tk.StringVar(value="未选择APK")
        ttk.Label(apk_frame, textvariable=self.apk_path_var).pack(side=tk.LEFT, padx=5)

        # 音量和并发设置
        ttk.Label(btn_frame, text="音量+次数:").pack(side=tk.LEFT)
        vol_entry = ttk.Entry(btn_frame, textvariable=self.volume_press_count, width=5)
        vol_entry.pack(side=tk.LEFT, padx=5)
        vol_entry.bind("<FocusOut>", lambda e: self.save_config())

        ttk.Label(btn_frame, text="设备并发数:").pack(side=tk.LEFT, padx=(20, 5))
        concur_cb = ttk.Combobox(btn_frame, textvariable=self.concurrent_devices, values=[2,3,4,5,6,7,8], width=5)
        concur_cb.pack(side=tk.LEFT)
        concur_cb.bind("<<ComboboxSelected>>", lambda e: self.save_config())

        # 控制按钮
        self.start_btn = ttk.Button(btn_frame, text="开始安装", command=self.start_install)
        self.start_btn.pack(side=tk.LEFT, padx=20)
        self.stop_btn = ttk.Button(btn_frame, text="停止", command=self.stop_process, state=tk.DISABLED)
        self.stop_btn.pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="清除日志", command=self.clear_log).pack(side=tk.LEFT, padx=5)

        # 状态显示
        status_frame = ttk.Frame(btn_frame)
        status_frame.pack(side=tk.RIGHT)
        self.current_mode_var = tk.StringVar(value="当前模式: 国内版")
        self.status_var = tk.StringVar(value="就绪")
        ttk.Label(status_frame, textvariable=self.current_mode_var, font=("SimHei", 10, "bold")).pack(side=tk.LEFT, padx=10)
        ttk.Label(status_frame, textvariable=self.status_var, foreground="blue").pack(side=tk.LEFT, padx=10)

        # 安装计数
        count_frame = ttk.Frame(self.root)
        count_frame.pack(fill=tk.X, padx=10, pady=5)
        self.cn_count_var = tk.StringVar(value="国内版已安装: 0台")
        self.global_count_var = tk.StringVar(value="全球版已安装: 0台")
        self.custom_count_var = tk.StringVar(value="自定义APK已安装: 0台")
        for var, color in zip([self.cn_count_var, self.global_count_var, self.custom_count_var], ["#228B22", "#1E90FF", "#FF4500"]):
            ttk.Label(count_frame, textvariable=var, font=("SimHei", 10, "bold"), foreground=color).pack(side=tk.LEFT, padx=10)

        # 设备列表（滚动框架）
        device_frame = ttk.LabelFrame(self.root, text="已发现设备", padding="10")
        device_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        self.device_canvas = tk.Canvas(device_frame)
        scrollbar = ttk.Scrollbar(device_frame, orient="vertical", command=self.device_canvas.yview)
        self.scrollable_frame = ttk.Frame(self.device_canvas)
        self.scrollable_frame.bind("<Configure>", lambda e: self.device_canvas.configure(scrollregion=self.device_canvas.bbox("all")))
        self.device_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.device_canvas.configure(yscrollcommand=scrollbar.set)
        self.device_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        self.device_frames = {}

        # 日志区域
        log_frame = ttk.LabelFrame(self.root, text="操作日志", padding="10")
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        self.log_text = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, font=("SimHei", 10))
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self.log_text.config(state=tk.DISABLED)

        self.on_mode_change()

    def on_mode_change(self):
        mode = self.install_mode.get()
        self.current_mode_var.set(f"当前模式: {mode}")
        if mode == "自定义APK":
            self.select_apk_btn.config(state=tk.NORMAL)
            self.apk_path_label.config(foreground="red") if hasattr(self, 'apk_path_label') else None
        else:
            self.select_apk_btn.config(state=tk.DISABLED)
            self.custom_apk_path = None
            self.apk_path_var.set("未选择APK")

    def select_custom_apk(self):
        path = filedialog.askopenfilename(title="选择APK文件", filetypes=[("APK文件", "*.apk"), ("所有文件", "*.*")])
        if path:
            self.custom_apk_path = path
            self.apk_path_var.set(os.path.basename(path))
            self.log(f"已选择自定义APK: {os.path.basename(path)}")
        else:
            self.custom_apk_path = None
            self.apk_path_var.set("未选择APK")

    def log(self, msg):
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, f"[{datetime.now().strftime('%H:%M:%S')}] {msg}\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)

    def clear_log(self):
        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete(1.0, tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.log("日志已清空")

    def update_install_count(self, version_type):
        if version_type == "国内版":
            self.cn_install_count += 1
            self.cn_count_var.set(f"国内版已安装: {self.cn_install_count}台")
        elif version_type == "全球版":
            self.global_install_count += 1
            self.global_count_var.set(f"全球版已安装: {self.global_install_count}台")
        elif version_type == "自定义APK":
            self.custom_install_count += 1
            self.custom_count_var.set(f"自定义APK已安装: {self.custom_install_count}台")

    def update_device_status(self, device_id, status, progress=0):
        if device_id in self.completed_devices and status != "安装完成":
            return
        self.devices[device_id] = {"status": status, "progress": progress}
        
        if device_id not in self.device_frames:
            frame = ttk.Frame(self.scrollable_frame)
            frame.pack(fill=tk.X, padx=5, pady=2)
            ttk.Label(frame, text=device_id, width=30, anchor="w").pack(side=tk.LEFT, padx=5)
            status_label = ttk.Label(frame, text=status, width=20, anchor="w")
            status_label.pack(side=tk.LEFT, padx=5)
            prog_var = tk.IntVar(value=progress)
            ttk.Progressbar(frame, variable=prog_var, maximum=100, length=250).pack(side=tk.LEFT, padx=5)
            ttk.Label(frame, text=f"{progress}%", width=8).pack(side=tk.LEFT, padx=5)
            self.device_frames[device_id] = {"frame": frame, "status_label": status_label, "prog_var": prog_var}
        else:
            frame_data = self.device_frames[device_id]
            frame_data["status_label"].config(text=status)
            frame_data["prog_var"].set(progress)
            frame_data["frame"].children["!label3"].config(text=f"{progress}%")

    def get_active_network_info(self):
        if os.name == 'nt':
            try:
                # WiFi检测（PowerShell）
                ps_wifi = '''Get-NetAdapter | Where-Object { $_.Status -eq 'Up' -and $_.InterfaceType -eq 71 } | ForEach-Object { $ip=(Get-NetIPAddress -InterfaceAlias $_.Name -AddressFamily IPv4 | Select-Object -First 1).IPAddress; if($ip){[PSCustomObject]@{Type='WiFi';IP=$ip} | ConvertTo-Json}}'''
                wifi_res = subprocess.run(["powershell", "-Command", ps_wifi], capture_output=True, text=True, timeout=10)
                if wifi_res.stdout.strip():
                    wifi_data = json.loads(wifi_res.stdout.strip())
                    prefix = ".".join(wifi_data["IP"].split(".")[:-1]) + "."
                    self.log(f"✅ WiFi已连接: IP={wifi_data['IP']}, 网段={prefix}")
                    return "WiFi", prefix

                # 以太网检测
                ps_eth = '''Get-NetAdapter | Where-Object { $_.Status -eq 'Up' -and $_.InterfaceType -eq 6 } | ForEach-Object { $ip=(Get-NetIPAddress -InterfaceAlias $_.Name -AddressFamily IPv4 | Select-Object -First 1).IPAddress; if($ip){[PSCustomObject]@{Type='以太网';IP=$ip} | ConvertTo-Json}}'''
                eth_res = subprocess.run(["powershell", "-Command", ps_eth], capture_output=True, text=True, timeout=10)
                if eth_res.stdout.strip():
                    eth_data = json.loads(eth_res.stdout.strip())
                    prefix = ".".join(eth_data["IP"].split(".")[:-1]) + "."
                    self.log(f"✅ 以太网已连接: IP={eth_data['IP']}, 网段={prefix}")
                    return "以太网", prefix
            except Exception as e:
                self.log(f"网络检测异常: {str(e)}")

        # 兜底方案
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("223.5.5.5", 53))
            local_ip = s.getsockname()[0]
            s.close()
            wifi_subs = ["192.168.0.", "192.168.1.", "192.168.10.", "192.168.31.", "192.168.100.", "10.0."]
            net_type = "WiFi" if any(local_ip.startswith(sub) for sub in wifi_subs) else "以太网"
            prefix = ".".join(local_ip.split(".")[:-1]) + "."
            self.log(f"兜底检测: IP={local_ip}, 判定{net_type}, 网段={prefix}")
            return net_type, prefix
        except:
            return "未知网络", "192.168.31."

    def check_adb_available(self):
        try:
            res = subprocess.run(["adb", "version"], capture_output=True, text=True, timeout=5)
            if res.returncode == 0:
                self.log("ADB已就绪")
                return True
            raise Exception("ADB未找到（需添加到系统PATH）")
        except Exception as e:
            self.log(f"ADB检测失败: {str(e)}")
            messagebox.showerror("错误", str(e))
            return False

    def start_install(self):
        if self.running:
            messagebox.showinfo("提示", "操作进行中")
            return
        mode = self.install_mode.get()
        self.current_mode = mode
        self.device_semaphore = Semaphore(self.concurrent_devices.get())

        # 校验参数
        if mode == "自定义APK" and (not self.custom_apk_path or not os.path.exists(self.custom_apk_path)):
            messagebox.showerror("错误", "请选择有效APK文件")
            return
        if mode != "自定义APK" and (not os.path.exists(mode) or not glob.glob(os.path.join(mode, "*.apk"))):
            messagebox.showerror("错误", f"{mode}文件夹无APK文件")
            return
        if not (0 < self.volume_press_count.get() <= 200):
            messagebox.showerror("错误", "音量次数需1-200")
            return

        # 启动流程
        self.running = True
        self.start_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL)
        self.status_var.set("运行中")
        self.completed_devices.clear()
        self.log(f"\n===== 开始{mode}安装流程 =====")
        self.log(f"并发数: {self.concurrent_devices.get()} | 音量次数: {self.volume_press_count.get()}")

        # 清空设备列表
        for did in list(self.device_frames.keys()):
            self.device_frames[did]["frame"].destroy()
            del self.device_frames[did]
        self.devices.clear()
        self.processing_devices.clear()
        threading.Thread(target=self.continuous_scan, daemon=True).start()

    def stop_process(self):
        if not self.running:
            return
        self.log("===== 停止所有操作 =====")
        self.running = self.scanning = False
        self.processing_devices.clear()
        self.completed_devices.clear()
        self.start_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.status_var.set("已停止")

        try:
            subprocess.run(["taskkill", "/f", "/im", "adb.exe"] if os.name == 'nt' else ["pkill", "adb"], capture_output=True, timeout=5)
            self.log("ADB进程已终止")
        except Exception as e:
            self.log(f"终止ADB失败: {str(e)}")

        for did in list(self.device_frames.keys()):
            self.device_frames[did]["frame"].destroy()
            del self.device_frames[did]
        self.devices.clear()
        self.log("===== 操作已停止 =====")

    def scan_single_ip(self, ip):
        if not (self.running and self.scanning):
            return
        try:
            res = subprocess.run(["adb", "connect", f"{ip}:5555"], capture_output=True, text=True, timeout=2)
            if "connected" in res.stdout:
                did = f"{ip}:5555"
                if did not in self.completed_devices and did not in self.processing_devices:
                    self.add_and_process_device(did)
        except:
            pass

    def continuous_scan(self):
        cycle = 1
        while self.running:
            self.log(f"\n===== 第{cycle}轮扫描 =====")
            self.scanning = True
            net_type, prefix = self.get_active_network_info()
            self.log(f"扫描网段: {prefix}1-254:5555")

            # 扫描已连接设备
            try:
                res = subprocess.run(["adb", "devices"], capture_output=True, text=True, timeout=5)
                for line in res.stdout.strip().split("\n")[1:]:
                    if self.running and line.strip() and "device" in line:
                        did = line.split()[0]
                        if did not in self.completed_devices and did not in self.processing_devices:
                            self.add_and_process_device(did)
            except Exception as e:
                self.log(f"扫描已连接设备失败: {str(e)}")

            # 扫描网段
            try:
                with ThreadPoolExecutor(max_workers=20) as ex:
                    ex.map(self.scan_single_ip, [f"{prefix}{i}" for i in range(1, 255)])
            except Exception as e:
                self.log(f"扫描网段失败: {str(e)}")

            self.scanning = False
            self.log(f"第{cycle}轮扫描完成 | 发现{len(self.devices)}设备（已完成{len(self.completed_devices)}）")
            cycle += 1
            for _ in range(20):
                if not self.running:
                    break
                time.sleep(1)
        self.log("扫描已停止")

    def add_and_process_device(self, device_id):
        if not self.running or device_id in self.completed_devices or device_id in self.processing_devices:
            return
        self.update_device_status(device_id, "等待授权", 0)
        self.log(f"发现新设备: {device_id}")
        self.processing_devices.add(device_id)
        threading.Thread(target=self.process_device_with_semaphore, args=(device_id, self.current_mode), daemon=True).start()

    def process_device_with_semaphore(self, device_id, mode):
        with self.device_semaphore:
            self.process_single_device(device_id, mode)

    def is_device_authorized(self, device_id):
        try:
            out = subprocess.run(["adb", "-s", device_id, "devices"], capture_output=True, text=True, timeout=3).stdout
            return f"{device_id}\tdevice" in out
        except:
            return False

    def wait_for_authorization(self, device_id):
        self.update_device_status(device_id, "等待授权", 0)
        start = time.time()
        while self.running and device_id not in self.completed_devices:
            if time.time() - start > 120:
                self.update_device_status(device_id, "授权超时", 0)
                self.log(f"设备{device_id}授权超时")
                self.processing_devices.discard(device_id)
                return False
            if self.is_device_authorized(device_id):
                self.update_device_status(device_id, "已授权", 10)
                self.log(f"设备{device_id}已授权")
                return True
            time.sleep(2)
        return False

    def set_volume(self, device_id):
        if not (self.running and device_id not in self.completed_devices):
            return False
        count = self.volume_press_count.get()
        self.update_device_status(device_id, "调整音量", 20)
        self.log(f"调整设备{device_id}音量: {count}次+按键")
        try:
            for i in range(count):
                if not self.running:
                    return False
                subprocess.run(["adb", "-s", device_id, "shell", "input", "keyevent", "24"], capture_output=True, timeout=1)
                self.update_device_status(device_id, "调整音量", 20 + int(10*(i+1)/count))
                time.sleep(0.05)
            self.update_device_status(device_id, "音量调整完成", 30)
            return True
        except Exception as e:
            self.log(f"音量调整失败: {str(e)}")
            return False

    def install_apks(self, device_id, mode):
        if not (self.running and device_id not in self.completed_devices):
            return False
        apk_list = [self.custom_apk_path] if mode == "自定义APK" else sorted(glob.glob(os.path.join(mode, "*.apk")), key=os.path.getsize, reverse=True)
        if not apk_list:
            self.log(f"设备{device_id}无APK可安装")
            return False

        total = len(apk_list)
        for i, apk in enumerate(apk_list):
            if not self.running:
                return False
            name = os.path.basename(apk)
            prog = 30 + int(50*(i+1)/total)
            self.update_device_status(device_id, f"安装{name}", prog)
            self.log(f"[{device_id}] 安装{i+1}/{total}: {name}")

            try:
                proc = subprocess.Popen(["adb", "-s", device_id, "install", "-r", apk], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                success = False
                err_msg = ""
                for line in proc.stdout:
                    if not self.running:
                        proc.kill()
                        return False
                    line = line.strip()
                    if line:
                        self.log(f"[{device_id}] {line}")
                        if "Failure" in line:
                            err_msg = line
                    if "Success" in line:
                        success = True
                        break
                proc.wait(timeout=300)
                if not success:
                    self.log(f"[{device_id}] {name}安装失败: {err_msg or proc.returncode}")
                    self.update_device_status(device_id, f"安装失败: {name}", prog)
                    return False
            except Exception as e:
                self.log(f"[{device_id}] 安装{name}异常: {str(e)}")
                return False

        self.update_device_status(device_id, "APK安装完成", 80)
        return True

    def reboot_device(self, device_id):
        if not (self.running and device_id not in self.completed_devices):
            return False
        self.update_device_status(device_id, "发送重启命令", 90)
        self.log(f"[{device_id}] 发送重启命令")
        try:
            subprocess.run(["adb", "-s", device_id, "reboot"], capture_output=True, timeout=10)
        except Exception as e:
            self.log(f"[{device_id}] 重启异常: {str(e)}")
        self.completed_devices.add(device_id)
        self.processing_devices.discard(device_id)
        self.update_device_status(device_id, "安装完成", 100)
        return True

    def process_single_device(self, device_id, mode):
        if device_id in self.completed_devices:
            return
        self.log(f"\n===== 处理设备: {device_id} =====")
        try:
            if not self.wait_for_authorization(device_id):
                return
            self.set_volume(device_id)
            if self.install_apks(device_id, mode):
                self.reboot_device(device_id)
                self.update_install_count(mode)
                self.log(f"===== 设备{device_id}处理完成 =====\n")
        except Exception as e:
            self.log(f"处理设备{device_id}失败: {str(e)}")
            self.update_device_status(device_id, "处理异常", 0)
        finally:
            self.processing_devices.discard(device_id)


if __name__ == "__main__":
    root = tk.Tk()
    app = ADBInstaller(root)
    root.mainloop()