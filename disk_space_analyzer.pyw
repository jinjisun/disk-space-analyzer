# -*- coding: utf-8 -*-
"""磁盘空间分析器 - 直观查看文件大头，方便清理。

用法：
    - 选择盘符或文件夹，点“扫描”
    - 左侧矩形图：面积越大占用越多；点击文件夹可下钻，点击文件打开所在位置
    - 右侧“文件夹”标签：当前目录下子项按大小排序
    - 右侧“最大文件”标签：整次扫描中最大的文件
    - 选中后点“打开位置”或“删除(回收站)”
"""
import os
import queue
import threading
import heapq
import ctypes
import subprocess
import time
from ctypes import wintypes

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------

def fmt_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024
    return f"{n:.1f} TB"


def open_location(path):
    """在资源管理器中打开并选中 path（文件夹则直接打开）。"""
    try:
        if os.path.isdir(path):
            subprocess.Popen(["explorer", os.path.normpath(path)])
        else:
            subprocess.Popen(["explorer", "/select,", os.path.normpath(path)])
    except Exception:
        try:
            os.startfile(os.path.dirname(path))
        except Exception:
            pass


class SHFILEOPSTRUCTW(ctypes.Structure):
    _fields_ = [
        ("hwnd", wintypes.HWND),
        ("wFunc", ctypes.c_uint),
        ("pFrom", ctypes.c_wchar_p),
        ("pTo", ctypes.c_wchar_p),
        ("fFlags", ctypes.c_ushort),
        ("fAnyOperationsAborted", wintypes.BOOL),
        ("hNameMappings", ctypes.c_void_p),
        ("lpszProgressTitle", ctypes.c_wchar_p),
    ]


def send_to_recycle_bin(path):
    """删除到回收站（可恢复）。"""
    p = os.path.abspath(path)
    pfrom = p + "\0\0"
    op = SHFILEOPSTRUCTW()
    op.hwnd = 0
    op.wFunc = 3  # FO_DELETE
    op.pFrom = pfrom
    op.pTo = None
    op.fFlags = 0x40 | 0x10  # FOF_ALLOWUNDO | FOF_NOCONFIRMATION
    op.fAnyOperationsAborted = False
    res = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
    return res == 0 and not op.fAnyOperationsAborted


# ---------------------------------------------------------------------------
# 数据结构与扫描
# ---------------------------------------------------------------------------

class Node:
    __slots__ = ("name", "path", "size", "is_dir", "children")

    def __init__(self, name, path, is_dir):
        self.name = name
        self.path = path
        self.is_dir = is_dir
        self.size = 0
        self.children = [] if is_dir else None


def _scan_worker(root_path, q, stop):
    top_files = []  # heapq 保存最大的 300 个文件 (size, path)

    def walk(path):
        node = Node(os.path.basename(path.rstrip("\\/")) or path, path, True)
        total = 0
        try:
            with os.scandir(path) as it:
                for entry in it:
                    if stop.is_set():
                        raise KeyboardInterrupt
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            child = walk(entry.path)
                            total += child.size
                            node.children.append(child)
                        else:
                            try:
                                fs = entry.stat(follow_symlinks=False).st_size
                            except OSError:
                                fs = 0
                            total += fs
                            node.children.append(Node(entry.name, entry.path, False))
                            node.children[-1].size = fs
                            heapq.heappush(top_files, (fs, entry.path))
                            if len(top_files) > 300:
                                heapq.heappop(top_files)
                        q.put(("progress", total, entry.path))
                    except (OSError, PermissionError):
                        continue
        except (OSError, PermissionError):
            pass
        except KeyboardInterrupt:
            raise
        node.size = total
        return node

    try:
        root = walk(root_path)
    except KeyboardInterrupt:
        q.put(("cancelled",))
        return
    except Exception as e:
        q.put(("error", str(e)))
        return
    top = sorted(top_files, reverse=True)
    q.put(("done", root, top))


# ---------------------------------------------------------------------------
# 矩形图（切片式树图）
# ---------------------------------------------------------------------------

def slice_treemap(items, x, y, w, h):
    """items: [(key, size)] 已按 size 降序，size>0。返回 {key: (x,y,w,h)}。"""
    rects = {}

    def layout(items, x, y, w, h):
        if not items:
            return
        if len(items) == 1:
            rects[items[0][0]] = (x, y, w, h)
            return
        total = sum(sz for _, sz in items)
        if total <= 0:
            return
        # 找到最接近一半的分割点
        half = total / 2.0
        acc = 0.0
        split = 0
        for i, (_, sz) in enumerate(items):
            acc += sz
            if acc >= half:
                split = i
                break
        left = items[: split + 1]
        right = items[split + 1 :]
        left_sum = sum(sz for _, sz in left)
        if w >= h:
            lw = w * left_sum / total
            layout(left, x, y, lw, h)
            layout(right, x + lw, y, w - lw, h)
        else:
            lh = h * left_sum / total
            layout(left, x, y, w, lh)
            layout(right, x, y + lh, w, h - lh)

    layout(items, x, y, w, h)
    return rects


PALETTE = [
    "#2e6fb7", "#e0782a", "#3a9d5d", "#c24343", "#8a5bb3",
    "#c07a2e", "#3f8f8f", "#b04a7a", "#6b7f2e", "#4a6ea9",
]


# ---------------------------------------------------------------------------
# 主界面
# ---------------------------------------------------------------------------

class App:
    def __init__(self, root):
        self.root = root
        root.title("磁盘空间分析器")
        root.geometry("1240x780")
        root.minsize(900, 560)

        self.q = queue.Queue()
        self.stop = threading.Event()
        self.scan_thread = None
        self.root_node = None
        self.current = None
        self.top_files = []
        self._rects = []  # [(node, x, y, w, h)]
        self._hover = None

        self._build_ui()
        self._poll()

    # ------------------------- UI 构建 -------------------------
    def _build_ui(self):
        # 顶部工具栏
        bar = ttk.Frame(self.root, padding=(8, 6))
        bar.pack(side="top", fill="x")
        ttk.Label(bar, text="路径:").pack(side="left")
        self.path_var = tk.StringVar(value=os.environ.get("USERPROFILE", "C:\\"))
        self.path_entry = ttk.Entry(bar, textvariable=self.path_var)
        self.path_entry.pack(side="left", fill="x", expand=True, padx=4)
        self.path_entry.bind("<Return>", lambda e: self.start_scan())

        self.drive_var = tk.StringVar()
        self.drive_box = ttk.Combobox(bar, textvariable=self.drive_var, width=8, state="readonly")
        self.drive_box["values"] = self._list_drives()
        if self.drive_box["values"]:
            self.drive_box.current(0)
        self.drive_box.pack(side="left", padx=2)
        self.drive_box.bind("<<ComboboxSelected>>", self._on_drive)

        ttk.Button(bar, text="浏览...", command=self._browse).pack(side="left", padx=2)
        self.scan_btn = ttk.Button(bar, text="扫描", command=self.start_scan)
        self.scan_btn.pack(side="left", padx=2)
        self.stop_btn = ttk.Button(bar, text="停止", command=self.stop_scan, state="disabled")
        self.stop_btn.pack(side="left", padx=2)
        self.back_btn = ttk.Button(bar, text="上级", command=self.go_up, state="disabled")
        self.back_btn.pack(side="left", padx=2)
        self.root_btn = ttk.Button(bar, text="根目录", command=self.go_root, state="disabled")
        self.root_btn.pack(side="left", padx=2)

        # 状态栏
        self.status_var = tk.StringVar(value="请选择盘符或文件夹后点击“扫描”")
        ttk.Label(self.root, textvariable=self.status_var, anchor="w",
                  padding=(8, 2)).pack(side="bottom", fill="x")

        # 主体：左树图 + 右标签页
        paned = ttk.PanedWindow(self.root, orient="horizontal")
        paned.pack(side="top", fill="both", expand=True)

        left = ttk.Frame(paned)
        paned.add(left, weight=3)
        self.breadcrumb = tk.StringVar(value="")
        ttk.Label(left, textvariable=self.breadcrumb, anchor="w", padding=(6, 2)).pack(fill="x")
        self.canvas = tk.Canvas(left, bg="#f2f2f2", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self._draw())
        self.canvas.bind("<Button-1>", self._on_click)
        self.canvas.bind("<Motion>", self._on_move)
        self.canvas.bind("<Leave>", lambda e: self._set_hover(None))
        self.canvas.bind("<Button-3>", self._on_right_click)

        right = ttk.Frame(paned)
        paned.add(right, weight=2)
        nb = ttk.Notebook(right)
        nb.pack(fill="both", expand=True)

        # 文件夹标签
        ftab = ttk.Frame(nb)
        nb.add(ftab, text="文件夹")
        self.folder_tree = ttk.Treeview(ftab, columns=("size", "type"), show="tree headings")
        self.folder_tree.heading("#0", text="名称", anchor="w")
        self.folder_tree.heading("size", text="大小", anchor="w")
        self.folder_tree.heading("type", text="类型", anchor="w")
        self.folder_tree.column("#0", width=180, stretch=True)
        self.folder_tree.column("size", width=90, anchor="e", stretch=False)
        self.folder_tree.column("type", width=70, anchor="w", stretch=False)
        vsb = ttk.Scrollbar(ftab, orient="vertical", command=self.folder_tree.yview)
        self.folder_tree.configure(yscrollcommand=vsb.set)
        self.folder_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="left", fill="y")
        self.folder_tree.bind("<Double-1>", self._on_folder_double)

        # 最大文件标签
        ftab2 = ttk.Frame(nb)
        nb.add(ftab2, text="最大文件")
        self.file_tree = ttk.Treeview(ftab2, columns=("size", "path"), show="tree headings")
        self.file_tree.heading("#0", text="文件", anchor="w")
        self.file_tree.heading("size", text="大小", anchor="w")
        self.file_tree.heading("path", text="完整路径", anchor="w")
        self.file_tree.column("#0", width=150, stretch=False)
        self.file_tree.column("size", width=90, anchor="e", stretch=False)
        self.file_tree.column("path", width=400, anchor="w", stretch=True)
        vsb2 = ttk.Scrollbar(ftab2, orient="vertical", command=self.file_tree.yview)
        self.file_tree.configure(yscrollcommand=vsb2.set)
        self.file_tree.pack(side="left", fill="both", expand=True)
        vsb2.pack(side="left", fill="y")
        self.file_tree.bind("<Double-1>", self._on_file_double)

        # 操作按钮
        act = ttk.Frame(right, padding=(6, 6))
        act.pack(fill="x")
        ttk.Button(act, text="打开位置", command=self._open_selected).pack(side="left", padx=2)
        ttk.Button(act, text="删除到回收站", command=self._delete_selected).pack(side="left", padx=2)
        ttk.Button(act, text="刷新当前目录", command=self._refresh_current).pack(side="left", padx=2)

        self._menu = tk.Menu(self.root, tearoff=0)
        self._menu.add_command(label="打开所在位置", command=self._open_selected)
        self._menu.add_command(label="删除到回收站", command=self._delete_selected)

    def _list_drives(self):
        drives = []
        for letter in "CDEFGHIJKLMNOPQRSTUVWXYZ":
            p = letter + ":\\"
            if os.path.exists(p):
                drives.append(p)
        return drives

    # ------------------------- 扫描控制 -------------------------
    def _on_drive(self, event=None):
        self.path_var.set(self.drive_var.get())

    def _browse(self):
        d = filedialog.askdirectory(initialdir=self.path_var.get())
        if d:
            self.path_var.set(d)

    def start_scan(self, path=None):
        if self.scan_thread and self.scan_thread.is_alive():
            return
        path = path or self.path_var.get().strip()
        if not path or not os.path.exists(path):
            messagebox.showerror("错误", f"路径不存在：{path}")
            return
        self.stop.clear()
        self.scan_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.status_var.set("正在扫描：%s ..." % path)
        self._t0 = time.time()
        self.scan_thread = threading.Thread(
            target=_scan_worker, args=(path, self.q, self.stop), daemon=True
        )
        self.scan_thread.start()

    def stop_scan(self):
        self.stop.set()
        self.status_var.set("正在停止...")

    # ------------------------- 消息轮询 -------------------------
    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "progress":
                    _, size, path = msg
                    if time.time() - self._t0 > 0.3:
                        self.status_var.set("扫描中，已累计 %s | %s" % (fmt_size(size), path))
                        self._t0 = time.time()
                elif kind == "done":
                    _, root_node, top_files = msg
                    self.root_node = root_node
                    self.current = root_node
                    self.top_files = top_files
                    self.scan_btn.config(state="normal")
                    self.stop_btn.config(state="disabled")
                    self.back_btn.config(state="disabled")
                    self.root_btn.config(state="disabled")
                    self.status_var.set("完成：%s 共 %s" % (root_node.path, fmt_size(root_node.size)))
                    self._refresh_views()
                elif kind == "cancelled":
                    self.status_var.set("已停止扫描")
                    self.scan_btn.config(state="normal")
                    self.stop_btn.config(state="disabled")
                elif kind == "error":
                    self.status_var.set("扫描出错：" + msg[1])
                    self.scan_btn.config(state="normal")
                    self.stop_btn.config(state="disabled")
                elif kind == "deleted":
                    self._on_deleted(msg[1], msg[2])
        except queue.Empty:
            pass
        self.root.after(120, self._poll)

    # ------------------------- 视图刷新 -------------------------
    def _refresh_views(self):
        self._refresh_folder_table()
        self._refresh_file_table()
        self._draw()

    def _refresh_folder_table(self):
        self.folder_tree.delete(*self.folder_tree.get_children())
        if not self.current:
            return
        self.breadcrumb.set(self.current.path)
        children = sorted(self.current.children or [], key=lambda c: -c.size)
        for c in children:
            kind = "文件夹" if c.is_dir else "文件"
            self.folder_tree.insert(
                "", "end", text=c.name, values=(fmt_size(c.size), kind),
                tags=(c.path,)
            )

    def _refresh_file_table(self):
        self.file_tree.delete(*self.file_tree.get_children())
        for size, path in self.top_files:
            self.file_tree.insert(
                "", "end", text=os.path.basename(path),
                values=(fmt_size(size), path), tags=(path,)
            )

    # ------------------------- 树图绘制 -------------------------
    def _draw(self):
        self.canvas.delete("all")
        self._rects = []
        self._hover = None
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if not self.current or w <= 1 or h <= 1:
            return
        children = [c for c in (self.current.children or []) if c.size > 0]
        if not children:
            self.canvas.create_text(w / 2, h / 2, text="(空目录)", fill="#888")
            return
        children = sorted(children, key=lambda c: -c.size)[:200]
        rects = slice_treemap([(c.path, c.size) for c in children], 2, 2, w - 4, h - 4)
        for i, c in enumerate(children):
            x, y, rw, rh = rects[c.path]
            color = PALETTE[i % len(PALETTE)]
            if not c.is_dir:
                color = "#c9c9c9"
            self.canvas.create_rectangle(x, y, x + rw, y + rh, fill=color, outline="white")
            if rw > 60 and rh > 20:
                label = c.name if len(c.name) < 30 else c.name[:28] + ".."
                self.canvas.create_text(x + rw / 2, y + rh / 2, text=label,
                                        fill="white", font=("Segoe UI", 9))
            self._rects.append((c, x, y, rw, rh))

    def _hit(self, ex, ey):
        for node, x, y, w, h in self._rects:
            if x <= ex <= x + w and y <= ey <= y + h:
                return node
        return None

    def _on_click(self, event):
        node = self._hit(event.x, event.y)
        if not node:
            return
        if node.is_dir:
            self.current = node
            self.back_btn.config(state="normal")
            self.root_btn.config(state="normal")
            self._refresh_views()
        else:
            open_location(node.path)

    def _on_move(self, event):
        node = self._hit(event.x, event.y)
        if node:
            self._set_hover(node)
        else:
            self._set_hover(None)

    def _set_hover(self, node):
        if node is None:
            self.breadcrumb.set(self.current.path if self.current else "")
        else:
            self.breadcrumb.set("%s  |  %s" % (fmt_size(node.size), node.path))

    def _on_right_click(self, event):
        node = self._hit(event.x, event.y)
        if node:
            self._selected_path = node.path
            self._menu.tk_popup(event.x_root, event.y_root)

    # ------------------------- 导航与操作 -------------------------
    def go_up(self):
        if self.current:
            parent = os.path.dirname(self.current.path.rstrip("\\/"))
            if parent and os.path.exists(parent):
                self._rescan_to(parent)

    def go_root(self):
        if self.root_node:
            self.current = self.root_node
            self.back_btn.config(state="disabled")
            self.root_btn.config(state="disabled")
            self._refresh_views()

    def _on_folder_double(self, event):
        sel = self.folder_tree.selection()
        if not sel:
            return
        path = self.folder_tree.item(sel[0], "tags")[0]
        if os.path.isdir(path):
            self._rescan_to(path)
        else:
            open_location(path)

    def _on_file_double(self, event):
        sel = self.file_tree.selection()
        if sel:
            open_location(self.file_tree.item(sel[0], "tags")[0])

    def _rescan_to(self, path):
        if not os.path.isdir(path):
            return
        self.path_var.set(path)
        self.start_scan(path)

    def _refresh_current(self):
        if self.current:
            self.start_scan(self.current.path)

    def _selected_item(self):
        """返回当前选中列表项对应的路径。"""
        focus = self.root.focus_get()
        if focus is self.folder_tree:
            sel = self.folder_tree.selection()
            if sel:
                return self.folder_tree.item(sel[0], "tags")[0]
        elif focus is self.file_tree:
            sel = self.file_tree.selection()
            if sel:
                return self.file_tree.item(sel[0], "tags")[0]
        return getattr(self, "_selected_path", None)

    def _open_selected(self):
        p = self._selected_item()
        if p and os.path.exists(p):
            open_location(p)

    def _delete_selected(self):
        p = self._selected_item()
        if not p or not os.path.exists(p):
            return
        if not messagebox.askyesno("确认删除", "删除到回收站？\n\n%s" % p):
            return
        self.status_var.set("正在删除：" + p)
        threading.Thread(target=self._do_delete, args=(p,), daemon=True).start()

    def _do_delete(self, path):
        ok = send_to_recycle_bin(path)
        self.q.put(("deleted", path, ok))

    def _on_deleted(self, path, ok):
        if ok:
            self.status_var.set("已删除到回收站：" + path)
        else:
            self.status_var.set("删除失败：" + path)
        if self.current:
            self._refresh_current()


def main():
    root = tk.Tk()
    app = App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
