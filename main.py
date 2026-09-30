#!/usr/bin/env python3
"""PSR Pro v4 — Professional Process Step Recorder
Non-destructive crop · Insert custom steps · Project naming
Vector annotation layer · Selectable objects with transform gizmo
Mouse-up screenshot capture · Per-step undo · Continue recording

Dependencies:
    pip install customtkinter pillow mss pynput pygetwindow fpdf2
    pip install tkinterdnd2          # optional: enables drag-and-drop
"""
from __future__ import annotations

import copy
import html as _html
import io
import json
import logging
import math
import os
import queue
import re
import struct
import subprocess
import sys
import threading
import time
import wave
import base64
import uuid
import webbrowser
from datetime import datetime

logging.basicConfig(level=logging.INFO, format="%(levelname)s [%(name)s] %(message)s")
log = logging.getLogger(__name__)

if sys.platform == "win32":
    try:    # per-monitor DPI awareness: mouse, monitor and screenshot coordinates must share one pixel space
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        pass

try:
    import winsound
except ImportError:
    winsound = None

import tkinter as tk
from tkinter import filedialog, messagebox
import customtkinter as ctk
from PIL import Image, ImageTk, ImageDraw, ImageGrab, ImageFont
import mss
from pynput import mouse, keyboard
from fpdf import FPDF

try:
    import pygetwindow as gw
    _HAS_GW = True
except ImportError:
    _HAS_GW = False

import importlib.util
_HAS_DND = importlib.util.find_spec("tkinterdnd2") is not None

from psr_constants import C, ICON, HANDLE_SZ, HANDLE_HIT, BASE_DIR, CAPTURE_MAX_W

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")
os.makedirs(BASE_DIR, exist_ok=True)


# ══════════════════════════════════════ GLOBALS ══════════════════════════════════════

recording         = False
current_session   = None
project_name      = ""
step_counter      = 1
log_data          = []
event_queue       = queue.Queue()
mouse_listener    = None
keyboard_listener = None
pressed_keys      = set()
_keys_lock        = threading.Lock()

# {step_index: [obj, ...]}
# rect obj:  {type, color, width, x1, y1, x2, y2}  - coords in ORIGINAL image space
# draw obj:  {type, color, width, points: [[x,y],...]}  - coords in ORIGINAL image space
step_objects: dict = {}

# {step_index: {x1, y1, x2, y2}}  — non-destructive crop in ORIGINAL image space
step_crops: dict   = {}


# Annotations drawn on every screenshot (normalized 0–1 coords). Saved in session as global_overlay.json
global_annotations: list = []

# {step_index: [json_snapshot, ...]}
undo_stacks: dict  = {}

annotation_tool   = "none"  # "none"|"highlight"|"redact"|"crop"|"draw"
capture_on_click  = True
capture_on_hotkey = False
capture_keyboard  = False   # record key presses / shortcuts (off by default)
ignore_psr_focus  = True    # skip recording input while a PSR window is active
paused            = False   # recording is running but events are suppressed
capture_delay_ms  = 100     # ms to wait before taking screenshot (lets menus/hovers render)
capture_format    = "jpg"   # "jpg" (fast, smaller) or "png" (lossless)
show_click_markers = True   # draw a ring at the click position (editor + exports)
_last_capture     = [("", "", "", None)]  # (step, keyword, rest, color)

from psr_settings import load_settings, save_settings as _save_settings_io

def _load_recording_settings() -> None:
    global capture_on_click, capture_on_hotkey, capture_keyboard, ignore_psr_focus, capture_delay_ms, capture_format, show_click_markers
    data = load_settings()
    if not data:
        return
    if data.get("capture_on_click") is not None:
        capture_on_click = bool(data["capture_on_click"])
    if data.get("capture_on_hotkey") is not None:
        capture_on_hotkey = bool(data["capture_on_hotkey"])
    if data.get("capture_keyboard") is not None:
        capture_keyboard = bool(data["capture_keyboard"])
    if data.get("ignore_psr_focus") is not None:
        ignore_psr_focus = bool(data["ignore_psr_focus"])
    if data.get("capture_delay_ms") is not None:
        capture_delay_ms = max(0, min(2000, int(data["capture_delay_ms"])))
    if data.get("capture_format") in ("jpg", "png"):
        capture_format = data["capture_format"]
    if data.get("show_click_markers") is not None:
        show_click_markers = bool(data["show_click_markers"])

_load_recording_settings()

def _save_recording_settings() -> None:
    _save_settings_io({
        "capture_on_click":  capture_on_click,
        "capture_on_hotkey": capture_on_hotkey,
        "capture_keyboard":  capture_keyboard,
        "ignore_psr_focus":  ignore_psr_focus,
        "capture_delay_ms":  capture_delay_ms,
        "capture_format":    capture_format,
        "show_click_markers": show_click_markers,
    })

draw_color      = "#e74c3c"
draw_width      = 3

active_index    = -1      # step shown in the editor
_selected: set  = set()   # selected step indices (multi-select)
_sel_anchor     = -1      # anchor for shift-range selection
draw_color_btns = []
pen_size_btns   = []

MODIFIER_KEYS = {
    keyboard.Key.ctrl,   keyboard.Key.ctrl_l,   keyboard.Key.ctrl_r,
    keyboard.Key.alt,    keyboard.Key.alt_l,    keyboard.Key.alt_r,
    keyboard.Key.shift,  keyboard.Key.shift_l,  keyboard.Key.shift_r,
}

# handle index -> (x1_moves, y1_moves, x2_moves, y2_moves)
_HANDLE_FX = [
    (1,1,0,0), (0,1,0,0), (0,1,1,0),
    (1,0,0,0),             (0,0,1,0),
    (1,0,0,1), (0,0,0,1), (0,0,1,1),
]


# ══════════════════════════════════════ TOOLTIP ══════════════════════════════════════

class _Tooltip:
    """Lightweight hover tooltip for any tkinter/CTk widget."""
    _DELAY = 500  # ms before showing

    def __init__(self, widget, text):
        self._w    = widget
        self._text = text
        self._job  = None
        self._win  = None
        widget.bind("<Enter>",  self._schedule, add="+")
        widget.bind("<Leave>",  self._cancel,   add="+")
        widget.bind("<Button>", self._cancel,   add="+")

    def _schedule(self, _=None):
        self._cancel()
        self._job = self._w.after(self._DELAY, self._show)

    def _cancel(self, _=None):
        if self._job:
            self._w.after_cancel(self._job)
            self._job = None
        if self._win:
            self._win.destroy()
            self._win = None

    def _show(self):
        x = self._w.winfo_rootx() + self._w.winfo_width() // 2
        y = self._w.winfo_rooty() + self._w.winfo_height() + 4
        self._win = tw = tk.Toplevel(self._w)
        tw.wm_overrideredirect(True)
        tw.wm_attributes("-topmost", True)
        lbl = tk.Label(tw, text=self._text, justify="left",
                       background=C["surface2"], foreground=C["text"],
                       highlightbackground=C["border_hi"], highlightthickness=1, relief="flat", borderwidth=0,
                       font=("Segoe UI", 9), padx=9, pady=6)
        lbl.pack()
        # reposition so tooltip stays on screen
        tw.update_idletasks()
        sw = tw.winfo_screenwidth()
        tx = min(x - tw.winfo_width() // 2, sw - tw.winfo_width() - 4)
        tw.wm_geometry(f"+{max(tx, 0)}+{y}")


def tip(widget, text):
    """Attach a hover tooltip to widget."""
    _Tooltip(widget, text)


# ══════════════════════════════════════ UTILS ══════════════════════════════════════

def _hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))


_RECT_TYPES = ("highlight", "redact", "blur")        # objects defined by two corners
TEXT_SIZES  = {2: 26, 5: 34, 10: 46, 18: 64}            # pen size -> text height (image px)
MARKER_R    = {2: 13, 5: 17, 10: 24, 18: 34}            # pen size -> numbered marker radius
BLUR_BLOCK  = 12                                        # pixelation block size (image px)
_FONT_CACHE: dict = {}


def _pil_font(size: int, bold: bool = False):
    key = (size, bold)
    f = _FONT_CACHE.get(key)
    if f is None:
        for name in (("segoeuib.ttf", "arialbd.ttf") if bold else ("segoeui.ttf", "arial.ttf")):
            try:
                f = ImageFont.truetype(name, size)
                break
            except OSError:
                continue
        if f is None:
            f = ImageFont.load_default(size)
        _FONT_CACHE[key] = f
    return f


def _text_extent(text: str, size: int) -> tuple[int, int]:
    r, b = ImageDraw.Draw(Image.new("L", (1, 1))).multiline_textbbox((0, 0), text or " ", font=_pil_font(size))[2:]
    return int(r) + 2, int(b) + 2


def _obj_bbox_img(obj):
    """Bounding box of an annotation object in original image coordinates."""
    t = obj["type"]
    if t in _RECT_TYPES:
        x1, x2 = sorted([obj["x1"], obj["x2"]])
        y1, y2 = sorted([obj["y1"], obj["y2"]])
        return x1, y1, x2, y2
    if t == "arrow":
        x1, x2 = sorted([obj["x1"], obj["x2"]])
        y1, y2 = sorted([obj["y1"], obj["y2"]])
        return x1, y1, x2, y2
    if t == "text":
        w, h = _text_extent(obj["text"], obj["size"])
        return obj["x"], obj["y"], obj["x"] + w, obj["y"] + h
    if t == "marker":
        r = obj["r"]
        return obj["x"] - r, obj["y"] - r, obj["x"] + r, obj["y"] + r
    pts = obj["points"]
    xs  = [p[0] for p in pts]
    ys  = [p[1] for p in pts]
    return min(xs), min(ys), max(xs), max(ys)


def _luma(rgb) -> float:
    return (0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]) / 255


def _draw_arrow(draw, x1, y1, x2, y2, rgb, w):
    """Arrow from (x1,y1) to (x2,y2) with a filled head at the end."""
    length = math.hypot(x2 - x1, y2 - y1)
    if length < 2:
        return
    head = min(length * 0.6, max(16, w * 4.5))
    ux, uy = (x2 - x1) / length, (y2 - y1) / length
    bx, by = x2 - ux * head, y2 - uy * head
    draw.line([(x1, y1), (bx + ux * 2, by + uy * 2)], fill=rgb, width=w)
    hw = head * 0.42
    draw.polygon([(x2, y2), (bx - uy * hw, by + ux * hw), (bx + uy * hw, by - ux * hw)], fill=rgb)
    r = w / 2
    draw.ellipse([x1 - r, y1 - r, x1 + r, y1 + r], fill=rgb)


def _step_id(entry: dict) -> str:
    """Stable id for a step (for fold state across rebuilds). Assigns id if missing."""
    if "id" not in entry:
        entry["id"] = str(uuid.uuid4())
    return entry["id"]


def _get_crop(step_index: int, img_size: tuple[int, int] | None = None) -> tuple[int, int, int, int]:
    """Return (x1,y1,x2,y2) crop region in original image space, or full image."""
    crop = step_crops.get(step_index)
    if crop:
        return crop["x1"], crop["y1"], crop["x2"], crop["y2"]
    if img_size:
        return 0, 0, img_size[0], img_size[1]
    entry    = log_data[step_index]
    img_path = os.path.join(current_session, entry["screenshot"])
    img      = Image.open(img_path)
    return 0, 0, img.size[0], img.size[1]


def _pdf_safe(text: str) -> str:
    """Make text safe for PDF built-in fonts (latin-1 subset)."""
    replacements = {
        '\u2018': "'", '\u2019': "'", '\u201c': '"', '\u201d': '"',
        '\u2013': '-', '\u2014': '--', '\u2026': '...', '\u00a0': ' ',
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text.encode('latin-1', errors='replace').decode('latin-1')


def _open_folder(filepath: str) -> None:
    """Open the folder containing filepath in the OS file manager."""
    folder = os.path.dirname(os.path.abspath(filepath))
    try:
        if sys.platform == "win32":
            os.startfile(folder)
        elif sys.platform == "darwin":
            subprocess.Popen(["open", folder])
        else:
            subprocess.Popen(["xdg-open", folder])
    except Exception as e:
        log.warning("Could not open folder: %s", e)


def _flatten_to_pil(step_index: int) -> Image.Image | None:
    """Composite crop + all vector objects onto screenshot. Returns a flat RGB PIL image, or None for text-only / missing."""
    entry = log_data[step_index]
    if entry.get("screenshot") is None:
        return None
    img_path = os.path.join(current_session, entry["screenshot"])
    if not os.path.exists(img_path):
        return None
    try:
        img = Image.open(img_path).convert("RGB")
    except Exception:
        return None
    orig_w, orig_h = img.size

    # Apply non-destructive crop
    cx1, cy1, cx2, cy2 = _get_crop(step_index, (orig_w, orig_h))
    cx1, cx2 = sorted([cx1, cx2]); cy1, cy2 = sorted([cy1, cy2])
    cx1 = max(0, min(cx1, orig_w));  cy1 = max(0, min(cy1, orig_h))
    cx2 = max(cx1+1, min(cx2, orig_w)); cy2 = max(cy1+1, min(cy2, orig_h))
    img = img.crop((cx1, cy1, cx2, cy2))

    click = None if entry.get("click_hidden") else entry.get("click")
    if show_click_markers and click:
        px, py = click[0] - cx1, click[1] - cy1
        r = _click_marker_radius((orig_w, orig_h))
        layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ld = ImageDraw.Draw(layer)
        ld.ellipse([px - r, py - r, px + r, py + r], fill=(231, 76, 60, 70), outline=(231, 76, 60, 255), width=4)
        ld.ellipse([px - 4, py - 4, px + 4, py + 4], fill=(231, 76, 60, 255))
        img = Image.alpha_composite(img.convert("RGBA"), layer).convert("RGB")

    objects = step_objects.get(step_index, [])
    if not objects and not global_annotations:
        return img

    draw_ctx = ImageDraw.Draw(img)
    for obj in objects:
        rgb = _hex_to_rgb(obj.get("color", "#000000"))
        if obj["type"] == "blur":
            x1, y1, x2, y2 = (int(v) for v in _obj_bbox_img(obj))
            x1 -= cx1; x2 -= cx1; y1 -= cy1; y2 -= cy1
            x1, y1 = max(0, x1), max(0, y1); x2, y2 = min(img.width, x2), min(img.height, y2)
            if x2 - x1 > 1 and y2 - y1 > 1:
                reg = img.crop((x1, y1, x2, y2))
                blk = max(2, min(BLUR_BLOCK, (x2 - x1) // 2, (y2 - y1) // 2))
                small = reg.resize((max(1, (x2 - x1) // blk), max(1, (y2 - y1) // blk)), Image.BILINEAR)
                img.paste(small.resize(reg.size, Image.NEAREST), (x1, y1))
        elif obj["type"] == "arrow":
            _draw_arrow(draw_ctx, obj["x1"] - cx1, obj["y1"] - cy1, obj["x2"] - cx1, obj["y2"] - cy1,
                        rgb, max(2, int(obj["width"])))
        elif obj["type"] == "text":
            stroke = (0, 0, 0) if _luma(rgb) > 0.45 else (255, 255, 255)
            draw_ctx.multiline_text((obj["x"] - cx1, obj["y"] - cy1), obj["text"], font=_pil_font(obj["size"]),
                                    fill=rgb, stroke_width=max(1, obj["size"] // 14), stroke_fill=stroke)
        elif obj["type"] == "marker":
            r = obj["r"]; mx, my = obj["x"] - cx1, obj["y"] - cy1
            draw_ctx.ellipse([mx - r, my - r, mx + r, my + r], fill=rgb,
                             outline=(255, 255, 255), width=max(2, r // 6))
            draw_ctx.text((mx, my), str(obj.get("n", 1)), font=_pil_font(int(r * 1.15), True),
                          fill=(0, 0, 0) if _luma(rgb) > 0.6 else (255, 255, 255), anchor="mm")
        elif obj["type"] == "highlight":
            x1 = obj["x1"]-cx1; y1 = obj["y1"]-cy1
            x2 = obj["x2"]-cx1; y2 = obj["y2"]-cy1
            x1,x2 = sorted([x1,x2]); y1,y2 = sorted([y1,y2])
            for w in range(5, 0, -1):
                draw_ctx.rectangle([x1,y1,x2,y2], outline=rgb, width=w)
            ov = Image.new("RGBA", img.size, (0,0,0,0))
            ImageDraw.Draw(ov).rectangle([x1,y1,x2,y2], fill=(*rgb, 28))
            img      = Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB")
            draw_ctx = ImageDraw.Draw(img)
        elif obj["type"] == "redact":
            x1 = obj["x1"]-cx1; y1 = obj["y1"]-cy1
            x2 = obj["x2"]-cx1; y2 = obj["y2"]-cy1
            x1,x2 = sorted([x1,x2]); y1,y2 = sorted([y1,y2])
            draw_ctx.rectangle([x1,y1,x2,y2], fill=(16,16,16))
            draw_ctx.rectangle([x1,y1,x2,y2], outline=(70,70,70), width=2)
        elif obj["type"] == "draw":
            pts = [(int(p[0])-cx1, int(p[1])-cy1) for p in obj["points"]]
            w   = obj["width"]
            if len(pts) >= 2:
                draw_ctx.line(pts, fill=rgb, width=w, joint="curve")
            r = w // 2
            for x, y in pts:
                draw_ctx.ellipse([x-r, y-r, x+r, y+r], fill=rgb)

    # Global overlay (same redaction/highlight on every step, normalized coords)
    cw, ch = img.size
    for g in global_annotations:
        if g.get("type") not in ("highlight", "redact"):
            continue
        x1 = int(g["x1_norm"] * cw); y1 = int(g["y1_norm"] * ch)
        x2 = int(g["x2_norm"] * cw); y2 = int(g["y2_norm"] * ch)
        x1, x2 = sorted([x1, x2]); y1, y2 = sorted([y1, y2])
        if g["type"] == "highlight":
            rgb = _hex_to_rgb(g["color"])
            for w in range(5, 0, -1):
                draw_ctx.rectangle([x1, y1, x2, y2], outline=rgb, width=w)
            ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
            ImageDraw.Draw(ov).rectangle([x1, y1, x2, y2], fill=(*rgb, 28))
            img = Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB")
            draw_ctx = ImageDraw.Draw(img)
        else:
            draw_ctx.rectangle([x1, y1, x2, y2], fill=(16, 16, 16))
            draw_ctx.rectangle([x1, y1, x2, y2], outline=(70, 70, 70), width=2)
    return img


# ══════════════════════════════════════ SESSION ══════════════════════════════════════

def _safe_folder_name(name: str) -> str:
    """Sanitize a string for use as a folder name."""
    name = re.sub(r'[<>:"/\\|?*]', '_', name.strip())
    name = name.strip('. ')
    return name[:80] if name else ""


def create_session(parent_dir: str | None = None) -> None:
    """Create the session folder. parent_dir: where to create it (default BASE_DIR)."""
    global current_session, global_annotations
    base = (parent_dir if parent_dir is not None else BASE_DIR)
    ts = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    try:
        pname = _safe_folder_name(project_name_var.get())
    except Exception:
        pname = ""
    folder = f"{pname}_{ts}" if pname else ts
    current_session = os.path.join(base, folder)
    os.makedirs(current_session)
    global_annotations = []


def _load_global_overlay() -> None:
    """Load global_annotations from current_session/global_overlay.json."""
    global global_annotations
    global_annotations = []
    if not current_session or not os.path.isdir(current_session):
        return
    path = os.path.join(current_session, "global_overlay.json")
    if not os.path.exists(path):
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            global_annotations = json.load(f)
    except Exception:
        log.exception("Failed to load global overlay")


def _save_global_overlay() -> None:
    if not current_session or not os.path.isdir(current_session):
        return
    path = os.path.join(current_session, "global_overlay.json")
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(global_annotations, f, indent=2)
    except OSError as exc:
        log.warning("Save global overlay failed: %s", exc)


def _clear_global_overlays() -> None:
    global global_annotations
    if not global_annotations:
        _set_status("No global overlays to clear", C["muted"])
        return
    global_annotations = []
    _save_global_overlay()
    editor.render()
    _set_status("Cleared all global overlays", C["success"])


def save_steps() -> None:
    if not current_session:
        return
    if not os.path.isdir(current_session):
        _set_status("⚠ Session folder missing — cannot save", C["danger"])
        return
    data = []
    for i, entry in enumerate(log_data):
        d = dict(entry)
        d["objects"] = step_objects.get(i, [])
        d["crop"]    = step_crops.get(i)
        data.append(d)
    try:
        pname = project_name_var.get().strip()
    except Exception:
        pname = project_name
    doc = {"project_name": pname, "steps": data}
    try:
        target = os.path.join(current_session, "steps.json")
        tmp    = target + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=4)
        os.replace(tmp, target)
    except OSError as exc:
        log.exception("Save steps failed: %s", exc)
        _set_status(f"⚠ Save failed: {exc}", C["danger"])


def _monitor_rect_at(px: int, py: int) -> dict:
    """Rectangle (physical pixels) of the monitor that contains the screen point — asked from Windows
    directly, so it does not matter in which order the monitors are listed."""
    if sys.platform == "win32":
        try:
            import ctypes
            from ctypes import wintypes

            class MONITORINFO(ctypes.Structure):
                _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT),
                            ("rcWork", wintypes.RECT), ("dwFlags", wintypes.DWORD)]

            u32 = ctypes.windll.user32
            u32.MonitorFromPoint.restype = ctypes.c_void_p
            u32.MonitorFromPoint.argtypes = [wintypes.POINT, wintypes.DWORD]
            u32.GetMonitorInfoW.argtypes = [ctypes.c_void_p, ctypes.POINTER(MONITORINFO)]
            hmon = u32.MonitorFromPoint(wintypes.POINT(int(px), int(py)), 2)   # 2 = nearest monitor
            mi = MONITORINFO(); mi.cbSize = ctypes.sizeof(MONITORINFO)
            if hmon and u32.GetMonitorInfoW(hmon, ctypes.byref(mi)):
                r = mi.rcMonitor
                return {"left": r.left, "top": r.top, "width": r.right - r.left, "height": r.bottom - r.top}
        except Exception:
            log.exception("MonitorFromPoint failed")
    with mss.mss() as sct:
        mons = sct.monitors[1:]
        for m in mons:
            if m["left"] <= px < m["left"] + m["width"] and m["top"] <= py < m["top"] + m["height"]:
                return dict(m)
        primary = next((m for m in mons if m.get("is_primary")), mons[0])
        return dict(primary)


def capture_screenshot(filename: str, mon: dict | None = None):
    """Grab one monitor (default: the one under the cursor). Returns (path, monitor dict, scale factor applied)."""
    filepath = os.path.join(current_session, filename)
    if mon is None:
        try:
            mon = _monitor_rect_at(*mouse.Controller().position)
        except Exception:
            mon = None
    with mss.mss() as sct:
        if mon is None:
            mon = dict(next((m for m in sct.monitors[1:] if m.get("is_primary")), sct.monitors[1]))
        shot = sct.grab(mon)
        img = Image.frombytes("RGB", shot.size, shot.rgb)
    ratio = 1.0
    if img.width > CAPTURE_MAX_W:
        ratio = CAPTURE_MAX_W / img.width
        img = img.resize((CAPTURE_MAX_W, int(img.height * ratio)), Image.BILINEAR)
    base = filepath.rsplit(".", 1)[0]
    if capture_format == "png":
        out = base + ".png"
        img.save(out, "PNG")
    else:
        out = base + ".jpg"
        img.save(out, "JPEG", quality=85)
    return out, mon, ratio


def get_active_window() -> str:
    if not _HAS_GW:
        return "Unknown"
    try:
        win = gw.getActiveWindow()
        return win.title if win else "Unknown"
    except Exception:
        return "Unknown"


# ── Capture flash + camera click SFX ─────────────────────────────────────────────────────
_CAPTURE_FLASH_MS = 280
_FLASH_TRANSPARENT = "#010101"  # invisible with -transparentcolor
_camera_click_path = None

def _make_camera_click_wav():
    """Generate a short camera-shutter style click (damped sine) as WAV bytes."""
    rate = 44100
    duration = 0.1
    freq = 1600
    buf = io.BytesIO()
    with wave.open(buf, "wb") as wav:
        wav.setnchannels(1)
        wav.setsampwidth(2)
        wav.setframerate(rate)
        n = int(rate * duration)
        frames = bytearray()
        for i in range(n):
            t = i / rate
            amp = 0.85 * math.exp(-t * 50) * math.sin(2 * math.pi * freq * t)
            frames += struct.pack("<h", max(-32767, min(32767, int(32767 * amp))))
        wav.writeframes(bytes(frames))
    return buf.getvalue()

def _play_capture_sound():
    if winsound is None:
        return
    global _camera_click_path
    try:
        if _camera_click_path is None or not os.path.exists(_camera_click_path):
            import tempfile
            fd, _camera_click_path = tempfile.mkstemp(suffix=".wav", prefix="psr_click_")
            with os.fdopen(fd, "wb") as f:
                f.write(_make_camera_click_wav())
        winsound.PlaySound(_camera_click_path,
                           winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
    except Exception:
        try:
            winsound.MessageBeep(winsound.MB_OK)
        except Exception:
            pass

def _cleanup_sound_file():
    if _camera_click_path:
        try:
            os.remove(_camera_click_path)
        except OSError:
            pass

def _show_capture_flash(mon=None):
    """Brief frame around the captured monitor."""
    try:
        if mon is None:
            with mss.mss() as sct:
                mon = sct.monitors[0]
        x, y, w, h = mon["left"], mon["top"], mon["width"], mon["height"]
    except Exception:
        return
    win = tk.Toplevel(root)
    win.overrideredirect(True)
    win.attributes("-topmost", True)
    win.attributes("-alpha", 0.0)
    win.attributes("-transparentcolor", _FLASH_TRANSPARENT)
    win.geometry(f"{w}x{h}+{x}+{y}")
    win.configure(bg=_FLASH_TRANSPARENT)
    canvas = tk.Canvas(win, width=w, height=h, bg=_FLASH_TRANSPARENT, highlightthickness=0)
    canvas.pack(fill="both", expand=True)
    inset = 3
    canvas.create_rectangle(inset, inset, w - inset, h - inset, outline=C["accent"], width=4)
    # (delay_ms_until_next_step, alpha) — total _CAPTURE_FLASH_MS
    steps = [(60, 0.7), (60, 0.9), (80, 0.5), (_CAPTURE_FLASH_MS - 200, 0.0)]
    step_idx = [0]

    def tick():
        delay, alpha = steps[step_idx[0]]
        step_idx[0] += 1
        try:
            win.attributes("-alpha", alpha)
        except Exception:
            pass
        if step_idx[0] < len(steps):
            win.after(delay, tick)
        else:
            win.after(delay, lambda: (win.destroy() if win.winfo_exists() else None))

    win.after(0, tick)


# ══════════════════════════════════════ STEP HANDLING ══════════════════════════════════════

_capture_done: queue.Queue = queue.Queue()   # worker thread -> tkinter main thread


def _capture_worker() -> None:
    """Sequentially turn input events into screenshots without blocking the UI or input hooks."""
    while True:
        event_text = event_queue.get()
        if event_text is None:
            break
        try:
            if not recording or paused:
                continue
            if ignore_psr_focus and _psr_is_active():
                continue
            window  = get_active_window()   # title at event time, before the click changes focus
            session = current_session
            m = re.search(r"mouse button at \((-?\d+), (-?\d+)\)", event_text)
            try:
                pt = (int(m.group(1)), int(m.group(2))) if m else mouse.Controller().position
                mon_hint = _monitor_rect_at(*pt)
            except Exception:
                pt, mon_hint = None, None
            if capture_delay_ms > 0:
                time.sleep(capture_delay_ms / 1000.0)
            if not recording or not session:
                continue
            filename = f"step_{datetime.now().strftime('%H%M%S%f')}.{capture_format}"
            out, mon, ratio = capture_screenshot(filename, mon_hint)
            log.info("capture at %s -> monitor %s", pt, mon)
            click = None
            if m:
                cx = (int(m.group(1)) - mon["left"]) * ratio
                cy = (int(m.group(2)) - mon["top"]) * ratio
                if 0 <= cx < mon["width"] * ratio and 0 <= cy < mon["height"] * ratio:
                    click = [int(cx), int(cy)]
            _capture_done.put((event_text, window, os.path.basename(out), session, click, mon))
        except Exception:
            log.exception("Screenshot capture failed")


threading.Thread(target=_capture_worker, daemon=True).start()


def _describe(event_text: str, window: str) -> str:
    """Human wording for a captured input event."""
    m = re.match(r"released (\w+) mouse button", event_text)
    if m:
        action = f"{m.group(1).capitalize()}-click"
    elif event_text.startswith("used keyboard shortcut "):
        action = "Press " + event_text[len("used keyboard shortcut "):]
    elif event_text.startswith("pressed "):
        action = "Press " + event_text[len("pressed "):].replace(" key", "")
    else:
        action = "Screenshot"
    return f"{action} in '{window}'" if window and window != "Unknown" else action


def handle_event(event_text: str, window: str, filename: str, click=None, mon=None) -> None:
    """Main thread: register a captured screenshot as a new step."""
    global step_counter
    _play_capture_sound()
    _show_capture_flash(mon)
    step_counter = len(log_data) + 1
    entry  = {
        "step":        step_counter,
        "description": _describe(event_text, window),
        "screenshot":  filename,
        "id":          str(uuid.uuid4()),
    }
    if click:
        entry["click"] = click
    log_data.append(entry)
    step_objects[step_counter - 1] = []
    # Extract the input keyword and color-code it in the tray
    et = event_text
    if "mouse" in et:
        # "released left mouse button at (x, y)" → keyword="left mouse button"
        m = re.match(r"released (\w+ mouse button) at", et)
        _cap_kw    = m.group(1) if m else "mouse"
        _cap_rest  = et[m.end():].strip() if m else ""
        _cap_color = C["accent"]       # blue
    elif "shortcut" in et:
        # "used keyboard shortcut CTRL + S" → keyword="CTRL + S"
        _cap_kw    = et.replace("used keyboard shortcut ", "")
        _cap_rest  = ""
        _cap_color = "#e0a030"         # orange
    elif "key" in et:
        # "pressed A key" → keyword="A"
        m = re.match(r"pressed (.+?) key", et)
        _cap_kw    = m.group(1) if m else et
        _cap_rest  = "key"
        _cap_color = "#e0a030"         # orange
    elif "Scroll Lock" in et:
        _cap_kw    = "Scroll Lock"
        _cap_rest  = ""
        _cap_color = C["success"]      # green
    else:
        _cap_kw    = et[:40]
        _cap_rest  = ""
        _cap_color = C["text"]
    _last_capture[0] = (f"#{step_counter}", _cap_kw, _cap_rest, _cap_color)
    save_steps()
    _append_card()
    _update_rec_panel()
    step_counter += 1


# ══════════════════════════════════════ LISTENERS ══════════════════════════════════════

def _key_str(key):
    try:    return key.char.upper()
    except Exception: return str(key).replace("Key.", "").upper()


def _psr_is_active():
    """Return True if the currently active window belongs to PSR (title starts with 'PSR Pro')."""
    return get_active_window().startswith("PSR Pro")


def _on_click(x, y, button, pressed):
    if (not pressed) and recording and not paused and capture_on_click:
        btn = str(button).replace("Button.", "")
        event_queue.put(f"released {btn} mouse button at ({x}, {y})")


_hotkey_actions: queue.Queue = queue.Queue()  # filled by pynput thread, consumed by tkinter main loop
_HOTKEYS = {keyboard.Key.f6: "stop", keyboard.Key.f7: "pause", keyboard.Key.f8: "tray"}

def _on_press_key(key):
    # F6 stop / F7 pause / F8 tray — global, work even when the window is hidden
    if recording and key in _HOTKEYS:
        _hotkey_actions.put(_HOTKEYS[key])
        return

    if not recording or paused:
        return

    if capture_on_hotkey and key == keyboard.Key.scroll_lock:
        event_queue.put("manual capture (Scroll Lock)")
        return

    if not capture_keyboard:
        return

    with _keys_lock:
        pressed_keys.add(key)
        mods     = [k for k in pressed_keys if k in MODIFIER_KEYS]
        non_mods = [k for k in pressed_keys if k not in MODIFIER_KEYS]
        if mods and non_mods:
            combo = " + ".join([_key_str(m) for m in mods] + [_key_str(k) for k in non_mods])
            event_queue.put(f"used keyboard shortcut {combo}")
            pressed_keys.clear()
            return
        if not mods:
            event_queue.put(f"pressed {_key_str(key)} key")


def _on_release_key(key):
    with _keys_lock:
        pressed_keys.discard(key)


def start_listeners():
    global mouse_listener, keyboard_listener
    while True:   # drop events left over from a previous run
        try: event_queue.get_nowait()
        except queue.Empty: break
    with _keys_lock:
        pressed_keys.clear()
    mouse_listener    = mouse.Listener(on_click=_on_click)
    keyboard_listener = keyboard.Listener(on_press=_on_press_key, on_release=_on_release_key)
    mouse_listener.start()
    keyboard_listener.start()


def stop_listeners():
    if mouse_listener and mouse_listener.is_alive():
        mouse_listener.stop()
    if keyboard_listener and keyboard_listener.is_alive():
        keyboard_listener.stop()


def process_queue():
    while True:
        try:
            text, window, filename, session, click, mon = _capture_done.get_nowait()
        except queue.Empty:
            break
        if session == current_session:
            handle_event(text, window, filename, click, mon)
        else:   # session was switched while the shot was in flight
            try: os.remove(os.path.join(session, filename))
            except OSError: pass
    while True:
        try:
            action = _hotkey_actions.get_nowait()
        except queue.Empty:
            break
        if not recording:
            continue
        if action == "stop":
            stop_recording()
        elif action == "pause":
            _toggle_pause()
        elif action == "tray":
            if _rec_minimized[0]:
                _restore_rec_tray()
            else:
                _minimize_rec_tray()
    root.after(50, process_queue)


# ══════════════════════════════════════ UNDO ══════════════════════════════════════

def push_undo(step_index):
    """Snapshot both objects and crop for this step."""
    if step_index not in undo_stacks:
        undo_stacks[step_index] = []
    undo_stacks[step_index].append(json.dumps({
        "objects": step_objects.get(step_index, []),
        "crop":    step_crops.get(step_index),
        "click_hidden": bool(log_data[step_index].get("click_hidden")) if step_index < len(log_data) else False,
    }))


def pop_undo(step_index):
    stack = undo_stacks.get(step_index, [])
    if not stack:
        return False
    state = json.loads(stack.pop())
    step_objects[step_index] = state["objects"]
    if step_index < len(log_data):
        if state.get("click_hidden"):
            log_data[step_index]["click_hidden"] = True
        else:
            log_data[step_index].pop("click_hidden", None)
    if state["crop"] is None:
        step_crops.pop(step_index, None)
    else:
        step_crops[step_index] = state["crop"]
    return True


# ══════════════════════════════════════ INSERT CUSTOM STEP ══════════════════════════════════════

def _shift_step_data_up(from_index):
    """Shift step_objects, step_crops, undo_stacks indices up by 1 from from_index."""
    n = len(log_data)  # already includes new entry
    for i in range(n - 1, from_index - 1, -1):
        if i in step_objects:  step_objects[i+1]  = step_objects.pop(i)
        if i in step_crops:    step_crops[i+1]    = step_crops.pop(i)
        if i in undo_stacks:   undo_stacks[i+1]   = undo_stacks.pop(i)


def insert_custom_step(after_index=None):
    """Open a dialog to create a manual step with optional custom screenshot."""
    if not current_session:
        messagebox.showwarning("No session", "Start or open a recording first.")
        return

    dlg = ctk.CTkToplevel(root)
    dlg.title("Insert Custom Step")
    dlg.geometry("560x350")
    dlg.configure(fg_color=C["bg"])
    dlg.grab_set()
    dlg.transient(root)
    dlg.resizable(False, False)

    ctk.CTkLabel(dlg, text="Insert Custom Step",
                 font=("Segoe UI", 15, "bold"), text_color=C["text"]
                 ).pack(pady=(22,4), padx=24, anchor="w")

    ctk.CTkLabel(dlg, text="Step description",
                 font=("Segoe UI", 10), text_color=C["muted"]
                 ).pack(padx=24, anchor="w")

    desc_box = ctk.CTkTextbox(
        dlg, height=90, font=("Segoe UI", 12),
        fg_color=C["surface"], border_width=1, border_color=C["border"],
        corner_radius=6, wrap="word", text_color=C["text"])
    desc_box.pack(fill="x", padx=24, pady=(4, 14))

    img_row = ctk.CTkFrame(dlg, fg_color="transparent")
    img_row.pack(fill="x", padx=24)
    img_path_var = tk.StringVar(value="")
    _full_path   = [""]

    ctk.CTkLabel(img_row, textvariable=img_path_var,
                 font=("Segoe UI", 10), text_color=C["muted"],
                 anchor="w", wraplength=300).pack(side="left", fill="x", expand=True)

    def pick_image():
        p = filedialog.askopenfilename(
            title="Choose screenshot",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp"), ("All", "*.*")])
        if p:
            img_path_var.set(os.path.basename(p))
            _full_path[0] = p

    ctk.CTkButton(img_row, text="📁  Choose image (optional)", width=210,
                  fg_color=C["surface"], hover_color="#333",
                  font=("Segoe UI", 11), border_width=1, border_color=C["border"],
                  command=pick_image).pack(side="right")

    btn_row = ctk.CTkFrame(dlg, fg_color="transparent")
    btn_row.pack(fill="x", padx=24, pady=(18, 0))

    result    = [False]
    saved_desc = [""]
    saved_img  = [""]

    def do_insert():
        saved_desc[0] = desc_box.get("1.0", "end").strip() or "Custom step"
        saved_img[0]  = _full_path[0] or img_path_var.get().strip()
        result[0] = True
        dlg.destroy()

    ctk.CTkButton(btn_row, text="Cancel", width=90,
                  fg_color=C["surface"], hover_color=C["danger"],
                  font=("Segoe UI", 11), border_width=0,
                  command=dlg.destroy).pack(side="right", padx=(8,0))
    ctk.CTkButton(btn_row, text="＋  Insert Step", width=150,
                  fg_color=C["acc_dark"], hover_color=C["accent"],
                  font=("Segoe UI", 11, "bold"), border_width=0,
                  command=do_insert).pack(side="right")

    dlg.wait_window()
    if not result[0]:
        return

    desc     = saved_desc[0]
    src_full = saved_img[0]

    insert_pos = len(log_data) if after_index is None else after_index + 1

    if src_full and os.path.exists(src_full):
        fname = f"step_custom_{datetime.now().strftime('%H%M%S%f')}.png"
        dst   = os.path.join(current_session, fname)
        Image.open(src_full).convert("RGB").save(dst, "PNG")
    else:
        fname = None

    _shift_step_data_up(insert_pos)

    log_data.insert(insert_pos, {
        "step":        insert_pos + 1,
        "description": desc,
        "screenshot":  fname,
        "id":          str(uuid.uuid4()),
    })
    step_objects[insert_pos] = []

    global step_counter
    step_counter = len(log_data) + 1
    _renumber_and_rebuild(scroll_to=insert_pos)
    _set_status(f"✔  Custom step inserted at position {insert_pos + 1}", C["success"])


# ══════════════════════════════════════ QUICK INSERT ══════════════════════════════════════

_IMG_EXTS = {'.png', '.jpg', '.jpeg', '.bmp', '.webp', '.gif'}


def _insert_step_image(src, insert_pos=None, desc=None):
    """Create a step from a file path (str) or PIL Image. Returns the insert index."""
    if not current_session:
        return None
    if insert_pos is None:
        insert_pos = len(log_data)

    fname = f"step_paste_{datetime.now().strftime('%H%M%S%f')}.png"
    dst   = os.path.join(current_session, fname)

    if isinstance(src, str):
        Image.open(src).convert("RGB").save(dst, "PNG")
        desc = desc or os.path.basename(src)
    else:
        src.convert("RGB").save(dst, "PNG")
        desc = desc or "Pasted image"

    _shift_step_data_up(insert_pos)
    log_data.insert(insert_pos, {
        "step":        insert_pos + 1,
        "description": desc,
        "screenshot":  fname,
        "id":          str(uuid.uuid4()),
    })
    step_objects[insert_pos] = []

    global step_counter
    step_counter = len(log_data) + 1
    return insert_pos


def _insert_step_text(text, insert_pos=None):
    """Create a text-only step. Returns the insert index."""
    if not current_session:
        return None
    if insert_pos is None:
        insert_pos = len(log_data)

    _shift_step_data_up(insert_pos)
    log_data.insert(insert_pos, {
        "step":        insert_pos + 1,
        "description": text[:4000],
        "screenshot":  None,
        "id":          str(uuid.uuid4()),
    })
    step_objects[insert_pos] = []

    global step_counter
    step_counter = len(log_data) + 1
    return insert_pos


# ══════════════════════════════════════ PASTE & DROP ══════════════════════════════════════

def _active_insert_pos():
    """Return the insert position after the active step, or end."""
    if 0 <= active_index < len(log_data):
        return active_index + 1
    return len(log_data)


def _handle_paste(event=None):
    """Ctrl+V — create new step(s) from clipboard image or text."""
    try:
        focus = root.focus_get()
    except KeyError:
        focus = None
    if focus:
        wclass = focus.winfo_class()
        if wclass in ('Text', 'Entry', 'TEntry', 'Spinbox', 'TSpinbox'):
            return

    if not current_session:
        _set_status("Start or open a recording to paste into", C["warn"])
        return "break"

    pos = _active_insert_pos()

    try:
        clip = ImageGrab.grabclipboard()
        if clip is not None:
            if isinstance(clip, Image.Image):
                _insert_step_image(clip, pos)
                _renumber_and_rebuild(scroll_to=pos)
                _set_status(f"✔  Pasted image as step {pos + 1}", C["success"])
                return "break"
            if isinstance(clip, list):
                count = 0
                for p in clip:
                    if isinstance(p, str) and os.path.splitext(p)[1].lower() in _IMG_EXTS:
                        _insert_step_image(p, pos + count)
                        count += 1
                if count:
                    _renumber_and_rebuild(scroll_to=pos)
                    _set_status(f"✔  Pasted {count} image(s) starting at step {pos + 1}", C["success"])
                    return "break"
    except Exception:
        pass

    try:
        text = root.clipboard_get()
        if text and text.strip():
            _insert_step_text(text.strip(), pos)
            _renumber_and_rebuild(scroll_to=pos)
            _set_status(f"✔  Pasted text as step {pos + 1}", C["success"])
            return "break"
    except Exception:
        pass


def _compute_drop_index(x_root, y_root):
    """Insertion index for a file drop: over the step list → at the pointer, else after the active step."""
    try:
        fx = filmstrip.canvas.winfo_rootx()
        if fx <= x_root <= fx + filmstrip.canvas.winfo_width():
            idx = filmstrip.index_at_root(y_root)
            if idx is not None:
                return idx
    except Exception:
        pass
    return _active_insert_pos()


def _handle_file_drop(raw_paths, x_root, y_root):
    """Process file paths dropped onto the app."""
    if not current_session:
        _set_status("Start or open a recording to drop into", C["warn"])
        return

    try:
        paths = root.tk.splitlist(raw_paths)
    except Exception:
        paths = raw_paths.split()

    pos   = _compute_drop_index(x_root, y_root)
    count = 0

    for fpath in paths:
        fpath = fpath.strip()
        if not os.path.isfile(fpath):
            continue
        ext = os.path.splitext(fpath)[1].lower()
        if ext in _IMG_EXTS:
            _insert_step_image(fpath, pos + count)
            count += 1
        elif ext in ('.txt', '.md', '.log'):
            try:
                with open(fpath, 'r', encoding='utf-8', errors='replace') as f:
                    text = f.read(4000).strip()
                if text:
                    _insert_step_text(text, pos + count)
                    count += 1
            except Exception:
                pass

    if count:
        _renumber_and_rebuild(scroll_to=pos)
        _set_status(f"✔  Dropped {count} item(s) at step {pos + 1}", C["success"])
    else:
        _set_status("No supported files found in drop", C["muted"])


def _setup_dnd():
    """Register the cards panel as a drag-and-drop target (requires tkinterdnd2)."""
    if not _HAS_DND:
        return
    try:
        tkdnd_path = os.path.join(os.path.dirname(
            __import__('tkinterdnd2').__file__), 'tkdnd')
        root.tk.call('lappend', 'auto_path', tkdnd_path)
        root.tk.eval('package require tkdnd')
    except Exception:
        return

    target_w = body._w

    def _tcl_drop(*args):
        raw = root.tk.getvar('::_psr_drop_data')
        x   = root.winfo_pointerx()
        y   = root.winfo_pointery()
        root.after(0, lambda: _handle_file_drop(raw, x, y))

    cmd = root.register(_tcl_drop)

    try:
        root.tk.call('tkdnd::drop_target', 'register', target_w, 'DND_Files')
        root.tk.eval(
            f'bind {target_w} <<Drop:DND_Files>> '
            f'{{set ::_psr_drop_data %D; {cmd}}}')
    except Exception as e:
        log.warning("DnD setup failed: %s", e)


# ══════════════════════════════════════ DESC AUTO-SAVE ══════════════════════════════════════

def _setup_desc_autosave(card):
    """Enable built-in undo and debounced auto-save on card.desc_box."""
    try:
        card.desc_box._textbox.configure(undo=True, maxundo=-1)
        card.desc_box._textbox.edit_reset()
    except Exception:
        pass
    card._desc_timer = None
    def _on_key(event):
        if card._desc_timer:
            card.desc_box.after_cancel(card._desc_timer)
        card._desc_timer = card.desc_box.after(400, lambda: _flush_desc(card))
    card.desc_box.bind("<KeyRelease>", _on_key)

def _flush_desc(card):
    """Persist current desc_box text to log_data and disk."""
    card._desc_timer = None
    try:
        new_text = card.desc_box.get("1.0", "end").strip()
    except Exception:
        return
    if 0 <= card.index < len(log_data) and log_data[card.index]["description"] != new_text:
        log_data[card.index]["description"] = new_text
        save_steps()
        _refresh_sidebar()


# ══════════════════════════════════════ STEP DELETE ══════════════════════════════════════

def _delete_step(idx):
    """Confirm and delete the step at idx, then rebuild."""
    _selected.clear()
    _selected.add(idx)
    _delete_selected()


def _delete_selected():
    """Confirm and delete all steps in _selected, then rebuild."""
    if not _selected:
        return
    to_delete = {i for i in _selected if 0 <= i < len(log_data)}
    if not to_delete:
        return
    n_del = len(to_delete)
    if n_del == 1:
        step_num = log_data[next(iter(to_delete))]["step"]
        msg = f"Delete Step {step_num}?"
    else:
        msg = f"Delete {n_del} selected steps?"
    if not messagebox.askyesno("Delete", msg):
        return

    editor._flush_pending()
    new_log   = []
    new_objs  = {}
    new_crops = {}
    new_idx   = 0
    for old_idx in range(len(log_data)):
        if old_idx in to_delete:
            screenshot = log_data[old_idx].get("screenshot")
            if screenshot:
                for p in (os.path.join(current_session, screenshot), _thumb_cache_file(os.path.join(current_session, screenshot))):
                    try: os.remove(p)
                    except OSError: pass
        else:
            new_log.append(log_data[old_idx])
            if old_idx in step_objects: new_objs[new_idx]  = step_objects[old_idx]
            if old_idx in step_crops:   new_crops[new_idx] = step_crops[old_idx]
            new_idx += 1

    log_data.clear();    log_data.extend(new_log)
    step_objects.clear(); step_objects.update(new_objs)
    step_crops.clear();   step_crops.update(new_crops)
    undo_stacks.clear()
    _selected.clear()
    global step_counter
    step_counter = len(log_data) + 1  # keep counter in sync for "Continue"
    _renumber_and_rebuild(scroll_to=min(min(to_delete), len(log_data) - 1) if log_data else None)


# ══════════════════════════════════════ THUMBNAIL CACHE ══════════════════════════════════════

THUMB_W, THUMB_H = 132, 74
def _rrect(cv, x1, y1, x2, y2, r, **kw):
    """Rounded rectangle on a tk.Canvas."""
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


def _round_corners(im: Image.Image, r: int) -> Image.Image:
    im = im.convert("RGBA")
    k = 4
    mask = Image.new("L", (im.width * k, im.height * k), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, im.width * k - 1, im.height * k - 1], r * k, fill=255)
    im.putalpha(mask.resize(im.size, Image.LANCZOS))
    return im


def _ellipsize(t: str, n: int) -> str:
    t = t.replace("\n", " ")
    return t if len(t) <= n else t[: n - 1] + "…"


def _split_desc(desc: str) -> tuple[str, str]:
    """(headline, secondary) for a step description — works for old and new recordings."""
    m = re.match(r"^(.*?) in '(.*)'$", desc, re.S)
    if m:
        return m.group(1), m.group(2)
    m = re.match(r"^In '(.*)', (.*)$", desc, re.S)
    if m:
        a = m.group(2)
        mm = re.match(r"released (\w+) mouse button", a)
        if mm:
            a = f"{mm.group(1).capitalize()}-click"
        elif a.startswith("used keyboard shortcut "):
            a = "Press " + a[len("used keyboard shortcut "):]
        elif a.startswith("pressed "):
            a = "Press " + a[len("pressed "):].replace(" key", "")
        return a, m.group(1)
    return desc, ""


_THUMB_MEM: dict = {}            # (path, mtime) -> PhotoImage  (main thread only)
_THUMB_MEM_MAX = 400
_thumb_req: queue.Queue = queue.Queue()
_thumb_res: queue.Queue = queue.Queue()
_thumb_pending: set = set()


def _thumb_cache_file(img_path: str) -> str:
    """Small JPEG kept next to the screenshots so reopening a session is instant."""
    folder = os.path.join(os.path.dirname(img_path), ".thumbs")
    return os.path.join(folder, os.path.splitext(os.path.basename(img_path))[0] + ".jpg")


def _thumb_worker():
    while True:
        img_path = _thumb_req.get()
        if img_path is None:
            break
        try:
            src_m = os.path.getmtime(img_path)
            cache = _thumb_cache_file(img_path)
            im = None
            if os.path.exists(cache) and os.path.getmtime(cache) >= src_m:
                try:
                    im = Image.open(cache); im.load()
                except Exception:
                    im = None
            if im is None:
                im = Image.open(img_path)
                if getattr(im, "format", "") == "JPEG":
                    try: im.draft("RGB", (THUMB_W * 2, THUMB_H * 2))
                    except Exception: pass
                im = im.convert("RGB")
                im.thumbnail((THUMB_W, THUMB_H), Image.BILINEAR)
                try:
                    os.makedirs(os.path.dirname(cache), exist_ok=True)
                    im.save(cache, "JPEG", quality=80)
                except OSError:
                    pass
            _thumb_res.put((img_path, src_m, im))
        except Exception:
            log.exception("Thumbnail failed for %s", img_path)
            _thumb_res.put((img_path, 0, None))


threading.Thread(target=_thumb_worker, daemon=True).start()


def _get_thumb(img_path: str):
    """PhotoImage for a screenshot, or None while it is still being generated."""
    try:
        mt = os.path.getmtime(img_path)
    except OSError:
        return None
    ph = _THUMB_MEM.get((img_path, mt))
    if ph is None and img_path not in _thumb_pending:
        _thumb_pending.add(img_path)
        _thumb_req.put(img_path)
        root.after(40, _drain_thumbs)
    return ph


def _drain_thumbs():
    got = False
    while True:
        try:
            img_path, mt, im = _thumb_res.get_nowait()
        except queue.Empty:
            break
        _thumb_pending.discard(img_path)
        if im is None:
            continue
        if len(_THUMB_MEM) >= _THUMB_MEM_MAX:
            for k in list(_THUMB_MEM)[: _THUMB_MEM_MAX // 2]:
                _THUMB_MEM.pop(k, None)
        _THUMB_MEM[(img_path, mt)] = ImageTk.PhotoImage(_round_corners(im, 8))
        got = True
    if got:
        filmstrip.redraw()
    if _thumb_pending:
        root.after(60, _drain_thumbs)


# ══════════════════════════════════════ FILMSTRIP ══════════════════════════════════════

class Filmstrip:
    """Virtualised step list: only the visible rows are drawn, thumbnails load lazily."""
    ITEM_H = 92

    def __init__(self, parent):
        self.frame = ctk.CTkFrame(parent, width=332, corner_radius=12, fg_color=C["panel"],
                                  border_width=1, border_color=C["border"])
        self.frame.pack_propagate(False)
        hdr = ctk.CTkFrame(self.frame, height=52, fg_color="transparent", corner_radius=0)
        hdr.pack(fill="x", padx=(16, 10)); hdr.pack_propagate(False)
        ctk.CTkLabel(hdr, text="Steps", font=(UI_FONT, 15, "bold"), text_color=C["text"]).pack(side="left")
        self.count_label = ctk.CTkLabel(hdr, text="0", font=(UI_FONT, 11), text_color=C["muted"],
                                        fg_color=C["surface"], corner_radius=8, width=26, height=20)
        self.count_label.pack(side="left", padx=8)
        self.add_btn = ctk.CTkButton(hdr, text=ICON["add"], command=lambda: insert_custom_step(),
            font=ic(15), width=34, height=34, corner_radius=8, fg_color=C["acc_soft"],
            text_color=C["accent"], hover_color=C["surface2"], border_width=0)
        self.add_btn.pack(side="right")
        tip(self.add_btn, "Add a blank step\n(Ctrl+V pastes an image or text as a step)")

        self.sb = ctk.CTkScrollbar(self.frame, command=self._on_sb, width=10)
        self.sb.pack(side="right", fill="y", padx=(0, 3), pady=(0, 8))
        self.canvas = tk.Canvas(self.frame, bg=C["panel"], highlightthickness=0, cursor="arrow")
        self.canvas.pack(side="left", fill="both", expand=True, padx=(6, 0), pady=(0, 8))

        self._y = 0
        self._drag = None
        c = self.canvas
        c.bind("<Configure>",       lambda e: self.redraw())
        c.bind("<MouseWheel>",      self._on_wheel)
        c.bind("<ButtonPress-1>",   self._on_press)
        c.bind("<B1-Motion>",       self._on_motion)
        c.bind("<ButtonRelease-1>", self._on_release)
        c.bind("<Button-3>",        self._on_right)

    # ── geometry helpers ──
    def _max_y(self):
        return max(0, len(log_data) * self.ITEM_H - self.canvas.winfo_height() + 4)

    def _clamp(self):
        self._y = max(0, min(self._y, self._max_y()))

    def index_at(self, y):
        if not log_data:
            return -1
        return max(0, min(len(log_data) - 1, int((y + self._y) // self.ITEM_H)))

    def index_at_root(self, y_root):
        """Insertion index for a pointer over the strip (None if the pointer is elsewhere)."""
        try:
            top = self.canvas.winfo_rooty()
            if not (top <= y_root <= top + self.canvas.winfo_height()):
                return None
            return max(0, min(len(log_data), int((y_root - top + self._y + self.ITEM_H // 2) // self.ITEM_H)))
        except Exception:
            return None

    def ensure_visible(self, index):
        if index < 0:
            return
        top = index * self.ITEM_H
        h = self.canvas.winfo_height()
        if top < self._y:
            self._y = top
        elif top + self.ITEM_H > self._y + h:
            self._y = top + self.ITEM_H - h + 4
        self.redraw()

    def scroll_to_end(self):
        self._y = self._max_y()
        self.redraw()

    # ── drawing ──
    def redraw(self):
        c = self.canvas
        c.delete("all")
        n = len(log_data)
        self.count_label.configure(text=str(n))
        W, H = c.winfo_width(), c.winfo_height()
        self._clamp()
        total = n * self.ITEM_H
        if total <= H:
            self.sb.set(0, 1)
        else:
            self.sb.set(self._y / total, (self._y + H) / total)
        if n == 0:
            _viewfinder(c, W // 2, 90, 46, C["border_hi"], 3)
            c.create_text(W // 2, 150, text="No steps yet", fill=C["muted"], font=(UI_FONT, 12, "bold"))
            c.create_text(W // 2, 178, text="Record a workflow, paste an\nimage (Ctrl+V) or drop files here",
                          fill=C["faint"], font=(UI_FONT, 10), justify="center")
            return
        first = self._y // self.ITEM_H
        last = min(n - 1, (self._y + H) // self.ITEM_H)
        for i in range(first, last + 1):
            self._draw_item(i, i * self.ITEM_H - self._y, W)
        if self._drag and self._drag["active"]:
            ly = self._drag["gap"] * self.ITEM_H - self._y
            _rrect(c, 6, ly - 2, W - 6, ly + 2, 2, fill=C["accent"], outline="", tags="drop")

    def _draw_item(self, i, y0, W):
        c = self.canvas
        entry = log_data[i]
        active = i == active_index
        selected = i in _selected
        bg = C["acc_soft"] if active else (C["surface"] if selected else C["card"])
        border = C["accent"] if active else (C["acc_dark"] if selected else C["border"])
        h = self.ITEM_H - 8
        _rrect(c, 3, y0 + 4, W - 3, y0 + 4 + h, 12, fill=bg, outline=border, width=2 if active else 1)
        tx, ty = 12, y0 + 4 + (h - THUMB_H) // 2
        shot = entry.get("screenshot")
        ph = _get_thumb(os.path.join(current_session, shot)) if shot and current_session else None
        if ph is not None:
            c.create_image(tx, ty, anchor="nw", image=ph)
        else:
            _rrect(c, tx, ty, tx + THUMB_W, ty + THUMB_H, 8, fill="#0a0c10", outline="")
            c.create_text(tx + THUMB_W // 2, ty + THUMB_H // 2, fill=C["faint"],
                          text=ICON["note"] if not shot else ICON["image"], font=ic(20))
        _rrect(c, tx + 6, ty + 6, tx + 34, ty + 24, 6, fill="#0b0d12", outline="")
        c.create_text(tx + 20, ty + 15, text=f"{entry['step']:02d}", fill=C["accent"],
                      font=("Consolas", 10, "bold"))
        x2 = tx + THUMB_W + 12
        tw = max(40, W - x2 - 12)
        title, sub = _split_desc(entry["description"])
        if shot:
            c.create_text(x2, y0 + 18, anchor="nw", text=_ellipsize(title, 22), width=tw,
                          fill=C["text"], font=(UI_FONT, 11, "bold"))
            if sub:
                c.create_text(x2, y0 + 42, anchor="nw", text=_ellipsize(sub, 40), width=tw,
                              fill=C["muted"], font=(UI_FONT, 9))
        else:
            c.create_text(x2, y0 + 18, anchor="nw", text=_ellipsize(entry["description"], 64), width=tw,
                          fill=C["text"], font=(UI_FONT, 10))

    # ── scrolling ──
    def _on_sb(self, *args):
        n = len(log_data) * self.ITEM_H
        if args[0] == "moveto":
            self._y = int(float(args[1]) * n)
        elif args[0] == "scroll":
            self._y += int(args[1]) * self.ITEM_H // (2 if args[2] == "units" else 1)
        self.redraw()

    def _on_wheel(self, e):
        self._y -= int(e.delta / 120 * self.ITEM_H * 0.7)
        self.redraw()

    # ── mouse ──
    def _on_press(self, e):
        global active_index, _sel_anchor
        self.canvas.focus_set()
        idx = self.index_at(e.y)
        if idx < 0:
            return
        ctrl  = (e.state & 0x0004) != 0
        shift = (e.state & 0x0001) != 0
        if shift and _sel_anchor >= 0:
            lo, hi = sorted([_sel_anchor, idx])
            _selected.clear(); _selected.update(range(lo, hi + 1))
        elif ctrl:
            _selected.symmetric_difference_update({idx})
            _sel_anchor = idx
        else:
            _selected.clear(); _selected.add(idx)
            _sel_anchor = idx
            self._drag = {"src": idx, "y0": e.y, "active": False, "gap": idx}
        active_index = idx
        editor.show(idx)
        self.redraw()

    def _on_motion(self, e):
        d = self._drag
        if not d:
            return
        if not d["active"] and abs(e.y - d["y0"]) > 6:
            d["active"] = True
        if d["active"]:
            H = self.canvas.winfo_height()
            if e.y < 20:   self._y -= 14
            elif e.y > H - 20: self._y += 14
            self._clamp()
            d["gap"] = max(0, min(len(log_data), int((e.y + self._y + self.ITEM_H // 2) // self.ITEM_H)))
            self.redraw()

    def _on_release(self, e):
        d, self._drag = self._drag, None
        if not d or not d["active"]:
            return
        src, gap = d["src"], d["gap"]
        dst = gap - 1 if gap > src else gap
        dst = max(0, min(dst, len(log_data) - 1))
        if dst != src:
            _reorder_step(src, dst)
        else:
            self.redraw()

    def _on_right(self, e):
        global active_index
        idx = self.index_at(e.y)
        if idx >= 0 and idx not in _selected:
            _selected.clear(); _selected.add(idx)
            active_index = idx
            editor.show(idx)
            self.redraw()
        _show_steps_context_menu(e)


def _viewfinder(c, cx, cy, size, col, w=3):
    """Four corner brackets — the app's visual motif — centred on (cx, cy)."""
    h, L = size / 2, size * 0.32
    for sx, sy in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
        x, y = cx + sx * h, cy + sy * h
        c.create_line(x - sx * L, y, x, y, x, y - sy * L, fill=col, width=w, capstyle="round", joinstyle="round")


def _refresh_sidebar():
    filmstrip.redraw()


# ══════════════════════════════════════ EDITOR VIEW ══════════════════════════════════════

class EditorView:
    """One big canvas for the active step: fit/zoom/pan, annotation tools, description."""

    def __init__(self, parent):
        self.index        = -1
        self.is_text_only = False
        self._src         = None      # full-resolution PIL image of the active screenshot
        self._src_key     = None
        self._orig        = (1, 1)
        self._photo       = None
        self._zoom        = 1.0
        self._pan         = (0.0, 0.0)
        self._vb          = (0, 0, 1, 1)   # view box (original image coordinates)
        self._scale       = 1.0            # canvas pixels per original pixel
        self._ox = self._oy = 0.0          # canvas position of the view box origin
        self._selected_obj = None
        self._sel_click    = False     # the captured click marker is selected
        self._drag_info    = None
        self._create_start = None
        self._create_rect  = None
        self._draw_pts     = []
        self._last_draw    = None
        self._resize_job   = None
        self._desc_timer   = None
        self._build(parent)

    # ── UI ────────────────────────────────────────────────────────────────
    def _build(self, parent):
        self.frame = ctk.CTkFrame(parent, corner_radius=12, fg_color=C["panel"],
                                  border_width=1, border_color=C["border"])
        hdr = ctk.CTkFrame(self.frame, height=52, fg_color="transparent", corner_radius=0)
        hdr.pack(side="top", fill="x", padx=(18, 10)); hdr.pack_propagate(False)
        self._title = ctk.CTkLabel(hdr, text="", font=(UI_FONT, 15, "bold"), text_color=C["text"])
        self._title.pack(side="left")
        self._sub = ctk.CTkLabel(hdr, text="", font=(UI_FONT, 11), text_color=C["faint"])
        self._sub.pack(side="left", padx=(10, 0))

        IB = dict(width=34, height=34, corner_radius=8, font=ic(15), fg_color="transparent",
                  text_color=C["muted"], border_width=0, hover_color=C["surface2"])
        def ibtn(icon, cmd, hint, **kw):
            b = ctk.CTkButton(hdr, text=icon, command=cmd, **{**IB, **kw})
            b.pack(side="right", padx=1)
            tip(b, hint)
            return b
        ibtn(ICON["delete"], lambda: self.index >= 0 and _delete_step(self.index), "Delete this step  [Del]",
             hover_color=C["danger"])
        ibtn(ICON["full"], self._show_fullscreen, "Show the annotated result full screen")
        ibtn(ICON["fit"], self.reset_view, "Fit to window  (double-click the image)")
        self._zoom_lbl = ctk.CTkLabel(hdr, text="", font=(UI_FONT, 10), text_color=C["muted"], width=46)
        self._zoom_lbl.pack(side="right")
        ctk.CTkFrame(hdr, width=1, fg_color=C["border"]).pack(side="right", fill="y", pady=12, padx=8)
        self._reset_crop_btn = ibtn(ICON["reset"], self._reset_crop, "Reset crop")
        self._undo_btn = ibtn(ICON["undo"], self._undo, "Undo  [Ctrl+Z]")

        # tool options: hint text on the left, colours + sizes on the right (filled by set_tool)
        self.opts = ctk.CTkFrame(self.frame, height=46, fg_color=C["surface"], corner_radius=10)
        self.opts.pack(side="top", fill="x", padx=14, pady=(0, 10)); self.opts.pack_propagate(False)
        self.hint = ctk.CTkLabel(self.opts, text="", font=(UI_FONT, 11), text_color=C["muted"], anchor="w")
        self.hint.pack(side="left", padx=16)
        self.opt_colors = ctk.CTkFrame(self.opts, fg_color="transparent")
        self.opt_sizes  = ctk.CTkFrame(self.opts, fg_color="transparent")

        # bottom: description (+ numbered callouts when the step has markers)
        bottom = ctk.CTkFrame(self.frame, fg_color="transparent")
        bottom.pack(side="bottom", fill="x", padx=14, pady=(10, 14))
        bottom.grid_columnconfigure(0, weight=3)
        bottom.grid_columnconfigure(1, weight=2)
        dcol = ctk.CTkFrame(bottom, fg_color="transparent")
        dcol.grid(row=0, column=0, sticky="nsew")
        ctk.CTkLabel(dcol, text="DESCRIPTION", font=(UI_FONT, 9, "bold"), text_color=C["faint"]
                     ).pack(anchor="w", pady=(0, 4))
        self.desc_box = ctk.CTkTextbox(
            dcol, height=68, font=(UI_FONT, 13), fg_color=C["surface"], border_width=1,
            border_color=C["border"], corner_radius=10, wrap="word", text_color=C["text"])
        self.desc_box.pack(fill="x")
        _setup_desc_autosave(self)

        self.callouts_col = ctk.CTkFrame(bottom, fg_color="transparent")     # gridded when markers exist
        ctk.CTkLabel(self.callouts_col, text="NUMBERS  ·  what each marker points at", font=(UI_FONT, 9, "bold"),
                     text_color=C["faint"]).pack(anchor="w", pady=(0, 4))
        self.callouts = ctk.CTkFrame(self.callouts_col, fg_color=C["surface"], corner_radius=10,
                                     border_width=1, border_color=C["border"])
        self.callouts.pack(fill="x", anchor="n")
        self._call_entries = {}
        self._note_timer = None

        # middle: tool rail right next to the picture
        mid = ctk.CTkFrame(self.frame, fg_color="transparent")
        mid.pack(side="top", fill="both", expand=True, padx=14)
        self.rail = ctk.CTkFrame(mid, fg_color=C["surface"], corner_radius=10)
        self.rail.pack(side="left", fill="y", padx=(0, 10))
        self._rail_items, self._rail_cols = [], 0
        mid.bind("<Configure>", lambda e: self.layout_rail())
        self._mid = mid

        wrap = ctk.CTkFrame(mid, fg_color=C["bg"], corner_radius=10)
        wrap.pack(side="left", fill="both", expand=True)
        self.canvas = tk.Canvas(wrap, bg=C["bg"], highlightthickness=0, cursor="arrow")
        self.canvas.pack(fill="both", expand=True, padx=6, pady=6)
        c = self.canvas
        c.bind("<ButtonPress-1>",   self._on_press)
        c.bind("<B1-Motion>",       self._on_drag)
        c.bind("<ButtonRelease-1>", self._on_release)
        c.bind("<Motion>",          self._on_motion)
        c.bind("<Button-3>",        self._on_right_click)
        c.bind("<Double-Button-1>", self._on_dblclick)
        c.bind("<MouseWheel>",      self._on_wheel)
        c.bind("<ButtonPress-2>",   self._pan_start)
        c.bind("<B2-Motion>",       self._pan_move)
        c.bind("<ButtonRelease-2>", lambda e: setattr(self, "_drag_info", None))
        c.bind("<Configure>",       self._on_configure)

    # ── tool rail (one column; wraps to two when the picture area is short) ─────
    def add_rail_item(self, kind, widget):
        self._rail_items.append((kind, widget))

    def layout_rail(self):
        if not self._rail_items:
            return
        avail = self._mid.winfo_height() - 12
        need = sum(42 if k == "btn" else 14 for k, _ in self._rail_items) + 10
        cols = 1 if need <= avail else 2
        if cols == self._rail_cols:
            return
        self._rail_cols = cols
        for _, w in self._rail_items:
            w.grid_forget()
        r = c = 0
        for kind, w in self._rail_items:
            if kind == "sep":
                if c:
                    r, c = r + 1, 0
                w.grid(row=r, column=0, columnspan=cols, pady=3)
                r += 1
            else:
                w.grid(row=r, column=c, padx=4, pady=(6 if r == 0 else 1, 1))
                c += 1
                if c >= cols:
                    r, c = r + 1, 0

    # ── numbered callouts ──────────────────────────────────────────────────
    def _markers(self):
        return [o for o in step_objects.get(self.index, []) if o["type"] == "marker"]

    def _renumber_markers(self):
        for k, o in enumerate(self._markers()):
            o["n"] = k + 1

    def refresh_callouts(self, focus_n=None):
        """One editable note per numbered marker, shown next to the description."""
        for w in self.callouts.winfo_children():
            w.destroy()
        self._call_entries = {}
        marks = self._markers() if self._usable() else []
        if not marks:
            self.callouts_col.grid_remove()
            return
        self.callouts_col.grid(row=0, column=1, sticky="nsew", padx=(14, 0))
        for o in marks:
            row = ctk.CTkFrame(self.callouts, fg_color="transparent")
            row.pack(fill="x", padx=4, pady=3)
            badge = tk.Canvas(row, width=26, height=26, bg=C["surface"], highlightthickness=0)
            badge.create_oval(2, 2, 24, 24, fill=o["color"], outline="#ffffff", width=2)
            badge.create_text(13, 13, text=str(o["n"]), font=("Segoe UI", -12, "bold"),
                              fill="#000000" if _luma(_hex_to_rgb(o["color"])) > 0.6 else "#ffffff")
            badge.pack(side="left", padx=(4, 8))
            ent = ctk.CTkEntry(row, height=30, fg_color=C["bg"], border_color=C["border"], text_color=C["text"],
                               font=(UI_FONT, 12), placeholder_text=f"What does {o['n']} point at?",
                               placeholder_text_color=C["faint"])
            ent.pack(side="left", fill="x", expand=True, padx=(0, 4))
            if o.get("note"):
                ent.insert(0, o["note"])
            ent.bind("<KeyRelease>", lambda e, ob=o, en=ent: self._note_typed(ob, en))
            ent.bind("<FocusIn>", lambda e, ob=o: self._select_marker(ob))
            self._call_entries[o["n"]] = ent
        if focus_n in self._call_entries:
            ent = self._call_entries[focus_n]
            self.frame.after(60, lambda: ent.winfo_exists() and ent.focus_set())

    def _note_typed(self, obj, entry):
        obj["note"] = entry.get().strip()
        if self._note_timer:
            self.frame.after_cancel(self._note_timer)
        self._note_timer = self.frame.after(350, save_steps)

    def _select_marker(self, obj):
        objs = step_objects.get(self.index, [])
        for i, o in enumerate(objs):
            if o is obj:
                self._selected_obj = i
                self._render_objects()
                return

    def _highlight_callout(self, obj):
        for n, ent in self._call_entries.items():
            ent.configure(border_color=C["accent"] if n == obj.get("n") else C["border"])

    def _on_configure(self, _e=None):
        if self._resize_job:
            self.canvas.after_cancel(self._resize_job)
        self._resize_job = self.canvas.after(40, self.render)

    # ── state ─────────────────────────────────────────────────────────────
    def _flush_pending(self):
        if self._desc_timer:
            try: self.desc_box.after_cancel(self._desc_timer)
            except Exception: pass
            _flush_desc(self)

    def _usable(self):
        return self.index >= 0 and not self.is_text_only and self._src is not None

    def show(self, index, force=False):
        """Display step `index` (or nothing for -1)."""
        if index == self.index and not force:
            return
        self._flush_pending()
        self._selected_obj = None
        self._sel_click    = False
        self._drag_info    = None
        self._create_rect  = self._create_start = None
        self._draw_pts     = []
        self._last_draw    = None
        self._zoom, self._pan = 1.0, (0.0, 0.0)
        if not (0 <= index < len(log_data)):
            self.index, self.is_text_only, self._src, self._src_key = -1, False, None, None
            self._title.configure(text="")
            self._sub.configure(text="")
            self.desc_box.configure(state="normal")
            self.desc_box.delete("1.0", "end")
            self.desc_box.configure(state="disabled")
            self._refresh_undo_btn()
            self.render()
            self.refresh_callouts()
            return
        self.index = index
        entry = log_data[index]
        self.is_text_only = entry.get("screenshot") is None
        self._title.configure(text=f"Step {entry['step']:02d}")
        self.desc_box.configure(state="normal", height=220 if self.is_text_only else 68)
        self.desc_box.delete("1.0", "end")
        self.desc_box.insert("end", entry["description"])
        try: self.desc_box._textbox.edit_reset()
        except Exception: pass
        self._load_src()
        self._sub.configure(text="Note" if self.is_text_only else (f"{self._orig[0]} × {self._orig[1]}" if self._src else "missing"))
        self._refresh_undo_btn()
        self.render()
        self.refresh_callouts()

    def _load_src(self):
        self._src = None
        if self.is_text_only or not current_session:
            self._src_key = None
            return
        path = os.path.join(current_session, log_data[self.index]["screenshot"])
        try:
            key = (path, os.path.getmtime(path))
            with Image.open(path) as im:
                self._src = im.convert("RGB")
            self._orig = self._src.size
            self._src_key = key
        except Exception:
            log.exception("Could not load %s", path)
            self._src_key = None

    def reload_src(self):
        self._src_key = None
        self._load_src()

    def reset_view(self):
        self._zoom, self._pan = 1.0, (0.0, 0.0)
        self.render()

    # ── coordinates ───────────────────────────────────────────────────────
    def _crop_box(self):
        """Crop region (or whole image) in original coordinates."""
        W, H = self._orig
        crop = step_crops.get(self.index)
        if not crop:
            return 0, 0, W, H
        x1, x2 = sorted([crop["x1"], crop["x2"]]); y1, y2 = sorted([crop["y1"], crop["y2"]])
        x1 = max(0, min(x1, W - 1)); y1 = max(0, min(y1, H - 1))
        return x1, y1, max(x1 + 1, min(x2, W)), max(y1 + 1, min(y2, H))

    def _view_box(self):
        # while the crop tool is active the whole image is shown so the crop can be redrawn freely
        if annotation_tool == "crop":
            return 0, 0, self._orig[0], self._orig[1]
        return self._crop_box()

    def _geometry(self):
        cw = max(2, self.canvas.winfo_width()); ch = max(2, self.canvas.winfo_height())
        self._vb = self._view_box()
        vx1, vy1, vx2, vy2 = self._vb
        vw, vh = max(1, vx2 - vx1), max(1, vy2 - vy1)
        m = 8
        fit = max(0.01, min((cw - 2 * m) / vw, (ch - 2 * m) / vh, 1.5))
        self._scale = fit * self._zoom
        if self._zoom <= 1.0:
            self._pan = (0.0, 0.0)
        self._ox = (cw - vw * self._scale) / 2 + self._pan[0]
        self._oy = (ch - vh * self._scale) / 2 + self._pan[1]

    def _c2f(self, cx, cy):
        vx1, vy1 = self._vb[0], self._vb[1]
        return vx1 + (cx - self._ox) / self._scale, vy1 + (cy - self._oy) / self._scale

    def _c2i(self, cx, cy):
        x, y = self._c2f(cx, cy)
        W, H = self._orig
        return int(round(max(0, min(W, x)))), int(round(max(0, min(H, y))))

    def _i2c(self, x, y):
        return self._ox + (x - self._vb[0]) * self._scale, self._oy + (y - self._vb[1]) * self._scale

    def _bbox_canvas(self, obj):
        x1, y1, x2, y2 = _obj_bbox_img(obj)
        return (*self._i2c(x1, y1), *self._i2c(x2, y2))

    # ── rendering ─────────────────────────────────────────────────────────
    def render(self):
        c = self.canvas
        c.delete("all")
        self._photo = None
        cw, ch = max(2, c.winfo_width()), max(2, c.winfo_height())
        if self.index < 0 or self.is_text_only or self._src is None:
            if self.index < 0:
                head, msg = "Nothing selected", "Pick a step on the left, or start a new recording."
            elif self.is_text_only:
                head, msg = "Note step", "This step has no screenshot — write the text below."
            else:
                head, msg = "Screenshot missing", "The image file could not be found."
            _viewfinder(c, cw // 2, ch // 2 - 34, 64, C["border_hi"], 4)
            c.create_text(cw // 2, ch // 2 + 26, text=head, fill=C["muted"], font=(UI_FONT, 14, "bold"))
            c.create_text(cw // 2, ch // 2 + 54, text=msg, fill=C["faint"], font=(UI_FONT, 11))
            self._zoom_lbl.configure(text="")
            return
        self._geometry()
        vx1, vy1, vx2, vy2 = self._vb
        s = self._scale
        # only the part of the image that is actually visible gets resampled
        bx0 = max(vx1, vx1 + (0 - self._ox) / s);  by0 = max(vy1, vy1 + (0 - self._oy) / s)
        bx1 = min(vx2, vx1 + (cw - self._ox) / s); by1 = min(vy2, vy1 + (ch - self._oy) / s)
        if bx1 - bx0 >= 1 and by1 - by0 >= 1:
            dw, dh = max(1, round((bx1 - bx0) * s)), max(1, round((by1 - by0) * s))
            resample = Image.LANCZOS if s < 0.75 else (Image.NEAREST if s >= 3 else Image.BILINEAR)
            img = self._src.resize((dw, dh), resample, box=(bx0, by0, bx1, by1))
            for obj in step_objects.get(self.index, []):
                if obj["type"] == "blur":
                    self._pixelate_preview(img, obj, bx0, by0, s)
            self._photo = ImageTk.PhotoImage(img)
            dx, dy = self._i2c(bx0, by0)
            c.create_rectangle(round(dx) - 1, round(dy) - 1, round(dx) + dw, round(dy) + dh,
                               outline=C["border_hi"], tags=("bg",))
            c.create_image(round(dx), round(dy), anchor="nw", image=self._photo, tags=("bg",))
        self._zoom_lbl.configure(text=f"{round(s * 100)}%")
        self._render_objects()

    @staticmethod
    def _pixelate_preview(img, obj, bx0, by0, s):
        x1, y1, x2, y2 = _obj_bbox_img(obj)
        X1, Y1 = max(0, int((x1 - bx0) * s)), max(0, int((y1 - by0) * s))
        X2, Y2 = min(img.width, int((x2 - bx0) * s)), min(img.height, int((y2 - by0) * s))
        if X2 - X1 < 2 or Y2 - Y1 < 2:
            return
        reg = img.crop((X1, Y1, X2, Y2))
        blk = max(2, int(BLUR_BLOCK * s))
        small = reg.resize((max(1, (X2 - X1) // blk), max(1, (Y2 - Y1) // blk)), Image.BILINEAR)
        img.paste(small.resize(reg.size, Image.NEAREST), (X1, Y1))

    def _click_geom(self):
        """(canvas x, y, radius) of the captured click marker, or None when hidden/absent/disabled."""
        entry = log_data[self.index] if 0 <= self.index < len(log_data) else {}
        click = entry.get("click")
        if not (show_click_markers and click) or entry.get("click_hidden"):
            return None
        px, py = self._i2c(*click)
        return px, py, max(8.0, _click_marker_radius(self._orig) * self._scale)

    def _click_at(self, cx, cy):
        g = self._click_geom()
        return bool(g) and math.hypot(cx - g[0], cy - g[1]) <= g[2] + 8

    def _set_click_hidden(self, hidden: bool):
        if self.index < 0 or not log_data[self.index].get("click"):
            return
        push_undo(self.index)
        if hidden:
            log_data[self.index]["click_hidden"] = True
        else:
            log_data[self.index].pop("click_hidden", None)
        self._sel_click = False
        self._changed()
        _set_status("Click marker removed — right-click the image to bring it back" if hidden
                    else "Click marker restored", C["muted"])

    def _render_objects(self):
        c = self.canvas
        c.delete("obj")
        if not self._usable():
            return
        objects = step_objects.get(self.index, [])
        for i, obj in enumerate(objects):
            self._render_one(i, obj)
        if self._selected_obj is not None and self._selected_obj < len(objects):
            self._draw_gizmo(objects[self._selected_obj])
        # global overlay (normalised to the cropped image)
        cx1, cy1, cx2, cy2 = self._crop_box()
        if annotation_tool != "crop":
            for g in global_annotations:
                if g.get("type") not in ("highlight", "redact"):
                    continue
                x1, y1 = self._i2c(cx1 + g["x1_norm"] * (cx2 - cx1), cy1 + g["y1_norm"] * (cy2 - cy1))
                x2, y2 = self._i2c(cx1 + g["x2_norm"] * (cx2 - cx1), cy1 + g["y2_norm"] * (cy2 - cy1))
                tag = ("obj", "global")
                if g["type"] == "highlight":
                    c.create_rectangle(x1, y1, x2, y2, outline=g["color"], width=3, fill="", tags=tag)
                    c.create_rectangle(x1 + 2, y1 + 2, x2 - 2, y2 - 2, outline="", fill=g["color"],
                                       stipple="gray12", tags=tag)
                else:
                    c.create_rectangle(x1, y1, x2, y2, outline="#555555", width=1, fill="#0a0a0a", tags=tag)
        # click marker captured with the screenshot
        click = self._click_geom()
        if click:
            px, py, r = click
            c.create_oval(px - r, py - r, px + r, py + r, outline="#e74c3c", width=3,
                          fill="#e74c3c", stipple="gray25", tags=("obj", "click"))
            c.create_oval(px - 3, py - 3, px + 3, py + 3, fill="#e74c3c", outline="", tags=("obj", "click"))
            if self._sel_click:
                c.create_oval(px - r - 5, py - r - 5, px + r + 5, py + r + 5, outline="#ffffff", width=1,
                              dash=(5, 3), tags=("obj", "gizmo"))
        # current crop while the crop tool shows the full image
        if annotation_tool == "crop" and self.index in step_crops:
            x1, y1 = self._i2c(cx1, cy1); x2, y2 = self._i2c(cx2, cy2)
            c.create_rectangle(x1, y1, x2, y2, outline=C["crop_col"], width=2, dash=(8, 4), tags=("obj", "cropbox"))

    def _render_one(self, i, obj):
        c = self.canvas
        tag = ("obj", f"obj_{i}")
        if obj["type"] == "highlight":
            x1, y1, x2, y2 = self._bbox_canvas(obj)
            c.create_rectangle(x1, y1, x2, y2, outline=obj["color"], width=3, fill="", tags=tag)
            c.create_rectangle(x1 + 2, y1 + 2, x2 - 2, y2 - 2, outline="", fill=obj["color"],
                               stipple="gray12", tags=tag)
        elif obj["type"] == "redact":
            x1, y1, x2, y2 = self._bbox_canvas(obj)
            c.create_rectangle(x1, y1, x2, y2, outline="#555555", width=1, fill="#0a0a0a", tags=tag)
        elif obj["type"] == "blur":
            x1, y1, x2, y2 = self._bbox_canvas(obj)
            c.create_rectangle(x1, y1, x2, y2, outline="#9fb3d1", width=1, dash=(3, 3), tags=tag)
        elif obj["type"] == "arrow":
            x1, y1 = self._i2c(obj["x1"], obj["y1"]); x2, y2 = self._i2c(obj["x2"], obj["y2"])
            wc = max(2, obj["width"] * self._scale)
            hl = max(10.0, wc * 4.5)
            c.create_line(x1, y1, x2, y2, fill=obj["color"], width=wc, capstyle=tk.ROUND,
                          arrow=tk.LAST, arrowshape=(hl, hl, hl * 0.45), tags=tag)
        elif obj["type"] == "text":
            x, y = self._i2c(obj["x"], obj["y"])
            px = -max(8, int(obj["size"] * self._scale * 0.75))
            font = ("Segoe UI", px)
            for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                c.create_text(x + dx, y + dy, anchor="nw", text=obj["text"], font=font,
                              fill="#000000" if _luma(_hex_to_rgb(obj["color"])) > 0.45 else "#ffffff", tags=tag)
            c.create_text(x, y, anchor="nw", text=obj["text"], font=font, fill=obj["color"], tags=tag)
        elif obj["type"] == "marker":
            x, y = self._i2c(obj["x"], obj["y"])
            r = obj["r"] * self._scale
            c.create_oval(x - r, y - r, x + r, y + r, fill=obj["color"], outline="#ffffff",
                          width=max(2, r / 6), tags=tag)
            dark = _luma(_hex_to_rgb(obj["color"])) > 0.6
            c.create_text(x, y, text=str(obj.get("n", 1)), font=("Segoe UI", -max(8, int(r * 1.15)), "bold"),
                          fill="#000000" if dark else "#ffffff", tags=tag)
        elif obj["type"] == "draw":
            if not obj["points"]:
                return
            pts = [self._i2c(p[0], p[1]) for p in obj["points"]]
            wc = max(1, int(obj["width"] * self._scale))
            if len(pts) >= 2:
                c.create_line(*[v for pt in pts for v in pt], fill=obj["color"], width=wc,
                              capstyle=tk.ROUND, smooth=True, joinstyle=tk.ROUND, tags=tag)
            r = max(1, wc // 2)
            c.create_oval(pts[0][0] - r, pts[0][1] - r, pts[0][0] + r, pts[0][1] + r,
                          fill=obj["color"], outline="", tags=tag)

    def _handle_positions(self, obj):
        bx1, by1, bx2, by2 = self._bbox_canvas(obj)
        if obj["type"] == "arrow":       # only the two end points are draggable
            return (bx1, by1, bx2, by2), [self._i2c(obj["x1"], obj["y1"]), self._i2c(obj["x2"], obj["y2"])]
        if obj["type"] in ("text", "marker"):
            return (bx1, by1, bx2, by2), []
        mx, my = (bx1 + bx2) / 2, (by1 + by2) / 2
        return (bx1, by1, bx2, by2), [
            (bx1, by1), (mx, by1), (bx2, by1),
            (bx1, my),             (bx2, my),
            (bx1, by2), (mx, by2), (bx2, by2)]

    def _draw_gizmo(self, obj):
        (bx1, by1, bx2, by2), positions = self._handle_positions(obj)
        self.canvas.create_rectangle(bx1 - 2, by1 - 2, bx2 + 2, by2 + 2,
            outline="#ffffff", width=1, dash=(5, 3), tags=("obj", "gizmo"))
        for hx, hy in positions:
            s = HANDLE_SZ
            self.canvas.create_rectangle(hx - s, hy - s, hx + s, hy + s,
                fill="#ffffff", outline="#111111", width=1, tags=("obj", "gizmo", "handle"))

    # ── hit testing ───────────────────────────────────────────────────────
    def _handle_at(self, cx, cy):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return None
        _, positions = self._handle_positions(objects[self._selected_obj])
        for i, (hx, hy) in enumerate(positions):
            if abs(cx - hx) <= HANDLE_HIT and abs(cy - hy) <= HANDLE_HIT:
                return i
        return None

    def _obj_at(self, cx, cy):
        objects = step_objects.get(self.index, [])
        for i in range(len(objects) - 1, -1, -1):
            x1, y1, x2, y2 = self._bbox_canvas(objects[i])
            if (x1 - 6) <= cx <= (x2 + 6) and (y1 - 6) <= cy <= (y2 + 6):
                return i
        return None

    # ── mouse ─────────────────────────────────────────────────────────────
    def _on_press(self, event):
        self.canvas.focus_set()
        if not self._usable():
            return
        if annotation_tool == "none":
            handle = self._handle_at(event.x, event.y)
            objects = step_objects.get(self.index, [])
            if handle is not None:
                obj = objects[self._selected_obj]
                self._drag_info = {"type": "handle", "handle": handle, "undo_pushed": False,
                                   "start": self._c2f(event.x, event.y),
                                   "obj_snapshot": copy.deepcopy(obj), "bbox_start": _obj_bbox_img(obj)}
                return
            hit = self._obj_at(event.x, event.y)
            if hit is not None:
                self._selected_obj = hit
                self._sel_click = False
                if objects[hit]["type"] == "marker":
                    self._highlight_callout(objects[hit])
                self._drag_info = {"type": "move", "undo_pushed": False,
                                   "start": self._c2f(event.x, event.y),
                                   "obj_snapshot": copy.deepcopy(objects[hit])}
                self._render_objects()
                self._update_color_swatches_for_selection()
                return
            self._selected_obj = None
            self._sel_click = self._click_at(event.x, event.y)
            self._drag_info = None if self._sel_click else {"type": "pan", "start": (event.x, event.y),
                                                            "pan0": self._pan}
            self._render_objects()
            return

        self._selected_obj = None
        if annotation_tool == "draw":
            self._draw_pts  = [(event.x, event.y)]
            self._last_draw = (event.x, event.y)
            return
        self._create_start = (event.x, event.y)
        if annotation_tool in ("text", "marker"):
            return                       # created on release (a click, no drag)
        if annotation_tool == "arrow":
            self._create_rect = self.canvas.create_line(
                event.x, event.y, event.x, event.y, fill=draw_color, width=max(2, draw_width * self._scale),
                arrow=tk.LAST, capstyle=tk.ROUND, tags=("tmp",))
            return
        if annotation_tool == "blur":
            kw = dict(outline="#9fb3d1", width=1, fill="", dash=(3, 3))
        elif annotation_tool == "highlight":
            kw = dict(outline=draw_color, width=3, fill="")
        elif annotation_tool == "redact":
            kw = dict(outline="#555", width=1, fill="#0a0a0a", stipple="gray50")
        else:  # crop
            kw = dict(outline=C["crop_col"], width=2, fill="", dash=(8, 4))
        self._create_rect = self.canvas.create_rectangle(
            event.x, event.y, event.x, event.y, **kw, tags=("tmp",))

    def _on_drag(self, event):
        if not self._usable():
            return
        di = self._drag_info
        if di and di["type"] == "pan":
            if self._zoom > 1.001:
                self._pan = (di["pan0"][0] + event.x - di["start"][0],
                             di["pan0"][1] + event.y - di["start"][1])
                self.render()
            return
        if annotation_tool == "draw" and self._last_draw:
            wc = max(1, int(draw_width * self._scale))
            self.canvas.create_line(self._last_draw[0], self._last_draw[1], event.x, event.y,
                fill=draw_color, width=wc, capstyle=tk.ROUND, smooth=True, tags=("tmp",))
            self._draw_pts.append((event.x, event.y))
            self._last_draw = (event.x, event.y)
            return
        if self._create_rect and self._create_start:
            self.canvas.coords(self._create_rect, self._create_start[0], self._create_start[1],
                               event.x, event.y)
            return
        objects = step_objects.get(self.index, [])
        if not di or self._selected_obj is None or self._selected_obj >= len(objects):
            return
        obj = objects[self._selected_obj]
        snap = di["obj_snapshot"]
        if not di["undo_pushed"]:
            # store the state from BEFORE the drag, once, when movement actually starts
            state = {"objects": [snap if o is obj else o for o in objects],
                     "crop": step_crops.get(self.index),
                     "click_hidden": bool(log_data[self.index].get("click_hidden"))}
            undo_stacks.setdefault(self.index, []).append(json.dumps(state))
            di["undo_pushed"] = True
            self._refresh_undo_btn()
        sx, sy = di["start"]
        cx, cy = self._c2f(event.x, event.y)
        dx, dy = round(cx - sx), round(cy - sy)

        if di["type"] == "move":
            if obj["type"] in _RECT_TYPES + ("arrow",):
                obj["x1"] = snap["x1"] + dx; obj["y1"] = snap["y1"] + dy
                obj["x2"] = snap["x2"] + dx; obj["y2"] = snap["y2"] + dy
            elif obj["type"] in ("text", "marker"):
                obj["x"] = snap["x"] + dx; obj["y"] = snap["y"] + dy
            elif obj["type"] == "draw":
                obj["points"] = [[p[0] + dx, p[1] + dy] for p in snap["points"]]
        elif di["type"] == "handle":
            if obj["type"] == "arrow":
                k = "1" if di["handle"] == 0 else "2"
                obj["x" + k] = snap["x" + k] + dx; obj["y" + k] = snap["y" + k] + dy
                self._render_objects()
                return
            x1f, y1f, x2f, y2f = _HANDLE_FX[di["handle"]]
            if obj["type"] in _RECT_TYPES:
                obj["x1"] = snap["x1"] + dx * x1f; obj["y1"] = snap["y1"] + dy * y1f
                obj["x2"] = snap["x2"] + dx * x2f; obj["y2"] = snap["y2"] + dy * y2f
            elif obj["type"] == "draw":
                bx1, by1, bx2, by2 = di["bbox_start"]
                nx1 = bx1 + dx * x1f; ny1 = by1 + dy * y1f
                nx2 = bx2 + dx * x2f; ny2 = by2 + dy * y2f
                if nx2 < nx1 + 5: nx2 = nx1 + 5
                if ny2 < ny1 + 5: ny2 = ny1 + 5
                ow = (bx2 - bx1) or 1; oh = (by2 - by1) or 1
                obj["points"] = [[nx1 + (p[0] - bx1) * (nx2 - nx1) / ow,
                                  ny1 + (p[1] - by1) * (ny2 - ny1) / oh] for p in snap["points"]]
        self._render_objects()

    def _on_release(self, event):
        di, self._drag_info = self._drag_info, None
        if not self._usable():
            return
        c = self.canvas
        c.delete("tmp")
        if annotation_tool == "draw":
            if not self._draw_pts:
                return
            push_undo(self.index)
            img_pts = [list(self._c2i(cx, cy)) for cx, cy in self._draw_pts]
            step_objects.setdefault(self.index, []).append(
                {"type": "draw", "color": draw_color, "width": draw_width, "points": img_pts})
            self._draw_pts = []; self._last_draw = None
            self._changed()
            return
        if annotation_tool == "arrow" and self._create_start:
            x1, y1 = self._c2i(*self._create_start)
            x2, y2 = self._c2i(event.x, event.y)
            self._create_rect = self._create_start = None
            if math.hypot(x2 - x1, y2 - y1) > 10:
                push_undo(self.index)
                step_objects.setdefault(self.index, []).append(
                    {"type": "arrow", "color": draw_color, "width": max(3, draw_width),
                     "x1": x1, "y1": y1, "x2": x2, "y2": y2})
                self._changed()
            else:
                self.render()
            return
        if annotation_tool in ("text", "marker") and self._create_start:
            x, y = self._c2i(*self._create_start)
            self._create_start = None
            if annotation_tool == "marker":
                objs = step_objects.setdefault(self.index, [])
                n = 1 + max([o.get("n", 0) for o in objs if o["type"] == "marker"] or [0])
                push_undo(self.index)
                objs.append({"type": "marker", "color": draw_color, "n": n, "x": x, "y": y,
                             "r": MARKER_R.get(draw_width, 17), "note": ""})
                self._changed(focus_n=n)
            else:
                txt = self._ask_text("")
                if txt:
                    push_undo(self.index)
                    step_objects.setdefault(self.index, []).append(
                        {"type": "text", "color": draw_color, "text": txt, "x": x, "y": y,
                         "size": TEXT_SIZES.get(draw_width, 34)})
                    self._changed()
            return
        if annotation_tool in ("crop", "highlight", "redact", "blur") and self._create_start:
            x1, y1 = self._create_start
            self._create_rect = self._create_start = None
            ix1, iy1 = self._c2i(x1, y1); ix2, iy2 = self._c2i(event.x, event.y)
            ix1, ix2 = sorted([ix1, ix2]); iy1, iy2 = sorted([iy1, iy2])
            if annotation_tool == "crop":
                if ix2 - ix1 > 10 and iy2 - iy1 > 10:
                    push_undo(self.index)
                    step_crops[self.index] = {"x1": ix1, "y1": iy1, "x2": ix2, "y2": iy2}
                    self._changed()
                else:
                    self.render()
            elif ix2 - ix1 > 4 and iy2 - iy1 > 4:
                push_undo(self.index)
                step_objects.setdefault(self.index, []).append({
                    "type": annotation_tool, "color": "#000000" if annotation_tool == "blur" else draw_color, "width": 3,
                    "x1": ix1, "y1": iy1, "x2": ix2, "y2": iy2})
                self._changed()
            else:
                self.render()
            return
        if di and di["type"] in ("move", "handle") and di["undo_pushed"]:
            self._changed()

    def _changed(self, focus_n=None):
        """Persist + redraw after any edit."""
        self._renumber_markers()
        save_steps()
        self.render()
        self._refresh_undo_btn()
        self.refresh_callouts(focus_n)

    def _on_motion(self, event):
        if annotation_tool != "none" or not self._usable():
            return
        if self._handle_at(event.x, event.y) is not None:
            self.canvas.configure(cursor="sizing")
        elif self._obj_at(event.x, event.y) is not None:
            self.canvas.configure(cursor="fleur")
        elif self._click_at(event.x, event.y):
            self.canvas.configure(cursor="hand2")
        else:
            self.canvas.configure(cursor="hand2" if self._zoom > 1.001 else "arrow")

    # ── zoom / pan ────────────────────────────────────────────────────────
    def _on_wheel(self, event):
        if not self._usable():
            return
        self._geometry()
        ix, iy = self._c2f(event.x, event.y)
        self._zoom = max(1.0, min(10.0, self._zoom * (1.2 if event.delta > 0 else 1 / 1.2)))
        self._geometry()
        nx, ny = self._i2c(ix, iy)
        if self._zoom > 1.0:
            self._pan = (self._pan[0] + event.x - nx, self._pan[1] + event.y - ny)
        self.render()

    def _pan_start(self, event):
        self._drag_info = {"type": "pan", "start": (event.x, event.y), "pan0": self._pan}

    def _pan_move(self, event):
        if self._drag_info and self._drag_info["type"] == "pan":
            self._on_drag(event)

    def _on_dblclick(self, event):
        if annotation_tool != "none" or not self._usable():
            return
        hit = self._obj_at(event.x, event.y)
        if hit is None:
            self.reset_view()
        elif step_objects[self.index][hit]["type"] == "text":
            self._selected_obj = hit
            self._edit_selected_text()

    def _edit_selected_text(self):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects) or objects[self._selected_obj]["type"] != "text":
            return
        obj = objects[self._selected_obj]
        txt = self._ask_text(obj["text"])
        if txt and txt != obj["text"]:
            push_undo(self.index)
            obj["text"] = txt
            self._changed()

    def _ask_text(self, initial):
        """Small modal dialog for annotation text. Returns the text, or None if cancelled."""
        dlg = ctk.CTkToplevel(root)
        dlg.title("Text")
        dlg.configure(fg_color=C["panel"])
        dlg.transient(root)
        dlg.resizable(False, False)
        w, h = 420, 150
        dlg.geometry(f"{w}x{h}+{root.winfo_rootx() + (root.winfo_width() - w) // 2}+{root.winfo_rooty() + 200}")
        ctk.CTkLabel(dlg, text="Annotation text", font=("Segoe UI", 12, "bold"),
                     text_color=C["text"]).pack(anchor="w", padx=20, pady=(18, 6))
        var = tk.StringVar(value=initial)
        entry = ctk.CTkEntry(dlg, textvariable=var, height=36, fg_color=C["surface"], border_color=C["border"],
                             text_color=C["text"], font=("Segoe UI", 12))
        entry.pack(fill="x", padx=20)
        result = [None]
        def ok(_e=None):
            result[0] = var.get().strip() or None
            dlg.destroy()
        row = ctk.CTkFrame(dlg, fg_color="transparent")
        row.pack(fill="x", padx=20, pady=14)
        ctk.CTkButton(row, text="Add", width=80, height=30, fg_color=C["accent"], hover_color=C["acc_dark"],
                      command=ok).pack(side="right")
        ctk.CTkButton(row, text="Cancel", width=80, height=30, fg_color="transparent", border_width=1,
                      border_color=C["border"], text_color=C["muted"], hover_color=C["surface"],
                      command=dlg.destroy).pack(side="right", padx=8)
        entry.bind("<Return>", ok)
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        dlg.after(120, lambda: (dlg.grab_set(), entry.focus_force(), entry.select_range(0, "end")))
        dlg.wait_window()
        return result[0]

    def apply_size_to_selection(self, w):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return False
        obj = objects[self._selected_obj]
        key = {"draw": ("width", w), "arrow": ("width", max(3, w)),
               "text": ("size", TEXT_SIZES.get(w, 34)), "marker": ("r", MARKER_R.get(w, 17))}.get(obj["type"])
        if not key:
            return False
        push_undo(self.index)
        obj[key[0]] = key[1]
        self._changed()
        return True

    # ── context menu ──────────────────────────────────────────────────────
    def _on_right_click(self, event):
        if not self._usable():
            return
        hit = self._obj_at(event.x, event.y)
        if hit is not None:
            self._selected_obj = hit
            self._sel_click = False
            self._render_objects()
            self._update_color_swatches_for_selection()
        elif self._click_at(event.x, event.y):
            self._selected_obj, self._sel_click = None, True
            self._render_objects()
        _MK = dict(bg=C["surface"], fg=C["text"], activebackground=C["accent"],
                   activeforeground="#fff", font=("Segoe UI", 10))
        menu = tk.Menu(self.canvas, tearoff=0, **_MK)
        objects = step_objects.get(self.index, [])
        if self._selected_obj is not None and self._selected_obj < len(objects):
            obj = objects[self._selected_obj]
            menu.add_command(label=f"Delete {obj['type'].capitalize()}  [Del]", command=self.delete_selected)
            if obj["type"] in ("highlight", "redact"):
                menu.add_command(label="Add to all steps", command=self._add_selection_to_global)
            if obj["type"] == "text":
                menu.add_command(label="Edit text…", command=self._edit_selected_text)
            if obj["type"] not in ("redact", "blur"):
                color_sub = tk.Menu(menu, tearoff=0, **_MK)
                for hex_col, col_lbl in _SWATCHES:
                    color_sub.add_command(label=f"● {col_lbl}", foreground=hex_col,
                        command=lambda c=hex_col: self.apply_color_to_selection(c))
                menu.add_cascade(label="Colour", menu=color_sub)
            menu.add_separator()
        entry = log_data[self.index]
        if entry.get("click"):
            if entry.get("click_hidden"):
                menu.add_command(label="Restore click marker", command=lambda: self._set_click_hidden(False))
            else:
                menu.add_command(label="Delete click marker  [Del]", command=lambda: self._set_click_hidden(True))
            menu.add_separator()
        if self.index in step_crops:
            menu.add_command(label="Apply crop (permanent)", command=self._apply_crop)
            menu.add_command(label="Clear crop", command=self._reset_crop)
            menu.add_separator()
        if global_annotations:
            menu.add_command(label="Clear all global overlays", command=_clear_global_overlays)
            menu.add_separator()
        menu.add_command(label="Fit to window", command=self.reset_view)
        menu.add_command(label="Full view", command=self._show_fullscreen)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _show_fullscreen(self):
        """Open a maximized top-level window showing the full annotated image."""
        if self.index < 0:
            return
        flat = _flatten_to_pil(self.index)
        if flat is None:
            return
        win = tk.Toplevel(root)
        win.title(f"Step {log_data[self.index]['step']:02d} — Full View")
        win.configure(bg="#111111")
        win.attributes("-topmost", True)
        win.state("zoomed")
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        ratio = min(sw / flat.width, sh / flat.height, 1.0)
        photo = ImageTk.PhotoImage(flat.resize((int(flat.width * ratio), int(flat.height * ratio)), Image.LANCZOS))
        canvas = tk.Canvas(win, bg="#111111", highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        canvas.create_image(sw // 2, sh // 2, anchor="center", image=photo)
        canvas._photo_ref = photo  # prevent GC
        win.bind("<Escape>", lambda e: win.destroy())
        win.bind("<Button-1>", lambda e: win.destroy())
        win.focus_set()

    # ── selection helpers ─────────────────────────────────────────────────
    def _update_color_swatches_for_selection(self):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return
        _sync_color_swatches(objects[self._selected_obj].get("color", draw_color))
        _set_status("Object selected — click a colour swatch to repaint it", C["accent"])

    def apply_color_to_selection(self, hex_color):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return False
        if objects[self._selected_obj]["type"] in ("redact", "blur"):
            return False
        push_undo(self.index)
        objects[self._selected_obj]["color"] = hex_color
        self._changed()
        return True

    def delete_selected(self):
        if self._sel_click:
            self._set_click_hidden(True)
            return
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return
        push_undo(self.index)
        del objects[self._selected_obj]
        self._selected_obj = None
        self._drag_info = None
        self._changed()
        _set_status("Object deleted", C["muted"])

    def _add_selection_to_global(self):
        """Add the selected highlight/redact to the global overlay (shown on every step)."""
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return
        obj = objects[self._selected_obj]
        if obj["type"] not in ("highlight", "redact"):
            _set_status("Only highlight or redact can be applied to all steps", C["muted"])
            return
        cx1, cy1, cx2, cy2 = self._crop_box()
        cw, ch = max(1, cx2 - cx1), max(1, cy2 - cy1)
        x1, y1, x2, y2 = _obj_bbox_img(obj)
        global_annotations.append({
            "type": obj["type"], "color": obj.get("color", "#e74c3c"), "width": obj.get("width", 3),
            "x1_norm": (x1 - cx1) / cw, "y1_norm": (y1 - cy1) / ch,
            "x2_norm": (x2 - cx1) / cw, "y2_norm": (y2 - cy1) / ch,
        })
        _save_global_overlay()
        self.render()
        _set_status("Added to all steps — appears on every screenshot", C["success"])

    # ── actions ───────────────────────────────────────────────────────────
    def _undo(self):
        if self.index < 0:
            return
        if pop_undo(self.index):
            self._selected_obj = None
            self._drag_info = None
            self._changed()
            _set_status("↩  Undo applied", C["warn"])
        else:
            _set_status("Nothing to undo for this step", C["muted"])

    def _reset_crop(self):
        if self.index not in step_crops:
            _set_status("No crop to reset on this step", C["muted"])
            return
        push_undo(self.index)
        step_crops.pop(self.index, None)
        self._changed()
        _set_status("↺  Crop reset to original", C["success"])

    def _apply_crop(self):
        """Permanently crop the screenshot to the current crop region and clear the crop."""
        if self.index not in step_crops or not current_session:
            _set_status("No crop to apply on this step", C["muted"])
            return
        entry = log_data[self.index]
        if not entry.get("screenshot"):
            return
        img_path = os.path.join(current_session, entry["screenshot"])
        if not os.path.exists(img_path):
            _set_status("Screenshot file missing", C["danger"])
            return
        try:
            img = Image.open(img_path).convert("RGB")
        except Exception as e:
            _set_status(f"Could not open image: {e}", C["danger"])
            return
        crop = step_crops[self.index]
        x1, x2 = sorted([crop["x1"], crop["x2"]]); y1, y2 = sorted([crop["y1"], crop["y2"]])
        x1 = max(0, min(x1, img.width)); y1 = max(0, min(y1, img.height))
        x2 = max(x1 + 1, min(x2, img.width)); y2 = max(y1 + 1, min(y2, img.height))
        try:
            img.crop((x1, y1, x2, y2)).save(
                img_path, "PNG" if img_path.lower().endswith(".png") else "JPEG", quality=85)
        except OSError as e:
            _set_status(f"Could not save: {e}", C["danger"])
            return
        new_w, new_h = x2 - x1, y2 - y1
        new_objs = []
        for obj in step_objects.get(self.index, []):
            if obj["type"] in _RECT_TYPES:
                o1, o2 = sorted([obj["x1"] - x1, obj["x2"] - x1]); q1, q2 = sorted([obj["y1"] - y1, obj["y2"] - y1])
                if o1 >= new_w or o2 <= 0 or q1 >= new_h or q2 <= 0:
                    continue
                new_objs.append({**obj, "x1": max(0, min(o1, new_w)), "y1": max(0, min(q1, new_h)),
                                 "x2": max(0, min(o2, new_w)), "y2": max(0, min(q2, new_h))})
            elif obj["type"] == "draw":
                pts = [(max(0, min(p[0] - x1, new_w)), max(0, min(p[1] - y1, new_h))) for p in obj["points"]]
                if pts:
                    new_objs.append({**obj, "points": pts})
            elif obj["type"] == "arrow":
                new_objs.append({**obj, "x1": obj["x1"] - x1, "y1": obj["y1"] - y1,
                                 "x2": obj["x2"] - x1, "y2": obj["y2"] - y1})
            elif obj["type"] in ("text", "marker"):
                new_objs.append({**obj, "x": obj["x"] - x1, "y": obj["y"] - y1})
        step_objects[self.index] = new_objs
        step_crops.pop(self.index, None)
        undo_stacks.pop(self.index, None)   # snapshots refer to the old image geometry
        click = entry.get("click")
        if click:
            nx, ny = click[0] - x1, click[1] - y1
            if 0 <= nx < new_w and 0 <= ny < new_h:
                entry["click"] = [nx, ny]
            else:
                entry.pop("click", None)
        self.reload_src()
        self._changed()
        _set_status("Crop applied — image permanently resized", C["success"])

    def _refresh_undo_btn(self):
        ok = self._usable() or (self.index >= 0 and not self.is_text_only)
        has = ok and bool(undo_stacks.get(self.index))
        self._undo_btn.configure(text_color=C["text"] if has else C["muted"],
                                 state="normal" if has else "disabled")
        has_crop = ok and self.index in step_crops
        self._reset_crop_btn.configure(text_color=C["text"] if has_crop else C["muted"],
                                       state="normal" if has_crop else "disabled")


def _click_marker_radius(size):
    return max(14, int(min(size) * 0.018))


# ══════════════════════════════════════ STEP LIST MANAGEMENT ══════════════════════════════════════

def _refresh_ui_state():
    """Enable/disable controls based on session and step availability."""
    has_steps   = bool(log_data)
    has_session = bool(current_session)
    s = "normal" if has_steps else "disabled"
    _btn_html.configure(state=s)
    _btn_pdf.configure(state=s)
    _set_tool_strip_enabled(has_steps)
    filmstrip.add_btn.configure(state="normal" if has_session else "disabled")
    if not recording:
        btn_continue.configure(state="normal" if has_session else "disabled")


def _build_all_cards(select=None):
    """Refresh the whole editor after the step list changed (name kept for the callers)."""
    global active_index, _sel_anchor
    n = len(log_data)
    if select is not None:
        active_index = select
    active_index = max(0, min(active_index, n - 1)) if n else -1
    for i in [i for i in _selected if i >= n]:
        _selected.discard(i)
    if select is not None or (n and not _selected):
        _selected.clear()
        if n:
            _selected.add(active_index)
    _sel_anchor = active_index
    filmstrip.ensure_visible(active_index)
    editor.show(active_index, force=True)
    _refresh_ui_state()


def _append_card():
    """A step was recorded: keep the strip in sync (the editor is not visible while recording)."""
    global active_index
    active_index = len(log_data) - 1
    _selected.clear(); _selected.add(active_index)
    filmstrip.scroll_to_end()


def _swap_steps(a, b):
    """Swap two adjacent steps and rebuild."""
    log_data[a], log_data[b] = log_data[b], log_data[a]
    step_objects[a], step_objects[b] = step_objects.get(b, []), step_objects.get(a, [])
    ca, cb = step_crops.pop(a, None), step_crops.pop(b, None)
    if cb is not None: step_crops[a] = cb
    if ca is not None: step_crops[b] = ca
    _renumber_and_rebuild(scroll_to=b)


def _renumber_and_rebuild(scroll_to=None):
    editor._flush_pending()
    for i, s in enumerate(log_data):
        s["step"] = i + 1
    save_steps()
    undo_stacks.clear()
    _build_all_cards(select=scroll_to)


def _reorder_step(src, dst):
    """Move step from index src to index dst, updating all data structures."""
    if src == dst or not (0 <= src < len(log_data)) or not (0 <= dst < len(log_data)):
        return
    editor._flush_pending()
    n = len(log_data)
    entries    = list(log_data)
    objs_list  = [step_objects.get(i, []) for i in range(n)]
    crops_list = [step_crops.get(i) for i in range(n)]
    entry = entries.pop(src); obj = objs_list.pop(src); crop = crops_list.pop(src)
    entries.insert(dst, entry); objs_list.insert(dst, obj); crops_list.insert(dst, crop)
    log_data.clear(); log_data.extend(entries)
    step_objects.clear(); step_crops.clear()
    for i in range(n):
        step_objects[i] = objs_list[i]
        if crops_list[i] is not None:
            step_crops[i] = crops_list[i]
    _renumber_and_rebuild(scroll_to=dst)
    _set_status(f"Moved step to position {dst + 1}", C["accent"])


def _select_relative(delta):
    """Arrow-key navigation through the steps."""
    global active_index
    if not log_data:
        return
    idx = max(0, min(len(log_data) - 1, (active_index if active_index >= 0 else 0) + delta))
    _selected.clear(); _selected.add(idx)
    active_index = idx
    filmstrip.ensure_visible(idx)
    editor.show(idx)


# ══════════════════════════════════════ CONTEXT MENU (shared) ══════════════════════════════

def _show_steps_context_menu(event):
    """Context menu of the step list."""
    _MK = dict(bg=C["surface"], fg=C["text"],
               activebackground=C["acc_dark"], activeforeground="#fff",
               font=("Segoe UI", 10), borderwidth=1, relief="solid")
    menu = tk.Menu(root, tearoff=0, **_MK)
    n_sel = len(_selected)
    if not log_data:
        menu.add_command(label="Insert step", command=lambda: insert_custom_step())
    elif n_sel > 1:
        menu.add_command(label=f"Delete {n_sel} steps",
            foreground=C["danger"], activeforeground=C["danger"], command=_delete_selected)
    else:
        idx = next(iter(_selected)) if n_sel == 1 else max(0, active_index)
        menu.add_command(label=f"Delete Step {log_data[idx]['step']}",
            foreground=C["danger"], activeforeground=C["danger"], command=_delete_selected)
        menu.add_separator()
        menu.add_command(label="Insert step above",
                         command=lambda i=idx: insert_custom_step(after_index=i - 1))
        menu.add_command(label="Insert step below",
                         command=lambda i=idx: insert_custom_step(after_index=i))
        menu.add_separator()
        menu.add_command(label="Move up  [Alt+↑]", state="normal" if idx > 0 else "disabled",
                         command=lambda i=idx: _swap_steps(i, i - 1))
        menu.add_command(label="Move down  [Alt+↓]", state="normal" if idx < len(log_data) - 1 else "disabled",
                         command=lambda i=idx: _swap_steps(i, i + 1))
    menu.post(event.x_root, event.y_root)


# ══════════════════════════════════════ TOOL / COLOUR ══════════════════════════════════════

_TOOL_HINTS = {
    "none":      "Pointer — click an object to move or resize it · drag empty space to pan · scroll to zoom",
    "highlight": "Highlight — drag a box around what matters",
    "redact":    "Redact — drag over sensitive content · it is burned into every export",
    "blur":      "Pixelate — drag over a region · irreversible in exports",
    "crop":      "Crop — drag on the full image · non-destructive until you apply it",
    "draw":      "Pen — draw freehand · pick colour and size on the right",
    "arrow":     "Arrow — drag from the tail to the head",
    "text":      "Text — click where the label should go",
    "marker":    "Number — click to drop the next numbered marker",
}


def set_tool(tool):
    global annotation_tool
    annotation_tool = tool
    for t, btn in tool_btns.items():
        on = t == tool
        btn.configure(fg_color=C["acc_soft"] if on else "transparent",
                      text_color=C["accent"] if on else C["muted"])
        if t == "marker":
            btn.configure(image=_MARKER_ICONS[on])
    editor.canvas.configure(cursor="crosshair" if tool != "none" else "arrow")
    editor._selected_obj = None
    editor._sel_click = False
    editor.opt_colors.pack_forget(); editor.opt_sizes.pack_forget()
    if tool in ("draw", "arrow", "text", "marker"):
        editor.opt_sizes.pack(side="right", padx=(0, 12))
    if tool in ("draw", "highlight", "arrow", "text", "marker"):
        editor.opt_colors.pack(side="right", padx=(0, 10))
    editor.hint.configure(text=_TOOL_HINTS[tool])
    editor.render()


def _sync_color_swatches(hex_color):
    for btn, col in draw_color_btns:
        if col is None:
            continue
        btn.configure(
            border_width=2 if col==hex_color else 1,
            border_color="#ffffff" if col==hex_color else "#555555")


def _set_draw_color_global(hex_color):
    global draw_color
    draw_color = hex_color
    _sync_color_swatches(hex_color)
    if editor.apply_color_to_selection(hex_color):
        _set_status("Object colour changed", C["success"])
        return
    _set_status("Draw colour set", C["muted"])


def _set_draw_width_global(w):
    global draw_width
    draw_width = w
    editor.apply_size_to_selection(w)
    for btn, bw in pen_size_btns:
        btn.configure(
            fg_color=C["acc_soft"] if bw==w else "transparent",
            border_color=C["accent"] if bw==w else C["border"])


def _set_tool_strip_enabled(enabled):
    """Grey out / restore the tool rail and its options."""
    st = "normal" if enabled else "disabled"
    for btn in tool_btns.values():
        btn.configure(state=st)
    for btn, _ in draw_color_btns:
        btn.configure(state=st)
    for btn, _ in pen_size_btns:
        btn.configure(state=st)


# ══════════════════════════════════════ PROJECT NAME ══════════════════════════════════════

def _apply_project_name():
    global project_name
    project_name = project_name_var.get().strip()
    if current_session:
        save_steps()
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")


# ══════════════════════════════════════ RECORDING ACTIONS ══════════════════════════════════════

def _default_recording_name():
    return datetime.now().strftime("Recording %Y-%m-%d %H-%M")


def _get_new_recording_settings(name_override=None, parent_dir_override=None):
    """Resolve and normalize recording settings from UI and optional overrides."""
    default_name = _default_recording_name()
    default_path = os.path.abspath(BASE_DIR)

    name = (name_override if name_override is not None else project_name_var.get()).strip()
    parent_dir = (parent_dir_override if parent_dir_override is not None else save_parent_dir_var.get()).strip()

    if not name:
        name = default_name
    if not parent_dir:
        parent_dir = default_path

    return name, parent_dir


def start_recording(name_override=None, parent_dir_override=None):
    global recording, step_counter, project_name
    name, parent_dir = _get_new_recording_settings(name_override, parent_dir_override)

    try:
        os.makedirs(parent_dir, exist_ok=True)
    except OSError as exc:
        messagebox.showerror("Cannot create folder", f"Save location is not writable:\n{parent_dir}\n\n{exc}")
        return

    project_name = name
    project_name_var.set(project_name)
    save_parent_dir_var.set(parent_dir)

    _selected.clear()
    _last_capture[0] = ("", "", "", None)
    create_session(parent_dir)
    log_data.clear()
    step_objects.clear()
    step_crops.clear()
    step_counter = 1
    recording    = True
    btn_start.configure(state="disabled")
    btn_stop.configure(state="normal")
    btn_continue.configure(state="disabled")
    _build_all_cards()
    threading.Thread(target=start_listeners, daemon=True).start()
    show_recording()


def stop_recording():
    global recording, paused
    recording = False
    paused    = False
    stop_listeners()
    save_steps()
    _set_status(f"◼  Stopped — {len(log_data)} steps saved", C["muted"])
    btn_start.configure(state="normal")
    btn_stop.configure(state="disabled")
    btn_continue.configure(state="normal" if current_session else "disabled")
    show_editing()


def continue_recording():
    global recording, step_counter
    if not current_session:
        return
    step_counter = len(log_data) + 1  # next step number from current count
    recording = True
    btn_start.configure(state="disabled")
    btn_stop.configure(state="normal")
    btn_continue.configure(state="disabled")
    threading.Thread(target=start_listeners, daemon=True).start()
    show_recording()


def _do_load_recording(folder):
    """Load a recording from folder path. Returns True on success."""
    global current_session, step_counter, project_name
    _selected.clear()
    json_path = os.path.join(folder, "steps.json")
    if not os.path.exists(json_path):
        messagebox.showerror("Error", "No steps.json found.")
        return False
    with open(json_path, "r", encoding="utf-8") as f:
        raw = json.load(f)

    # Support old list format and new {project_name, steps} format
    if isinstance(raw, list):
        steps_raw    = raw
        project_name = ""
    else:
        steps_raw    = raw.get("steps", [])
        project_name = raw.get("project_name", "")

    log_data.clear(); step_objects.clear(); step_crops.clear()
    for i, entry in enumerate(steps_raw):
        objs = entry.pop("objects", [])
        crop = entry.pop("crop", None)
        _step_id(entry)  # ensure id for fold state
        log_data.append(entry)
        step_objects[i] = objs
        if crop:
            step_crops[i] = crop
    _load_global_overlay()

    current_session = folder
    step_counter    = len(log_data) + 1
    undo_stacks.clear()
    project_name_var.set(project_name)
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")
    _build_all_cards(select=0 if log_data else None)
    _set_status(f"📂  Loaded: {os.path.basename(folder)}  ({len(log_data)} steps)", C["accent"])
    btn_continue.configure(state="normal" if current_session else "disabled")
    return True


def load_recording():
    folder = filedialog.askdirectory(initialdir=BASE_DIR, title="Open Recording")
    if not folder:
        return
    if _do_load_recording(folder):
        show_editing()


# ══════════════════════════════════════ EXPORT ══════════════════════════════════════

def _export_title():
    return project_name_var.get().strip() or os.path.basename(current_session)

def _export_filename(ext):
    """Build an export filename from the project name, e.g. 'My Project.html'."""
    name = _safe_folder_name(project_name_var.get().strip())
    if not name:
        name = "report"
    return os.path.join(current_session, f"{name}.{ext}")


def _step_notes(i: int):
    """(n, colour, note) for every numbered marker of step i that has a note."""
    return [(o.get("n", 0), o.get("color", "#4d9bff"), o["note"])
            for o in step_objects.get(i, []) if o["type"] == "marker" and o.get("note")]


def _legend_html(i: int) -> str:
    rows = "".join(
        f'<li><span class="badge" style="background:{col};color:{"#000" if _luma(_hex_to_rgb(col)) > 0.6 else "#fff"}">{n}</span>'
        f'<span>{_html.escape(note)}</span></li>' for n, col, note in _step_notes(i))
    return f'<ol class="legend">{rows}</ol>' if rows else ""


def export_html():
    if not log_data:
        messagebox.showwarning("Nothing to export", "No steps to export."); return
    title       = _html.escape(_export_title())
    report_path = _export_filename("html")
    total       = len(log_data)
    gen_date    = datetime.now().strftime('%Y-%m-%d %H:%M')
    gen_year    = datetime.now().year

    # Pre-encode all images once (shared by both views)
    step_images = []
    for i, entry in enumerate(log_data):
        flat = _flatten_to_pil(i)
        if flat is not None:
            buf = io.BytesIO()
            flat.save(buf, "JPEG", quality=90, optimize=True)
            step_images.append(base64.b64encode(buf.getvalue()).decode())
        else:
            step_images.append(None)

    try:
        with open(report_path, "w", encoding="utf-8") as f:
            f.write(f"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="utf-8"><title>{title}</title>
<style>
*,*::before,*::after{{box-sizing:border-box;margin:0;padding:0}}
:root{{--bg:#0b0d12;--surface:#12151c;--border:#252b3a;--accent:#4d9bff;--accent12:rgba(77,155,255,.14);
       --text:#e8ecf4;--muted:#8b95ab;--radius:12px}}
html,body{{height:100%}}
body{{background:var(--bg);color:var(--text);font-family:'Segoe UI',system-ui,-apple-system,sans-serif;font-weight:300;
     display:flex;flex-direction:column;overflow:hidden}}

/* ── top bar ── */
.topbar{{display:flex;align-items:center;justify-content:space-between;
         padding:10px 28px;border-bottom:1px solid var(--border);flex-shrink:0}}
.topbar h1{{font-family:Consolas,'Courier New',monospace;font-size:16px;font-weight:600;color:var(--accent)}}
.topbar .right{{display:flex;align-items:center;gap:16px}}
.topbar .meta{{color:var(--muted);font-family:Consolas,'Courier New',monospace;font-size:11px}}
.view-toggle{{display:flex;gap:2px;background:var(--surface);border:1px solid var(--border);
              border-radius:6px;padding:2px;overflow:hidden}}
.view-toggle button{{background:none;border:none;color:var(--muted);font-family:Consolas,'Courier New',monospace;
                     font-size:11px;padding:4px 14px;border-radius:4px;cursor:pointer;transition:.15s}}
.view-toggle button:hover{{color:var(--text)}}
.view-toggle button.on{{background:var(--accent);color:#fff}}

/* ═══════════ DECK MODE ═══════════ */
.deck-wrap{{flex:1;display:flex;flex-direction:column;overflow:hidden}}
.deck-wrap.hidden{{display:none}}
.deck{{flex:1;display:flex;align-items:center;justify-content:center;position:relative;
       overflow:hidden;padding:24px 80px}}
.slide{{display:none;flex-direction:column;align-items:center;width:100%;max-width:1100px;
        height:100%;animation:fadeIn .25s ease}}
.slide.active{{display:flex}}
@keyframes fadeIn{{from{{opacity:0;transform:translateY(8px)}}to{{opacity:1;transform:translateY(0)}}}}
.slide.title-slide{{justify-content:center;gap:12px}}
.slide.title-slide h2{{font-family:Consolas,'Courier New',monospace;font-size:36px;font-weight:600;color:var(--accent)}}
.slide.title-slide p{{font-size:14px;color:var(--muted);font-family:Consolas,'Courier New',monospace}}
.slide .step-num{{font-family:Consolas,'Courier New',monospace;font-size:11px;font-weight:600;color:var(--accent);
                  background:var(--accent12);padding:4px 14px;border-radius:6px;white-space:nowrap;flex-shrink:0}}
.slide .step-hdr{{display:flex;align-items:center;gap:14px;width:100%;padding:0 4px;flex-shrink:0}}
.slide .step-desc{{font-size:14px;color:var(--text);line-height:1.5}}
.slide .img-wrap{{flex:1;display:flex;align-items:center;justify-content:center;
                  min-height:0;width:100%;padding:14px 0 4px}}
.slide .img-wrap img{{max-width:100%;max-height:100%;object-fit:contain;border-radius:var(--radius);
                      border:1px solid var(--border);background:var(--surface)}}
.slide .note-body{{flex:1;display:flex;align-items:center;justify-content:center;
                   font-size:18px;color:var(--text);line-height:1.7;text-align:center;
                   max-width:700px;padding:40px 20px}}
.nav{{position:absolute;top:50%;transform:translateY(-50%);width:48px;height:48px;border-radius:50%;
     background:var(--surface);border:1px solid var(--border);color:var(--muted);font-size:22px;
     display:flex;align-items:center;justify-content:center;cursor:pointer;transition:.15s;z-index:10;
     user-select:none}}
.nav:hover{{background:var(--accent);color:#fff;border-color:var(--accent)}}
.nav.disabled{{opacity:.2;pointer-events:none}}
.nav.prev{{left:16px}}
.nav.next{{right:16px}}
.bottombar{{display:flex;align-items:center;justify-content:center;gap:6px;position:relative;
            padding:10px 28px;border-top:1px solid var(--border);flex-shrink:0}}
.dot{{width:8px;height:8px;border-radius:50%;background:var(--border);cursor:pointer;transition:.15s}}
.dot.active{{background:var(--accent);box-shadow:0 0 6px rgba(61,142,240,.5)}}
.dot:hover{{background:var(--accent)}}
.counter{{position:absolute;right:28px;font-family:Consolas,'Courier New',monospace;font-size:11px;color:var(--muted)}}

/* ═══════════ LIST MODE ═══════════ */
.list-wrap{{flex:1;overflow-y:auto;padding:40px 24px 80px}}
.list-wrap.hidden{{display:none}}
.list-inner{{max-width:1020px;margin:0 auto}}
.card{{background:var(--surface);border:1px solid var(--border);border-radius:10px;overflow:hidden;margin-bottom:28px}}
.card-hdr{{display:flex;align-items:center;gap:14px;padding:14px 20px;border-bottom:1px solid var(--border)}}
.card-num{{font-family:Consolas,'Courier New',monospace;font-size:10px;font-weight:600;color:var(--accent);
           background:var(--accent12);padding:3px 10px;border-radius:4px;white-space:nowrap}}
.card-desc{{font-size:14px;color:var(--text);line-height:1.55}}
.card img{{display:block;width:100%;height:auto}}
.card .card-note{{padding:28px 24px;font-size:15px;line-height:1.7;color:var(--text)}}

.legend{{list-style:none;display:flex;flex-wrap:wrap;gap:8px 26px;padding:12px 4px 0;width:100%;flex-shrink:0}}
.legend li{{display:flex;gap:10px;align-items:center;font-size:14px;line-height:1.4}}
.legend .badge{{width:24px;height:24px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;
                font:600 12px Consolas,monospace;flex-shrink:0;border:2px solid #fff}}
.card .legend{{padding:4px 22px 20px}}
.footer{{text-align:center;color:var(--muted);font-size:11px;font-family:Consolas,'Courier New',monospace;
         margin-top:48px;padding-top:20px;border-top:1px solid var(--border)}}
</style></head><body>

<div class="topbar">
  <h1>{title}</h1>
  <div class="right">
    <span class="meta">{total} steps &middot; {gen_date}</span>
    <div class="view-toggle" id="viewToggle">
      <button class="on" data-mode="deck">Deck</button>
      <button data-mode="list">List</button>
    </div>
  </div>
</div>

<!-- ═══════ DECK VIEW ═══════ -->
<div class="deck-wrap" id="deckWrap">
  <div class="deck" id="deck">
    <div class="nav prev disabled" id="prev" onclick="go(-1)">&lsaquo;</div>
    <div class="nav next" id="next" onclick="go(1)">&rsaquo;</div>
    <div class="slide title-slide active" data-idx="0">
      <h2>{title}</h2>
      <p>{total} steps</p>
      <p style="margin-top:24px;font-size:12px;color:var(--muted)">Press &rarr; or click to begin</p>
    </div>
""")
            for i, entry in enumerate(log_data):
                sn = entry["step"]
                desc_html = _html.escape(entry['description'])
                b64 = step_images[i]
                if b64 is not None:
                    body = (f'<div class="img-wrap">'
                            f'<img src="data:image/jpeg;base64,{b64}" alt="Step {sn}">'
                            f'</div>')
                else:
                    body = f'<div class="note-body">{desc_html}</div>'
                f.write(f"""    <div class="slide" data-idx="{i+1}">
      <div class="step-hdr"><span class="step-num">STEP {sn:02d}</span><span class="step-desc">{desc_html}</span></div>
      {body}
      {_legend_html(i)}
    </div>
""")

            f.write(f"""  </div>
  <div class="bottombar" id="dots"><span class="counter" id="counter">0 / {total}</span></div>
</div>

<!-- ═══════ LIST VIEW ═══════ -->
<div class="list-wrap hidden" id="listWrap">
  <div class="list-inner">
""")
            for i, entry in enumerate(log_data):
                sn = entry["step"]
                desc_html = _html.escape(entry['description'])
                b64 = step_images[i]
                if b64 is not None:
                    img_tag = f'\n    <img data-from="{i+1}" alt="Step {sn}">'
                else:
                    img_tag = f'\n    <div class="card-note">{desc_html}</div>'
                f.write(f"""    <div class="card">
      <div class="card-hdr"><span class="card-num">STEP {sn:02d}</span><span class="card-desc">{desc_html}</span></div>{img_tag}
      {_legend_html(i)}
    </div>
""")

            f.write(f"""    <div class="footer">Generated by PSR Pro &middot; {gen_year}</div>
  </div>
</div>

<script>
/* list view reuses the deck's embedded images (each image is stored once) */
document.querySelectorAll('img[data-from]').forEach(im=>{{
  const src=document.querySelector('.slide[data-idx="'+im.dataset.from+'"] img');
  if(src)im.src=src.src;
}});
/* ── view toggle ── */
const deckWrap=document.getElementById('deckWrap'),
      listWrap=document.getElementById('listWrap'),
      toggleBtns=document.querySelectorAll('#viewToggle button');
let mode='deck';
function setMode(m){{
  mode=m;
  deckWrap.classList.toggle('hidden',m!=='deck');
  listWrap.classList.toggle('hidden',m!=='list');
  toggleBtns.forEach(b=>b.classList.toggle('on',b.dataset.mode===m));
}}
toggleBtns.forEach(b=>b.addEventListener('click',()=>setMode(b.dataset.mode)));

/* ── deck navigation ── */
const slides=document.querySelectorAll('.slide'),
      dots=document.getElementById('dots'),
      counter=document.getElementById('counter'),
      prevBtn=document.getElementById('prev'),
      nextBtn=document.getElementById('next'),
      N=slides.length;
let cur=0;
for(let i=0;i<N;i++){{
  const d=document.createElement('span');
  d.className='dot'+(i===0?' active':'');
  d.onclick=()=>goTo(i);
  dots.insertBefore(d,counter);
}}
const allDots=dots.querySelectorAll('.dot');
function goTo(i){{
  if(i<0||i>=N)return;
  slides[cur].classList.remove('active');
  allDots[cur].classList.remove('active');
  cur=i;
  slides[cur].classList.add('active');
  allDots[cur].classList.add('active');
  counter.textContent=cur===0?'0 / {total}':(cur+' / {total}');
  prevBtn.classList.toggle('disabled',cur===0);
  nextBtn.classList.toggle('disabled',cur===N-1);
}}
function go(d){{goTo(cur+d)}}
document.addEventListener('keydown',e=>{{
  if(mode!=='deck')return;
  if(e.key==='ArrowRight'||e.key===' '){{e.preventDefault();go(1)}}
  if(e.key==='ArrowLeft'){{e.preventDefault();go(-1)}}
  if(e.key==='Home'){{e.preventDefault();goTo(0)}}
  if(e.key==='End'){{e.preventDefault();goTo(N-1)}}
}});
document.getElementById('deck').addEventListener('click',e=>{{
  if(e.target.closest('.nav'))return;
  go(1);
}});
</script>
</body></html>""")
    except Exception as exc:
        log.exception("HTML export failed: %s", exc)
        messagebox.showerror("HTML Export Error", f"Failed to export HTML:\n{exc}")
        return

    _set_status("✔  HTML report exported", C["success"])
    webbrowser.open(os.path.abspath(report_path))


def export_pdf():
    if not log_data:
        messagebox.showwarning("Nothing to export", "No steps to export."); return

    title       = _pdf_safe(_export_title())
    report_path = _export_filename("pdf")
    tmp_imgs    = []

    try:
        pdf = FPDF(orientation="L", unit="mm", format="A4")
        pdf.set_auto_page_break(auto=True, margin=16)
        pdf.set_margins(16, 16, 16)

        pdf.add_page()
        pdf.set_fill_color(11,13,18); pdf.rect(0,0,297,210,"F")
        pdf.set_font("Helvetica","B",30); pdf.set_text_color(77,155,255); pdf.set_y(72)
        pdf.cell(0, 12, title, align="C", new_x="LMARGIN", new_y="NEXT")
        pdf.set_font("Helvetica","",11); pdf.set_text_color(130,130,130); pdf.ln(6)
        pdf.cell(0, 7, _pdf_safe(f"{len(log_data)} steps  -  Generated {datetime.now().strftime('%Y-%m-%d %H:%M')}"),
                 align="C", new_x="LMARGIN", new_y="NEXT")

        for i, entry in enumerate(log_data):
            pdf.add_page()
            pdf.set_fill_color(18,21,28); pdf.rect(0,0,297,22,"F")
            pdf.set_font("Helvetica","B",10); pdf.set_text_color(77,155,255); pdf.set_xy(16,6)
            pdf.cell(26, 9, f"STEP {entry['step']:02d}", new_x="RIGHT", new_y="LAST")
            pdf.set_font("Helvetica","",9); pdf.set_text_color(210,210,210)
            desc = entry["description"]
            pdf.cell(0, 9, _pdf_safe(desc[:117] + "…" if len(desc) > 120 else desc), new_x="LMARGIN", new_y="NEXT")

            flat = _flatten_to_pil(i)
            if flat is None:
                pdf.set_xy(16, 34); pdf.set_font("Helvetica", "", 14); pdf.set_text_color(60, 60, 60)
                pdf.multi_cell(0, 8, _pdf_safe(desc), new_x="LMARGIN", new_y="NEXT")
            else:
                flat.thumbnail((2600, 1300), Image.LANCZOS)
                tmp  = os.path.join(current_session, f"_tmp_{i}.jpg")
                flat.save(tmp, "JPEG", quality=88)
                tmp_imgs.append(tmp)
                iw, ih = flat.size
                notes  = _step_notes(i)
                rows   = (len(notes) + 1) // 2
                ratio  = min(265/iw, (176 - (rows * 8 + 3 if rows else 0))/ih)
                fw, fh = iw*ratio, ih*ratio
                pdf.image(tmp, x=(297-fw)/2, y=24, w=fw, h=fh)
                for k, (n, col, note) in enumerate(notes):
                    bx = 16 + (k % 2) * 135
                    by = 24 + fh + 5 + (k // 2) * 8
                    rgb = _hex_to_rgb(col)
                    pdf.set_fill_color(*rgb); pdf.ellipse(bx, by, 6, 6, "F")
                    pdf.set_font("Helvetica", "B", 7)
                    pdf.set_text_color(0, 0, 0) if _luma(rgb) > 0.6 else pdf.set_text_color(255, 255, 255)
                    pdf.set_xy(bx, by); pdf.cell(6, 6, str(n), align="C")
                    pdf.set_font("Helvetica", "", 10); pdf.set_text_color(60, 60, 60)
                    pdf.set_xy(bx + 9, by); pdf.cell(122, 6, _pdf_safe(note[:70]))

        pdf.output(report_path)
    except Exception as exc:
        log.exception("PDF export failed: %s", exc)
        messagebox.showerror("PDF Export Error", f"Failed to export PDF:\n{exc}")
        return
    finally:
        for t in tmp_imgs:
            try: os.remove(t)
            except Exception: pass

    _set_status("✔  PDF report exported", C["success"])
    _open_folder(report_path)


# ══════════════════════════════════════ STATUS ══════════════════════════════════════

def _set_status(text, color):
    status_label.configure(text=text, text_color=color)


# ══════════════════════════════════════ GUI ══════════════════════════════════════

root = ctk.CTk()
root.title("PSR Pro — Process Step Recorder")
root.geometry("900x620")
root.minsize(760, 520)
root.configure(fg_color=C["bg"])

import tkinter.font as _tkfont
_FAMILIES = set(_tkfont.families(root))
ICON_FAMILY = "Segoe Fluent Icons" if "Segoe Fluent Icons" in _FAMILIES else "Segoe MDL2 Assets"
UI_FONT     = "Segoe UI Variable Text" if "Segoe UI Variable Text" in _FAMILIES else "Segoe UI"


def ic(size: int = 16):
    """Font tuple for icon glyphs."""
    return (ICON_FAMILY, size)


def _draw_logo(cv: tk.Canvas, size: int, fg: str = C["accent"], dot: str = C["danger"]) -> None:
    """The 'viewfinder' mark: four corner brackets around a record dot."""
    cv.delete("all")
    m, L, w = size * 0.13, size * 0.30, max(2, size // 11)
    for x, y, dx, dy in ((m, m, 1, 1), (size - m, m, -1, 1), (m, size - m, 1, -1), (size - m, size - m, -1, -1)):
        cv.create_line(x + dx * L, y, x, y, x, y + dy * L, fill=fg, width=w, capstyle="round", joinstyle="round")
    r, c = size * 0.12, size / 2
    cv.create_oval(c - r, c - r, c + r, c + r, fill=dot, outline="")


class Btn(ctk.CTkFrame):
    """Icon + label button with hover states (CTkButton cannot mix an icon font with a text font)."""
    _KINDS = {
        "ghost":   dict(bg="transparent", hover=C["surface2"], fg=C["muted"],  hfg=C["text"], border=None),
        "solid":   dict(bg=C["surface"],  hover=C["surface2"], fg=C["text"],   hfg=C["text"], border=C["border"]),
        "primary": dict(bg=C["accent"],   hover="#72b0ff",     fg="#06101f",   hfg="#06101f", border=None),
        "success": dict(bg="#123527",     hover="#1a4a36",     fg=C["success"], hfg="#7cf0bd", border="#1c5a40"),
        "danger":  dict(bg="#3a1620",     hover="#4d1b28",     fg=C["danger"], hfg="#ff8a99", border="#5c2230"),
        "warn":    dict(bg="#3a2a12",     hover="#4d3716",     fg=C["warn"],   hfg="#ffce85", border="#5c4218"),
    }

    def __init__(self, parent, icon="", text="", command=None, kind="ghost", size=12, pad=12,
                 center=False, height=None, **kw):
        kd = self._KINDS[kind]
        super().__init__(parent, corner_radius=8, fg_color=kd["bg"],
                         border_width=1 if kd["border"] else 0, border_color=kd["border"] or C["border"], **kw)
        self._kind, self._command, self._state, self._hover = kind, command, "normal", False
        holder = self
        if center:      # fixed-height, content centred (used for full-width buttons)
            self.configure(height=height or 46)
            self.pack_propagate(False)
            holder = ctk.CTkFrame(self, fg_color="transparent")
            holder.place(relx=0.5, rely=0.5, anchor="center")
        self._icon = ctk.CTkLabel(holder, text=icon, font=ic(size + 3), text_color=kd["fg"], width=18)
        self._label = ctk.CTkLabel(holder, text=text, font=(UI_FONT, size, "bold"), text_color=kd["fg"])
        if icon:
            self._icon.pack(side="left", padx=(pad, 6 if text else pad), pady=7)
        if text:
            self._label.pack(side="left", padx=(0 if icon else pad, pad), pady=7)
        widgets = (self, holder, self._icon, self._label) if center else (self, self._icon, self._label)
        for w in widgets:
            w.bind("<Enter>", self._on_enter, add="+")
            w.bind("<Leave>", self._on_leave, add="+")
            w.bind("<Button-1>", self._on_click, add="+")
            try: w.configure(cursor="hand2")
            except Exception: pass

    def _paint(self):
        kd = self._KINDS[self._kind]
        if self._state == "disabled":
            self._icon.configure(text_color=C["faint"]); self._label.configure(text_color=C["faint"])
            super().configure(fg_color="transparent" if kd["bg"] == "transparent" else C["surface"])
            return
        fg = kd["hfg"] if self._hover else kd["fg"]
        self._icon.configure(text_color=fg); self._label.configure(text_color=fg)
        super().configure(fg_color=kd["hover"] if self._hover else kd["bg"])

    def _on_enter(self, _e=None):
        if self._state == "normal":
            self._hover = True; self._paint()

    def _on_leave(self, _e=None):
        self._hover = False; self._paint()

    def _on_click(self, _e=None):
        if self._state == "normal" and self._command:
            self._command()

    def configure(self, require_redraw=False, **kw):
        state = kw.pop("state", None); text = kw.pop("text", None)
        kind = kw.pop("kind", None); icon = kw.pop("icon", None); kw.pop("command", None)
        if kw:
            super().configure(**kw)
        if not hasattr(self, "_label"):      # called from CTkFrame.__init__ / early setup
            return
        if text is not None: self._label.configure(text=text)
        if icon is not None: self._icon.configure(text=icon)
        if kind: self._kind = kind
        if state: self._state = state
        self._paint()


# ── Three top-level panels (only one visible at a time) ────────────────────────────
home_panel = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])
rec_panel  = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"], border_width=1, border_color=C["border_hi"])
edit_panel = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])


# ── App bar ─────────────────────────────────────────────────────────────────────────
appbar = ctk.CTkFrame(edit_panel, height=60, corner_radius=0, fg_color=C["panel"])
appbar.pack(side="top", fill="x")
appbar.pack_propagate(False)
ctk.CTkFrame(edit_panel, height=1, corner_radius=0, fg_color=C["border"]).pack(side="top", fill="x")

_logo = tk.Canvas(appbar, width=30, height=30, bg=C["panel"], highlightthickness=0)
_draw_logo(_logo, 30)
_logo.pack(side="left", padx=(18, 8), pady=15)
ctk.CTkLabel(appbar, text="PSR Pro", font=(UI_FONT, 16, "bold"), text_color=C["text"]).pack(side="left", padx=(0, 16))
ctk.CTkFrame(appbar, width=1, fg_color=C["border"]).pack(side="left", fill="y", pady=14)

project_name_var = tk.StringVar(value="")
project_name_entry = ctk.CTkEntry(
    appbar, textvariable=project_name_var, placeholder_text="Untitled recording",
    width=250, height=34, corner_radius=8, fg_color=C["surface"], border_width=1, border_color=C["border"],
    font=(UI_FONT, 13, "bold"), text_color=C["text"], placeholder_text_color=C["faint"])
project_name_entry.pack(side="left", padx=(16, 14), pady=13)
project_name_entry.bind("<Return>",   lambda e: (_apply_project_name(), root.focus()))
project_name_entry.bind("<FocusOut>", lambda e:  _apply_project_name())
tip(project_name_entry, "Project name — used for the folder and the export title")

_btn_open = Btn(appbar, ICON["open"], "Open", load_recording, kind="ghost")
_btn_open.pack(side="left", padx=2, pady=13)
tip(_btn_open, "Open an existing recording  [Ctrl+O]")

btn_start = Btn(appbar, ICON["record"], "New recording", start_recording, kind="success")
btn_start.pack(side="left", padx=4, pady=13)
tip(btn_start, "Start a new recording")

btn_continue = Btn(appbar, ICON["play"], "Continue", continue_recording, kind="warn")
btn_continue.pack(side="left", padx=2, pady=13)
btn_continue.configure(state="disabled")
tip(btn_continue, "Resume recording — appends to the current steps")

btn_stop = Btn(appbar, ICON["stop"], "Stop", stop_recording, kind="danger")   # only used while recording
btn_stop.configure(state="disabled")

# capture mode vars (shared with the recording tray)
_cap_click_var  = tk.BooleanVar(value=capture_on_click)
_cap_hotkey_var = tk.BooleanVar(value=capture_on_hotkey)

def _sync_globals(*_):
    global capture_on_click, capture_on_hotkey
    capture_on_click  = _cap_click_var.get()
    capture_on_hotkey = _cap_hotkey_var.get()

_cap_click_var.trace_add("write", _sync_globals)
_cap_hotkey_var.trace_add("write", _sync_globals)

_btn_pdf = Btn(appbar, ICON["doc"], "PDF", export_pdf, kind="primary")
_btn_pdf.pack(side="right", padx=(4, 18), pady=13)
tip(_btn_pdf, "Export as PDF  [Ctrl+Shift+P]")
_btn_html = Btn(appbar, ICON["globe"], "HTML", export_html, kind="solid")
_btn_html.pack(side="right", padx=4, pady=13)
tip(_btn_html, "Export as a single interactive HTML file  [Ctrl+Shift+H]")


# ── Status bar ──────────────────────────────────────────────────────────────────────
statusbar = ctk.CTkFrame(edit_panel, height=30, corner_radius=0, fg_color=C["panel"])
statusbar.pack(side="bottom", fill="x")
statusbar.pack_propagate(False)
ctk.CTkFrame(edit_panel, height=1, corner_radius=0, fg_color=C["border"]).pack(side="bottom", fill="x")
status_label = ctk.CTkLabel(statusbar, text="Ready", font=(UI_FONT, 11), text_color=C["muted"], anchor="w")
status_label.pack(side="left", padx=18)
ctk.CTkLabel(statusbar, text="Scroll = zoom   ·   Drag = pan   ·   ↑↓ = steps   ·   Ctrl+V = paste as step",
             font=(UI_FONT, 10), text_color=C["faint"]).pack(side="right", padx=18)


# ── Body: tool rail · filmstrip · editor ────────────────────────────────────────────
body = ctk.CTkFrame(edit_panel, corner_radius=0, fg_color=C["bg"])
body.pack(fill="both", expand=True, padx=12, pady=12)

filmstrip = Filmstrip(body)
filmstrip.frame.pack(side="left", fill="y", padx=(0, 10))
editor = EditorView(body)
editor.frame.pack(side="left", fill="both", expand=True)
_btn_step = filmstrip.add_btn

# tool rail ------------------------------------------------------------------------
tool_btns: dict = {}
_TOOLS = (
    ("none",      "pointer",   "Pointer",   "V", "Select, move and resize annotations"),
    None,
    ("highlight", "highlight", "Highlight", "U", "Draw a translucent highlight box"),
    ("arrow",     "arrow",     "Arrow",     "A", "Point at something"),
    ("text",      "text",      "Text",      "T", "Click to add a text label"),
    ("marker",    "marker",    "Number",    "N", "Click to drop a numbered marker (1, 2, 3…)"),
    ("draw",      "draw",      "Pen",       "B", "Freehand drawing"),
    None,
    ("redact",    "redact",    "Redact",    "M", "Cover a region with a solid box"),
    ("blur",      "blur",      "Pixelate",  "X", "Pixelate a region (irreversible in exports)"),
    None,
    ("crop",      "crop",      "Crop",      "C", "Non-destructive crop"),
)
def _marker_icon(color: str) -> ctk.CTkImage:
    """Numbered-circle icon for the marker tool (drawn, so it matches the icon font's weight)."""
    k = 4; n = 20 * k
    im = Image.new("RGBA", (n, n), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    d.ellipse([2 * k, 2 * k, n - 2 * k, n - 2 * k], outline=color, width=int(1.6 * k))
    d.text((n / 2, n / 2 + k * 0.3), "1", font=_pil_font(int(12 * k), True), fill=color, anchor="mm")
    return ctk.CTkImage(light_image=im, dark_image=im, size=(20, 20))

_MARKER_ICONS = {False: _marker_icon(C["muted"]), True: _marker_icon(C["accent"])}

for _t in _TOOLS:
    if _t is None:
        _sep = ctk.CTkFrame(editor.rail, height=1, width=26, fg_color=C["border_hi"])
        editor.add_rail_item("sep", _sep)
        continue
    _tool, _icon, _name, _key, _desc = _t
    _b = ctk.CTkButton(editor.rail, text=ICON[_icon] if _icon != "marker" else "", width=38, height=38, corner_radius=10,
        font=ic(17), image=_marker_icon(C["muted"]) if _icon == "marker" else None,
        fg_color="transparent", hover_color=C["surface2"], text_color=C["muted"], text_color_disabled=C["faint"],
        border_width=0, command=lambda t=_tool: set_tool(t))
    tip(_b, f"{_name}  [{_key}]\n{_desc}")
    tool_btns[_tool] = _b
    editor.add_rail_item("btn", _b)
editor.layout_rail()

# tool options bar lives inside the editor (colour swatches + sizes) --------------------
draw_color_btns.clear(); pen_size_btns.clear()
_SWATCHES = [
    ("#ff5468", "Red"), ("#ff9f43", "Orange"), ("#ffd93d", "Yellow"),
    ("#2fd08a", "Green"), ("#4d9bff", "Blue"), ("#ffffff", "White"), ("#111111", "Black"),
]
for hex_col, col_lbl in _SWATCHES:
    sw = ctk.CTkButton(editor.opt_colors, text="", width=22, height=22, corner_radius=11,
        fg_color=hex_col, hover_color=hex_col, border_width=1, border_color=C["border_hi"],
        command=lambda c=hex_col: _set_draw_color_global(c))
    sw.pack(side="left", padx=3)
    draw_color_btns.append((sw, hex_col))
    tip(sw, col_lbl)
draw_color_btns[0][0].configure(border_width=2, border_color="#ffffff")
draw_color = _SWATCHES[0][0]

def _open_color_picker():
    from tkinter import colorchooser
    result = colorchooser.askcolor(color=draw_color, title="Pick colour")
    if result and result[1]:
        _set_draw_color_global(result[1])

_color_picker_btn = ctk.CTkButton(editor.opt_colors, text=ICON["palette"], width=26, height=26, corner_radius=8,
    fg_color="transparent", hover_color=C["surface2"], font=ic(14), text_color=C["muted"],
    command=_open_color_picker)
_color_picker_btn.pack(side="left", padx=(6, 0))
draw_color_btns.append((_color_picker_btn, None))
tip(_color_picker_btn, "Custom colour")

for _plbl, _ppx, _ptip in (("S", 2, "Small"), ("M", 5, "Medium"), ("L", 10, "Large"), ("XL", 18, "Extra large")):
    pb = ctk.CTkButton(editor.opt_sizes, text=_plbl, width=34, height=26, corner_radius=8,
        fg_color=C["acc_soft"] if _plbl == "S" else "transparent", border_width=1,
        border_color=C["accent"] if _plbl == "S" else C["border"], text_color=C["text"],
        hover_color=C["surface2"], font=(UI_FONT, 10, "bold"),
        command=lambda w=_ppx: _set_draw_width_global(w))
    pb.pack(side="left", padx=2)
    pen_size_btns.append((pb, _ppx))
    tip(pb, f"{_ptip} — line width, text size, marker size")


# ══════════════════════════════════════ RECORDING PANEL ══════════════════════════════════════
# Floating toolbar — borderless, fully draggable, snipping-tool style.
# Row 1:  [⠿ ● ■ ⏸]  [⚙]  [▾]
# Row 2:  [#12  ↳ left mouse button at (512,340)          project-name]

_rec_row1 = ctk.CTkFrame(rec_panel, height=36, corner_radius=0, fg_color=C["panel"])
_rec_row1.pack(fill="x")
_rec_row1.pack_propagate(False)

# — Left: grip + status + action buttons —
_rec_grip = ctk.CTkLabel(_rec_row1, text="⠿", font=("Segoe UI", 14),
    text_color=C["faint"], width=16, cursor="fleur")
_rec_grip.pack(side="left", padx=(8, 2))

_rec_status = ctk.CTkLabel(_rec_row1, text=ICON["record"],
    font=ic(13), text_color=C["danger"], width=18)
_rec_status.pack(side="left", padx=(0, 4))

_AB = dict(height=26, corner_radius=8, font=ic(13))

_rec_stop_btn = ctk.CTkButton(_rec_row1, text=ICON["stop"], command=stop_recording,
    fg_color=C["danger"], hover_color="#ff7a8a", text_color="#1a0a0e", width=30, border_width=0, **_AB)
_rec_stop_btn.pack(side="left", padx=(0, 2), pady=6)
tip(_rec_stop_btn, "Stop recording  [F6]")

_btn_pause = ctk.CTkButton(_rec_row1, text=ICON["pause"], command=lambda: _toggle_pause(),
    fg_color=C["surface"], hover_color=C["surface2"], text_color=C["text"],
    width=30, border_width=1, border_color=C["border"], **_AB)
_btn_pause.pack(side="left", padx=(0, 2), pady=6)
tip(_btn_pause, "Pause / resume  [F7]")

# — Capture mode indicators (between actions and right-side buttons) —
_rec_mode_label = ctk.CTkLabel(_rec_row1, text="",
    font=(UI_FONT, 9, "bold"), text_color=C["faint"], anchor="w")
_rec_mode_label.pack(side="left", padx=(8, 0))

# — Right: minimize —
_rec_minimized = [False]

def _minimize_rec_tray():
    _rec_minimized[0] = True
    root.overrideredirect(False)
    root.iconify()

def _restore_rec_tray():
    if not _rec_minimized[0]:
        return
    _rec_minimized[0] = False
    root.deiconify()
    root.overrideredirect(True)
    root.attributes("-topmost", True)
    root.lift()

_rec_hide_btn = ctk.CTkButton(_rec_row1, text=ICON["chevron_down"], command=_minimize_rec_tray,
    fg_color="transparent", hover_color=C["surface2"],
    text_color=C["muted"], width=26, height=26, corner_radius=8,
    font=ic(11), border_width=0)
_rec_hide_btn.pack(side="right", padx=(0, 6))
tip(_rec_hide_btn, "Minimize to taskbar  [F8]")

# — Settings gear — opens a flyout popup —
_rec_flyout = None
_was_paused_before_flyout = [False]
_flyout_close_bind_id = [None]

def _close_rec_settings():
    """Close the settings flyout and resume if needed."""
    global _rec_flyout, paused
    if _rec_flyout is not None:
        try: _rec_flyout.destroy()
        except Exception: pass
        _rec_flyout = None
        _save_recording_settings()
    if _flyout_close_bind_id[0]:
        try: root.unbind("<Button-1>", _flyout_close_bind_id[0])
        except Exception: pass
        _flyout_close_bind_id[0] = None
    if not _was_paused_before_flyout[0] and paused:
        paused = False
        _update_rec_panel()

def _toggle_settings_flyout():
    global _rec_flyout, paused
    if _rec_flyout is not None:
        _close_rec_settings()
        return
    _was_paused_before_flyout[0] = paused
    if not paused:
        paused = True
        _update_rec_panel()
    x = root.winfo_x()
    y = root.winfo_y() + root.winfo_height()
    _rec_flyout = tk.Toplevel(root)
    _rec_flyout.overrideredirect(True)
    _rec_flyout.attributes("-topmost", True)
    _rec_flyout.configure(bg=C["panel"])

    pad = ctk.CTkFrame(_rec_flyout, fg_color=C["panel"], corner_radius=6,
        border_width=1, border_color=C["border"])
    pad.pack(fill="both", expand=True, padx=1, pady=1)

    _ignore_psr_var   = tk.BooleanVar(value=ignore_psr_focus)
    _cap_keyboard_var = tk.BooleanVar(value=capture_keyboard)
    _marker_var       = tk.BooleanVar(value=show_click_markers)

    def _sync(*_a):
        global ignore_psr_focus, capture_keyboard, show_click_markers
        ignore_psr_focus = _ignore_psr_var.get()
        capture_keyboard = _cap_keyboard_var.get()
        show_click_markers = _marker_var.get()
        _update_rec_panel()
    _ignore_psr_var.trace_add("write", _sync)
    _cap_keyboard_var.trace_add("write", _sync)
    _marker_var.trace_add("write", _sync)

    _CBO = dict(fg_color=C["accent"], hover_color=C["acc_dark"], border_color=C["border"],
        height=24, checkbox_width=14, checkbox_height=14, corner_radius=3,
        font=("Segoe UI", 10))

    ctk.CTkLabel(pad, text="Capture", font=("Segoe UI", 9, "bold"),
        text_color=C["muted"]).pack(anchor="w", padx=10, pady=(8, 2))

    for _cvar, _ctxt, _ctip in (
        (_cap_click_var,    "Mouse clicks",      "Capture on every mouse click"),
        (_cap_hotkey_var,   "Scroll Lock key",   "Capture on Scroll Lock press"),
        (_cap_keyboard_var, "Keyboard shortcuts", "Record keyboard combos as steps"),
        (_ignore_psr_var,   "Ignore this tray",   "Don't record clicks on this toolbar"),
        (_marker_var,       "Mark click position", "Draw a red ring where you clicked (editor + exports)"),
    ):
        cb = ctk.CTkCheckBox(pad, text=_ctxt, variable=_cvar,
            text_color=C["text"], **_CBO)
        cb.pack(anchor="w", padx=12, pady=2)
        tip(cb, _ctip)

    ctk.CTkFrame(pad, height=1, fg_color=C["border"]).pack(fill="x", padx=8, pady=6)

    ctk.CTkLabel(pad, text="Screenshot", font=("Segoe UI", 9, "bold"),
        text_color=C["muted"]).pack(anchor="w", padx=10, pady=(0, 2))

    _DDS = dict(height=24, corner_radius=4,
        fg_color=C["surface"], button_color=C["border"], button_hover_color=C["acc_dark"],
        dropdown_fg_color=C["surface"], dropdown_hover_color=C["acc_dark"],
        font=("Segoe UI", 10), dropdown_font=("Segoe UI", 10), text_color=C["text"])

    row_d = ctk.CTkFrame(pad, fg_color="transparent")
    row_d.pack(fill="x", padx=10, pady=2)
    ctk.CTkLabel(row_d, text="Delay", font=("Segoe UI", 10),
        text_color=C["muted"], width=48).pack(side="left")

    _delay_var = tk.StringVar(value=f"{capture_delay_ms}ms")
    _DELAY_OPTS = ["0ms", "50ms", "100ms", "200ms"]
    def _on_delay(*_a):
        global capture_delay_ms
        raw = _delay_var.get().replace("ms", "")
        try: capture_delay_ms = int(raw)
        except Exception: capture_delay_ms = 100
    _delay_var.trace_add("write", _on_delay)
    ctk.CTkOptionMenu(row_d, variable=_delay_var, values=_DELAY_OPTS, width=70, **_DDS
        ).pack(side="left", padx=(4, 0))

    row_f = ctk.CTkFrame(pad, fg_color="transparent")
    row_f.pack(fill="x", padx=10, pady=(2, 8))
    ctk.CTkLabel(row_f, text="Format", font=("Segoe UI", 10),
        text_color=C["muted"], width=48).pack(side="left")

    _fmt_var_local = tk.StringVar(value=capture_format.upper())
    def _on_fmt(*_a):
        global capture_format
        capture_format = _fmt_var_local.get().lower()
    _fmt_var_local.trace_add("write", _on_fmt)
    ctk.CTkOptionMenu(row_f, variable=_fmt_var_local, values=["JPG", "PNG"], width=70, **_DDS
        ).pack(side="left", padx=(4, 0))

    _rec_flyout.update_idletasks()
    _rec_flyout.geometry(f"+{x}+{y}")

    # Delayed bind so the opening click doesn't immediately trigger close
    def _bind_close():
        def _on_click(e):
            if _rec_flyout is None or not _rec_flyout.winfo_exists():
                return
            try:
                wx, wy = _rec_flyout.winfo_rootx(), _rec_flyout.winfo_rooty()
                ww, wh = _rec_flyout.winfo_width(), _rec_flyout.winfo_height()
                if not (wx <= e.x_root <= wx+ww and wy <= e.y_root <= wy+wh):
                    _close_rec_settings()
            except Exception:
                pass
        _flyout_close_bind_id[0] = root.bind("<Button-1>", _on_click, add="+")
    root.after(150, _bind_close)

_rec_gear_btn = ctk.CTkButton(_rec_row1, text=ICON["settings"], command=_toggle_settings_flyout,
    fg_color="transparent", hover_color=C["surface2"],
    text_color=C["muted"], width=28, height=26, corner_radius=8,
    font=ic(13), border_width=0)
_rec_gear_btn.pack(side="right", padx=(0, 2))
tip(_rec_gear_btn, "Recording settings")

# — Row 2: step count + feedback —
_rec_row2 = ctk.CTkFrame(rec_panel, height=26, corner_radius=0, fg_color=C["bg"])
_rec_row2.pack(fill="x")
_rec_row2.pack_propagate(False)

_rec_steps = ctk.CTkLabel(_rec_row2, text="0", font=("Consolas", 11, "bold"),
    text_color=C["accent"], fg_color=C["acc_soft"], corner_radius=6, width=30, height=18)
_rec_steps.pack(side="left", padx=(10, 2))

_rec_cap_step = ctk.CTkLabel(_rec_row2, text="",
    font=(UI_FONT, 9), text_color=C["muted"], anchor="w")
_rec_cap_step.pack(side="left", padx=(2, 0))

_rec_cap_input = ctk.CTkLabel(_rec_row2, text="",
    font=(UI_FONT, 9, "bold"), text_color=C["muted"], anchor="w")
_rec_cap_input.pack(side="left", padx=(2, 0))

_rec_cap_rest = ctk.CTkLabel(_rec_row2, text="",
    font=(UI_FONT, 9), text_color=C["faint"], anchor="w")
_rec_cap_rest.pack(side="left", padx=(2, 0))

_rec_project = ctk.CTkLabel(_rec_row2, text="",
    font=(UI_FONT, 9), text_color=C["faint"])
_rec_project.pack(side="right", padx=(0, 10))

# ── Dragging — bind_all with event filter for reliability ──
_rec_drag = {"x": 0, "y": 0, "active": False}

_REC_INTERACTIVE = (ctk.CTkButton, ctk.CTkCheckBox, ctk.CTkOptionMenu,
                    ctk.CTkEntry, ctk.CTkTextbox, ctk.CTkSwitch)

def _is_rec_interactive(widget):
    """Walk up from widget to rec_panel; return True if any ancestor is interactive."""
    w = widget
    while w:
        if isinstance(w, _REC_INTERACTIVE):
            return True
        if w == rec_panel:
            return False
        w = getattr(w, 'master', None)
    return True  # outside rec_panel — don't drag

def _rec_press(e):
    if not rec_panel.winfo_ismapped():
        return
    if _is_rec_interactive(e.widget):
        return
    _rec_drag["x"] = e.x_root - root.winfo_x()
    _rec_drag["y"] = e.y_root - root.winfo_y()
    _rec_drag["active"] = True

def _rec_motion(e):
    if _rec_drag["active"] and rec_panel.winfo_ismapped():
        root.geometry(f"+{e.x_root - _rec_drag['x']}+{e.y_root - _rec_drag['y']}")

def _rec_release(e):
    _rec_drag["active"] = False

root.bind("<ButtonPress-1>", _rec_press, add="+")
root.bind("<B1-Motion>", _rec_motion, add="+")
root.bind("<ButtonRelease-1>", _rec_release, add="+")


_pulse_on = [True]

def _pulse_rec_dot():
    """Gentle blink of the record indicator while a recording is running."""
    if recording and not paused and rec_panel.winfo_ismapped():
        _pulse_on[0] = not _pulse_on[0]
        _rec_status.configure(text_color=C["danger"] if _pulse_on[0] else "#7a2a35")
    root.after(700, _pulse_rec_dot)


def _toggle_pause():
    global paused
    paused = not paused
    _update_rec_panel()


def _update_rec_panel():
    _rec_project.configure(text=project_name or "Untitled")
    count = len(log_data)
    _rec_steps.configure(text=str(count))
    if paused:
        _rec_status.configure(text=ICON["pause"], text_color=C["warn"])
        _btn_pause.configure(text=ICON["play"], border_color=C["warn"])
    elif recording:
        _rec_status.configure(text=ICON["record"], text_color=C["danger"])
        _btn_pause.configure(text=ICON["pause"], border_color=C["border"])
    else:
        _rec_status.configure(text=ICON["stop"], text_color=C["muted"])
        _btn_pause.configure(text=ICON["pause"], border_color=C["border"])
    # Build compact capture-mode indicator
    modes = []
    if capture_on_click:  modes.append("CLICKS")
    if capture_keyboard:  modes.append("KEYS")
    if capture_on_hotkey: modes.append("HOTKEY")
    _rec_mode_label.configure(text="  ·  ".join(modes) if modes else "NOTHING ARMED")
    step_num, kw, rest, cap_color = _last_capture[0]
    if kw:
        _rec_cap_step.configure(text=f"↳ {step_num}")
        _rec_cap_input.configure(text=kw, text_color=cap_color or C["text"])
        _rec_cap_rest.configure(text=rest)
    else:
        _rec_cap_step.configure(text="")
        _rec_cap_input.configure(text="")
        _rec_cap_rest.configure(text="")


# ══════════════════════════════════════ HOME PANEL ══════════════════════════════════════
# One centred column on a quiet background; the four corner brackets echo the logo.

_home_bg = tk.Canvas(home_panel, bg=C["bg"], highlightthickness=0)
_home_bg.place(relx=0, rely=0, relwidth=1, relheight=1)

def _paint_home_bg(_e=None):
    cv = _home_bg
    cv.delete("all")
    w, h = cv.winfo_width(), cv.winfo_height()
    m, L = 30, 56
    for x, y, dx, dy in ((m, m, 1, 1), (w - m, m, -1, 1), (m, h - m, 1, -1), (w - m, h - m, -1, -1)):
        cv.create_line(x + dx * L, y, x, y, x, y + dy * L, fill=C["border"], width=2, capstyle="round", joinstyle="round")

_home_bg.bind("<Configure>", _paint_home_bg)

_hl = ctk.CTkFrame(home_panel, fg_color="transparent")
_hl.place(relx=0.5, rely=0.5, anchor="center")

_home_logo = tk.Canvas(_hl, width=84, height=84, bg=C["bg"], highlightthickness=0)
_draw_logo(_home_logo, 84)
_home_logo.pack()
ctk.CTkLabel(_hl, text="PSR Pro", font=(UI_FONT, 38, "bold"), text_color=C["text"]).pack(pady=(14, 0))
ctk.CTkLabel(_hl, text="Record a workflow. Get a guide.", font=(UI_FONT, 14),
             text_color=C["muted"]).pack(pady=(2, 30))

_home_row = ctk.CTkFrame(_hl, fg_color="transparent")
_home_row.pack()
_home_name = ctk.CTkEntry(_home_row, textvariable=project_name_var, width=330, height=50, corner_radius=10,
    fg_color=C["surface"], border_width=1, border_color=C["border"], font=(UI_FONT, 14),
    text_color=C["text"])
_home_name.pack(side="left")
_home_name.bind("<Return>", lambda e: start_recording())
Btn(_home_row, ICON["record"], "Record", start_recording, kind="primary", size=14,
    center=True, height=50, width=140).pack(side="left", padx=(10, 0))

save_parent_dir_var = tk.StringVar(value=os.path.abspath(BASE_DIR))
_home_meta = ctk.CTkFrame(_hl, fg_color="transparent")
_home_meta.pack(pady=(16, 0))
Btn(_home_meta, ICON["open"], "Open recording", load_recording, kind="ghost").pack(side="left")
ctk.CTkLabel(_home_meta, text="·", text_color=C["faint"]).pack(side="left", padx=6)
_home_path_lbl = ctk.CTkLabel(_home_meta, text="", font=(UI_FONT, 11), text_color=C["faint"])
_home_path_lbl.pack(side="left")

def _short_path(pth: str) -> str:
    parts = os.path.normpath(pth).split(os.sep)
    return "…" + os.sep + os.sep.join(parts[-2:]) if len(parts) > 3 else pth

def _update_home_path(*_):
    _home_path_lbl.configure(text=f"Saving to  {_short_path(save_parent_dir_var.get())}")

def _browse_home_save_dir():
    folder = filedialog.askdirectory(initialdir=save_parent_dir_var.get(), title="Choose folder")
    if folder:
        save_parent_dir_var.set(folder)
        _refresh_home()

save_parent_dir_var.trace_add("write", _update_home_path)
_update_home_path()
Btn(_home_meta, "", "Change", _browse_home_save_dir, kind="ghost", size=11, pad=8).pack(side="left", padx=(2, 0))

_home_recents_inner = [None]


def _open_recent(folder):
    if _do_load_recording(folder):
        show_editing()


def _refresh_home():
    """Compact 'recent' list under the start controls (hidden when empty)."""
    if _home_recents_inner[0]:
        try: _home_recents_inner[0].destroy()
        except Exception: pass
        _home_recents_inner[0] = None

    recent, seen = [], set()
    for base in dict.fromkeys([BASE_DIR, save_parent_dir_var.get()]):
        if not os.path.isdir(base):
            continue
        for name in os.listdir(base):
            folder = os.path.join(base, name)
            json_path = os.path.join(folder, "steps.json")
            if folder in seen or not os.path.exists(json_path):
                continue
            seen.add(folder)
            try:
                mtime = os.path.getmtime(json_path)
                with open(json_path, encoding="utf-8") as f:
                    raw = json.load(f)
                steps = raw if isinstance(raw, list) else raw.get("steps", [])
                pname = name if isinstance(raw, list) else (raw.get("project_name") or name)
                if steps:
                    recent.append((mtime, pname, len(steps), folder))
            except Exception:
                pass
    recent.sort(key=lambda r: r[0], reverse=True)
    recent = recent[:3]
    if not recent:
        return

    box = ctk.CTkFrame(_hl, fg_color="transparent")
    box.pack(pady=(34, 0))
    _home_recents_inner[0] = box
    ctk.CTkLabel(box, text="RECENT", font=(UI_FONT, 9, "bold"), text_color=C["faint"]).pack(anchor="w", padx=6, pady=(0, 4))
    for mtime, pname, n, folder in recent:
        row = ctk.CTkFrame(box, width=480, height=38, corner_radius=8, fg_color="transparent", cursor="hand2")
        row.pack(pady=1)
        row.pack_propagate(False)
        name_lbl = ctk.CTkLabel(row, text=_ellipsize(pname, 44), font=(UI_FONT, 12), text_color=C["text"], anchor="w")
        name_lbl.pack(side="left", padx=(12, 0))
        meta = f"{n} step{'s' if n != 1 else ''}  ·  {datetime.fromtimestamp(mtime).strftime('%b %d')}"
        meta_lbl = ctk.CTkLabel(row, text=meta, font=(UI_FONT, 11), text_color=C["faint"])
        meta_lbl.pack(side="right", padx=(0, 12))

        def _make(f, r):
            def _click(_e): _open_recent(f)
            def _enter(_e): r.configure(fg_color=C["surface"])
            def _leave(_e): r.configure(fg_color="transparent")
            return _click, _enter, _leave
        _click, _enter, _leave = _make(folder, row)
        for w in (row, name_lbl, meta_lbl):
            w.bind("<Button-1>", _click); w.bind("<Enter>", _enter); w.bind("<Leave>", _leave)


# ══════════════════════════════════════ PANEL SWITCHING ══════════════════════════════════════

def show_home():
    _close_rec_settings()
    rec_panel.pack_forget()
    edit_panel.pack_forget()
    root.overrideredirect(False)
    _refresh_home()
    home_panel.pack(fill="both", expand=True)
    root.geometry("900x620")
    root.minsize(700, 540)
    root.resizable(True, True)
    root.attributes("-topmost", False)
    root.title("PSR Pro — Process Step Recorder")
    if not project_name_var.get().strip():
        project_name_var.set(_default_recording_name())
    # Restore toolbar button to its default label for when we return to edit mode
    btn_start.configure(text="Start recording")
    tip(btn_start, "Start a new recording")


def show_recording():
    home_panel.pack_forget()
    edit_panel.pack_forget()
    _update_rec_panel()
    rec_panel.pack(fill="both", expand=True)
    # Leave fullscreen/zoomed so the tray is actually small (not fullscreen)
    try:
        root.state("normal")
    except Exception:
        pass
    sw = root.winfo_screenwidth()
    root.overrideredirect(True)
    w = 280
    root.geometry(f"{w}x64+{(sw - w) // 2}+8")
    root.minsize(220, 64)
    root.resizable(True, False)
    root.attributes("-topmost", True)


def show_editing():
    _close_rec_settings()
    home_panel.pack_forget()
    rec_panel.pack_forget()
    root.overrideredirect(False)
    edit_panel.pack(fill="both", expand=True)
    root.geometry("1500x900")
    root.minsize(960, 640)
    root.resizable(True, True)
    root.attributes("-topmost", False)
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")
    # In edit mode "Start" means "new recording", not "start the current one"
    btn_start.configure(text="New recording")
    tip(btn_start, "Start a new recording — replaces the current session")
    _build_all_cards()


# ══════════════════════════════════════ KEYBOARD SHORTCUTS ══════════════════════════

_TEXT_FOCUS_CLASSES = ("Text", "Entry", "TEntry", "Spinbox", "TSpinbox")

def _focus_in_text_input():
    """True if keyboard focus is in a text/entry widget (don't steal shortcuts)."""
    try:
        focus = root.focus_get()
    except KeyError:   # popdown/menu widgets are unknown to tkinter
        return False
    return bool(focus) and focus.winfo_class() in _TEXT_FOCUS_CLASSES


def _on_root_key(event):
    if event.keysym in ("Delete", "BackSpace"):
        if _focus_in_text_input():
            return
        # Annotation delete takes priority over step delete
        if (editor._selected_obj is not None or editor._sel_click) and edit_panel.winfo_ismapped():
            editor.delete_selected()
            return "break"
        if _selected:
            _delete_selected()
            return "break"


def _on_tool_hotkey(event):
    if event.state & 0x0004 or event.state & 0x20000:   # Ctrl / Alt
        return
    if _focus_in_text_input():
        return
    _TOOL_KEYS = {'v': 'none', 'u': 'highlight', 'm': 'redact', 'c': 'crop', 'b': 'draw'}
    tool = _TOOL_KEYS.get(event.char.lower())
    if tool:
        set_tool(tool)
        return "break"


def _on_undo(event=None):
    if _focus_in_text_input():
        return
    if edit_panel.winfo_ismapped():
        editor._undo()
        return "break"


def _on_arrow(event):
    if not edit_panel.winfo_ismapped() or _focus_in_text_input():
        return
    delta = -1 if event.keysym == "Up" else 1
    if event.state & 0x20000 and 0 <= active_index < len(log_data):   # Alt+Up/Down moves the step
        j = active_index + delta
        if 0 <= j < len(log_data):
            _swap_steps(active_index, j)
    else:
        _select_relative(delta)
    return "break"


def _on_map(event):
    """Fired when the window becomes visible again (e.g. restored from taskbar)."""
    if _rec_minimized[0] and recording:
        root.after(50, _restore_rec_tray)

root.bind("<Map>", _on_map)
root.bind("<Delete>",    _on_root_key)
root.bind("<BackSpace>", _on_root_key)
root.bind("<Control-v>", _handle_paste)
root.bind("<Control-z>", _on_undo)
root.bind("<Up>",   _on_arrow)
root.bind("<Down>", _on_arrow)
root.bind("<Alt-Up>",   _on_arrow)
root.bind("<Alt-Down>", _on_arrow)
root.bind("<Control-o>", lambda e: load_recording())
root.bind("<Control-O>", lambda e: load_recording())
root.bind("<Control-Shift-H>", lambda e: export_html())
root.bind("<Control-Shift-P>", lambda e: export_pdf())
for _hk in ('v', 'u', 'm', 'c', 'b'):
    root.bind(f"<KeyPress-{_hk}>", _on_tool_hotkey)
    root.bind(f"<KeyPress-{_hk.upper()}>", _on_tool_hotkey)


# ══════════════════════════════════════ START ══════════════════════════════════════

root.protocol("WM_DELETE_WINDOW", lambda: (stop_listeners(), _cleanup_sound_file(), root.destroy()))
root.after(100, process_queue)
root.after(700, _pulse_rec_dot)
root.after(300, _setup_dnd)
set_tool("none")
show_home()
root.mainloop()
