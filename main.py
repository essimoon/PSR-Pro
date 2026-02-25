#!/usr/bin/env python3
"""
PSR Pro v4 — Professional Process Step Recorder
Non-destructive crop · Insert custom steps · Project naming
Vector annotation layer · Selectable objects with transform gizmo
Mouse-up screenshot capture · Per-step undo · Continue recording

Dependencies:
    pip install customtkinter pillow mss pynput pygetwindow fpdf2
    pip install tkinterdnd2          # optional: enables drag-and-drop
"""

import copy, html as _html, io, os, re, json, queue, subprocess, sys, time, threading, base64, webbrowser
from datetime import datetime

import tkinter as tk
from tkinter import filedialog, messagebox
import customtkinter as ctk
from PIL import Image, ImageTk, ImageDraw, ImageGrab
import mss
from pynput import mouse, keyboard
from fpdf import FPDF

try:
    import pygetwindow as gw
    _HAS_GW = True
except ImportError:
    _HAS_GW = False

try:
    from tkinterdnd2 import TkinterDnD
    _HAS_DND = True
except ImportError:
    _HAS_DND = False


# ══════════════════════════════════════ THEME ══════════════════════════════════════

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

C = {
    "bg":       "#111111",
    "panel":    "#1a1a1a",
    "surface":  "#222222",
    "card":     "#1e1e1e",
    "border":   "#2c2c2c",
    "accent":   "#3d8ef0",
    "acc_dark": "#2a6cbf",
    "danger":   "#c0392b",
    "success":  "#27ae60",
    "warn":     "#e67e22",
    "text":     "#e4e4e4",
    "muted":    "#777777",
    "crop_col": "#f0c040",
}

CARD_IMG_MAX_W = 860
HANDLE_SZ      = 6
HANDLE_HIT     = 9


# ══════════════════════════════════════ GLOBALS ══════════════════════════════════════

BASE_DIR = "recordings"
os.makedirs(BASE_DIR, exist_ok=True)

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
_last_capture     = [("", "", "", None)]  # (step, keyword, rest, color)
draw_color      = "#e74c3c"
draw_width      = 3

step_cards      = []
active_card_ref = [None]
_selected: set  = set()   # selected step indices (multi-select)
_sel_anchor     = -1      # anchor for shift-range selection
draw_color_btns = []
pen_size_btns   = []
view_mode       = "default"   # "default" | "list" | "grid"
_prev_view_mode = ""          # set when jumping to detail via double-click

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
                       background="#1e1e1e", foreground="#aaaaaa",
                       relief="solid", borderwidth=1,
                       font=("Segoe UI", 9), padx=7, pady=4)
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


def _obj_bbox_img(obj):
    """Bounding box of an annotation object in original image coordinates."""
    if obj["type"] in ("highlight", "redact"):
        x1, x2 = sorted([obj["x1"], obj["x2"]])
        y1, y2 = sorted([obj["y1"], obj["y2"]])
        return x1, y1, x2, y2
    pts = obj["points"]
    xs  = [p[0] for p in pts]
    ys  = [p[1] for p in pts]
    return min(xs), min(ys), max(xs), max(ys)


def _get_crop(step_index, img_size=None):
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


def _pdf_safe(text):
    """Make text safe for PDF built-in fonts (latin-1 subset)."""
    replacements = {
        '\u2018': "'", '\u2019': "'", '\u201c': '"', '\u201d': '"',
        '\u2013': '-', '\u2014': '--', '\u2026': '...', '\u00a0': ' ',
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return text.encode('latin-1', errors='replace').decode('latin-1')


def _open_folder(filepath):
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
        print(f"[PSR] Could not open folder: {e}")


def _flatten_to_pil(step_index):
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

    objects = step_objects.get(step_index, [])
    if not objects:
        return img

    draw_ctx = ImageDraw.Draw(img)
    for obj in objects:
        rgb = _hex_to_rgb(obj["color"])
        if obj["type"] == "highlight":
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
    return img


# ══════════════════════════════════════ SESSION ══════════════════════════════════════

def _safe_folder_name(name):
    """Sanitize a string for use as a folder name."""
    name = re.sub(r'[<>:"/\\|?*]', '_', name.strip())
    name = name.strip('. ')
    return name[:80] if name else ""


def create_session(parent_dir=None):
    """Create the session folder. parent_dir: where to create it (default BASE_DIR)."""
    global current_session
    base = (parent_dir if parent_dir is not None else BASE_DIR)
    ts = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    try:
        pname = _safe_folder_name(project_name_var.get())
    except Exception:
        pname = ""
    folder = f"{pname}_{ts}" if pname else ts
    current_session = os.path.join(base, folder)
    os.makedirs(current_session)


def save_steps():
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
        with open(os.path.join(current_session, "steps.json"), "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=4)
    except OSError as exc:
        _set_status(f"⚠ Save failed: {exc}", C["danger"])


CAPTURE_MAX_W = 1920  # cap screenshot width — matches Windows Steps Recorder behaviour

def capture_screenshot(filename):
    filepath = os.path.join(current_session, filename)
    with mss.mss() as sct:
        shot = sct.grab(sct.monitors[1])
        img = Image.frombytes("RGB", shot.size, shot.rgb)
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
    return out


def get_active_window():
    if not _HAS_GW:
        return "Unknown"
    try:
        win = gw.getActiveWindow()
        return win.title if win else "Unknown"
    except Exception:
        return "Unknown"


# ══════════════════════════════════════ STEP HANDLING ══════════════════════════════════════

def handle_event(event_text):
    global step_counter
    if not recording or not current_session:
        return
    if capture_delay_ms > 0:
        time.sleep(capture_delay_ms / 1000.0)
    filename = f"step_{step_counter}.{capture_format}"
    try:
        capture_screenshot(filename)
    except Exception as exc:
        print(f"[PSR] Screenshot error: {exc}")
        return
    window = get_active_window()
    entry  = {
        "step":        step_counter,
        "description": f"In '{window}', {event_text}",
        "screenshot":  filename,
    }
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
    root.after(0, _append_card)
    root.after(0, _update_rec_panel)
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
        if ignore_psr_focus and _psr_is_active():
            return
        btn = str(button).replace("Button.", "")
        event_queue.put(f"released {btn} mouse button at ({x}, {y})")


_show_tray_flag = [False]  # set by pynput thread, consumed by tkinter main loop

def _on_press_key(key):
    # F8 toggles tray visibility — works even when window is hidden
    if key == keyboard.Key.f8 and recording:
        _show_tray_flag[0] = True
        return

    if not recording or paused:
        return

    if ignore_psr_focus and _psr_is_active():
        return

    if capture_on_hotkey and key == keyboard.Key.scroll_lock:
        event_queue.put("manual capture (Scroll Lock)")
        return

    if not capture_keyboard:
        return

    if not capture_on_click:
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
    try:
        text = event_queue.get_nowait()
        handle_event(text)
    except queue.Empty:
        pass
    # Check if F8 was pressed (pynput thread) to restore/minimize tray
    if _show_tray_flag[0]:
        _show_tray_flag[0] = False
        if recording:
            if _rec_minimized[0]:
                _restore_rec_tray()
            else:
                _minimize_rec_tray()
    root.after(100, process_queue)


# ══════════════════════════════════════ UNDO ══════════════════════════════════════

def push_undo(step_index):
    """Snapshot both objects and crop for this step."""
    if step_index not in undo_stacks:
        undo_stacks[step_index] = []
    undo_stacks[step_index].append(json.dumps({
        "objects": step_objects.get(step_index, []),
        "crop":    step_crops.get(step_index),
    }))


def pop_undo(step_index):
    stack = undo_stacks.get(step_index, [])
    if not stack:
        return False
    state = json.loads(stack.pop())
    step_objects[step_index] = state["objects"]
    if state["crop"] is None:
        step_crops.pop(step_index, None)
    else:
        step_crops[step_index] = state["crop"]
    return True


def clear_undo_stack(step_index):
    undo_stacks.pop(step_index, None)


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
    })
    step_objects[insert_pos] = []

    global step_counter
    step_counter = len(log_data) + 1
    return insert_pos


# ══════════════════════════════════════ PASTE & DROP ══════════════════════════════════════

def _active_insert_pos():
    """Return the insert position after the currently active card, or end."""
    card = active_card_ref[0]
    if card is not None and card.index < len(log_data):
        return card.index + 1
    return len(log_data)


def _handle_paste(event=None):
    """Ctrl+V — create new step(s) from clipboard image or text."""
    focus = root.focus_get()
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


def _compute_drop_index(x_root, y_root, *, allow_after_last=True):
    """Compute card insertion index from screen coordinates.

    allow_after_last=True  → inserting a file drop after the last card is valid.
    allow_after_last=False → clamp to last card index (used for reorder DnD).
    """
    if not step_cards:
        return 0
    if view_mode == "grid":
        best, best_dist = 0, float("inf")
        for i, card in enumerate(step_cards):
            try:
                wx = card.outer.winfo_rootx()
                wy = card.outer.winfo_rooty()
                ww = card.outer.winfo_width()
                wh = card.outer.winfo_height()
                dist = abs(y_root - (wy + wh // 2)) * 2 + abs(x_root - (wx + ww // 2))
                if dist < best_dist:
                    best_dist = dist
                    best = i
            except Exception:
                pass
        return best
    for i, card in enumerate(step_cards):
        try:
            wy = card.outer.winfo_rooty()
            wh = card.outer.winfo_height()
            if y_root < wy + wh // 2:
                return i
        except Exception:
            pass
    return len(step_cards) if allow_after_last else len(step_cards) - 1


def _handle_file_drop(raw_paths, x_root, y_root):
    """Process file paths dropped onto the app."""
    if not current_session:
        _set_status("Start or open a recording to drop into", C["warn"])
        return

    try:
        paths = root.tk.splitlist(raw_paths)
    except Exception:
        paths = raw_paths.split()

    pos   = _compute_drop_index(x_root, y_root, allow_after_last=True)
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

    target_w = right_frame._w

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
        print(f"[PSR] DnD setup failed: {e}")


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
    if card.index < len(log_data) and log_data[card.index]["description"] != new_text:
        log_data[card.index]["description"] = new_text
        save_steps()
        _refresh_sidebar()


# ══════════════════════════════════════ STEP CARD ══════════════════════════════════════

def _delete_step(idx):
    """Confirm and delete the step at idx, then rebuild cards."""
    global _selected
    _selected.clear()
    _selected.add(idx)
    _delete_selected()


def _delete_selected():
    """Confirm and delete all steps in _selected, then rebuild."""
    global _selected
    if not _selected:
        return
    to_delete = set(_selected)
    n_del = len(to_delete)
    if n_del == 1:
        step_num = log_data[next(iter(to_delete))]["step"]
        msg = f"Delete Step {step_num}?"
    else:
        msg = f"Delete {n_del} selected steps?"
    if not messagebox.askyesno("Delete", msg):
        return

    new_log   = []
    new_objs  = {}
    new_crops = {}
    new_idx   = 0
    for old_idx in range(len(log_data)):
        if old_idx in to_delete:
            screenshot = log_data[old_idx].get("screenshot")
            if screenshot:
                img_path = os.path.join(current_session, screenshot)
                if os.path.exists(img_path):
                    try: os.remove(img_path)
                    except Exception: pass
            clear_undo_stack(old_idx)
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
    _renumber_and_rebuild()


def _refresh_card_highlights():
    """Update card border color to reflect current _selected set."""
    for card in step_cards:
        if not hasattr(card, "outer"):
            continue
        try:
            sel = card.index in _selected
            card.outer.configure(
                border_color=C["accent"] if sel else C["border"],
                border_width=2 if sel else 1)
        except Exception:
            pass


def _apply_sidebar_selection():
    """Push _selected → sidebar listbox (without firing <<ListboxSelect>>)."""
    sidebar_list.selection_clear(0, tk.END)
    for i in _selected:
        try: sidebar_list.selection_set(i)
        except Exception: pass


class BaseCard:
    """Shared interface for all card view types."""
    def delete_selected(self): pass
    def reload_image(self):    pass
    def _refresh_undo_btn(self): pass
    def update_header(self):   pass
    def _delete(self):
        _delete_step(self.index)


class StepCard(BaseCard):
    def __init__(self, parent, index):
        self.index        = index
        self.is_text_only = log_data[index].get("screenshot") is None
        self._disp_size   = (CARD_IMG_MAX_W, 100)
        self._orig_size   = (1920, 1080)
        self._crop_region = (0, 0, 1920, 1080)
        self._photo       = None
        self.canvas        = None
        self._folded      = False
        self._fold_btn    = None
        self._hdr         = None   # kept so we can read its actual height when folding

        self._create_start = None
        self._create_rect  = None
        self._draw_pts     = []
        self._last_draw    = None

        self._selected_obj = None
        self._drag_info    = None

        self._build(parent)
        self._loaded = False
        _bind_card_context(self)

    def _toggle_fold(self):
        self._folded = not self._folded
        if self._fold_btn:
            self._fold_btn.configure(text="▸" if self._folded else "▾")
        if self._folded:
            if self.canvas:
                self.canvas.pack_forget()
            self.desc_box.pack_forget()
            # Lock outer to header height so it doesn't stay full-size and block clicks
            self.outer.update_idletasks()
            hdr_h = self._hdr.winfo_height() if self._hdr else 42
            self.outer.configure(height=hdr_h)
            self.outer.pack_propagate(False)
        else:
            # Release height lock before re-packing children
            self.outer.pack_propagate(True)
            self.outer.configure(height=0)
            if self.canvas:
                self.canvas.pack(fill="x")
            self.desc_box.pack(fill="x", padx=12, pady=(8, 10))

    # ── Build ─────────────────────────────────────────────────────────────

    def _build(self, parent):
        self.outer = ctk.CTkFrame(parent, corner_radius=8,
            fg_color=C["card"], border_width=1, border_color=C["border"])
        self.outer.pack(fill="x", pady=(0,14), padx=2)
        self._build_header()
        if not self.is_text_only:
            self._build_canvas()
        self._build_desc()

    def _build_header(self):
        hdr = ctk.CTkFrame(self.outer, height=42, fg_color=C["surface"], corner_radius=0)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        self._hdr = hdr

        # Fold toggle (leftmost)
        self._fold_btn = ctk.CTkButton(hdr, text="▾", command=self._toggle_fold,
            fg_color="transparent", hover_color=C["surface"],
            text_color=C["muted"], width=20, height=28, corner_radius=4,
            font=("Segoe UI", 10), border_width=0)
        self._fold_btn.pack(side="left", padx=(4, 0))

        grip = ctk.CTkLabel(hdr, text="⠿", font=("Segoe UI", 14),
                            text_color=C["muted"], width=22, cursor="fleur")
        grip.pack(side="left", padx=(2,0))
        grip.bind("<ButtonPress-1>",   lambda e: _card_drag_start(self.index, e))
        grip.bind("<B1-Motion>",       _card_drag_motion)
        grip.bind("<ButtonRelease-1>", _card_drag_release)

        entry = log_data[self.index]
        self._num_label = ctk.CTkLabel(
            hdr, text=f"  STEP {entry['step']:02d}",
            font=("Courier New", 11, "bold"), text_color=C["accent"],
            width=80, anchor="w")
        self._num_label.pack(side="left", padx=(2,0))

        if self.is_text_only:
            ctk.CTkLabel(hdr, text="note", font=("Segoe UI", 9),
                         text_color=C["muted"]).pack(side="left", padx=(0,6))

        IB = dict(height=28, width=32, corner_radius=4, font=("Segoe UI", 12), border_width=0)
        ctk.CTkButton(hdr, text="↓", command=self._move_down,
            fg_color="transparent", hover_color=C["acc_dark"],
            text_color=C["muted"], **IB).pack(side="right", padx=(1,6), pady=7)
        ctk.CTkButton(hdr, text="↑", command=self._move_up,
            fg_color="transparent", hover_color=C["acc_dark"],
            text_color=C["muted"], **IB).pack(side="right", padx=1, pady=7)
        ctk.CTkButton(hdr, text="✕", command=self._delete,
            fg_color="transparent", hover_color=C["danger"],
            text_color=C["muted"], **IB).pack(side="right", padx=(1,2), pady=7)

        ctk.CTkLabel(hdr, text="│", text_color=C["border"], width=12).pack(side="right")

        ctk.CTkButton(hdr, text="＋", command=lambda: insert_custom_step(self.index),
            fg_color="transparent", hover_color=C["success"],
            text_color=C["muted"], height=28, width=32,
            corner_radius=4, font=("Segoe UI", 14), border_width=0
        ).pack(side="right", padx=2, pady=7)

        if not self.is_text_only:
            ctk.CTkLabel(hdr, text="│", text_color=C["border"], width=12).pack(side="right")
            self._undo_btn = ctk.CTkButton(
                hdr, text="↩ Undo", command=self._undo,
                fg_color="transparent", hover_color=C["surface"],
                text_color=C["muted"], height=28, width=74,
                corner_radius=4, font=("Segoe UI", 10), border_width=0)
            self._undo_btn.pack(side="right", padx=2, pady=7)
            self._reset_crop_btn = ctk.CTkButton(
                hdr, text="↺ Reset Crop", command=self._reset_crop,
                fg_color="transparent", hover_color=C["surface"],
                text_color=C["muted"], height=28, width=90,
                corner_radius=4, font=("Segoe UI", 10), border_width=0)
            self._reset_crop_btn.pack(side="right", padx=2, pady=7)
            self._refresh_undo_btn()
        else:
            self._undo_btn = None
            self._reset_crop_btn = None

    def _build_canvas(self):
        self.canvas = tk.Canvas(self.outer, bg="#0d0d0d", highlightthickness=0, cursor="arrow")
        self.canvas.pack(fill="x")
        self.canvas.bind("<ButtonPress-1>",   self._on_press)
        self.canvas.bind("<B1-Motion>",       self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<Motion>",          self._on_motion)
        self.canvas.bind("<Button-3>",        self._on_canvas_right_click)
        self.canvas.bind("<Double-Button-1>", self._on_canvas_dblclick)

    def _build_desc(self):
        h = 100 if self.is_text_only else 56
        self.desc_box = ctk.CTkTextbox(
            self.outer, height=h, font=("Segoe UI", 11),
            fg_color=C["surface"], border_width=1, border_color=C["border"],
            corner_radius=6, wrap="word", text_color=C["text"])
        self.desc_box.pack(fill="x", padx=12, pady=(8,10))
        self.desc_box.insert("end", log_data[self.index]["description"])
        _setup_desc_autosave(self)

    # ── Image / Render ────────────────────────────────────────────────────

    def reload_image(self):
        if self.is_text_only or not current_session:
            return
        entry    = log_data[self.index]
        img_path = os.path.join(current_session, entry["screenshot"])
        if not os.path.exists(img_path):
            return
        img = Image.open(img_path).convert("RGB")
        self._orig_size = img.size

        # Apply crop region in memory only
        cx1, cy1, cx2, cy2 = _get_crop(self.index, img.size)
        cx1, cx2 = sorted([cx1, cx2]); cy1, cy2 = sorted([cy1, cy2])
        cx1 = max(0, min(cx1, img.size[0])); cy1 = max(0, min(cy1, img.size[1]))
        cx2 = max(cx1+1, min(cx2, img.size[0])); cy2 = max(cy1+1, min(cy2, img.size[1]))
        self._crop_region = (cx1, cy1, cx2, cy2)

        cropped  = img.crop((cx1, cy1, cx2, cy2))
        try:
            avail_w = self.outer.winfo_width() - 4
        except Exception:
            avail_w = CARD_IMG_MAX_W
        max_w    = max(CARD_IMG_MAX_W, avail_w) if avail_w > 100 else CARD_IMG_MAX_W
        ratio    = min(max_w / cropped.size[0], 1.0)
        dw       = int(cropped.size[0] * ratio)
        dh       = int(cropped.size[1] * ratio)
        self._disp_size = (dw, dh)
        self._photo     = ImageTk.PhotoImage(cropped.resize((dw, dh), Image.LANCZOS))
        self.canvas.configure(width=dw, height=dh)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=self._photo, tags=("bg",))
        self._render_objects()

    def _render_objects(self):
        self.canvas.delete("obj")
        objects = step_objects.get(self.index, [])
        for i, obj in enumerate(objects):
            self._render_one(i, obj)
        if self._selected_obj is not None and self._selected_obj < len(objects):
            self._draw_gizmo(objects[self._selected_obj])

    def _render_one(self, i, obj):
        tag = ("obj", f"obj_{i}")
        if obj["type"] == "highlight":
            x1c, y1c, x2c, y2c = self._img_bbox_to_canvas(_obj_bbox_img(obj))
            self.canvas.create_rectangle(x1c, y1c, x2c, y2c,
                outline=obj["color"], width=3, fill="", tags=tag)
            self.canvas.create_rectangle(x1c+2, y1c+2, x2c-2, y2c-2,
                outline="", fill=obj["color"], stipple="gray12", tags=tag)
        elif obj["type"] == "redact":
            x1c, y1c, x2c, y2c = self._img_bbox_to_canvas(_obj_bbox_img(obj))
            self.canvas.create_rectangle(x1c, y1c, x2c, y2c,
                outline="#555555", width=1, fill="#0a0a0a", tags=tag)
        elif obj["type"] == "draw":
            if not obj["points"]:
                return
            dw, _  = self._disp_size
            cx1, cy1, cx2, cy2 = self._crop_region
            crop_w = cx2 - cx1
            scale  = dw / crop_w
            pts_c  = [(int((p[0]-cx1)*scale), int((p[1]-cy1)*scale))
                      for p in obj["points"]]
            wc = max(1, int(obj["width"] * scale))
            if len(pts_c) >= 2:
                flat = [c for pt in pts_c for c in pt]
                self.canvas.create_line(*flat, fill=obj["color"], width=wc,
                    capstyle=tk.ROUND, smooth=True, joinstyle=tk.ROUND, tags=tag)
            r = max(1, wc//2)
            self.canvas.create_oval(
                pts_c[0][0]-r, pts_c[0][1]-r,
                pts_c[0][0]+r, pts_c[0][1]+r,
                fill=obj["color"], outline="", tags=tag)

    def _draw_gizmo(self, obj):
        bx1, by1, bx2, by2 = self._img_bbox_to_canvas(_obj_bbox_img(obj))
        self.canvas.create_rectangle(bx1-2, by1-2, bx2+2, by2+2,
            outline="#ffffff", width=1, dash=(5,3), tags=("obj","gizmo"))
        mx = (bx1+bx2)/2; my = (by1+by2)/2
        positions = [
            (bx1,by1),(mx,by1),(bx2,by1),
            (bx1,my),          (bx2,my),
            (bx1,by2),(mx,by2),(bx2,by2),
        ]
        for hx, hy in positions:
            s = HANDLE_SZ
            self.canvas.create_rectangle(hx-s, hy-s, hx+s, hy+s,
                fill="#ffffff", outline="#111111", width=1,
                tags=("obj","gizmo","handle"))

    # ── Coordinate helpers (crop-aware) ───────────────────────────────────

    def _canvas_to_img(self, cx, cy):
        """Canvas pixel -> original image pixel, accounting for crop offset."""
        dw, dh = self._disp_size
        rx1, ry1, rx2, ry2 = self._crop_region
        cw = rx2 - rx1; ch = ry2 - ry1
        return max(0, int(rx1 + cx * cw / dw)), max(0, int(ry1 + cy * ch / dh))

    def _img_to_canvas(self, ix, iy):
        """Original image pixel -> canvas pixel, accounting for crop offset."""
        dw, dh = self._disp_size
        rx1, ry1, rx2, ry2 = self._crop_region
        cw = rx2 - rx1; ch = ry2 - ry1
        return int((ix - rx1) * dw / cw), int((iy - ry1) * dh / ch)

    def _img_bbox_to_canvas(self, bbox):
        x1, y1, x2, y2 = bbox
        return (*self._img_to_canvas(x1, y1), *self._img_to_canvas(x2, y2))

    # ── Hit testing ───────────────────────────────────────────────────────

    def _handle_at(self, cx, cy):
        if self._selected_obj is None:
            return None
        objects = step_objects.get(self.index, [])
        if self._selected_obj >= len(objects):
            return None
        bx1, by1, bx2, by2 = self._img_bbox_to_canvas(
            _obj_bbox_img(objects[self._selected_obj]))
        mx = (bx1+bx2)/2; my = (by1+by2)/2
        positions = [
            (bx1,by1),(mx,by1),(bx2,by1),
            (bx1,my),          (bx2,my),
            (bx1,by2),(mx,by2),(bx2,by2),
        ]
        for i, (hx, hy) in enumerate(positions):
            if abs(cx-hx) <= HANDLE_HIT and abs(cy-hy) <= HANDLE_HIT:
                return i
        return None

    def _obj_at(self, cx, cy):
        ix, iy  = self._canvas_to_img(cx, cy)
        objects = step_objects.get(self.index, [])
        PAD     = 6
        for i in range(len(objects)-1, -1, -1):
            x1, y1, x2, y2 = _obj_bbox_img(objects[i])
            if (x1-PAD)<=ix<=(x2+PAD) and (y1-PAD)<=iy<=(y2+PAD):
                return i
        return None

    # ── Mouse events ──────────────────────────────────────────────────────

    def _on_press(self, event):
        active_card_ref[0] = self

        if annotation_tool == "none":
            handle = self._handle_at(event.x, event.y)
            if handle is not None:
                objects = step_objects.get(self.index, [])
                obj     = objects[self._selected_obj]
                push_undo(self.index)
                self._drag_info = {
                    "type": "handle", "handle": handle,
                    "start_canvas": (event.x, event.y),
                    "obj_snapshot": copy.deepcopy(obj),
                    "bbox_start":   _obj_bbox_img(obj),
                }
                return
            hit = self._obj_at(event.x, event.y)
            if hit is not None:
                self._selected_obj = hit
                objects = step_objects.get(self.index, [])
                push_undo(self.index)
                self._drag_info = {
                    "type": "move",
                    "start_canvas": (event.x, event.y),
                    "start_img":    self._canvas_to_img(event.x, event.y),
                    "obj_snapshot": copy.deepcopy(objects[hit]),
                }
                self._render_objects()
                self._update_color_swatches_for_selection()
                return
            self._selected_obj = None
            self._drag_info    = None
            self._render_objects()
            return

        self._selected_obj = None

        if annotation_tool == "draw":
            push_undo(self.index)
            self._draw_pts  = [(event.x, event.y)]
            self._last_draw = (event.x, event.y)
            return

        self._create_start = (event.x, event.y)
        if annotation_tool == "highlight":
            kw = dict(outline=draw_color, width=3, fill="")
        elif annotation_tool == "redact":
            kw = dict(outline="#555", width=1, fill="#0a0a0a", stipple="gray50")
        else:  # crop
            kw = dict(outline=C["crop_col"], width=2, fill="", dash=(8,4))
        self._create_rect = self.canvas.create_rectangle(
            event.x, event.y, event.x, event.y, **kw, tags=("obj",))
        if annotation_tool in ("highlight", "redact"):
            push_undo(self.index)

    def _on_drag(self, event):
        if annotation_tool == "draw" and self._last_draw:
            dw, _ = self._disp_size
            ow, _ = self._orig_size
            wc    = max(1, int(draw_width * dw / ow))
            self.canvas.create_line(
                self._last_draw[0], self._last_draw[1], event.x, event.y,
                fill=draw_color, width=wc, capstyle=tk.ROUND, smooth=True, tags=("obj",))
            self._draw_pts.append((event.x, event.y))
            self._last_draw = (event.x, event.y)
            return

        if self._create_rect and self._create_start:
            self.canvas.coords(self._create_rect,
                self._create_start[0], self._create_start[1], event.x, event.y)
            return

        if not self._drag_info:
            return
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return
        obj  = objects[self._selected_obj]

        if self._drag_info["type"] == "move":
            sx, sy = self._drag_info["start_img"]
            cx, cy = self._canvas_to_img(event.x, event.y)
            dx = cx-sx; dy = cy-sy
            snap = self._drag_info["obj_snapshot"]
            if obj["type"] in ("highlight", "redact"):
                obj["x1"]=snap["x1"]+dx; obj["y1"]=snap["y1"]+dy
                obj["x2"]=snap["x2"]+dx; obj["y2"]=snap["y2"]+dy
            elif obj["type"] == "draw":
                obj["points"] = [[p[0]+dx, p[1]+dy] for p in snap["points"]]

        elif self._drag_info["type"] == "handle":
            sx, sy = self._canvas_to_img(*self._drag_info["start_canvas"])
            cx, cy = self._canvas_to_img(event.x, event.y)
            dx = cx-sx; dy = cy-sy
            x1f, y1f, x2f, y2f = _HANDLE_FX[self._drag_info["handle"]]
            snap = self._drag_info["obj_snapshot"]
            if obj["type"] in ("highlight", "redact"):
                obj["x1"]=snap["x1"]+dx*x1f; obj["y1"]=snap["y1"]+dy*y1f
                obj["x2"]=snap["x2"]+dx*x2f; obj["y2"]=snap["y2"]+dy*y2f
            elif obj["type"] == "draw":
                bx1,by1,bx2,by2 = self._drag_info["bbox_start"]
                nx1=bx1+dx*x1f; ny1=by1+dy*y1f
                nx2=bx2+dx*x2f; ny2=by2+dy*y2f
                if nx2<nx1+5: nx2=nx1+5
                if ny2<ny1+5: ny2=ny1+5
                ow=(bx2-bx1) or 1; oh=(by2-by1) or 1
                obj["points"] = [
                    [nx1+(p[0]-bx1)*(nx2-nx1)/ow, ny1+(p[1]-by1)*(ny2-ny1)/oh]
                    for p in snap["points"]
                ]
        self._render_objects()

    def _on_release(self, event):
        # Finalize draw stroke
        if annotation_tool == "draw":
            if not self._draw_pts:
                return
            img_pts = [list(self._canvas_to_img(cx, cy)) for cx, cy in self._draw_pts]
            step_objects.setdefault(self.index, []).append(
                {"type": "draw", "color": draw_color, "width": draw_width, "points": img_pts})
            self._draw_pts  = []
            self._last_draw = None
            save_steps()
            self.reload_image()
            self._refresh_undo_btn()
            return

        # Non-destructive crop
        if annotation_tool == "crop" and self._create_start:
            x1, y1 = self._create_start
            x2, y2 = event.x, event.y
            self._create_rect  = None
            self._create_start = None
            ix1,iy1 = self._canvas_to_img(x1, y1)
            ix2,iy2 = self._canvas_to_img(x2, y2)
            ix1,ix2 = sorted([ix1,ix2]); iy1,iy2 = sorted([iy1,iy2])
            if ix2-ix1 > 10 and iy2-iy1 > 10:
                push_undo(self.index)
                step_crops[self.index] = {"x1": ix1, "y1": iy1, "x2": ix2, "y2": iy2}
                save_steps()
                self.reload_image()
                self._refresh_undo_btn()
            else:
                self.reload_image()
            return

        # Rect annotations
        if annotation_tool in ("highlight", "redact") and self._create_start:
            x1,y1 = self._create_start
            x2,y2 = event.x, event.y
            self._create_rect  = None
            self._create_start = None
            ix1,iy1 = self._canvas_to_img(x1,y1)
            ix2,iy2 = self._canvas_to_img(x2,y2)
            if abs(ix2-ix1)>4 and abs(iy2-iy1)>4:
                step_objects.setdefault(self.index, []).append({
                    "type": annotation_tool, "color": draw_color, "width": 3,
                    "x1": min(ix1,ix2), "y1": min(iy1,iy2),
                    "x2": max(ix1,ix2), "y2": max(iy1,iy2)
                })
            save_steps()
            self.reload_image()
            self._refresh_undo_btn()
            return

        # Finalize transform
        if self._drag_info:
            self._drag_info = None
            save_steps()
            self._render_objects()
            self._refresh_undo_btn()

    def _on_motion(self, event):
        if annotation_tool != "none":
            return
        if self._handle_at(event.x, event.y) is not None:
            self.canvas.configure(cursor="sizing")
        elif self._obj_at(event.x, event.y) is not None:
            self.canvas.configure(cursor="fleur")
        else:
            self.canvas.configure(cursor="arrow")

    # ── Right-click context menu on canvas objects ───────────────────────

    def _on_canvas_right_click(self, event):
        hit = self._obj_at(event.x, event.y)
        if hit is not None:
            self._selected_obj = hit
            self._render_objects()
            self._update_color_swatches_for_selection()
        menu = tk.Menu(self.canvas, tearoff=0, bg=C["surface"], fg=C["text"],
                       activebackground=C["accent"], activeforeground="#fff",
                       font=("Segoe UI", 10))
        if self._selected_obj is not None:
            objects = step_objects.get(self.index, [])
            if self._selected_obj < len(objects):
                obj = objects[self._selected_obj]
                label = obj["type"].capitalize()
                menu.add_command(label=f"Delete {label}  [Del]", command=self.delete_selected)
                if obj["type"] != "redact":
                    color_sub = tk.Menu(menu, tearoff=0, bg=C["surface"], fg=C["text"],
                        activebackground=C["accent"], activeforeground="#fff",
                        font=("Segoe UI", 10))
                    for hex_col, col_lbl in _SWATCHES:
                        color_sub.add_command(label=f"● {col_lbl}",
                            foreground=hex_col,
                            command=lambda c=hex_col: self.apply_color_to_selection(c))
                    menu.add_cascade(label="Colour", menu=color_sub)
                menu.add_separator()
        menu.add_command(label="Full view", command=lambda: self._show_fullscreen())
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    # ── Double-click for fullscreen image view ─────────────────────────

    def _on_canvas_dblclick(self, event):
        if annotation_tool != "none":
            return
        self._show_fullscreen()

    def _show_fullscreen(self):
        """Open a maximized top-level window showing the full annotated image."""
        flat = _flatten_to_pil(self.index)
        if flat is None:
            return
        win = tk.Toplevel(root)
        win.title(f"Step {log_data[self.index]['step']:02d} — Full View")
        win.configure(bg="#111111")
        win.attributes("-topmost", True)
        win.state("zoomed")

        sw = win.winfo_screenwidth()
        sh = win.winfo_screenheight()
        ratio = min(sw / flat.width, sh / flat.height, 1.0)
        dw = int(flat.width * ratio)
        dh = int(flat.height * ratio)
        resized = flat.resize((dw, dh), Image.LANCZOS)
        photo = ImageTk.PhotoImage(resized)

        canvas = tk.Canvas(win, bg="#111111", highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        canvas.create_image(sw // 2, sh // 2, anchor="center", image=photo)
        canvas._photo_ref = photo  # prevent GC

        win.bind("<Escape>", lambda e: win.destroy())
        win.bind("<Button-1>", lambda e: win.destroy())
        win.focus_set()

    # ── Selection helpers ─────────────────────────────────────────────────

    def _update_color_swatches_for_selection(self):
        if self._selected_obj is None:
            return
        objects = step_objects.get(self.index, [])
        if self._selected_obj >= len(objects):
            return
        col = objects[self._selected_obj].get("color", draw_color)
        _sync_color_swatches(col)
        _set_status("Object selected — click a colour swatch to repaint it", C["accent"])

    def apply_color_to_selection(self, hex_color):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return False
        push_undo(self.index)
        objects[self._selected_obj]["color"] = hex_color
        save_steps()
        self._render_objects()
        self._refresh_undo_btn()
        return True

    def delete_selected(self):
        objects = step_objects.get(self.index, [])
        if self._selected_obj is None or self._selected_obj >= len(objects):
            return
        push_undo(self.index)
        del objects[self._selected_obj]
        self._selected_obj = None
        self._drag_info    = None
        save_steps()
        self._render_objects()
        self._refresh_undo_btn()
        _set_status("Object deleted", C["muted"])

    # ── Card actions ──────────────────────────────────────────────────────

    def _undo(self):
        if pop_undo(self.index):
            self._selected_obj = None
            self._drag_info    = None
            save_steps()
            self.reload_image()
            self._refresh_undo_btn()
            _set_status("↩  Undo applied", C["warn"])
        else:
            _set_status("Nothing to undo for this step", C["muted"])

    def _reset_crop(self):
        if self.index not in step_crops:
            _set_status("No crop to reset on this step", C["muted"])
            return
        push_undo(self.index)
        step_crops.pop(self.index, None)
        save_steps()
        self.reload_image()
        self._refresh_undo_btn()
        _set_status("↺  Crop reset to original", C["success"])

    def _move_up(self):
        if self.index > 0:
            _swap_steps(self.index, self.index - 1)

    def _move_down(self):
        if self.index < len(log_data) - 1:
            _swap_steps(self.index, self.index + 1)

    # ── Helpers ───────────────────────────────────────────────────────────

    def _refresh_undo_btn(self):
        if self._undo_btn is None:
            return
        has = bool(undo_stacks.get(self.index))
        self._undo_btn.configure(
            text_color=C["text"] if has else C["muted"],
            state="normal" if has else "disabled")
        if self._reset_crop_btn is not None:
            has_crop = self.index in step_crops
            self._reset_crop_btn.configure(
                text_color=C["text"] if has_crop else C["muted"],
                state="normal" if has_crop else "disabled")

    def update_header(self):
        entry = log_data[self.index]
        self._num_label.configure(text=f"  STEP {entry['step']:02d}")
        self.desc_box.delete("1.0", "end")
        self.desc_box.insert("end", entry["description"])
        self._refresh_undo_btn()


# ══════════════════════════════════════ LIST CARD ══════════════════════════════════════

LIST_THUMB_W = 180


class ListCard(BaseCard):
    """Compact row: small thumbnail on the left, description on the right."""

    def __init__(self, parent, index):
        self.index        = index
        self.is_text_only = log_data[index].get("screenshot") is None
        self.canvas        = None
        self._photo       = None
        self._selected_obj = None
        self._undo_btn     = None
        self._reset_crop_btn = None

        self.outer = ctk.CTkFrame(parent, corner_radius=6,
            fg_color=C["card"], border_width=1, border_color=C["border"], height=80)
        self.outer.pack(fill="x", pady=(0,6), padx=2)
        self.outer.pack_propagate(False)

        grip = ctk.CTkLabel(self.outer, text="⠿", font=("Segoe UI", 12),
                            text_color=C["muted"], width=18, cursor="fleur")
        grip.pack(side="left", padx=(4,0))
        grip.bind("<ButtonPress-1>",   lambda e: _card_drag_start(self.index, e))
        grip.bind("<B1-Motion>",       _card_drag_motion)
        grip.bind("<ButtonRelease-1>", _card_drag_release)

        entry = log_data[index]
        self._num_label = ctk.CTkLabel(self.outer,
            text=f"{entry['step']:02d}", font=("Courier New", 10, "bold"),
            text_color=C["accent"], width=26)
        self._num_label.pack(side="left", padx=(2,4))

        if not self.is_text_only:
            self._thumb_label = ctk.CTkLabel(self.outer, text="",
                width=LIST_THUMB_W, height=68, corner_radius=4, fg_color="#0d0d0d")
            self._thumb_label.pack(side="left", padx=(0,8), pady=6)
            self._load_thumb()
        else:
            ctk.CTkLabel(self.outer, text="[note]", font=("Segoe UI", 9),
                         text_color=C["muted"], width=LIST_THUMB_W
                         ).pack(side="left", padx=(0,8))

        IB = dict(height=24, width=26, corner_radius=4, font=("Segoe UI", 10), border_width=0)
        ctk.CTkButton(self.outer, text="✕", command=self._delete,
            fg_color="transparent", hover_color=C["danger"],
            text_color=C["muted"], **IB).pack(side="right", padx=(0,6), pady=4)

        self.desc_box = ctk.CTkTextbox(
            self.outer, height=54, font=("Segoe UI", 10),
            fg_color=C["surface"], border_width=1, border_color=C["border"],
            corner_radius=4, wrap="word", text_color=C["text"])
        self.desc_box.pack(side="left", fill="both", expand=True, padx=(0,6), pady=6)
        self.desc_box.insert("end", entry["description"])
        _setup_desc_autosave(self)
        _bind_card_context(self)

    def _load_thumb(self):
        if not current_session:
            return
        entry = log_data[self.index]
        if entry.get("screenshot") is None:
            return
        img_path = os.path.join(current_session, entry["screenshot"])
        if not os.path.exists(img_path):
            return
        img = Image.open(img_path).convert("RGB")
        img.thumbnail((LIST_THUMB_W, 68), Image.BILINEAR)
        self._photo = ImageTk.PhotoImage(img)
        self._thumb_label.configure(image=self._photo)


# ══════════════════════════════════════ GRID CARD ══════════════════════════════════════

GRID_TILE_W = 260


class GridCard(BaseCard):
    """Square-ish tile for grid layout."""

    def __init__(self, parent, index):
        self.index        = index
        self.is_text_only = log_data[index].get("screenshot") is None
        self.canvas        = None
        self._photo       = None
        self._selected_obj = None
        self._undo_btn     = None
        self._reset_crop_btn = None

        self.outer = ctk.CTkFrame(parent, corner_radius=6,
            fg_color=C["card"], border_width=1, border_color=C["border"],
            width=GRID_TILE_W)

        entry = log_data[index]

        hdr = ctk.CTkFrame(self.outer, height=28, fg_color=C["surface"], corner_radius=0)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)

        grip = ctk.CTkLabel(hdr, text="⠿", font=("Segoe UI", 11),
                            text_color=C["muted"], width=18, cursor="fleur")
        grip.pack(side="left", padx=(4,0))
        grip.bind("<ButtonPress-1>",   lambda e: _card_drag_start(self.index, e))
        grip.bind("<B1-Motion>",       _card_drag_motion)
        grip.bind("<ButtonRelease-1>", _card_drag_release)

        self._num_label = ctk.CTkLabel(hdr,
            text=f"STEP {entry['step']:02d}", font=("Courier New", 9, "bold"),
            text_color=C["accent"])
        self._num_label.pack(side="left", padx=4)

        ctk.CTkButton(hdr, text="✕", command=self._delete,
            fg_color="transparent", hover_color=C["danger"],
            text_color=C["muted"], height=22, width=22, corner_radius=4,
            font=("Segoe UI", 10), border_width=0).pack(side="right", padx=4)

        if not self.is_text_only:
            self._thumb_label = ctk.CTkLabel(self.outer, text="",
                width=GRID_TILE_W-4, height=150, corner_radius=0, fg_color="#0d0d0d")
            self._thumb_label.pack(padx=2, pady=(2,0))
            self._load_thumb()

        self.desc_box = ctk.CTkTextbox(
            self.outer, height=48, font=("Segoe UI", 9),
            fg_color=C["surface"], border_width=1, border_color=C["border"],
            corner_radius=4, wrap="word", text_color=C["text"])
        self.desc_box.pack(fill="x", padx=6, pady=(4,6))
        self.desc_box.insert("end", entry["description"])
        _setup_desc_autosave(self)
        _bind_card_context(self)

    def _load_thumb(self):
        if not current_session:
            return
        entry = log_data[self.index]
        if entry.get("screenshot") is None:
            return
        img_path = os.path.join(current_session, entry["screenshot"])
        if not os.path.exists(img_path):
            return
        img = Image.open(img_path).convert("RGB")
        img.thumbnail((GRID_TILE_W-4, 150), Image.BILINEAR)
        self._photo = ImageTk.PhotoImage(img)
        self._thumb_label.configure(image=self._photo)


# ══════════════════════════════════════ CARD MANAGEMENT ══════════════════════════════════════

def _clear_cards():
    _card_drag_cleanup()
    active_card_ref[0] = None
    for card in step_cards:
        try: card.outer.destroy()
        except Exception: pass
    step_cards.clear()
    for child in list(cards_scroll.winfo_children()):
        try: child.destroy()
        except Exception: pass


def _refresh_ui_state():
    """Enable/disable controls based on session and step availability."""
    has_steps   = bool(log_data)
    has_session = bool(current_session)
    s = "normal" if has_steps else "disabled"
    _btn_html.configure(state=s)
    _btn_pdf.configure(state=s)
    # Tools are enabled only in edit mode AND when steps exist
    _set_tool_strip_enabled(has_steps and view_mode == "default")
    _btn_step.configure(state="normal" if has_session else "disabled")
    if not recording:
        btn_continue.configure(state="normal" if has_session else "disabled")


def _build_all_cards():
    _clear_cards()
    if not log_data:
        # Empty state — centred hint inside the scroll area
        _ph = ctk.CTkFrame(cards_scroll, fg_color="transparent")
        _ph.pack(fill="both", expand=True)
        _ph.pack_propagate(False)
        _empty_hint = ("No steps yet.\n\n"
            "⏩  Continue to resume recording into this session\n"
            "＋  Step to add a blank step manually\n"
            "or drop images directly into this area.")
        ctk.CTkLabel(_ph, text=_empty_hint,
            font=("Segoe UI", 11), text_color=C["muted"], justify="center",
        ).place(relx=0.5, rely=0.4, anchor="center")
    elif view_mode == "grid":
        _grid_frame = ctk.CTkFrame(cards_scroll, fg_color="transparent")
        _grid_frame.pack(fill="x", anchor="nw")
        cols = max(1, (cards_scroll._parent_canvas.winfo_width() - 20) // (GRID_TILE_W + 12))
        for i in range(len(log_data)):
            card = GridCard(_grid_frame, i)
            r, c = divmod(i, cols)
            card.outer.grid(row=r, column=c, padx=6, pady=6, sticky="n")
            step_cards.append(card)
    elif view_mode == "list":
        for i in range(len(log_data)):
            step_cards.append(ListCard(cards_scroll, i))
    else:
        for i in range(len(log_data)):
            step_cards.append(StepCard(cards_scroll, i))
    _refresh_sidebar()
    _refresh_ui_state()
    root.after(30, _reset_cards_scroll)
    root.after(50, _refresh_card_highlights)
    root.after(80, _lazy_load_visible_cards)


def _lazy_load_visible_cards():
    """Load images only for cards currently visible in the scroll viewport."""
    try:
        canvas = cards_scroll._parent_canvas
        cy = canvas.winfo_rooty()
        ch = canvas.winfo_height()
    except Exception:
        return
    for card in step_cards:
        if not isinstance(card, StepCard) or card._loaded or card.is_text_only:
            continue
        try:
            wy = card.outer.winfo_rooty()
            wh = card.outer.winfo_height()
        except Exception:
            continue
        if wy + wh >= cy and wy <= cy + ch:
            card._loaded = True
            card.reload_image()


_lazy_load_timer = [None]

def _on_cards_scroll(*_args):
    """Debounced lazy loading — avoids firing per-pixel during fast scrolls."""
    if _lazy_load_timer[0]:
        root.after_cancel(_lazy_load_timer[0])
    _lazy_load_timer[0] = root.after(100, _lazy_load_visible_cards)


def _reset_cards_scroll():
    """Force the scrollable frame to recalculate its region and scroll to top."""
    try:
        canvas = cards_scroll._parent_canvas
        canvas.update_idletasks()
        # Pin inner frame width to canvas width to suppress horizontal overflow.
        items = canvas.find_all()
        if items:
            canvas.itemconfigure(items[0], width=canvas.winfo_width())
        canvas.configure(scrollregion=canvas.bbox("all"))
        canvas.yview_moveto(0.0)
    except Exception:
        pass


def _append_card():
    i = len(log_data) - 1
    if view_mode == "default":
        step_cards.append(StepCard(cards_scroll, i))
    elif view_mode == "list":
        step_cards.append(ListCard(cards_scroll, i))
    else:
        _build_all_cards()
        return
    _refresh_sidebar()
    root.after(80, lambda: cards_scroll._parent_canvas.yview_moveto(1.0))
    root.after(120, _lazy_load_visible_cards)


def _swap_steps(a, b):
    """Swap two adjacent steps and rebuild."""
    log_data[a], log_data[b] = log_data[b], log_data[a]
    step_objects[a], step_objects[b] = step_objects.get(b, []), step_objects.get(a, [])
    step_crops[a], step_crops[b] = step_crops.get(b), step_crops.get(a)
    _renumber_and_rebuild(scroll_to=min(a, b))


def _renumber_and_rebuild(scroll_to=None):
    for i, s in enumerate(log_data):
        s["step"] = i + 1
    save_steps()
    undo_stacks.clear()
    _build_all_cards()
    if scroll_to is not None:
        root.after(120, lambda: _scroll_to_card(scroll_to))


def _scroll_to_card(index):
    if not step_cards or index >= len(step_cards): return
    cards_scroll._parent_canvas.yview_moveto(index / max(len(step_cards), 1))


def _reorder_step(src, dst):
    """Move step from index src to index dst, updating all data structures."""
    if src == dst or not (0 <= src < len(log_data)) or not (0 <= dst < len(log_data)):
        return
    n = len(log_data)
    entries    = list(log_data)
    objs_list  = [step_objects.get(i, []) for i in range(n)]
    crops_list = [step_crops.get(i) for i in range(n)]

    entry = entries.pop(src)
    obj   = objs_list.pop(src)
    crop  = crops_list.pop(src)

    entries.insert(dst, entry)
    objs_list.insert(dst, obj)
    crops_list.insert(dst, crop)

    log_data.clear()
    log_data.extend(entries)
    step_objects.clear()
    step_crops.clear()
    for i in range(n):
        step_objects[i] = objs_list[i]
        if crops_list[i] is not None:
            step_crops[i] = crops_list[i]
    _renumber_and_rebuild(scroll_to=dst)
    _set_status(f"Moved step to position {dst + 1}", C["accent"])


# ══════════════════════════════════════ SIDEBAR ══════════════════════════════════════

_sidebar_drag = {"active": False, "src": -1, "dst": -1, "line": None, "suppress_sel": False}


def _refresh_sidebar():
    sidebar_list.delete(0, tk.END)
    for entry in log_data:
        desc    = entry["description"]
        is_note = entry.get("screenshot") is None
        if is_note:
            trunc = desc[:30] + "…" if len(desc) > 30 else desc
            label = f"  {entry['step']:>2}. [note] {trunc}"
        elif len(desc) > 36:
            label = f"  {entry['step']:>2}.  {desc[:36]}…"
        else:
            label = f"  {entry['step']:>2}.  {desc}"
        sidebar_list.insert(tk.END, label)
    count_label.configure(text=f"{len(log_data)} step{'s' if len(log_data)!=1 else ''}")


def _sidebar_drop_index(event_y):
    """Compute the insertion index based on cursor y relative to item midpoints."""
    if not log_data:
        return 0
    n = sidebar_list.size()
    for i in range(n):
        bbox = sidebar_list.bbox(i)
        if bbox is None:
            continue
        _, by, _, bh = bbox
        mid = by + bh // 2
        if event_y < mid:
            return i
    return n - 1


def _sidebar_hide_line():
    line = _sidebar_drag.get("line")
    if line:
        line.place_forget()


def _sidebar_show_line(drop_idx):
    """Place a coloured insertion line at the gap above drop_idx."""
    line = _sidebar_drag.get("line")
    if line is None or not line.winfo_exists():
        line = tk.Frame(sidebar_list, height=2, bg=C["accent"])
        _sidebar_drag["line"] = line
    bbox = sidebar_list.bbox(drop_idx)
    if bbox is None:
        line.place_forget()
        return
    _, by, bw, _ = bbox
    line.place(x=4, y=by - 1, width=bw - 8, height=2)
    line.lift()


def _sidebar_press(event):
    global _sel_anchor
    if not log_data:
        return
    idx = sidebar_list.nearest(event.y)
    if idx < 0 or idx >= len(log_data):
        return
    ctrl  = (event.state & 0x0004) != 0
    shift = (event.state & 0x0001) != 0
    if ctrl:
        _sel_anchor = idx
    elif not shift:
        # Plain click — start potential drag
        _sel_anchor = idx
        _sidebar_drag["src"]    = idx
        _sidebar_drag["dst"]    = idx
        _sidebar_drag["active"] = False
        _scroll_to_card(idx)
    # Selection is handled by EXTENDED mode; <<ListboxSelect>> syncs _selected


def _on_sidebar_sel_change(event):
    """Sync sidebar listbox selection → _selected, then refresh card highlights."""
    if _sidebar_drag.get("suppress_sel"):
        return
    _selected.clear()
    for i in sidebar_list.curselection():
        _selected.add(i)
    _refresh_card_highlights()


def _sidebar_motion(event):
    src = _sidebar_drag["src"]
    if src < 0 or not log_data:
        return
    _sidebar_drag["active"]       = True
    _sidebar_drag["suppress_sel"] = True
    dst = _sidebar_drop_index(event.y)
    _sidebar_drag["dst"] = dst
    sidebar_list.selection_clear(0, tk.END)
    sidebar_list.selection_set(src)
    for i in range(sidebar_list.size()):
        fg = C["muted"] if i == src else C["text"]
        sidebar_list.itemconfigure(i, fg=fg)
    _sidebar_show_line(dst)


def _sidebar_release(event):
    was_drag = _sidebar_drag["active"]
    src      = _sidebar_drag["src"]
    dst      = _sidebar_drag["dst"]
    _sidebar_drag["active"]       = False
    _sidebar_drag["suppress_sel"] = False
    _sidebar_drag["src"]          = -1
    _sidebar_drag["dst"]          = -1
    _sidebar_hide_line()
    for i in range(sidebar_list.size()):
        sidebar_list.itemconfigure(i, fg=C["text"])
    if not was_drag or src < 0 or not log_data:
        return
    dst = max(0, min(dst, len(log_data) - 1))
    if src != dst:
        _reorder_step(src, dst)


def _sidebar_context(event):
    if log_data:
        idx = sidebar_list.nearest(event.y)
        idx = max(0, min(idx, len(log_data) - 1))
        # If right-click lands outside current selection, select just that item
        if idx not in _selected:
            _selected.clear()
            _selected.add(idx)
            sidebar_list.selection_clear(0, tk.END)
            sidebar_list.selection_set(idx)
            _refresh_card_highlights()
    _show_steps_context_menu(event)


# ══════════════════════════════════════ CONTEXT MENU (shared) ══════════════════════════════

def _show_steps_context_menu(event):
    """Context menu used by both the sidebar and card right-click."""
    _MK = dict(bg=C["surface"], fg=C["text"],
               activebackground=C["acc_dark"], activeforeground="#fff",
               font=("Segoe UI", 10), borderwidth=1, relief="solid")
    menu = tk.Menu(root, tearoff=0, **_MK)

    n_sel = len(_selected)

    if not log_data:
        menu.add_command(label="Insert step", command=lambda: insert_custom_step())
    elif n_sel > 1:
        menu.add_command(
            label=f"Delete {n_sel} steps",
            foreground=C["danger"], activeforeground=C["danger"],
            command=_delete_selected)
    else:
        # 0 or 1 item selected — show insert + optional delete
        idx = next(iter(_selected)) if n_sel == 1 else (
            max(0, min(sidebar_list.nearest(event.y_root - sidebar_list.winfo_rooty()),
                       len(log_data) - 1)) if log_data else 0)
        if n_sel == 1:
            menu.add_command(
                label=f"Delete Step {log_data[idx]['step']}",
                foreground=C["danger"], activeforeground=C["danger"],
                command=_delete_selected)
            menu.add_separator()
        menu.add_command(label="Insert step above",
                         command=lambda i=idx: insert_custom_step(after_index=i - 1 if i > 0 else -1))
        menu.add_command(label="Insert step below",
                         command=lambda i=idx: insert_custom_step(after_index=i))

    menu.post(event.x_root, event.y_root)


def _bind_card_context(card):
    """Bind right-click context menu + Ctrl/Shift click selection to a card."""
    def _on_right(event):
        # If right-clicked card is not in selection, replace selection with it
        if card.index not in _selected:
            _selected.clear()
            _selected.add(card.index)
            _apply_sidebar_selection()
            _refresh_card_highlights()
        _show_steps_context_menu(event)

    def _on_left(event):
        global _sel_anchor
        idx   = card.index
        ctrl  = (event.state & 0x0004) != 0
        shift = (event.state & 0x0001) != 0
        if shift and _sel_anchor >= 0:
            lo, hi = sorted([_sel_anchor, idx])
            _selected.clear()
            for i in range(lo, hi + 1):
                _selected.add(i)
        elif ctrl:
            if idx in _selected:
                _selected.discard(idx)
            else:
                _selected.add(idx)
            _sel_anchor = idx
        else:
            _selected.clear()
            _selected.add(idx)
            _sel_anchor = idx
        _apply_sidebar_selection()
        _refresh_card_highlights()

    # Double-click on overview cards → open in detail view
    if isinstance(card, (ListCard, GridCard)):
        def _on_dbl(event, _idx=card.index):
            _open_in_detail(_idx)
        def _bind_dbl(widget):
            if not isinstance(widget, (tk.Text, ctk.CTkEntry, ctk.CTkButton,
                                        tk.Button, ctk.CTkCheckBox)):
                try: widget.bind("<Double-Button-1>", _on_dbl)
                except Exception: pass
            for child in widget.winfo_children():
                _bind_dbl(child)
        _bind_dbl(card.outer)

    def _bind_recursive(widget):
        # Skip tk.Canvas — it has its own annotation-aware right-click handler
        if isinstance(widget, tk.Canvas):
            return
        try: widget.bind("<Button-3>", _on_right)
        except Exception: pass
        if not isinstance(widget, (tk.Text, ctk.CTkEntry, ctk.CTkButton,
                                    tk.Button, ctk.CTkCheckBox)):
            try: widget.bind("<ButtonPress-1>", _on_left, add="+")
            except Exception: pass
        for child in widget.winfo_children():
            _bind_recursive(child)

    _bind_recursive(card.outer)


# ══════════════════════════════════════ CARD DND ══════════════════════════════════════

_card_drag = {"active": False, "src": -1, "ghost": None, "line": None, "dst": -1, "hi_card": -1}

_DROP_LINE_H  = 3
_GHOST_ALPHA  = 0.88
_AUTO_SCROLL  = 40


def _card_drag_cleanup():
    """Destroy ghost/line widgets and reset all DnD state — safe to call anytime."""
    ghost = _card_drag.pop("ghost", None)
    if ghost:
        try: ghost.destroy()
        except Exception: pass
    _card_drag["ghost"] = None

    line = _card_drag.pop("line", None)
    if line:
        try: line.destroy()
        except Exception: pass
    _card_drag["line"] = None

    hi = _card_drag.get("hi_card", -1)
    if 0 <= hi < len(step_cards):
        try: step_cards[hi].outer.configure(border_color=C["border"])
        except Exception: pass
    _card_drag["hi_card"] = -1

    src = _card_drag.get("src", -1)
    if 0 <= src < len(step_cards):
        try: step_cards[src].outer.configure(fg_color=C["card"], border_color=C["border"])
        except Exception: pass

    _card_drag["active"] = False
    _card_drag["src"]    = -1
    _card_drag["dst"]    = -1


def _card_drag_start(index, event):
    _card_drag["src"]    = index
    _card_drag["active"] = False


def _card_show_drop_line(dst):
    """Show drop feedback: horizontal line for list/default, border highlight for grid."""
    if not step_cards:
        return

    if view_mode == "grid":
        prev_hi = _card_drag.get("hi_card", -1)
        if prev_hi != dst and 0 <= prev_hi < len(step_cards):
            try: step_cards[prev_hi].outer.configure(border_color=C["border"])
            except Exception: pass
        _card_drag["hi_card"] = dst
        if 0 <= dst < len(step_cards):
            try: step_cards[dst].outer.configure(border_color=C["accent"])
            except Exception: pass
        return

    line = _card_drag.get("line")
    if line is None or not line.winfo_exists():
        line = tk.Frame(cards_scroll, height=_DROP_LINE_H, bg=C["accent"])
        _card_drag["line"] = line

    target = step_cards[min(dst, len(step_cards) - 1)]
    try:
        target.outer.update_idletasks()
        ty = target.outer.winfo_y()
        tw = target.outer.winfo_width()
        if dst >= len(step_cards):
            ty = target.outer.winfo_y() + target.outer.winfo_height() + 4
        line.place(in_=cards_scroll, x=6, y=ty - 4, width=tw - 12, height=_DROP_LINE_H)
        line.lift()
    except Exception:
        line.place_forget()


def _card_auto_scroll(y_root):
    """Auto-scroll the cards panel when dragging near the edges."""
    try:
        canvas = cards_scroll._parent_canvas
        cy     = canvas.winfo_rooty()
        ch     = canvas.winfo_height()
        if y_root < cy + _AUTO_SCROLL:
            canvas.yview_scroll(-3, "units")
        elif y_root > cy + ch - _AUTO_SCROLL:
            canvas.yview_scroll(3, "units")
    except Exception: pass


def _card_drag_motion(event):
    src = _card_drag["src"]
    if src < 0 or not log_data:
        return
    _card_drag["active"] = True

    ghost = _card_drag.get("ghost")
    if ghost is None:
        ghost = tk.Toplevel(root)
        ghost.overrideredirect(True)
        ghost.attributes("-alpha", _GHOST_ALPHA)
        ghost.configure(bg=C["panel"])
        inner = tk.Frame(ghost, bg=C["panel"], padx=10, pady=6)
        inner.pack()
        tk.Label(inner, text=f"  STEP {src+1:02d}  ",
                 bg=C["accent"], fg="#fff",
                 font=("Courier New", 10, "bold"),
                 padx=6, pady=2).pack(side="left")
        desc = log_data[src]["description"][:40]
        tk.Label(inner, text=f"  {desc}",
                 bg=C["panel"], fg=C["text"],
                 font=("Segoe UI", 9)).pack(side="left", padx=(6,0))
        _card_drag["ghost"] = ghost
        if src < len(step_cards):
            try: step_cards[src].outer.configure(fg_color="#0c0c0c", border_color="#1a1a1a")
            except Exception: pass

    ghost.geometry(f"+{event.x_root + 16}+{event.y_root - 12}")
    ghost.lift()

    dst = _compute_drop_index(event.x_root, event.y_root, allow_after_last=False)
    _card_drag["dst"] = dst
    _card_show_drop_line(dst)
    _card_auto_scroll(event.y_root)


def _card_drag_release(event):
    was_drag = _card_drag["active"]
    src      = _card_drag["src"]
    dst      = _card_drag["dst"]

    _card_drag_cleanup()

    if not was_drag or src < 0 or not log_data:
        return
    dst = max(0, min(dst, len(log_data) - 1))
    if src != dst:
        _reorder_step(src, dst)


# ══════════════════════════════════════ TOOL / COLOUR ══════════════════════════════════════

def set_tool(tool):
    global annotation_tool
    annotation_tool = tool
    for t, btn in (
        ("none",      btn_pointer),
        ("highlight", btn_highlight),
        ("redact",    btn_redact),
        ("crop",      btn_crop),
        ("draw",      btn_draw),
    ):
        active = t == tool
        btn.configure(
            fg_color=C["acc_dark"] if active else "transparent",
            border_color=C["accent"] if active else C["border"])
    cursor = "crosshair" if tool != "none" else "arrow"
    for card in step_cards:
        if card.canvas:
            card.canvas.configure(cursor=cursor)
    # Show colour swatches for draw + highlight; pen sizes only for draw
    if tool in ("draw", "highlight"):
        _draw_sep1.pack(side="left", fill="y", pady=8, padx=6)
        for btn, _ in draw_color_btns:
            btn.pack(side="left", padx=2, pady=12)
        if tool == "draw":
            _draw_sep2.pack(side="left", fill="y", pady=8, padx=6)
            for btn, _ in pen_size_btns:
                btn.pack(side="left", padx=2, pady=9)
        else:
            for btn, _ in pen_size_btns:
                btn.pack_forget()
            _draw_sep2.pack_forget()
    else:
        for btn, _ in draw_color_btns:
            btn.pack_forget()
        for btn, _ in pen_size_btns:
            btn.pack_forget()
        _draw_sep1.pack_forget()
        _draw_sep2.pack_forget()
    hints = {
        "none":      "Pointer — click object to select, drag to move, handles to resize",
        "highlight": "Highlight — drag a coloured box  ·  active colour sets box colour",
        "redact":    "Redact — drag to cover region  ·  baked into image on export",
        "crop":      "Crop — non-destructive, drag again to adjust  ·  ↩ Undo to remove",
        "draw":      "Draw — freehand pen  ·  pick colour & size  ·  ↩ Undo per stroke",
    }
    _set_status(hints[tool], C["muted"])


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
    card = active_card_ref[0]
    if card is not None and card.apply_color_to_selection(hex_color):
        _set_status("Object colour changed", C["success"])
        return
    _set_status("Draw colour set", C["muted"])


def _set_draw_width_global(w):
    global draw_width
    draw_width = w
    for btn, bw in pen_size_btns:
        btn.configure(
            fg_color=C["acc_dark"] if bw==w else "transparent",
            border_color=C["accent"] if bw==w else C["border"])


# ══════════════════════════════════════ VIEW MODE ══════════════════════════════════════

view_mode_btns = []


def _open_in_detail(idx):
    """Double-click from overview → jump to detail view, remember source for back button."""
    global _prev_view_mode
    _prev_view_mode = view_mode
    _set_view_mode("default")
    root.after(160, lambda: _scroll_to_card(idx))


def _set_tool_strip_enabled(enabled):
    """Grey out / restore all tool strip interactive widgets."""
    s = "normal" if enabled else "disabled"
    for btn in (btn_pointer, btn_highlight, btn_redact, btn_crop, btn_draw):
        btn.configure(state=s)
    for btn, _ in draw_color_btns:
        btn.configure(state=s)
    for btn, _ in pen_size_btns:
        btn.configure(state=s)


def _set_view_mode(mode):
    global view_mode, _prev_view_mode
    # Capture previous mode before overwriting — so clicking ✎ Edit from list/grid
    # always shows the ← Back button, regardless of how we got here.
    if mode == "default" and view_mode in ("list", "grid"):
        _prev_view_mode = view_mode
    view_mode = mode
    # Update view tab highlight states
    for btn, m in view_mode_btns:
        active = (m == mode)
        btn.configure(
            fg_color=C["acc_dark"] if active else "transparent",
            border_color=C["accent"] if active else C["border"])
    if mode == "default":
        # Edit mode: enable tools, hide the Edit tab (already here),
        # always show ← Back so the user can reach the overview.
        _set_tool_strip_enabled(bool(log_data))
        for btn, m in view_mode_btns:
            if m == "default":
                btn.pack_forget()   # hide only the Edit tab
            else:
                btn.pack_forget()   # also hide List/Grid tabs — overview via Back only
        # Always show Back in edit mode; label reflects where it will go.
        dest = _prev_view_mode or "list"
        btn_back.configure(text=f"← {'List' if dest == 'list' else 'Grid'}")
        btn_back.pack(side="left", padx=(8, 2), pady=5)
    else:
        # List / Grid: grey out tools, show List + Grid + Edit tabs, hide Back
        _set_tool_strip_enabled(False)
        btn_back.pack_forget()
        for btn, m in view_mode_btns:
            btn.pack(side="left", padx=(8 if m == "list" else 2, 2), pady=5)
    _build_all_cards()


# ══════════════════════════════════════ PROJECT NAME ══════════════════════════════════════

def _apply_project_name():
    global project_name
    project_name = project_name_var.get().strip()
    if current_session:
        save_steps()
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")


# ══════════════════════════════════════ RECORDING ACTIONS ══════════════════════════════════════

def _default_recording_name():
    return datetime.now().strftime("Recording %Y-%m-%d %H:%M")


def _prompt_new_recording():
    """Combined dialog: project name + save location. Returns (name, parent_dir) or None."""
    ts_default   = _default_recording_name()
    default_path = os.path.abspath(BASE_DIR)

    dlg = ctk.CTkToplevel(root)
    dlg.title("New Recording")
    dlg.geometry("480x240")
    dlg.resizable(False, False)
    dlg.transient(root)
    dlg.grab_set()

    # Centre on the main window
    dlg.update_idletasks()
    rx, ry = root.winfo_rootx(), root.winfo_rooty()
    rw, rh = root.winfo_width(), root.winfo_height()
    dw, dh = 480, 240
    dlg.geometry(f"{dw}x{dh}+{rx + (rw - dw) // 2}+{ry + (rh - dh) // 2}")

    result = [None]

    # ── Project name ──
    ctk.CTkLabel(dlg, text="Project Name",
        font=("Segoe UI", 13, "bold"), text_color=C["text"]
    ).pack(padx=24, pady=(20, 2), anchor="w")

    name_var = tk.StringVar(value=project_name_var.get().strip() or ts_default)
    name_entry = ctk.CTkEntry(dlg, textvariable=name_var, width=432,
        font=("Segoe UI", 11), fg_color=C["surface"],
        border_color=C["border"], text_color=C["text"])
    name_entry.pack(padx=24, pady=(4, 12))
    name_entry.select_range(0, tk.END)
    name_entry.focus_force()

    # ── Save location ──
    ctk.CTkLabel(dlg, text="Save to",
        font=("Segoe UI", 9), text_color=C["muted"]
    ).pack(padx=24, anchor="w")

    path_row = ctk.CTkFrame(dlg, fg_color="transparent")
    path_row.pack(fill="x", padx=24, pady=(2, 14))

    path_var = tk.StringVar(value=default_path)
    path_entry = ctk.CTkEntry(path_row, textvariable=path_var, width=340,
        font=("Segoe UI", 10), fg_color=C["surface"],
        border_color=C["border"], text_color=C["muted"], state="readonly")
    path_entry.pack(side="left")

    def _browse():
        folder = filedialog.askdirectory(initialdir=path_var.get(), title="Choose folder")
        if folder:
            path_var.set(folder)

    ctk.CTkButton(path_row, text="Browse…", command=_browse,
        fg_color=C["surface"], hover_color="#333", border_width=1,
        border_color=C["border"], text_color=C["text"],
        width=80, height=28, corner_radius=5,
        font=("Segoe UI", 10)).pack(side="left", padx=(8, 0))

    # ── Buttons ──
    btn_row = ctk.CTkFrame(dlg, fg_color="transparent")
    btn_row.pack(fill="x", padx=24, pady=(0, 16))

    def do_ok(event=None):
        name = name_var.get().strip() or ts_default
        folder = path_var.get().strip()
        if not folder:
            folder = default_path
        os.makedirs(folder, exist_ok=True)
        result[0] = (name, folder)
        dlg.destroy()

    def do_cancel():
        dlg.destroy()

    ctk.CTkButton(btn_row, text="Start Recording", command=do_ok,
        fg_color=C["accent"], hover_color=C["acc_dark"],
        width=140, height=32).pack(side="right", padx=(8, 0))
    ctk.CTkButton(btn_row, text="Cancel", command=do_cancel,
        fg_color="transparent", hover_color=C["surface"], border_width=1,
        border_color=C["border"], text_color=C["muted"],
        width=90, height=32).pack(side="right")

    name_entry.bind("<Return>", do_ok)
    dlg.bind("<Escape>", lambda e: do_cancel())

    dlg.wait_window()
    return result[0]


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
    global recording, step_counter, log_data, project_name
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
    global recording
    if not current_session:
        return
    recording = True
    btn_start.configure(state="disabled")
    btn_stop.configure(state="normal")
    btn_continue.configure(state="disabled")
    threading.Thread(target=start_listeners, daemon=True).start()
    show_recording()


def _do_load_recording(folder):
    """Load a recording from folder path. Returns True on success."""
    global log_data, current_session, step_counter, project_name
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
        log_data.append(entry)
        step_objects[i] = objs
        if crop:
            step_crops[i] = crop

    current_session = folder
    step_counter    = len(log_data) + 1
    undo_stacks.clear()
    project_name_var.set(project_name)
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")
    _build_all_cards()
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


def export_html():
    if not log_data:
        messagebox.showwarning("Nothing to export", "No steps to export."); return
    title       = _export_title()
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
            flat.save(buf, "PNG")
            step_images.append(base64.b64encode(buf.getvalue()).decode())
        else:
            step_images.append(None)

    try:
        with open(report_path, "w", encoding="utf-8") as f:
            f.write(f"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="utf-8"><title>{title}</title>
<style>
@import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@300;400;600&display=swap');
*,*::before,*::after{{box-sizing:border-box;margin:0;padding:0}}
:root{{--bg:#0e0e0e;--surface:#141414;--border:#252525;--accent:#3d8ef0;--accent12:rgba(61,142,240,.12);
       --text:#e2e2e2;--muted:#666;--radius:12px}}
html,body{{height:100%}}
body{{background:var(--bg);color:var(--text);font-family:'IBM Plex Sans',sans-serif;font-weight:300;
     display:flex;flex-direction:column;overflow:hidden}}

/* ── top bar ── */
.topbar{{display:flex;align-items:center;justify-content:space-between;
         padding:10px 28px;border-bottom:1px solid var(--border);flex-shrink:0}}
.topbar h1{{font-family:'IBM Plex Mono',monospace;font-size:16px;font-weight:600;color:var(--accent)}}
.topbar .right{{display:flex;align-items:center;gap:16px}}
.topbar .meta{{color:var(--muted);font-family:'IBM Plex Mono',monospace;font-size:11px}}
.view-toggle{{display:flex;gap:2px;background:var(--surface);border:1px solid var(--border);
              border-radius:6px;padding:2px;overflow:hidden}}
.view-toggle button{{background:none;border:none;color:var(--muted);font-family:'IBM Plex Mono',monospace;
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
.slide.title-slide h2{{font-family:'IBM Plex Mono',monospace;font-size:36px;font-weight:600;color:var(--accent)}}
.slide.title-slide p{{font-size:14px;color:var(--muted);font-family:'IBM Plex Mono',monospace}}
.slide .step-num{{font-family:'IBM Plex Mono',monospace;font-size:11px;font-weight:600;color:var(--accent);
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
.counter{{position:absolute;right:28px;font-family:'IBM Plex Mono',monospace;font-size:11px;color:var(--muted)}}

/* ═══════════ LIST MODE ═══════════ */
.list-wrap{{flex:1;overflow-y:auto;padding:40px 24px 80px}}
.list-wrap.hidden{{display:none}}
.list-inner{{max-width:1020px;margin:0 auto}}
.card{{background:var(--surface);border:1px solid var(--border);border-radius:10px;overflow:hidden;margin-bottom:28px}}
.card-hdr{{display:flex;align-items:center;gap:14px;padding:14px 20px;border-bottom:1px solid var(--border)}}
.card-num{{font-family:'IBM Plex Mono',monospace;font-size:10px;font-weight:600;color:var(--accent);
           background:var(--accent12);padding:3px 10px;border-radius:4px;white-space:nowrap}}
.card-desc{{font-size:14px;color:var(--text);line-height:1.55}}
.card img{{display:block;width:100%;height:auto}}
.card .card-note{{padding:28px 24px;font-size:15px;line-height:1.7;color:var(--text)}}

.footer{{text-align:center;color:var(--muted);font-size:11px;font-family:'IBM Plex Mono',monospace;
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
                            f'<img src="data:image/png;base64,{b64}" alt="Step {sn}">'
                            f'</div>')
                else:
                    body = f'<div class="note-body">{desc_html}</div>'
                f.write(f"""    <div class="slide" data-idx="{i+1}">
      <div class="step-hdr"><span class="step-num">STEP {sn:02d}</span><span class="step-desc">{desc_html}</span></div>
      {body}
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
                    img_tag = f'\n    <img src="data:image/png;base64,{b64}" alt="Step {sn}">'
                else:
                    img_tag = f'\n    <div class="card-note">{desc_html}</div>'
                f.write(f"""    <div class="card">
      <div class="card-hdr"><span class="card-num">STEP {sn:02d}</span><span class="card-desc">{desc_html}</span></div>{img_tag}
    </div>
""")

            f.write(f"""    <div class="footer">Generated by PSR Pro &middot; {gen_year}</div>
  </div>
</div>

<script>
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
        pdf.set_fill_color(17,17,17); pdf.rect(0,0,297,210,"F")
        pdf.set_font("Helvetica","B",30); pdf.set_text_color(61,142,240); pdf.set_y(72)
        pdf.cell(0, 12, title, align="C", new_x="LMARGIN", new_y="NEXT")
        pdf.set_font("Helvetica","",11); pdf.set_text_color(130,130,130); pdf.ln(6)
        pdf.cell(0, 7, _pdf_safe(f"{len(log_data)} steps  -  Generated {datetime.now().strftime('%Y-%m-%d %H:%M')}"),
                 align="C", new_x="LMARGIN", new_y="NEXT")

        for i, entry in enumerate(log_data):
            pdf.add_page()
            pdf.set_fill_color(26,26,26); pdf.rect(0,0,297,22,"F")
            pdf.set_font("Helvetica","B",10); pdf.set_text_color(61,142,240); pdf.set_xy(16,6)
            pdf.cell(26, 9, f"STEP {entry['step']:02d}", new_x="RIGHT", new_y="LAST")
            pdf.set_font("Helvetica","",9); pdf.set_text_color(210,210,210)
            desc = entry["description"]
            pdf.cell(0, 9, _pdf_safe(desc[:117] + "…" if len(desc) > 120 else desc), new_x="LMARGIN", new_y="NEXT")

            flat = _flatten_to_pil(i)
            if flat is not None:
                flat.thumbnail((2600, 1300), Image.LANCZOS)
                tmp  = os.path.join(current_session, f"_tmp_{i}.jpg")
                flat.save(tmp, "JPEG", quality=88)
                tmp_imgs.append(tmp)
                iw, ih = flat.size
                ratio  = min(265/iw, 176/ih)
                fw, fh = iw*ratio, ih*ratio
                pdf.image(tmp, x=(297-fw)/2, y=24, w=fw, h=fh)

        pdf.output(report_path)
    except Exception as exc:
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
root.geometry("700x520")
root.minsize(560, 400)
root.configure(fg_color=C["bg"])

# ── Three top-level panels (only one visible at a time) ────────────────────────────
home_panel = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])
rec_panel  = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])
edit_panel = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])


# ── Toolbar — recording controls · project name · export ──────────────────────────

toolbar = ctk.CTkFrame(edit_panel, height=46, corner_radius=0, fg_color=C["panel"])
toolbar.pack(side="top", fill="x")
toolbar.pack_propagate(False)
_B = dict(height=28, corner_radius=5, font=("Segoe UI", 10, "bold"), border_width=0)

# Recording controls (left)
# ── File operations (Open / New — like a File menu) ───────────────────────────────
_btn_open = ctk.CTkButton(toolbar, text="📂  Open", command=load_recording,
    fg_color=C["surface"], hover_color="#333", width=80, **_B)
_btn_open.pack(side="left", padx=(10,2), pady=9)
tip(_btn_open, "Open an existing recording folder  [Ctrl+O]")

btn_start = ctk.CTkButton(toolbar, text="▶  Start", command=start_recording,
    fg_color=C["success"], hover_color="#1d7a43", width=88, **_B)
btn_start.pack(side="left", padx=(2,3), pady=9)
tip(btn_start, "Start a new recording")

# ── Session actions (context of the current recording) ────────────────────────────
ctk.CTkFrame(toolbar, width=1, fg_color=C["border"]).pack(side="left", fill="y", pady=8, padx=4)

btn_continue = ctk.CTkButton(toolbar, text="⏩  Continue", command=continue_recording,
    fg_color=C["warn"], hover_color="#b05a10", width=106, state="disabled", **_B)
btn_continue.pack(side="left", padx=3, pady=9)
tip(btn_continue, "Resume recording — appends to existing steps")

btn_stop = ctk.CTkButton(toolbar, text="■  Stop", command=stop_recording,
    fg_color=C["danger"], hover_color="#a02020", width=80, state="disabled", **_B)
btn_stop.pack(side="left", padx=3, pady=9)
tip(btn_stop, "Stop recording  [F6]")


# Capture mode vars (shared with recording tray — no widgets in toolbar)
_cap_click_var  = tk.BooleanVar(value=True)
_cap_hotkey_var = tk.BooleanVar(value=False)

def _sync_globals(*_):
    global capture_on_click, capture_on_hotkey
    capture_on_click  = _cap_click_var.get()
    capture_on_hotkey = _cap_hotkey_var.get()

_cap_click_var.trace_add("write", _sync_globals)
_cap_hotkey_var.trace_add("write", _sync_globals)

# Project name (center-left)
ctk.CTkFrame(toolbar, width=1, fg_color=C["border"]).pack(side="left", fill="y", pady=8, padx=(10,6))
ctk.CTkLabel(toolbar, text="Project:", font=("Segoe UI", 9),
             text_color=C["muted"]).pack(side="left", padx=(0,3))
project_name_var = tk.StringVar(value=_default_recording_name())
project_name_entry = ctk.CTkEntry(
    toolbar, textvariable=project_name_var,
    placeholder_text="Untitled recording",
    width=200, height=28, corner_radius=5,
    fg_color=C["surface"], border_width=1, border_color=C["border"],
    font=("Segoe UI", 10), text_color=C["text"])
project_name_entry.pack(side="left", padx=3, pady=9)
project_name_entry.bind("<Return>",   lambda e: (_apply_project_name(), root.focus()))
project_name_entry.bind("<FocusOut>", lambda e:  _apply_project_name())

# Export (right)
_btn_html = ctk.CTkButton(toolbar, text="↓ HTML", command=export_html,
    fg_color=C["surface"], hover_color="#333", width=72, **_B)
_btn_html.pack(side="right", padx=(2, 10), pady=9)
tip(_btn_html, "Export as interactive HTML  [Ctrl+Shift+H]")

_btn_pdf = ctk.CTkButton(toolbar, text="↓ PDF", command=export_pdf,
    fg_color=C["acc_dark"], hover_color=C["accent"], width=72, **_B)
_btn_pdf.pack(side="right", padx=2, pady=9)
tip(_btn_pdf, "Export as PDF  [Ctrl+Shift+P]")


# ── Tool strip ────────────────────────────────────────────────────────────────────

tool_strip = ctk.CTkFrame(edit_panel, height=44, corner_radius=0, fg_color=C["surface"])
tool_strip.pack(side="top", fill="x")
tool_strip.pack_propagate(False)

_TB = dict(height=26, corner_radius=4, font=("Segoe UI", 10), border_width=1, width=108)

btn_pointer = ctk.CTkButton(tool_strip, text="🖱  Pointer",
    fg_color=C["acc_dark"], border_color=C["accent"], hover_color=C["acc_dark"],
    command=lambda: set_tool("none"), **_TB)
btn_pointer.pack(side="left", padx=(10,3), pady=9)
tip(btn_pointer, "Select / move / resize annotations  [V]")

btn_highlight = ctk.CTkButton(tool_strip, text="🔴  Highlight",
    fg_color="transparent", border_color=C["border"], hover_color="#4a1010",
    command=lambda: set_tool("highlight"), **_TB)
btn_highlight.pack(side="left", padx=3, pady=9)
tip(btn_highlight, "Draw a semi-transparent highlight box  [U]")

btn_redact = ctk.CTkButton(tool_strip, text="⬛  Redact",
    fg_color="transparent", border_color=C["border"], hover_color="#222",
    command=lambda: set_tool("redact"), **_TB)
btn_redact.pack(side="left", padx=3, pady=9)
tip(btn_redact, "Cover a region with a solid black box  [M]")

btn_crop = ctk.CTkButton(tool_strip, text="✂  Crop",
    fg_color="transparent", border_color=C["border"], hover_color="#3a3010",
    command=lambda: set_tool("crop"), **_TB)
btn_crop.pack(side="left", padx=3, pady=9)
tip(btn_crop, "Non-destructive crop — drag to set region  [C]")

btn_draw = ctk.CTkButton(tool_strip, text="✏  Draw",
    fg_color="transparent", border_color=C["border"], hover_color="#1a2a1a",
    command=lambda: set_tool("draw"), **_TB)
btn_draw.pack(side="left", padx=3, pady=9)
tip(btn_draw, "Freehand pen — arrows, circles, underlines  [B]")

_draw_sep1 = ctk.CTkFrame(tool_strip, width=1, fg_color=C["border"])
_draw_sep1.pack(side="left", fill="y", pady=8, padx=6)

# Colour swatches (only visible when Draw is active)
_SWATCHES = [
    ("#e74c3c","Red"), ("#e67e22","Orange"), ("#f1c40f","Yellow"),
    ("#2ecc71","Green"), ("#3d8ef0","Blue"), ("#ffffff","White"), ("#111111","Black"),
]
for hex_col, col_lbl in _SWATCHES:
    sw = ctk.CTkButton(tool_strip, text="", width=20, height=20, corner_radius=10,
        fg_color=hex_col, hover_color=hex_col,
        border_width=1, border_color="#555555",
        command=lambda c=hex_col: _set_draw_color_global(c))
    sw.pack(side="left", padx=2, pady=12)
    draw_color_btns.append((sw, hex_col))
    tip(sw, col_lbl)
draw_color_btns[0][0].configure(border_width=2, border_color="#ffffff")

def _open_color_picker():
    from tkinter import colorchooser
    result = colorchooser.askcolor(color=draw_color, title="Pick Colour")
    if result and result[1]:
        _set_draw_color_global(result[1])

_color_picker_btn = ctk.CTkButton(tool_strip, text="⊕", width=22, height=20, corner_radius=10,
    fg_color="transparent", hover_color=C["surface"],
    border_width=1, border_color="#555555",
    font=("Segoe UI", 12), text_color=C["muted"],
    command=_open_color_picker)
_color_picker_btn.pack(side="left", padx=(4, 0), pady=12)
draw_color_btns.append((_color_picker_btn, None))
tip(_color_picker_btn, "Custom colour picker")

_draw_sep2 = ctk.CTkFrame(tool_strip, width=1, fg_color=C["border"])
_draw_sep2.pack(side="left", fill="y", pady=8, padx=6)

# Pen sizes (only visible when Draw is active)
for _plbl, _ppx, _ptip in (("S", 2, "2 px"), ("M", 5, "5 px"), ("L", 10, "10 px"), ("XL", 18, "18 px")):
    pb = ctk.CTkButton(tool_strip, text=_plbl, width=32, height=24, corner_radius=4,
        fg_color=C["acc_dark"] if _plbl == "S" else "transparent",
        border_width=1,
        border_color=C["accent"] if _plbl == "S" else C["border"],
        hover_color=C["acc_dark"],
        font=("Segoe UI", 9, "bold"),
        command=lambda w=_ppx: _set_draw_width_global(w))
    pb.pack(side="left", padx=2, pady=9)
    pen_size_btns.append((pb, _ppx))
    tip(pb, f"Pen width: {_ptip}")

# Draw-only widgets start hidden (default tool is Pointer)
for _w in draw_color_btns:
    _w[0].pack_forget()
for _w in pen_size_btns:
    _w[0].pack_forget()
_draw_sep1.pack_forget()
_draw_sep2.pack_forget()

status_label = ctk.CTkLabel(tool_strip, text="◼  Ready",
    font=("Segoe UI", 9), text_color=C["muted"])
status_label.pack(side="right", padx=12)

# ── Body ──────────────────────────────────────────────────────────────────────────

body = ctk.CTkFrame(edit_panel, corner_radius=0, fg_color=C["bg"])
body.pack(fill="both", expand=True, padx=10, pady=(8,10))

sidebar = ctk.CTkFrame(body, width=268, corner_radius=8, fg_color=C["panel"])
sidebar.pack(side="left", fill="y", padx=(0,8))
sidebar.pack_propagate(False)

_sidebar_collapsed = [False]

shdr = ctk.CTkFrame(sidebar, height=36, fg_color=C["surface"], corner_radius=0)
shdr.pack(fill="x"); shdr.pack_propagate(False)
ctk.CTkLabel(shdr, text="STEPS", font=("Segoe UI", 9, "bold"),
             text_color=C["muted"]).pack(side="left", padx=14, pady=8)
count_label = ctk.CTkLabel(shdr, text="0 steps", font=("Segoe UI", 9),
                            text_color=C["muted"])
count_label.pack(side="right", padx=4)

def _toggle_sidebar():
    if _sidebar_collapsed[0]:
        sidebar.configure(width=268)
        sidebar_list.pack(fill="both", expand=True, padx=4, pady=4)
        _dnd_hint.pack(fill="x", padx=8, pady=(0, 6))
        count_label.pack(side="right", padx=4)
        _sidebar_toggle_btn.configure(text="«")
        _sidebar_collapsed[0] = False
    else:
        count_label.pack_forget()
        sidebar_list.pack_forget()
        _dnd_hint.pack_forget()
        sidebar.configure(width=30)
        _sidebar_toggle_btn.configure(text="»")
        _sidebar_collapsed[0] = True

_sidebar_toggle_btn = ctk.CTkButton(shdr, text="«", command=_toggle_sidebar,
    fg_color="transparent", hover_color=C["surface"],
    text_color=C["muted"], width=24, height=28, corner_radius=4,
    font=("Segoe UI", 11), border_width=0)
_sidebar_toggle_btn.pack(side="right", padx=(0, 2))
tip(_sidebar_toggle_btn, "Collapse / expand the step list panel")

sidebar_list = tk.Listbox(sidebar, bg=C["panel"], fg=C["text"],
    selectbackground=C["acc_dark"], selectforeground="#fff",
    font=("Segoe UI", 9), borderwidth=0, relief="flat",
    highlightthickness=0, activestyle="none",
    selectmode=tk.EXTENDED)
sidebar_list.pack(fill="both", expand=True, padx=4, pady=4)
sidebar_list.bind("<ButtonPress-1>",   _sidebar_press)
sidebar_list.bind("<B1-Motion>",       _sidebar_motion)
sidebar_list.bind("<ButtonRelease-1>", _sidebar_release)
sidebar_list.bind("<Button-3>",        _sidebar_context)
sidebar_list.bind("<<ListboxSelect>>", _on_sidebar_sel_change)

_dnd_hint = ctk.CTkLabel(sidebar, text="drag to reorder  ·  right-click to insert",
    font=("Segoe UI", 9), text_color=C["muted"], height=20)
_dnd_hint.pack(fill="x", padx=8, pady=(0,6))

right_frame = ctk.CTkFrame(body, corner_radius=8, fg_color=C["panel"])
right_frame.pack(side="right", fill="both", expand=True)

# ── View bar — navigation tabs + content actions (lives inside the cards panel) ───
view_bar = ctk.CTkFrame(right_frame, height=36, corner_radius=0, fg_color=C["surface"])
view_bar.pack(side="top", fill="x")
view_bar.pack_propagate(False)

_VBT = dict(height=26, corner_radius=4, font=("Segoe UI", 9), border_width=1)

# Right side first (packed right → left)
_btn_step = ctk.CTkButton(view_bar, text="＋  Step",
    command=lambda: insert_custom_step(),
    fg_color="transparent", border_color=C["border"],
    hover_color="#1d3a1d", width=72, **_VBT)
_btn_step.pack(side="right", padx=(2, 8), pady=5)
tip(_btn_step, "Add a blank step at the end")

ctk.CTkFrame(view_bar, width=1, fg_color=C["border"]).pack(side="right", fill="y", pady=6, padx=4)

# Left side: view tabs
def _back_to_overview():
    global _prev_view_mode
    target = _prev_view_mode or "list"
    _prev_view_mode = ""
    _set_view_mode(target)

btn_back = ctk.CTkButton(view_bar, text="← Back",
    command=_back_to_overview,
    fg_color="transparent", border_color=C["border"],
    hover_color=C["acc_dark"], width=66, **_VBT)
tip(btn_back, "Back to overview  [Esc]")
# Not packed by default — shown only when entering detail from list/grid

for _vlbl, _vmode, _vtip in (
    ("≡  List", "list", "List overview — double-click a step to annotate it"),
    ("⊞  Grid", "grid", "Grid overview — double-click a step to annotate it"),
    ("✎  Edit", "default", "Edit mode — annotate with tools below"),
):
    _vb = ctk.CTkButton(view_bar,
        text=_vlbl,
        fg_color=C["acc_dark"] if _vmode == "default" else "transparent",
        border_color=C["accent"] if _vmode == "default" else C["border"],
        hover_color=C["acc_dark"],
        command=lambda m=_vmode: _set_view_mode(m), **_VBT)
    _vb.pack(side="left", padx=(8 if _vmode == "list" else 2, 2), pady=5)
    view_mode_btns.append((_vb, _vmode))
    tip(_vb, _vtip)

cards_scroll = ctk.CTkScrollableFrame(right_frame, corner_radius=0, fg_color=C["bg"],
    scrollbar_button_color=C["border"], scrollbar_button_hover_color=C["accent"])
cards_scroll.pack(fill="both", expand=True, padx=10, pady=10)

# Keep the inner frame width pinned to the canvas width so content never
# overflows horizontally and no horizontal scrollbar can appear.
def _pin_scroll_width(event):
    try:
        canvas = cards_scroll._parent_canvas
        canvas.itemconfigure(canvas.find_all()[0], width=event.width)
    except Exception:
        pass
cards_scroll._parent_canvas.bind("<Configure>", _pin_scroll_width)
cards_scroll.bind_all("<MouseWheel>", lambda e: _on_cards_scroll(), add="+")


# ══════════════════════════════════════ RECORDING PANEL ══════════════════════════════════════
# Floating toolbar — borderless, fully draggable, snipping-tool style.
# Row 1:  [⠿ ● ■ ⏸]  [⚙]  [▾]
# Row 2:  [#12  ↳ left mouse button at (512,340)          project-name]

_rec_row1 = ctk.CTkFrame(rec_panel, height=36, corner_radius=0, fg_color=C["panel"])
_rec_row1.pack(fill="x")
_rec_row1.pack_propagate(False)

# — Left: grip + status + action buttons —
_rec_grip = ctk.CTkLabel(_rec_row1, text="⠿", font=("Segoe UI", 14),
    text_color="#555", width=16, cursor="fleur")
_rec_grip.pack(side="left", padx=(8, 2))

_rec_status = ctk.CTkLabel(_rec_row1, text="●",
    font=("Segoe UI", 10, "bold"), text_color=C["danger"], width=14)
_rec_status.pack(side="left", padx=(0, 4))

_AB = dict(height=24, corner_radius=4, font=("Segoe UI", 10))

_rec_stop_btn = ctk.CTkButton(_rec_row1, text="■", command=stop_recording,
    fg_color=C["danger"], hover_color="#a02020", width=28, border_width=0, **_AB)
_rec_stop_btn.pack(side="left", padx=(0, 2), pady=6)
tip(_rec_stop_btn, "Stop recording  [F6]")

_btn_pause = ctk.CTkButton(_rec_row1, text="⏸", command=lambda: _toggle_pause(),
    fg_color="transparent", hover_color=C["warn"],
    width=28, border_width=1, border_color=C["border"], **_AB)
_btn_pause.pack(side="left", padx=(0, 2), pady=6)
tip(_btn_pause, "Pause / resume  [F7]")

# — Capture mode indicators (between actions and right-side buttons) —
_rec_mode_label = ctk.CTkLabel(_rec_row1, text="",
    font=("Segoe UI", 9), text_color=C["muted"], anchor="w")
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

_rec_hide_btn = ctk.CTkButton(_rec_row1, text="▾", command=_minimize_rec_tray,
    fg_color="transparent", hover_color=C["surface"],
    text_color="#555", width=22, height=22, corner_radius=4,
    font=("Segoe UI", 11), border_width=0)
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

    def _sync(*_a):
        global ignore_psr_focus, capture_keyboard
        ignore_psr_focus = _ignore_psr_var.get()
        capture_keyboard = _cap_keyboard_var.get()
        _update_rec_panel()
    _ignore_psr_var.trace_add("write", _sync)
    _cap_keyboard_var.trace_add("write", _sync)

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

_rec_gear_btn = ctk.CTkButton(_rec_row1, text="⚙", command=_toggle_settings_flyout,
    fg_color="transparent", hover_color=C["surface"],
    text_color=C["muted"], width=28, height=24, corner_radius=4,
    font=("Segoe UI", 12), border_width=0)
_rec_gear_btn.pack(side="right", padx=(0, 2))
tip(_rec_gear_btn, "Recording settings")

# — Row 2: step count + feedback —
_rec_row2 = ctk.CTkFrame(rec_panel, height=28, corner_radius=0, fg_color=C["bg"])
_rec_row2.pack(fill="x")
_rec_row2.pack_propagate(False)

_rec_steps = ctk.CTkLabel(_rec_row2, text="0",
    font=("Courier New", 10, "bold"), text_color=C["accent"], width=28)
_rec_steps.pack(side="left", padx=(10, 0))

_rec_cap_step = ctk.CTkLabel(_rec_row2, text="",
    font=("Segoe UI", 9), text_color="#555", anchor="w")
_rec_cap_step.pack(side="left", padx=(2, 0))

_rec_cap_input = ctk.CTkLabel(_rec_row2, text="",
    font=("Segoe UI", 9, "bold"), text_color="#555", anchor="w")
_rec_cap_input.pack(side="left", padx=(2, 0))

_rec_cap_rest = ctk.CTkLabel(_rec_row2, text="",
    font=("Segoe UI", 9), text_color="#444", anchor="w")
_rec_cap_rest.pack(side="left", padx=(2, 0))

_rec_project = ctk.CTkLabel(_rec_row2, text="",
    font=("Segoe UI", 9), text_color="#444")
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


def _toggle_pause():
    global paused
    paused = not paused
    _update_rec_panel()


def _update_rec_panel():
    _rec_project.configure(text=project_name or "Untitled")
    count = len(log_data)
    _rec_steps.configure(text=str(count))
    if paused:
        _rec_status.configure(text="⏸", text_color=C["warn"])
        _btn_pause.configure(text="▶", border_color=C["warn"])
    elif recording:
        _rec_status.configure(text="●", text_color=C["danger"])
        _btn_pause.configure(text="⏸", border_color=C["border"])
    else:
        _rec_status.configure(text="◼", text_color=C["muted"])
        _btn_pause.configure(text="⏸", border_color=C["border"])
    # Build compact capture-mode indicator
    modes = []
    if capture_on_click:  modes.append("🖱")
    if capture_keyboard:  modes.append("⌨")
    if capture_on_hotkey: modes.append("⎙")
    _rec_mode_label.configure(text=" ".join(modes) if modes else "—")
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

_home_hdr = ctk.CTkFrame(home_panel, height=60, corner_radius=0, fg_color=C["panel"])
_home_hdr.pack(side="top", fill="x")
_home_hdr.pack_propagate(False)

ctk.CTkLabel(_home_hdr, text="PSR Pro",
    font=("Segoe UI", 18, "bold"), text_color=C["accent"]
).pack(side="left", padx=24, pady=16)

ctk.CTkLabel(_home_hdr, text="Process Step Recorder",
    font=("Segoe UI", 10), text_color=C["muted"]
).pack(side="left")

# ── Centre content ─────────────────────────────────────────────────────────────────
_home_center = ctk.CTkFrame(home_panel, fg_color="transparent")
_home_center.place(relx=0.5, rely=0.5, anchor="center")

_home_actions = ctk.CTkFrame(_home_center, fg_color="transparent")
_home_actions.pack()

_home_new_project = ctk.CTkFrame(_home_center, fg_color="transparent")
_home_new_project.pack(fill="x", padx=8, pady=(0, 12))

ctk.CTkLabel(_home_new_project, text="Project Name",
    font=("Segoe UI", 13, "bold"), text_color=C["text"]
).pack(anchor="w")

ctk.CTkEntry(_home_new_project, textvariable=project_name_var,
    placeholder_text="Recording name (optional)",
    width=420, height=34, corner_radius=6,
    fg_color=C["surface"], border_width=1, border_color=C["border"],
    font=("Segoe UI", 11), text_color=C["text"]
).pack(anchor="w", pady=(6, 10))

ctk.CTkLabel(_home_new_project, text="Save to",
    font=("Segoe UI", 10), text_color=C["muted"]
).pack(anchor="w")

_home_save_row = ctk.CTkFrame(_home_new_project, fg_color="transparent")
_home_save_row.pack(fill="x", pady=(5, 0))

save_parent_dir_var = tk.StringVar(value=os.path.abspath(BASE_DIR))
_home_save_entry = ctk.CTkEntry(_home_save_row, textvariable=save_parent_dir_var,
    width=330, height=32, corner_radius=6,
    fg_color=C["surface"], border_width=1, border_color=C["border"],
    font=("Segoe UI", 10), text_color=C["muted"], state="readonly")
_home_save_entry.pack(side="left")

def _browse_home_save_dir():
    folder = filedialog.askdirectory(initialdir=save_parent_dir_var.get(), title="Choose folder")
    if folder:
        save_parent_dir_var.set(folder)

ctk.CTkButton(_home_save_row, text="Browse...",
    command=_browse_home_save_dir,
    fg_color=C["surface"], hover_color="#333", border_width=1,
    border_color=C["border"], text_color=C["text"],
    width=84, height=32, corner_radius=6,
    font=("Segoe UI", 10)
).pack(side="left", padx=(8, 0))

ctk.CTkButton(_home_actions, text="▶  Start New Recording",
    fg_color=C["success"], hover_color="#1d7a43",
    font=("Segoe UI", 12, "bold"), height=40, width=220, corner_radius=8,
    command=start_recording
).pack(side="left", padx=(0, 10))

ctk.CTkButton(_home_actions, text="📂  Open",
    fg_color=C["surface"], hover_color="#333",
    font=("Segoe UI", 12), height=40, width=100, corner_radius=8,
    border_width=1, border_color=C["border"],
    command=load_recording
).pack(side="left")

_home_recents_inner = [None]


def _open_recent(folder):
    if _do_load_recording(folder):
        show_editing()


def _refresh_home():
    if _home_recents_inner[0]:
        try: _home_recents_inner[0].destroy()
        except Exception: pass

    container = ctk.CTkFrame(_home_center, fg_color="transparent")
    container.pack(pady=(20, 0))
    _home_recents_inner[0] = container

    recent = []
    if os.path.isdir(BASE_DIR):
        for name in sorted(os.listdir(BASE_DIR)):
            folder = os.path.join(BASE_DIR, name)
            json_path = os.path.join(folder, "steps.json")
            if os.path.isdir(folder) and os.path.exists(json_path):
                try:
                    mtime = os.path.getmtime(json_path)
                    with open(json_path, encoding="utf-8") as f:
                        raw = json.load(f)
                    if isinstance(raw, list):
                        pname  = name
                        nsteps = len(raw)
                    else:
                        pname  = raw.get("project_name") or name
                        nsteps = len(raw.get("steps", []))
                    recent.append((mtime, pname, nsteps, folder))
                except Exception:
                    pass

    recent.sort(reverse=True)
    recent = recent[:3]

    if not recent:
        ctk.CTkLabel(container,
            text="No recordings yet.",
            font=("Segoe UI", 9), text_color=C["muted"]
        ).pack(pady=4)
        return

    ctk.CTkLabel(container, text="RECENT",
        font=("Segoe UI", 9, "bold"), text_color=C["muted"]
    ).pack(anchor="w", pady=(0, 4))

    for i, (mtime, pname, nsteps, folder) in enumerate(recent):
        if i > 0:
            ctk.CTkFrame(container, height=1, fg_color=C["border"]).pack(fill="x")

        row = ctk.CTkFrame(container, fg_color="transparent", cursor="hand2")
        row.pack(fill="x")

        date_str = datetime.fromtimestamp(mtime).strftime("%b %d")
        name_lbl = ctk.CTkLabel(row,
            text=pname or os.path.basename(folder),
            font=("Segoe UI", 10), text_color=C["text"], anchor="w")
        name_lbl.pack(side="left", pady=5)

        meta_lbl = ctk.CTkLabel(row,
            text=f"  {date_str} · {nsteps}s",
            font=("Segoe UI", 9), text_color=C["muted"])
        meta_lbl.pack(side="left")

        arrow_lbl = ctk.CTkLabel(row, text="→",
            font=("Segoe UI", 10), text_color=C["muted"], width=20)
        arrow_lbl.pack(side="right", pady=5)

        def _make_handlers(f, r, a):
            def _click(_e):  _open_recent(f)
            def _enter(_e):
                r.configure(fg_color=C["surface"])
                a.configure(text_color=C["accent"])
            def _leave(_e):
                r.configure(fg_color="transparent")
                a.configure(text_color=C["muted"])
            return _click, _enter, _leave

        _click, _enter, _leave = _make_handlers(folder, row, arrow_lbl)
        for w in (row, name_lbl, meta_lbl, arrow_lbl):
            try:
                w.bind("<Button-1>", _click)
                w.bind("<Enter>",    _enter)
                w.bind("<Leave>",    _leave)
            except Exception:
                pass


# ══════════════════════════════════════ PANEL SWITCHING ══════════════════════════════════════

def _close_rec_flyout():
    _close_rec_settings()

def show_home():
    _close_rec_flyout()
    rec_panel.pack_forget()
    edit_panel.pack_forget()
    root.overrideredirect(False)
    _refresh_home()
    home_panel.pack(fill="both", expand=True)
    root.geometry("700x520")
    root.minsize(560, 400)
    root.resizable(True, True)
    root.attributes("-topmost", False)
    root.title("PSR Pro — Process Step Recorder")
    # Restore toolbar button to its default label for when we return to edit mode
    btn_start.configure(text="▶  Start")
    tip(btn_start, "Start a new recording")


def show_recording():
    home_panel.pack_forget()
    edit_panel.pack_forget()
    _update_rec_panel()
    rec_panel.pack(fill="both", expand=True)
    sw = root.winfo_screenwidth()
    root.overrideredirect(True)
    w = 280
    root.geometry(f"{w}x64+{(sw - w) // 2}+8")
    root.minsize(220, 64)
    root.resizable(True, False)
    root.attributes("-topmost", True)


def show_editing():
    _close_rec_flyout()
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
    btn_start.configure(text="▶  New")
    tip(btn_start, "Start a new recording — replaces current session")
    # Stop is only relevant if recording is still running (opened from tray)
    if recording:
        btn_stop.pack(side="left", padx=3, pady=9)
    else:
        btn_stop.pack_forget()
    # Re-apply view mode so tab states (Edit hidden/shown, tool strip) are correct.
    _set_view_mode(view_mode)


# ══════════════════════════════════════ KEYBOARD SHORTCUTS ══════════════════════════

_TEXT_FOCUS_CLASSES = ("Text", "Entry", "TEntry", "Spinbox", "TSpinbox")

def _focus_in_text_input():
    """True if keyboard focus is in a text/entry widget (don't steal shortcuts)."""
    focus = root.focus_get()
    return focus and focus.winfo_class() in _TEXT_FOCUS_CLASSES


def _on_root_key(event):
    if event.keysym in ("Delete", "BackSpace"):
        if _focus_in_text_input():
            return
        # Annotation delete takes priority over step delete
        card = active_card_ref[0]
        if (card is not None and not card.is_text_only
                and hasattr(card, '_selected_obj') and card._selected_obj is not None):
            card.delete_selected()
            return "break"
        if _selected:
            _delete_selected()
            return "break"


def _on_tool_hotkey(event):
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
    card = active_card_ref[0]
    if card is not None and not card.is_text_only:
        card._undo()
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
root.bind("<Control-o>", lambda e: load_recording())
root.bind("<Control-O>", lambda e: load_recording())
root.bind("<Control-Shift-H>", lambda e: export_html())
root.bind("<Control-Shift-P>", lambda e: export_pdf())
for _hk in ('v', 'u', 'm', 'c', 'b'):
    root.bind(f"<KeyPress-{_hk}>", _on_tool_hotkey)
    root.bind(f"<KeyPress-{_hk.upper()}>", _on_tool_hotkey)


# ══════════════════════════════════════ START ══════════════════════════════════════

root.after(100, process_queue)
root.after(300, _setup_dnd)
show_home()
root.mainloop()
