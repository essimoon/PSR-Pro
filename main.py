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

import copy, io, os, json, queue, subprocess, sys, threading, base64, webbrowser
from datetime import datetime

import tkinter as tk
from tkinter import filedialog, messagebox
import customtkinter as ctk
from PIL import Image, ImageTk, ImageDraw, ImageGrab
import mss, mss.tools
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

annotation_tool = "none"   # "none"|"highlight"|"redact"|"crop"|"draw"
capture_on_click  = True
capture_on_hotkey = False
draw_color      = "#e74c3c"
draw_width      = 3

step_cards      = []
active_card_ref = [None]
draw_color_btns = []
pen_size_btns   = []
view_mode       = "default"   # "default" | "list" | "grid"

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
    """Composite crop + all vector objects onto screenshot. Returns a flat RGB PIL image, or None for text-only."""
    entry = log_data[step_index]
    if entry.get("screenshot") is None:
        return None
    img = Image.open(os.path.join(current_session, entry["screenshot"])).convert("RGB")
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
    import re
    name = re.sub(r'[<>:"/\\|?*]', '_', name.strip())
    name = name.strip('. ')
    return name[:80] if name else ""


def create_session():
    global current_session
    ts = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    try:
        pname = _safe_folder_name(project_name_var.get())
    except Exception:
        pname = ""
    folder = f"{pname}_{ts}" if pname else ts
    current_session = os.path.join(BASE_DIR, folder)
    os.makedirs(current_session)


def save_steps():
    if not current_session:
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
    with open(os.path.join(current_session, "steps.json"), "w", encoding="utf-8") as f:
        json.dump(doc, f, indent=4)


def capture_screenshot(filename):
    filepath = os.path.join(current_session, filename)
    with mss.mss() as sct:
        shot = sct.grab(sct.monitors[1])
        mss.tools.to_png(shot.rgb, shot.size, output=filepath)
    return filepath


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
    filename = f"step_{step_counter}.png"
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
    save_steps()
    root.after(0, _append_card)
    step_counter += 1


# ══════════════════════════════════════ LISTENERS ══════════════════════════════════════

def _key_str(key):
    try:    return key.char.upper()
    except: return str(key).replace("Key.", "").upper()


def _on_click(x, y, button, pressed):
    if (not pressed) and recording and capture_on_click:
        btn = str(button).replace("Button.", "")
        event_queue.put(f"released {btn} mouse button at ({x}, {y})")


def _on_press_key(key):
    if not recording:
        return

    if capture_on_hotkey and key == keyboard.Key.scroll_lock:
        event_queue.put("manual capture (Scroll Lock)")
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
        while True:
            text = event_queue.get_nowait()
            handle_event(text)
    except queue.Empty:
        pass
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

    ctk.CTkLabel(img_row, textvariable=img_path_var,
                 font=("Segoe UI", 10), text_color=C["muted"],
                 anchor="w", wraplength=300).pack(side="left", fill="x", expand=True)

    def pick_image():
        p = filedialog.askopenfilename(
            title="Choose screenshot",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp"), ("All", "*.*")])
        if p:
            img_path_var.set(os.path.basename(p))
            img_path_var._full = p   # stash full path

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
        saved_img[0]  = getattr(img_path_var, "_full", None) or img_path_var.get().strip()
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


def _drop_insert_pos(x_root, y_root):
    """Compute insertion index from screen coords using visible cards."""
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
    return len(step_cards)


def _handle_file_drop(raw_paths, x_root, y_root):
    """Process file paths dropped onto the app."""
    if not current_session:
        _set_status("Start or open a recording to drop into", C["warn"])
        return

    try:
        paths = root.tk.splitlist(raw_paths)
    except Exception:
        paths = raw_paths.split()

    pos   = _drop_insert_pos(x_root, y_root)
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
    except: pass
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
    except:
        return
    if card.index < len(log_data) and log_data[card.index]["description"] != new_text:
        log_data[card.index]["description"] = new_text
        save_steps()
        _refresh_sidebar()


# ══════════════════════════════════════ STEP CARD ══════════════════════════════════════

class StepCard:
    def __init__(self, parent, index):
        self.index        = index
        self.is_text_only = log_data[index].get("screenshot") is None
        self._disp_size   = (CARD_IMG_MAX_W, 100)
        self._orig_size   = (1920, 1080)
        self._crop_region = (0, 0, 1920, 1080)
        self._photo       = None
        self.canvas        = None

        self._create_start = None
        self._create_rect  = None
        self._draw_pts     = []
        self._last_draw    = None

        self._selected_obj = None
        self._drag_info    = None

        self._build(parent)
        if not self.is_text_only:
            self.reload_image()
        _bind_card_context(self)

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

        grip = ctk.CTkLabel(hdr, text="⠿", font=("Segoe UI", 14),
                            text_color=C["muted"], width=22, cursor="fleur")
        grip.pack(side="left", padx=(6,0))
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
        ratio    = min(CARD_IMG_MAX_W / cropped.size[0], 1.0)
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
        i = self.index
        if i == 0: return
        log_data[i], log_data[i-1] = log_data[i-1], log_data[i]
        step_objects[i], step_objects[i-1] = step_objects.get(i-1,[]), step_objects.get(i,[])
        step_crops[i],   step_crops[i-1]   = step_crops.get(i-1),     step_crops.get(i)
        _renumber_and_rebuild(scroll_to=i-1)

    def _move_down(self):
        i = self.index
        if i >= len(log_data)-1: return
        log_data[i], log_data[i+1] = log_data[i+1], log_data[i]
        step_objects[i], step_objects[i+1] = step_objects.get(i+1,[]), step_objects.get(i,[])
        step_crops[i],   step_crops[i+1]   = step_crops.get(i+1),     step_crops.get(i)
        _renumber_and_rebuild(scroll_to=i+1)

    def _delete(self):
        if not messagebox.askyesno("Delete Step", f"Delete Step {log_data[self.index]['step']}?"):
            return
        idx = self.index
        screenshot = log_data[idx].get("screenshot")
        if screenshot:
            img_path = os.path.join(current_session, screenshot)
            if os.path.exists(img_path):
                try: os.remove(img_path)
                except: pass
        clear_undo_stack(idx)
        del log_data[idx]
        step_objects.pop(idx, None)
        step_crops.pop(idx, None)
        n = len(log_data)
        for i in range(idx, n):
            if (i + 1) in step_objects:
                step_objects[i] = step_objects.pop(i + 1)
            if (i + 1) in step_crops:
                step_crops[i] = step_crops.pop(i + 1)
            if (i + 1) in undo_stacks:
                undo_stacks[i] = undo_stacks.pop(i + 1)
        _renumber_and_rebuild()

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


class ListCard:
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
        flat = _flatten_to_pil(self.index)
        if flat is None:
            return
        flat.thumbnail((LIST_THUMB_W, 68), Image.LANCZOS)
        self._photo = ImageTk.PhotoImage(flat)
        self._thumb_label.configure(image=self._photo)

    def _delete(self):
        if not messagebox.askyesno("Delete Step", f"Delete Step {log_data[self.index]['step']}?"):
            return
        idx = self.index
        screenshot = log_data[idx].get("screenshot")
        if screenshot:
            img_path = os.path.join(current_session, screenshot)
            if os.path.exists(img_path):
                try: os.remove(img_path)
                except: pass
        clear_undo_stack(idx)
        del log_data[idx]
        step_objects.pop(idx, None)
        step_crops.pop(idx, None)
        n = len(log_data)
        for i in range(idx, n):
            if (i + 1) in step_objects: step_objects[i] = step_objects.pop(i + 1)
            if (i + 1) in step_crops:   step_crops[i]   = step_crops.pop(i + 1)
            if (i + 1) in undo_stacks:  undo_stacks[i]  = undo_stacks.pop(i + 1)
        _renumber_and_rebuild()

    def delete_selected(self): pass
    def reload_image(self): pass
    def _refresh_undo_btn(self): pass
    def update_header(self): pass


# ══════════════════════════════════════ GRID CARD ══════════════════════════════════════

GRID_TILE_W = 260


class GridCard:
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
        flat = _flatten_to_pil(self.index)
        if flat is None:
            return
        flat.thumbnail((GRID_TILE_W-4, 150), Image.LANCZOS)
        self._photo = ImageTk.PhotoImage(flat)
        self._thumb_label.configure(image=self._photo)

    def _delete(self):
        if not messagebox.askyesno("Delete Step", f"Delete Step {log_data[self.index]['step']}?"):
            return
        idx = self.index
        screenshot = log_data[idx].get("screenshot")
        if screenshot:
            img_path = os.path.join(current_session, screenshot)
            if os.path.exists(img_path):
                try: os.remove(img_path)
                except: pass
        clear_undo_stack(idx)
        del log_data[idx]
        step_objects.pop(idx, None)
        step_crops.pop(idx, None)
        n = len(log_data)
        for i in range(idx, n):
            if (i + 1) in step_objects: step_objects[i] = step_objects.pop(i + 1)
            if (i + 1) in step_crops:   step_crops[i]   = step_crops.pop(i + 1)
            if (i + 1) in undo_stacks:  undo_stacks[i]  = undo_stacks.pop(i + 1)
        _renumber_and_rebuild()

    def delete_selected(self): pass
    def reload_image(self): pass
    def _refresh_undo_btn(self): pass
    def update_header(self): pass


# ══════════════════════════════════════ CARD MANAGEMENT ══════════════════════════════════════

def _clear_cards():
    _card_drag_cleanup()
    for card in step_cards:
        try:    card.outer.destroy()
        except: pass
    step_cards.clear()
    for child in list(cards_inner.winfo_children()):
        try: child.destroy()
        except: pass


def _build_all_cards():
    _clear_cards()
    if view_mode == "grid":
        _grid_frame = ctk.CTkFrame(cards_inner, fg_color="transparent")
        _grid_frame.pack(fill="both", expand=True)
        cols = max(1, (cards_scroll.winfo_width() - 30) // (GRID_TILE_W + 12))
        for i in range(len(log_data)):
            card = GridCard(_grid_frame, i)
            r, c = divmod(i, cols)
            card.outer.grid(row=r, column=c, padx=6, pady=6, sticky="n")
            step_cards.append(card)
    elif view_mode == "list":
        for i in range(len(log_data)):
            step_cards.append(ListCard(cards_inner, i))
    else:
        for i in range(len(log_data)):
            step_cards.append(StepCard(cards_inner, i))
    _refresh_sidebar()
    root.after(30, _reset_cards_scroll)


def _reset_cards_scroll():
    """Force the scrollable frame to recalculate its region and scroll to top."""
    try:
        canvas = cards_scroll._parent_canvas
        canvas.update_idletasks()
        canvas.configure(scrollregion=canvas.bbox("all"))
        canvas.yview_moveto(0.0)
    except:
        pass


def _append_card():
    i = len(log_data) - 1
    if view_mode == "default":
        step_cards.append(StepCard(cards_inner, i))
    elif view_mode == "list":
        step_cards.append(ListCard(cards_inner, i))
    else:
        _build_all_cards()
        return
    _refresh_sidebar()
    root.after(80, lambda: cards_scroll._parent_canvas.yview_moveto(1.0))


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

_sidebar_drag = {"active": False, "src": -1, "dst": -1, "line": None}


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
    if not log_data:
        return
    idx = sidebar_list.nearest(event.y)
    if idx < 0 or idx >= len(log_data):
        return
    _sidebar_drag["src"]    = idx
    _sidebar_drag["dst"]    = idx
    _sidebar_drag["active"] = False
    sidebar_list.selection_clear(0, tk.END)
    sidebar_list.selection_set(idx)
    _scroll_to_card(idx)


def _sidebar_motion(event):
    src = _sidebar_drag["src"]
    if src < 0 or not log_data:
        return
    _sidebar_drag["active"] = True
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
    _sidebar_drag["active"] = False
    _sidebar_drag["src"]    = -1
    _sidebar_drag["dst"]    = -1
    _sidebar_hide_line()
    for i in range(sidebar_list.size()):
        sidebar_list.itemconfigure(i, fg=C["text"])
    if not was_drag or src < 0 or not log_data:
        return
    dst = max(0, min(dst, len(log_data) - 1))
    if src != dst:
        _reorder_step(src, dst)


def _sidebar_context(event):
    menu = tk.Menu(root, tearoff=0, bg=C["surface"], fg=C["text"],
                   activebackground=C["acc_dark"], activeforeground="#fff",
                   font=("Segoe UI", 10), borderwidth=1, relief="solid")
    if not log_data:
        menu.add_command(label="Insert step here",
                         command=lambda: insert_custom_step())
    else:
        idx = sidebar_list.nearest(event.y)
        idx = max(0, min(idx, len(log_data) - 1))
        menu.add_command(label="Insert step above",
                         command=lambda i=idx: insert_custom_step(after_index=i-1 if i > 0 else -1))
        menu.add_command(label="Insert step below",
                         command=lambda i=idx: insert_custom_step(after_index=i))
    menu.post(event.x_root, event.y_root)


# ══════════════════════════════════════ CARD CONTEXT MENU ══════════════════════════════════════

def _card_context_menu(index, event):
    """Right-click menu on a card: insert step above / below."""
    idx = max(0, min(index, len(log_data) - 1))
    menu = tk.Menu(root, tearoff=0, bg=C["surface"], fg=C["text"],
                   activebackground=C["acc_dark"], activeforeground="#fff",
                   font=("Segoe UI", 10), borderwidth=1, relief="solid")
    menu.add_command(label="Insert step above",
                     command=lambda: insert_custom_step(after_index=idx - 1 if idx > 0 else -1))
    menu.add_command(label="Insert step below",
                     command=lambda: insert_custom_step(after_index=idx))
    menu.post(event.x_root, event.y_root)


def _bind_card_context(card):
    """Bind right-click context menu recursively to a card and all its descendants."""
    def _on_right(event):
        _card_context_menu(card.index, event)
    def _bind_recursive(widget):
        try: widget.bind("<Button-3>", _on_right)
        except: pass
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
        except: pass
    _card_drag["ghost"] = None

    line = _card_drag.pop("line", None)
    if line:
        try: line.destroy()
        except: pass
    _card_drag["line"] = None

    hi = _card_drag.get("hi_card", -1)
    if 0 <= hi < len(step_cards):
        try: step_cards[hi].outer.configure(border_color=C["border"])
        except: pass
    _card_drag["hi_card"] = -1

    src = _card_drag.get("src", -1)
    if 0 <= src < len(step_cards):
        try: step_cards[src].outer.configure(fg_color=C["card"], border_color=C["border"])
        except: pass

    _card_drag["active"] = False
    _card_drag["src"]    = -1
    _card_drag["dst"]    = -1


def _card_drag_start(index, event):
    _card_drag["src"]    = index
    _card_drag["active"] = False


def _card_drop_index(x_root, y_root):
    """Determine insertion index by checking midpoints of each card."""
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
            except:
                pass
        return best
    for i, card in enumerate(step_cards):
        try:
            wy = card.outer.winfo_rooty()
            wh = card.outer.winfo_height()
            if y_root < wy + wh // 2:
                return i
        except:
            pass
    return len(step_cards) - 1


def _card_show_drop_line(dst):
    """Show drop feedback: horizontal line for list/default, border highlight for grid."""
    if not step_cards:
        return

    if view_mode == "grid":
        prev_hi = _card_drag.get("hi_card", -1)
        if prev_hi != dst and 0 <= prev_hi < len(step_cards):
            try: step_cards[prev_hi].outer.configure(border_color=C["border"])
            except: pass
        _card_drag["hi_card"] = dst
        if 0 <= dst < len(step_cards):
            try: step_cards[dst].outer.configure(border_color=C["accent"])
            except: pass
        return

    line = _card_drag.get("line")
    if line is None or not line.winfo_exists():
        line = tk.Frame(cards_inner, height=_DROP_LINE_H, bg=C["accent"])
        _card_drag["line"] = line

    target = step_cards[min(dst, len(step_cards) - 1)]
    try:
        target.outer.update_idletasks()
        ty = target.outer.winfo_y()
        tw = target.outer.winfo_width()
        if dst >= len(step_cards):
            ty = target.outer.winfo_y() + target.outer.winfo_height() + 4
        line.place(in_=cards_inner, x=6, y=ty - 4, width=tw - 12, height=_DROP_LINE_H)
        line.lift()
    except:
        line.place_forget()


def _card_hide_drop_line():
    line = _card_drag.get("line")
    if line:
        try: line.place_forget()
        except: pass

    hi = _card_drag.get("hi_card", -1)
    if 0 <= hi < len(step_cards):
        try: step_cards[hi].outer.configure(border_color=C["border"])
        except: pass
    _card_drag["hi_card"] = -1


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
    except:
        pass


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
            except: pass

    ghost.geometry(f"+{event.x_root + 16}+{event.y_root - 12}")
    ghost.lift()

    dst = _card_drop_index(event.x_root, event.y_root)
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


def _set_view_mode(mode):
    global view_mode
    view_mode = mode
    for btn, m in view_mode_btns:
        btn.configure(
            fg_color=C["acc_dark"] if m == mode else "transparent",
            border_color=C["accent"] if m == mode else C["border"])
    _build_all_cards()


# ══════════════════════════════════════ PROJECT NAME ══════════════════════════════════════

def _apply_project_name():
    global project_name
    project_name = project_name_var.get().strip()
    if current_session:
        save_steps()
    root.title(f"PSR Pro — {project_name}" if project_name else "PSR Pro — Process Step Recorder")


# ══════════════════════════════════════ RECORDING ACTIONS ══════════════════════════════════════

def _prompt_project_name():
    """Show a dialog to name the project before recording. Returns the name or None to cancel."""
    ts_default = datetime.now().strftime("Recording %Y-%m-%d %H:%M")
    dlg = ctk.CTkToplevel(root)
    dlg.title("New Recording")
    dlg.geometry("440x180")
    dlg.resizable(False, False)
    dlg.transient(root)
    dlg.grab_set()

    result = [None]

    ctk.CTkLabel(dlg, text="Project Name",
        font=("Segoe UI", 14, "bold"), text_color=C["text"]
    ).pack(padx=24, pady=(20,4), anchor="w")
    ctk.CTkLabel(dlg, text="Used for the folder name and export filenames.",
        font=("Segoe UI", 10), text_color=C["muted"]
    ).pack(padx=24, anchor="w")

    name_var = tk.StringVar(value=project_name_var.get().strip() or ts_default)
    name_entry = ctk.CTkEntry(dlg, textvariable=name_var, width=392,
        font=("Segoe UI", 12), fg_color=C["surface"],
        border_color=C["border"], text_color=C["text"])
    name_entry.pack(padx=24, pady=(10,14))
    name_entry.select_range(0, tk.END)
    name_entry.focus_force()

    btn_row = ctk.CTkFrame(dlg, fg_color="transparent")
    btn_row.pack(fill="x", padx=24, pady=(0,16))

    def do_ok(event=None):
        result[0] = name_var.get().strip() or ts_default
        dlg.destroy()
    def do_cancel():
        dlg.destroy()

    ctk.CTkButton(btn_row, text="Start Recording", command=do_ok,
        fg_color=C["accent"], hover_color=C["acc_dark"],
        width=140, height=32).pack(side="right", padx=(8,0))
    ctk.CTkButton(btn_row, text="Cancel", command=do_cancel,
        fg_color="transparent", hover_color=C["surface"], border_width=1,
        border_color=C["border"], text_color=C["muted"],
        width=90, height=32).pack(side="right")

    name_entry.bind("<Return>", do_ok)
    dlg.bind("<Escape>", lambda e: do_cancel())

    dlg.wait_window()
    return result[0]


def start_recording():
    global recording, step_counter, log_data, project_name
    name = _prompt_project_name()
    if name is None:
        return
    project_name = name
    project_name_var.set(project_name)
    root.title(f"PSR Pro — {project_name}")

    create_session()
    log_data.clear()
    step_objects.clear()
    step_crops.clear()
    step_counter = 1
    recording    = True
    _set_status("● RECORDING — screenshot taken on every mouse release", C["danger"])
    btn_start.configure(state="disabled")
    btn_stop.configure(state="normal")
    btn_continue.configure(state="disabled")
    _build_all_cards()
    threading.Thread(target=start_listeners, daemon=True).start()


def stop_recording():
    global recording
    recording = False
    stop_listeners()
    save_steps()
    _set_status(f"◼  Stopped — {len(log_data)} steps saved", C["muted"])
    btn_start.configure(state="normal")
    btn_stop.configure(state="disabled")
    btn_continue.configure(state="normal" if (current_session and log_data) else "disabled")


def continue_recording():
    global recording
    if not current_session or not log_data:
        return
    recording = True
    _set_status("● RECORDING (continued)", C["danger"])
    btn_start.configure(state="disabled")
    btn_stop.configure(state="normal")
    btn_continue.configure(state="disabled")
    threading.Thread(target=start_listeners, daemon=True).start()


def load_recording():
    global log_data, current_session, step_counter, project_name
    folder = filedialog.askdirectory(initialdir=BASE_DIR, title="Open Recording")
    if not folder: return
    json_path = os.path.join(folder, "steps.json")
    if not os.path.exists(json_path):
        messagebox.showerror("Error", "No steps.json found."); return
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
    btn_continue.configure(state="normal" if log_data else "disabled")


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
                desc_html = entry['description'].replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
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
                desc_html = entry['description'].replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
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
            pdf.cell(0, 9, _pdf_safe(entry["description"][:120]), new_x="LMARGIN", new_y="NEXT")

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
            except: pass

    _set_status("✔  PDF report exported", C["success"])
    _open_folder(report_path)


# ══════════════════════════════════════ STATUS ══════════════════════════════════════

def _set_status(text, color):
    status_label.configure(text=text, text_color=color)


# ══════════════════════════════════════ GUI ══════════════════════════════════════

root = ctk.CTk()
root.title("PSR Pro — Process Step Recorder")
root.geometry("1500x900")
root.minsize(960, 640)
root.configure(fg_color=C["bg"])


# ── Toolbar ───────────────────────────────────────────────────────────────────────

toolbar = ctk.CTkFrame(root, height=58, corner_radius=0, fg_color=C["panel"])
toolbar.pack(side="top", fill="x")
toolbar.pack_propagate(False)
_B = dict(height=36, corner_radius=6, font=("Segoe UI", 11, "bold"), border_width=0)

btn_start = ctk.CTkButton(toolbar, text="▶  Start", command=start_recording,
    fg_color=C["success"], hover_color="#1d7a43", width=100, **_B)
btn_start.pack(side="left", padx=(12,3), pady=11)

btn_stop = ctk.CTkButton(toolbar, text="■  Stop", command=stop_recording,
    fg_color=C["danger"], hover_color="#a02020", width=100, state="disabled", **_B)
btn_stop.pack(side="left", padx=3, pady=11)

btn_continue = ctk.CTkButton(toolbar, text="⏩  Continue", command=continue_recording,
    fg_color=C["warn"], hover_color="#b05a10", width=120, state="disabled", **_B)
btn_continue.pack(side="left", padx=3, pady=11)

ctk.CTkButton(toolbar, text="📂  Open", command=load_recording,
    fg_color=C["surface"], hover_color="#333", width=100, **_B
).pack(side="left", padx=(10,3), pady=11)

ctk.CTkButton(toolbar, text="＋  Step", command=lambda: insert_custom_step(),
    fg_color=C["surface"], hover_color="#1d7a43", width=100, **_B
).pack(side="left", padx=3, pady=11)

# ── Capture mode ──────────────────────────────────────────────────────────────────

ctk.CTkLabel(toolbar, text="│", text_color=C["border"], width=14).pack(side="left")
ctk.CTkLabel(toolbar, text="Capture:", font=("Segoe UI", 10),
             text_color=C["muted"]).pack(side="left", padx=(4,6))

_cap_click_var  = tk.BooleanVar(value=True)
_cap_hotkey_var = tk.BooleanVar(value=False)

def _sync_capture_mode(*_):
    global capture_on_click, capture_on_hotkey
    capture_on_click  = _cap_click_var.get()
    capture_on_hotkey = _cap_hotkey_var.get()

_cap_click_var.trace_add("write", _sync_capture_mode)
_cap_hotkey_var.trace_add("write", _sync_capture_mode)

ctk.CTkCheckBox(toolbar, text="Per click",
    variable=_cap_click_var, font=("Segoe UI", 10), text_color=C["text"],
    fg_color=C["accent"], hover_color=C["acc_dark"], border_color=C["border"],
    height=36, checkbox_width=16, checkbox_height=16, corner_radius=4
).pack(side="left", padx=(0,6), pady=11)

ctk.CTkCheckBox(toolbar, text="Per Scroll Lock",
    variable=_cap_hotkey_var, font=("Segoe UI", 10), text_color=C["text"],
    fg_color=C["accent"], hover_color=C["acc_dark"], border_color=C["border"],
    height=36, checkbox_width=16, checkbox_height=16, corner_radius=4
).pack(side="left", padx=(0,4), pady=11)

# ── Project name ──────────────────────────────────────────────────────────────────

ctk.CTkLabel(toolbar, text="Project:", font=("Segoe UI", 10),
             text_color=C["muted"]).pack(side="left", padx=(16,4))
project_name_var = tk.StringVar(value="")
project_name_entry = ctk.CTkEntry(
    toolbar, textvariable=project_name_var,
    placeholder_text="Untitled recording",
    width=240, height=34, corner_radius=6,
    fg_color=C["surface"], border_width=1, border_color=C["border"],
    font=("Segoe UI", 11), text_color=C["text"])
project_name_entry.pack(side="left", padx=3, pady=12)
project_name_entry.bind("<Return>",   lambda e: (_apply_project_name(), root.focus()))
project_name_entry.bind("<FocusOut>", lambda e:  _apply_project_name())

# ── Export buttons ────────────────────────────────────────────────────────────────

ctk.CTkButton(toolbar, text="🌐  HTML", command=export_html,
    fg_color=C["surface"], hover_color="#333", width=100, **_B
).pack(side="right", padx=(3,12), pady=11)
ctk.CTkButton(toolbar, text="📄  PDF", command=export_pdf,
    fg_color=C["acc_dark"], hover_color=C["accent"], width=100, **_B
).pack(side="right", padx=3, pady=11)


# ── Tool strip ────────────────────────────────────────────────────────────────────

tool_strip = ctk.CTkFrame(root, height=50, corner_radius=0, fg_color=C["surface"])
tool_strip.pack(side="top", fill="x")
tool_strip.pack_propagate(False)

ctk.CTkLabel(tool_strip, text="TOOLS", font=("Segoe UI", 9, "bold"),
             text_color=C["muted"], width=54).pack(side="left", padx=(14,4))

_TB = dict(height=30, corner_radius=5, font=("Segoe UI", 11), border_width=1, width=126)

btn_pointer = ctk.CTkButton(tool_strip, text="🖱  Pointer (V)",
    fg_color=C["acc_dark"], border_color=C["accent"], hover_color=C["acc_dark"],
    command=lambda: set_tool("none"), **_TB)
btn_pointer.pack(side="left", padx=3, pady=10)

btn_highlight = ctk.CTkButton(tool_strip, text="🔴  Highlight (U)",
    fg_color="transparent", border_color=C["border"], hover_color="#4a1010",
    command=lambda: set_tool("highlight"), **_TB)
btn_highlight.pack(side="left", padx=3, pady=10)

btn_redact = ctk.CTkButton(tool_strip, text="⬛  Redact (M)",
    fg_color="transparent", border_color=C["border"], hover_color="#1a1a1a",
    command=lambda: set_tool("redact"), **_TB)
btn_redact.pack(side="left", padx=3, pady=10)

btn_crop = ctk.CTkButton(tool_strip, text="✂  Crop (C)",
    fg_color="transparent", border_color=C["border"], hover_color="#3a3010",
    command=lambda: set_tool("crop"), **_TB)
btn_crop.pack(side="left", padx=3, pady=10)

btn_draw = ctk.CTkButton(tool_strip, text="✏  Draw (B)",
    fg_color="transparent", border_color=C["border"], hover_color="#1a2a1a",
    command=lambda: set_tool("draw"), **_TB)
btn_draw.pack(side="left", padx=3, pady=10)

ctk.CTkLabel(tool_strip, text="│", text_color=C["border"], width=14).pack(side="left")

# Colour swatches
_SWATCHES = [
    ("#e74c3c","Red"), ("#e67e22","Orange"), ("#f1c40f","Yellow"),
    ("#2ecc71","Green"), ("#3d8ef0","Blue"), ("#ffffff","White"), ("#111111","Black"),
]
for hex_col, lbl in _SWATCHES:
    sw = ctk.CTkButton(tool_strip, text="", width=22, height=22, corner_radius=11,
        fg_color=hex_col, hover_color=hex_col,
        border_width=1, border_color="#555555",
        command=lambda c=hex_col: _set_draw_color_global(c))
    sw.pack(side="left", padx=2, pady=14)
    draw_color_btns.append((sw, hex_col))
draw_color_btns[0][0].configure(border_width=2, border_color="#ffffff")

ctk.CTkLabel(tool_strip, text="│", text_color=C["border"], width=14).pack(side="left")

# Pen sizes
for label, px in (("S",2),("M",5),("L",10),("XL",18)):
    pb = ctk.CTkButton(tool_strip, text=label, width=34, height=28, corner_radius=5,
        fg_color=C["acc_dark"] if label=="S" else "transparent",
        border_width=1,
        border_color=C["accent"] if label=="S" else C["border"],
        hover_color=C["acc_dark"],
        font=("Segoe UI", 10, "bold"),
        command=lambda w=px: _set_draw_width_global(w))
    pb.pack(side="left", padx=2, pady=10)
    pen_size_btns.append((pb, px))

status_label = ctk.CTkLabel(tool_strip, text="◼  Ready",
    font=("Segoe UI", 10, "bold"), text_color=C["muted"])
status_label.pack(side="right", padx=16)

ctk.CTkLabel(tool_strip, text="│", text_color=C["border"], width=14).pack(side="right")
ctk.CTkLabel(tool_strip, text="VIEW", font=("Segoe UI", 8, "bold"),
             text_color=C["muted"]).pack(side="right", padx=(4,2))

_VB = dict(height=26, corner_radius=4, font=("Segoe UI", 9), border_width=1, width=56)
for vlbl, vmode in (("Detail", "default"), ("List", "list"), ("Grid", "grid")):
    vb = ctk.CTkButton(tool_strip, text=vlbl,
        fg_color=C["acc_dark"] if vmode == "default" else "transparent",
        border_color=C["accent"] if vmode == "default" else C["border"],
        hover_color=C["acc_dark"],
        command=lambda m=vmode: _set_view_mode(m), **_VB)
    vb.pack(side="right", padx=2, pady=12)
    view_mode_btns.append((vb, vmode))


# ── Body ──────────────────────────────────────────────────────────────────────────

body = ctk.CTkFrame(root, corner_radius=0, fg_color=C["bg"])
body.pack(fill="both", expand=True, padx=10, pady=(8,10))

sidebar = ctk.CTkFrame(body, width=268, corner_radius=8, fg_color=C["panel"])
sidebar.pack(side="left", fill="y", padx=(0,8))
sidebar.pack_propagate(False)

shdr = ctk.CTkFrame(sidebar, height=36, fg_color=C["surface"], corner_radius=0)
shdr.pack(fill="x"); shdr.pack_propagate(False)
ctk.CTkLabel(shdr, text="STEPS", font=("Segoe UI", 9, "bold"),
             text_color=C["muted"]).pack(side="left", padx=14, pady=8)
count_label = ctk.CTkLabel(shdr, text="0 steps", font=("Segoe UI", 9),
                            text_color=C["muted"])
count_label.pack(side="right", padx=14)

sidebar_list = tk.Listbox(sidebar, bg=C["panel"], fg=C["text"],
    selectbackground=C["acc_dark"], selectforeground="#fff",
    font=("Segoe UI", 9), borderwidth=0, relief="flat",
    highlightthickness=0, activestyle="none")
sidebar_list.pack(fill="both", expand=True, padx=4, pady=4)
sidebar_list.bind("<ButtonPress-1>",   _sidebar_press)
sidebar_list.bind("<B1-Motion>",       _sidebar_motion)
sidebar_list.bind("<ButtonRelease-1>", _sidebar_release)
sidebar_list.bind("<Button-3>",        _sidebar_context)

_dnd_hint = ctk.CTkLabel(sidebar, text="drag to reorder  ·  right-click to insert",
    font=("Segoe UI", 8), text_color=C["muted"], height=20)
_dnd_hint.pack(fill="x", padx=8, pady=(0,6))

right_frame = ctk.CTkFrame(body, corner_radius=8, fg_color=C["panel"])
right_frame.pack(side="right", fill="both", expand=True)
cards_scroll = ctk.CTkScrollableFrame(right_frame, corner_radius=0, fg_color=C["bg"],
    scrollbar_button_color=C["border"], scrollbar_button_hover_color=C["accent"])
cards_scroll.pack(fill="both", expand=True, padx=10, pady=10)
cards_inner = cards_scroll


# ══════════════════════════════════════ KEYBOARD SHORTCUTS ══════════════════════════

def _on_root_key(event):
    if event.keysym in ("Delete", "BackSpace"):
        card = active_card_ref[0]
        if card is not None and not card.is_text_only:
            card.delete_selected()
            return "break"


def _on_tool_hotkey(event):
    focus = root.focus_get()
    if focus:
        wclass = focus.winfo_class()
        if wclass in ('Text', 'Entry', 'TEntry', 'Spinbox', 'TSpinbox'):
            return
    _TOOL_KEYS = {'v': 'none', 'u': 'highlight', 'm': 'redact', 'c': 'crop', 'b': 'draw'}
    tool = _TOOL_KEYS.get(event.char.lower())
    if tool:
        set_tool(tool)
        return "break"


def _on_undo(event=None):
    focus = root.focus_get()
    if focus:
        wclass = focus.winfo_class()
        if wclass in ('Text', 'Entry', 'TEntry', 'Spinbox', 'TSpinbox'):
            return
    card = active_card_ref[0]
    if card is not None and not card.is_text_only:
        card._undo()
        return "break"


root.bind("<Delete>",    _on_root_key)
root.bind("<BackSpace>", _on_root_key)
root.bind("<Control-v>", _handle_paste)
root.bind("<Control-z>", _on_undo)
for _hk in ('v', 'u', 'm', 'c', 'b'):
    root.bind(f"<KeyPress-{_hk}>", _on_tool_hotkey)
    root.bind(f"<KeyPress-{_hk.upper()}>", _on_tool_hotkey)


# ══════════════════════════════════════ START ══════════════════════════════════════

root.after(100, process_queue)
root.after(300, _setup_dnd)
root.mainloop()
