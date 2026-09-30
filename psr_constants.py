"""PSR Pro — shared constants (theme, sizes). No app imports."""

import os
import sys

# "Viewfinder" palette — cool near-black surfaces, one electric-blue accent, record-red for capture
C = {
    "bg":       "#0b0d12",
    "panel":    "#12151c",
    "surface":  "#1a1e28",
    "surface2": "#232938",
    "card":     "#141821",
    "border":   "#252b3a",
    "border_hi":"#343c52",
    "accent":   "#4d9bff",
    "acc_dark": "#2b6fd6",
    "acc_soft": "#15274a",
    "danger":   "#ff5468",
    "success":  "#2fd08a",
    "warn":     "#ffb454",
    "text":     "#e8ecf4",
    "muted":    "#8b95ab",
    "faint":    "#566078",
    "crop_col": "#f0c040",
}

# Segoe Fluent Icons code points (Windows 11; Segoe MDL2 Assets on Windows 10 has the same ones)
ICON = {
    "pointer": "", "highlight": "", "redact": "", "blur": "",
    "crop": "", "draw": "", "arrow": "", "text": "", "marker": "",
    "undo": "", "delete": "", "add": "", "fit": "", "full": "",
    "open": "", "record": "", "play": "", "stop": "", "pause": "",
    "settings": "", "chevron_down": "", "globe": "", "doc": "",
    "image": "", "note": "", "reset": "", "palette": "", "clock": "",
}

HANDLE_SZ = 6
HANDLE_HIT = 9
# Anchored to the app location so recordings do not depend on the launch directory
_APP_DIR = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
BASE_DIR = os.path.join(_APP_DIR, "recordings")
CAPTURE_MAX_W = 1920  # cap screenshot width — matches Windows Steps Recorder behaviour
