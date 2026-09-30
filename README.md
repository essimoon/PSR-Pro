# PSR Pro — Process Step Recorder

A professional offline tool for recording and documenting workflows — think Windows Steps Recorder, but actually good.

## Install

```bash
pip install -r requirements.txt
python main.py
```

## Usage

| Action | How |
|--------|-----|
| **Start** | ▶ Start — every mouse click is captured as a step with a screenshot (a red ring marks the click) |
| **Stop / Pause / Tray** | `F6` / `F7` / `F8` (global hotkeys while recording) |
| **Browse steps** | Filmstrip on the left — click, `↑`/`↓`, drag to reorder, right-click for more |
| **Zoom / pan** | Mouse wheel zooms, drag the image (or middle mouse) pans, double-click / *Fit* resets |
| **Annotate** | Tool rail on the left: `V` pointer · `U` highlight · `A` arrow · `T` text · `N` numbered marker · `B` pen · `M` redact · `X` pixelate · `C` crop. Colour and size appear above the image. |
| **Numbers** | Drop numbered markers with `N` — each one gets a note field next to the description. The notes appear as a legend in HTML and PDF. |
| **Edit text** | Type in the box under the image — saved automatically |
| **Add steps** | `＋ Step`, paste an image/text with `Ctrl+V`, or drop files onto the window |
| **Export** | 🌐 HTML (single portable file) or 📄 PDF |
| **Open old session** | 📂 Open (`Ctrl+O`) or pick one from the home screen |

## Notes

- **Redact** permanently blacks out the selected region — use before sharing screenshots with sensitive info
- **Highlight** draws a red box to draw attention to a UI element
- The HTML report embeds all screenshots as base64, so it's a **single file** you can email or share
- All data stays **100% offline** — nothing leaves your machine

## Packaging (optional)

To distribute as a standalone `.exe`:

```bash
pip install pyinstaller
pyinstaller --onefile --windowed --name "PSR Pro" main.py
```
