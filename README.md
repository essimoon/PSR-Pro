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
| **Start** | Click ▶ Start — every mouse click and keyboard shortcut is captured as a step with a screenshot |
| **Stop** | Click ■ Stop — session is auto-saved to `recordings/<timestamp>/` |
| **Annotate** | Select a step → choose 🔴 Highlight or ⬛ Redact → drag a box on the screenshot |
| **Edit** | Click a step, edit the description, click 💾 Save Description |
| **Delete** | Select a step → 🗑 Delete Step |
| **Export** | 🌐 HTML (single portable file, dark theme) or 📄 PDF (landscape A4, cover page) |
| **Open old session** | 📂 Open → pick any folder inside `recordings/` |

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
