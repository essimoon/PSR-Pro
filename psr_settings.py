"""PSR Pro — recording settings load/save (pure I/O). No app globals."""

from __future__ import annotations

import json
import os
import sys
import logging

logger = logging.getLogger(__name__)

SETTINGS_FILENAME = "psr_pro_settings.json"


def get_settings_path() -> str:
    if getattr(sys, "frozen", False):
        base = os.path.dirname(sys.executable)
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, SETTINGS_FILENAME)


def load_settings() -> dict | None:
    """Return settings dict from disk, or None if missing/invalid."""
    path = get_settings_path()
    if not os.path.isfile(path):
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        logger.exception("Failed to load settings from %s: %s", path, e)
        return None


def save_settings(data: dict) -> None:
    """Write settings dict to disk."""
    path = get_settings_path()
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception as e:
        logger.exception("Failed to save settings to %s: %s", path, e)
