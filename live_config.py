#!/usr/bin/env python3
from __future__ import annotations

import json
import os
from typing import Optional, Dict, Any

DEFAULT_CONFIG_PATH = "live_config.json"
DEFAULT_BG_PATH = "live_bg.png"


def load_json(path: str) -> Optional[Dict[str, Any]]:
    if not path or not os.path.exists(path):
        return None
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_json(path: str, data: Dict[str, Any]) -> None:
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def build_live_config(
    panel_aoi: Dict[str, int],
    presence_params: Dict[str, Any],
    roi_project_path: Optional[str],
    bg_path: Optional[str],
    bg_shape: Optional[list],
    decode_params: Dict[str, Any],
) -> Dict[str, Any]:
    return {
        "panel_aoi": {
            "x": int(panel_aoi.get("x", 0)),
            "y": int(panel_aoi.get("y", 0)),
            "w": int(panel_aoi.get("w", 0)),
            "h": int(panel_aoi.get("h", 0)),
        },
        "presence_params": {
            "diff_threshold": int(presence_params.get("diff_threshold", 18)),
            "occupancy_threshold": float(presence_params.get("occupancy_threshold", 0.10)),
            "debounce_on": int(presence_params.get("debounce_on", 4)),
            "debounce_off": int(presence_params.get("debounce_off", 6)),
            "blur_ksize": int(presence_params.get("blur_ksize", 5)),
            "morph_ksize": int(presence_params.get("morph_ksize", 5)),
        },
        "roi_project": roi_project_path,
        "bg": {"path": bg_path, "shape": bg_shape},
        "decode_params": decode_params or {}
    }
