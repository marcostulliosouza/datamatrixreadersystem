#!/usr/bin/env python3
"""
DataMatrix Reader - Live Trigger (AOI + ROIs) - IMPROVED

✅ Edição de ROIs com mouse: arrastar, redimensionar, rotacionar
✅ Salvamento UNIFICADO: um único botão salva TUDO (camera, decode, trigger, ROIs, BG, AOI, processing)
✅ Trigger por ocupação (AOI) + ROIs fixos do projeto
✅ DEBUG: mosaico do último trigger (não pisca) + opções (mask/raw/processed)
✅ PERFORMANCE: Decode em paralelo + escolha do frame mais nítido
"""

from __future__ import annotations

import json
import base64
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import deque
from dataclasses import dataclass, asdict
from datetime import datetime
from typing import Optional, Tuple, Dict, Any, List
import math

import cv2
import numpy as np
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from PIL import Image, ImageTk
from tkinter import simpledialog
import re
from queue import Queue, Empty
import os

from camera_controller import BaslerCameraController
from decoder import DataMatrixDecoder, ImagePreprocessor
from panel_presence import PanelPresenceDetector, PresenceParams
from live_config import load_json, save_json, DEFAULT_CONFIG_PATH
import cmcontrol_mqtt
from cmcontrol_mqtt import CmControlMqttClient
import login



# ---------------- ROI project loader ----------------

@dataclass
class ROI:
    id: int
    cx: float
    cy: float
    w: float
    h: float
    angle: float = 0.0

    def contains_point(self, x: float, y: float, tolerance: float = 8.0) -> bool:
        pts = self.get_rect_points().astype(np.float32)
        return cv2.pointPolygonTest(pts, (float(x), float(y)), True) >= -float(tolerance)

    def get_rect_points(self) -> np.ndarray:
        rect = ((self.cx, self.cy), (self.w, self.h), self.angle)
        box = cv2.boxPoints(rect)
        return box.astype(np.int32)

    def get_corner_positions(self) -> List[Tuple[float, float]]:
        """Retorna os 4 cantos da ROI em ordem: TL, TR, BR, BL"""
        box = self.get_rect_points()
        return [(float(box[i][0]), float(box[i][1])) for i in range(4)]

    def distance_to_corner(self, x: float, y: float, corner_idx: int) -> float:
        """Distância de (x,y) até um canto específico"""
        corners = self.get_corner_positions()
        cx, cy = corners[corner_idx]
        return math.sqrt((x - cx) ** 2 + (y - cy) ** 2)

    def nearest_corner(self, x: float, y: float) -> int:
        """Retorna o índice do canto mais próximo de (x,y)"""
        corners = self.get_corner_positions()
        dists = [math.sqrt((x - cx) ** 2 + (y - cy) ** 2) for cx, cy in corners]
        return int(np.argmin(dists))


def load_rois_from_project_json(path: str) -> Tuple[str, List[ROI], Dict[str, Any]]:
    """
    Lê projeto ROI do json (mesmo formato do roi_manager).
    Retorna: (project_name, rois, processing_params)
    """
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)

    pname = data.get("project_name") or data.get("name") or os.path.basename(path)

    rois_data = data.get("rois") or data.get("ROIs") or []
    rois: List[ROI] = []
    for i, r in enumerate(rois_data, 1):
        rois.append(
            ROI(
                id=int(r.get("id", i)),
                cx=float(r.get("cx", r.get("x", 0))),
                cy=float(r.get("cy", r.get("y", 0))),
                w=float(r.get("w", r.get("width", 0))),
                h=float(r.get("h", r.get("height", 0))),
                angle=float(r.get("angle", 0.0)),
            )
        )

    processing = data.get("processing") or {}
    return pname, rois, processing


# ---------------- UI helpers ----------------

class _ZoomPan:
    def __init__(self):
        self.scale = 1.0
        self.min_scale = 0.2
        self.max_scale = 8.0
        self.offx = 0.0
        self.offy = 0.0
        self._dragging = False
        self._lastx = 0
        self._lasty = 0

    def reset(self):
        self.scale = 1.0
        self.offx = 0.0
        self.offy = 0.0

    def clamp(self):
        self.scale = float(np.clip(self.scale, self.min_scale, self.max_scale))


# ---------------- Main GUI ----------------

class LiveModeTriggerGUI:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("DataMatrix Reader - Live Trigger (ROI Editor + Unified Save)")
        self.root.geometry("1650x930")

        # =========================
        # Login
        # =========================

        self.login = login

        # =========================
        # Locks / runtime cfg
        # =========================
        self._cfg_lock = threading.Lock()
        self._runtime_cfg = {}

        # =========================
        # Engine
        # =========================
        self.camera = BaslerCameraController()
        self.decoder = DataMatrixDecoder(use_neural=True)

        # Buffer de frames recentes
        self._recent_frames = deque(maxlen=6)
        self._recent_lock = threading.Lock()

        # Pool de decode
        self.decode_pool: ThreadPoolExecutor | None = None
        self._decode_pool_workers: int = 0

        # Trigger detector
        self.panel_detector = PanelPresenceDetector(aoi=(0, 0, 0, 0), params=PresenceParams())
        self.state = "WAIT_PRESENT"

        # =========================
        # Config / projeto
        # =========================
        self.project_path: Optional[str] = None
        self.project_name: str = "novo_projeto"
        self.project_processing: Dict[str, Any] = {}
        self.rois: List[ROI] = []

        # Result status
        self.last_passed: bool = False
        self.last_trigger_ts: Optional[str] = None

        # =========================
        # ROI editor state
        # =========================
        self.roi_edit_mode = tk.BooleanVar(value=False)
        self.roi_draw_mode = tk.BooleanVar(value=False)
        self.selected_roi_id: Optional[int] = None

        self._roi_edit_action: Optional[str] = None
        self._roi_edit_start_pos: Optional[Tuple[float, float]] = None
        self._roi_edit_corner_idx: Optional[int] = None
        self._roi_original_state: Optional[Dict[str, float]] = None

        self._roi_draw_start = None
        self._roi_draw_rect_id = None

        # ROI editor vars
        self.roi_cx = tk.DoubleVar(value=0.0)
        self.roi_cy = tk.DoubleVar(value=0.0)
        self.roi_w = tk.DoubleVar(value=0.0)
        self.roi_h = tk.DoubleVar(value=0.0)
        self.roi_angle = tk.DoubleVar(value=0.0)

        # =========================
        # Camera / processing vars
        # =========================
        self.cam_exposure_us = tk.IntVar(value=8000)
        self.proc_kernel_center = tk.IntVar(value=5)
        self.proc_thresh_c = tk.IntVar(value=6)

        # =========================
        # UI state / shared
        # =========================
        self.is_running = False
        self.stop_event = threading.Event()
        self.capture_thread: Optional[threading.Thread] = None

        self._lock = threading.Lock()
        self._shared: Dict[str, Any] = {
            "frame": None,
            "fps": 0.0,
            "decode_ms": 0.0,
            "panel_occ": 0.0,
            "panel_has_bg": False,
            "panel_present": False,
            "last_trigger_codes": [],
            "last_trigger_debug": None,
            "last_mask_live": None,
            "last_passed": None,
            "last_artifact": None,
        }

        # Debug mode
        self.debug_mode = tk.StringVar(value="roi_processed")
        self.hold_last_trigger = tk.BooleanVar(value=True)
        self.mosaic_cols = tk.IntVar(value=2)

        # Video controls
        self.freeze = tk.BooleanVar(value=False)
        self.show_overlay = tk.BooleanVar(value=True)
        self.var_show_config = tk.BooleanVar(value=True)
        self.fps_limit = tk.IntVar(value=12)
        self.process_every_n = tk.IntVar(value=1)

        # AOI fields
        self.aoi_x = tk.IntVar(value=0)
        self.aoi_y = tk.IntVar(value=0)
        self.aoi_w = tk.IntVar(value=0)
        self.aoi_h = tk.IntVar(value=0)

        self.diff_thr = tk.IntVar(value=10)
        self.occ_thr = tk.DoubleVar(value=0.80)
        self.deb_on = tk.IntVar(value=4)
        self.deb_off = tk.IntVar(value=6)

        # Decode params
        self.dec_pad = tk.IntVar(value=30)
        self.dec_invert = tk.BooleanVar(value=False)
        self.dec_timeout_fast = tk.IntVar(value=60)
        self.dec_timeout_std = tk.IntVar(value=90)

        # AOI selection mode
        self._aoi_select_active = False
        self._aoi_sel_start = None
        self._aoi_sel_rect_id = None

        # Tk image refs
        self._img_tk_original = None
        self._img_tk_debug = None
        self._last_bgr_original = None
        self._last_bgr_debug = None

        # Zoom states
        self.zp_orig = _ZoomPan()
        self.zp_dbg = _ZoomPan()

        # =========================
        # CMControl vars (PRECISAM EXISTIR ANTES DO _build_ui)
        # =========================
        self.cmc_enabled = tk.BooleanVar(value=True)
        self.cmc_batch_mode = tk.BooleanVar(value=True)

        self._cmc_queue = Queue(maxsize=200)
        self._cmc_stop = threading.Event()

        self._cmc_last_status = None  # "OK" / "ERR" / None
        self._cmc_last_msg = ""

        # =========================
        # Build UI PRIMEIRO
        # =========================
        self._build_ui()

        # =========================
        # Load config (agora UI já existe)
        # =========================
        self.load_config(DEFAULT_CONFIG_PATH, silent=True)

        # =========================
        # UI loop (agora labels já existem)
        # =========================
        self._ui_job = None
        self._schedule_ui()

        # =========================
        # Start CMControl thread por último
        # =========================
        self.cfg = cmcontrol_mqtt.load_config_from_env()
        self.cmc = CmControlMqttClient(self.cfg)
        self.cmc.on_apontamento_ok = self._cmc_ap_ok
        self.cmc.on_apontamento_error = self._cmc_ap_err
        self.cmc.on_apontamento_response = self._cmc_ap_payload
        self._cmc_ready = threading.Event()

        self._cmc_thread = threading.Thread(target=self._cmc_worker_loop, daemon=True)
        self._cmc_thread.start()

    # ---------------- Parallel decode helpers ----------------
    def _cmc_ap_payload(self, payload: dict):
        # exemplo: logar e refletir algum campo na UI
        def _ui():
            # se existir "log", mostra ele; se não, mostra status
            status = payload.get("status")
            log = payload.get("log")
            if hasattr(self, "lbl_cmc"):
                if log:
                    self.lbl_cmc.config(text=f"CMC: {status} | {str(log)[:60]}", fg="#ffaa00")
                else:
                    self.lbl_cmc.config(text=f"CMC: status={status}", fg="#00ff00")

        try:
            self.root.after(0, _ui)
        except Exception:
            pass

    def _cmc_ap_ok(self):
        # callback vem da thread do MQTT → agenda no Tk
        def _ui():
            self._cmc_last_status = "OK"
            self._cmc_last_msg = "Apontamento OK"
            if hasattr(self, "lbl_cmc"):
                self.lbl_cmc.config(text="CMC: OK", fg="#00ff00")
        try:
            self.root.after(0, _ui)
        except Exception:
            pass
        print("✅ CMC: Apontamento OK")

    def _cmc_ap_err(self, err: str):
        def _ui():
            self._cmc_last_status = "ERR"
            self._cmc_last_msg = str(err)
            if hasattr(self, "lbl_cmc"):
                self.lbl_cmc.config(text=f"CMC: ERRO", fg="#ff4040")
        try:
            self.root.after(0, _ui)
        except Exception:
            pass
        print(f"❌ CMC: Erro apontamento: {err}")

    def _cmc_worker_loop(self):
        retry_s = 2.0
        max_retry_s = 30.0

        def ui_status(txt: str, color: str = "#ffaa00"):
            def _ui():
                if hasattr(self, "lbl_cmc"):
                    self.lbl_cmc.config(text=txt, fg=color)

            try:
                self.root.after(0, _ui)
            except Exception:
                pass

        ui_status("CMC: conectando...", "#ffaa00")

        # Loop principal: nunca morre por falha de login
        while not self._cmc_stop.is_set():

            # 1) garantir conectado + logado
            try:
                # Se você tiver métodos is_connected()/disconnect(), ótimo.
                # Se não tiver, pode deixar só connect/ensure_login dentro do try.
                self.cmc.connect()
                self.cmc.ensure_login(timeout_s=15)
                self._cmc_ready.set()
                ui_status("CMC: OK (logado)", "#00ff00")
                retry_s = 2.0  # reset backoff quando deu certo
            except Exception as e:
                self._cmc_ready.clear()
                ui_status(f"CMC: ERRO login ({str(e)[:40]})", "#ff4040")
                print(f"❌ CMC: falha conectar/logar: {e}")
                time.sleep(retry_s)
                retry_s = min(max_retry_s, retry_s * 1.8)
                continue  # tenta de novo

            # 2) enquanto estiver logado, processa fila + keepalive
            while not self._cmc_stop.is_set():
                # item da fila
                try:
                    item = self._cmc_queue.get(timeout=0.5)
                except Empty:
                    item = None

                # keepalive / renovação do token
                try:
                    if not self.cmc.is_token_valid():
                        ui_status("CMC: renovando token...", "#ffaa00")
                        self.cmc.ensure_login(timeout_s=15)
                        ui_status("CMC: OK (logado)", "#00ff00")
                except Exception as e:
                    ui_status(f"CMC: ERRO token ({str(e)[:40]})", "#ff4040")
                    print(f"⚠️ CMC keepalive/login: {e}")
                    # quebra esse loop interno pra voltar ao loop externo e reconectar
                    break

                # processa item (se houver)
                if item is not None:
                    try:
                        if isinstance(item, (list, tuple)):
                            seriais = [str(s).strip() for s in item if str(s).strip()]
                            if not seriais:
                                continue

                            if bool(self.cmc_batch_mode.get()):
                                self.cmc.apontar(seriais, timeout_s=15)
                                print(f"📤 CMC batch ({len(seriais)}): {seriais[:3]}{'...' if len(seriais) > 3 else ''}")
                            else:
                                self.cmc.apontar_um_a_um(seriais, timeout_s=15, delay_s=0.2)
                                print(f"📤 CMC um-a-um ({len(seriais)})")
                        else:
                            serial = str(item).strip()
                            if serial:
                                self.cmc.apontar(serial, timeout_s=15)
                                print(f"📤 CMC 1x: {serial}")

                    except Exception as e:
                        ui_status("CMC: ERRO apontamento", "#ff4040")
                        print(f"❌ CMC: falha apontando {item}: {e}")
                    finally:
                        try:
                            self._cmc_queue.task_done()
                        except Exception:
                            pass

            # se caiu aqui, é porque deu erro no keepalive ou stop — tenta reconectar
            try:
                self.cmc.disconnect()
            except Exception:
                pass

        # Encerramento
        try:
            self.cmc.disconnect()
        except Exception:
            pass
        ui_status("CMC: desligado", "#aaaaaa")
        print("🛑 CMC desconectado")

    def _ensure_decode_pool(self, n_rois: int) -> None:
        want = max(1, min(int(n_rois), int(os.cpu_count() or 4)))
        if self.decode_pool is not None and self._decode_pool_workers == want:
            return
        try:
            if self.decode_pool is not None:
                self.decode_pool.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
        self.decode_pool = ThreadPoolExecutor(max_workers=want)
        self._decode_pool_workers = want
        print(f"🧵 Decode pool: workers={want} (rois={n_rois})")

    def _push_recent_frame(self, frame: np.ndarray) -> None:
        try:
            fr = frame.copy()
        except Exception:
            fr = frame
        with self._recent_lock:
            self._recent_frames.append((time.time(), fr))

    def _get_recent_frames(self, k: int = 3) -> List[np.ndarray]:
        with self._recent_lock:
            items = list(self._recent_frames)[-max(1, int(k)):]
        return [fr for _, fr in items]

    @staticmethod
    def _sharpness(gray: np.ndarray) -> float:
        if gray is None or gray.size == 0:
            return 0.0
        if gray.ndim != 2:
            gray = gray[:, :, 0]
        lap = cv2.Laplacian(gray, cv2.CV_64F)
        return float(lap.var())

    def _extract_roi_gray(self, frame: np.ndarray, roi: ROI) -> Optional[np.ndarray]:
        roi_img = ImagePreprocessor.extract_roi(frame, roi.cx, roi.cy, roi.w, roi.h, roi.angle)
        if roi_img is None or roi_img.size == 0:
            return None
        if roi_img.ndim == 2:
            return roi_img
        if roi_img.ndim == 3 and roi_img.shape[2] == 1:
            return roi_img[:, :, 0]
        if roi_img.ndim == 3 and roi_img.shape[2] >= 3:
            return cv2.cvtColor(roi_img, cv2.COLOR_BGR2GRAY)
        return roi_img[:, :, 0]

    def _choose_best_gray_for_roi(self, roi: ROI, frames: List[np.ndarray]) -> Optional[np.ndarray]:
        best = None
        best_s = -1.0
        for fr in frames:
            g = self._extract_roi_gray(fr, roi)
            if g is None:
                continue
            s = self._sharpness(g)
            if s > best_s:
                best_s = s
                best = g
        return best

    def _clamp_timeouts(self) -> Tuple[int, int]:
        tf = max(20, int(self.dec_timeout_fast.get()))
        ts = max(40, int(self.dec_timeout_std.get()))
        if tf != int(self.dec_timeout_fast.get()):
            self.dec_timeout_fast.set(tf)
        if ts != int(self.dec_timeout_std.get()):
            self.dec_timeout_std.set(ts)
        return tf, ts

    def _decode_one_roi_bestframe(self, roi: ROI, frames: List[np.ndarray], decode_params: dict) -> Dict[str, Any]:
        t0 = time.time()
        raw_gray = self._choose_best_gray_for_roi(roi, frames)
        if raw_gray is None:
            return {"roi_id": roi.id, "text": None, "ms": 0.0, "method": "roi_invalid", "raw": None, "proc": None}

        dec1 = self.decoder.decode(raw_gray, roi_size=None, filter_params=decode_params)

        dec = dec1
        if not dec1.text:
            p2 = dict(decode_params)
            p2["invert"] = not bool(decode_params.get("invert", False))
            dec2 = self.decoder.decode(raw_gray, roi_size=None, filter_params=p2)
            if dec2.text:
                dec = dec2

        ms = (time.time() - t0) * 1000.0
        return {
            "roi_id": roi.id,
            "text": dec.text,
            "ms": ms,
            "method": dec.method,
            "raw": raw_gray,
            "proc": dec.processed_image if dec.processed_image is not None else raw_gray
        }

    # ---------------- UI build ----------------

    def _build_ui(self):
        main = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashwidth=6)
        main.pack(fill=tk.BOTH, expand=True)

        # Left: two canvases
        left = tk.Frame(main, bg="#1e1e1e")
        main.add(left, stretch="always")

        panes = tk.PanedWindow(left, orient=tk.HORIZONTAL, sashwidth=6, bg="#1e1e1e")
        panes.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        p1 = tk.Frame(panes, bg="#1e1e1e")
        p2 = tk.Frame(panes, bg="#1e1e1e")
        self._p2_frame = p2
        panes.add(p1, stretch="always")
        panes.add(p2, stretch="always")

        tk.Label(p1, text="ORIGINAL (AOI roxo + ROIs amarelo) - Clique para editar", bg="#1e1e1e", fg="white",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        tk.Label(p2, text="DEBUG (mosaico do último trigger / mask ao vivo)", bg="#1e1e1e", fg="white",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        self.canvas_original = tk.Canvas(p1, bg="#202020", highlightthickness=0)
        self.canvas_debug = tk.Canvas(p2, bg="#202020", highlightthickness=0)
        self.canvas_original.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.canvas_debug.pack(fill=tk.BOTH, expand=True, pady=(4, 0))

        self._bind_zoom_pan(self.canvas_original, self.zp_orig, which="original")
        self._bind_zoom_pan(self.canvas_debug, self.zp_dbg, which="debug")

        # Bottom bar
        bar = tk.Frame(left, bg="#2d2d2d", height=60)
        bar.pack(fill=tk.X, padx=6, pady=6)

        self.btn_start = tk.Button(bar, text="▶ Iniciar", bg="#28a745", fg="white",
                                   font=("Segoe UI", 10, "bold"), width=12, command=self.start)
        self.btn_stop = tk.Button(bar, text="⏸ Parar", bg="#dc3545", fg="white",
                                  font=("Segoe UI", 10, "bold"), width=12, command=self.stop, state=tk.DISABLED)
        self.btn_start.pack(side=tk.LEFT, padx=6, pady=10)
        self.btn_stop.pack(side=tk.LEFT, padx=6, pady=10)

        tk.Checkbutton(bar, text="❄ Congelar", variable=self.freeze,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(side=tk.LEFT, padx=(14, 0))
        tk.Checkbutton(bar, text="Overlay", variable=self.show_overlay,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(side=tk.LEFT, padx=(14, 0))

        tk.Checkbutton(bar, text="🛠 Config", variable=self.var_show_config,
                       command=self.toggle_config_view, bg="#2d2d2d", fg="white", selectcolor="#404040").pack(
            side=tk.LEFT, padx=(14, 0))

        tk.Label(bar, text="FPS:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(18, 5))
        tk.Spinbox(bar, from_=1, to=30, textvariable=self.fps_limit, width=5).pack(side=tk.LEFT, padx=5)

        tk.Label(bar, text="Proc N:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(18, 5))
        tk.Spinbox(bar, from_=1, to=10, textvariable=self.process_every_n, width=5).pack(side=tk.LEFT, padx=5)

        # Right: sidebar
        right = tk.Frame(main, bg="#252525", width=430)
        self._right_frame = right
        main.add(right, minsize=380)

        self.sidebar = self._make_scrollable_sidebar(right)

        tk.Label(self.sidebar, text="⚙️ Configuração Completa", bg="#252525", fg="white",
                 font=("Segoe UI", 12, "bold")).pack(pady=(10, 5))

        # Debug frame
        dbg = tk.LabelFrame(self.sidebar, text="Debug", bg="#2d2d2d", fg="white",
                            font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        dbg.pack(fill=tk.X, padx=10, pady=5)

        tk.Radiobutton(dbg, text="Trigger mask (AOI)", variable=self.debug_mode, value="trigger_mask",
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(anchor="w")
        tk.Radiobutton(dbg, text="ROI raw", variable=self.debug_mode, value="roi_raw",
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(anchor="w")
        tk.Radiobutton(dbg, text="ROI processed", variable=self.debug_mode, value="roi_processed",
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(anchor="w")

        tk.Checkbutton(dbg, text="Hold último trigger (não piscar)", variable=self.hold_last_trigger,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(anchor="w", pady=(6, 0))

        row = tk.Frame(dbg, bg="#2d2d2d")
        row.pack(fill=tk.X, pady=(6, 0))
        tk.Label(row, text="Cols:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT)
        tk.Spinbox(row, from_=1, to=8, textvariable=self.mosaic_cols, width=4).pack(side=tk.LEFT, padx=6)
        tk.Button(row, text="Limpar debug", command=self.clear_debug).pack(side=tk.RIGHT)

        # Camera frame
        cam = tk.LabelFrame(self.sidebar, text="Câmera", bg="#2d2d2d", fg="white",
                            font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        cam.pack(fill=tk.X, padx=10, pady=5)

        crow = tk.Frame(cam, bg="#2d2d2d")
        crow.pack(fill=tk.X)
        tk.Label(crow, text="Exposure(us):", bg="#2d2d2d", fg="white").pack(side=tk.LEFT)
        tk.Spinbox(crow, from_=100, to=200000, increment=100, textvariable=self.cam_exposure_us, width=8).pack(
            side=tk.LEFT, padx=6)

        # Processing frame
        proc = tk.LabelFrame(self.sidebar, text="Processing", bg="#2d2d2d", fg="white",
                             font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        proc.pack(fill=tk.X, padx=10, pady=5)

        prow = tk.Frame(proc, bg="#2d2d2d")
        prow.pack(fill=tk.X)
        tk.Label(prow, text="kernel_center:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT)
        tk.Spinbox(prow, from_=1, to=25, textvariable=self.proc_kernel_center, width=5).pack(side=tk.LEFT, padx=6)
        tk.Label(prow, text="thresh_c:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(10, 0))
        tk.Spinbox(prow, from_=-50, to=50, textvariable=self.proc_thresh_c, width=5).pack(side=tk.LEFT, padx=6)

        # ROI editor frame - SIMPLIFICADO
        editor = tk.LabelFrame(self.sidebar, text="Editor de ROIs (mouse no canvas)", bg="#2d2d2d", fg="white",
                               font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        editor.pack(fill=tk.X, padx=10, pady=5)

        tk.Label(editor, text="Modo Edição: Clique na ROI para selecionar", bg="#2d2d2d", fg="#ffff00",
                 font=("Segoe UI", 8)).pack(anchor="w")
        tk.Label(editor, text="• Ctrl+Arraste: Mover ROI", bg="#2d2d2d", fg="white",
                 font=("Segoe UI", 8)).pack(anchor="w")
        tk.Label(editor, text="• Shift+Arraste canto: Redimensionar", bg="#2d2d2d", fg="white",
                 font=("Segoe UI", 8)).pack(anchor="w")
        tk.Label(editor, text="• Alt+Arraste: Rotacionar", bg="#2d2d2d", fg="white",
                 font=("Segoe UI", 8)).pack(anchor="w")
        tk.Label(editor, text="• Desenhar: Arraste sem modificadores", bg="#2d2d2d", fg="white",
                 font=("Segoe UI", 8)).pack(anchor="w")

        rowm = tk.Frame(editor, bg="#2d2d2d")
        rowm.pack(fill=tk.X, pady=(8, 0))
        tk.Checkbutton(rowm, text="Editar", variable=self.roi_edit_mode,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(side=tk.LEFT)
        tk.Checkbutton(rowm, text="Desenhar", variable=self.roi_draw_mode,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(side=tk.LEFT, padx=(10, 0))
        tk.Button(rowm, text="🗑 Remover", command=self.delete_selected_roi).pack(side=tk.RIGHT)

        frm = tk.Frame(editor, bg="#2d2d2d")
        frm.pack(fill=tk.X, pady=(8, 0))

        def _frow(lbl, var, r):
            tk.Label(frm, text=lbl, bg="#2d2d2d", fg="white").grid(row=r, column=0, sticky="w")
            e = tk.Entry(frm, textvariable=var, width=10, bg="#1e1e1e", fg="white", insertbackground="white")
            e.grid(row=r, column=1, sticky="w", padx=(6, 0))
            return e

        _frow("cx", self.roi_cx, 0)
        _frow("cy", self.roi_cy, 1)
        _frow("w", self.roi_w, 2)
        _frow("h", self.roi_h, 3)
        _frow("ang", self.roi_angle, 4)

        tk.Button(editor, text="✅ Aplicar na ROI selecionada", command=self.apply_roi_fields,
                  bg="#17a2b8", fg="black").pack(fill=tk.X, pady=(8, 0))
        tk.Button(editor, text="🧹 Limpar ROIs", command=self.clear_all_rois,
                  bg="#6c757d", fg="white").pack(fill=tk.X, pady=(6, 0))

        # Trigger frame
        trig = tk.LabelFrame(self.sidebar, text="Trigger (AOI)", bg="#2d2d2d", fg="white",
                             font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        trig.pack(fill=tk.X, padx=10, pady=5)

        tk.Label(trig, text="AOI (x,y,w,h):", bg="#2d2d2d", fg="white").grid(row=0, column=0, columnspan=4, sticky="w")

        def _entry(var, r, c, w=6):
            e = tk.Entry(trig, textvariable=var, width=w, bg="#1e1e1e", fg="white", insertbackground="white")
            e.grid(row=r, column=c, padx=2, pady=2, sticky="w")
            return e

        _entry(self.aoi_x, 1, 0)
        _entry(self.aoi_y, 1, 1)
        _entry(self.aoi_w, 1, 2)
        _entry(self.aoi_h, 1, 3)

        tk.Button(trig, text="🟣 Selecionar AOI", command=self.start_select_aoi,
                  bg="#6f42c1", fg="white").grid(row=2, column=0, columnspan=2, sticky="we", pady=(4, 2))
        tk.Button(trig, text="📸 Capturar BG", command=self.capture_bg,
                  bg="#198754", fg="white").grid(row=2, column=2, columnspan=2, sticky="we", pady=(4, 2))

        tk.Label(trig, text="Diff:", bg="#2d2d2d", fg="white").grid(row=3, column=0, sticky="w")
        tk.Spinbox(trig, from_=5, to=80, textvariable=self.diff_thr, width=5).grid(row=3, column=1, sticky="w")

        tk.Label(trig, text="Occ:", bg="#2d2d2d", fg="white").grid(row=3, column=2, sticky="w")
        tk.Spinbox(trig, from_=0.05, to=0.99, increment=0.01, textvariable=self.occ_thr, width=6).grid(row=3, column=3,
                                                                                                       sticky="w")

        tk.Label(trig, text="Deb ON/OFF:", bg="#2d2d2d", fg="white").grid(row=4, column=0, columnspan=2, sticky="w")
        tk.Spinbox(trig, from_=1, to=30, textvariable=self.deb_on, width=5).grid(row=4, column=2, sticky="w")
        tk.Spinbox(trig, from_=1, to=60, textvariable=self.deb_off, width=5).grid(row=4, column=3, sticky="w")

        self.lbl_occ = tk.Label(trig, text="Ocupação: 0% | BG: não | vazio",
                                bg="#2d2d2d", fg="white", font=("Segoe UI", 9))
        self.lbl_occ.grid(row=5, column=0, columnspan=4, sticky="w", pady=(4, 0))

        # Decode frame
        dec = tk.LabelFrame(self.sidebar, text="Decode", bg="#2d2d2d", fg="white",
                            font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        dec.pack(fill=tk.X, padx=10, pady=5)

        rowd = tk.Frame(dec, bg="#2d2d2d")
        rowd.pack(fill=tk.X)
        tk.Label(rowd, text="Pad(px):", bg="#2d2d2d", fg="white").pack(side=tk.LEFT)
        tk.Spinbox(rowd, from_=0, to=80, textvariable=self.dec_pad, width=5).pack(side=tk.LEFT, padx=6)
        tk.Checkbutton(rowd, text="Invert", variable=self.dec_invert,
                       bg="#2d2d2d", fg="white", selectcolor="#404040").pack(side=tk.LEFT, padx=8)

        rowt = tk.Frame(dec, bg="#2d2d2d")
        rowt.pack(fill=tk.X, pady=(6, 0))
        tk.Label(rowt, text="T fast:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT)
        tk.Spinbox(rowt, from_=20, to=400, textvariable=self.dec_timeout_fast, width=5).pack(side=tk.LEFT, padx=6)
        tk.Label(rowt, text="T std:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(10, 0))
        tk.Spinbox(rowt, from_=40, to=600, textvariable=self.dec_timeout_std, width=5).pack(side=tk.LEFT, padx=6)

        # UNIFIED SAVE/LOAD - DESTAQUE
        btns = tk.Frame(self.sidebar, bg="#252525")
        btns.pack(fill=tk.X, padx=10, pady=10)

        tk.Label(btns, text="💾 Projeto Completo (salva TUDO)", bg="#252525", fg="#00ff00",
                 font=("Segoe UI", 10, "bold")).pack(pady=(0, 6))

        tk.Button(btns, text="💾 SALVAR PROJETO COMPLETO", bg="#20c997", fg="black",
                  font=("Segoe UI", 10, "bold"), command=self.save_unified_project).pack(fill=tk.X, pady=2)
        tk.Button(btns, text="📂 CARREGAR PROJETO COMPLETO", bg="#0dcaf0", fg="black",
                  font=("Segoe UI", 10, "bold"), command=self.load_unified_project).pack(fill=tk.X, pady=2)

        tk.Frame(btns, height=2, bg="#444").pack(fill=tk.X, pady=8)

        tk.Button(btns, text="🔁 Rearmar Trigger", bg="#ffc107", fg="black", command=self.rearm_trigger).pack(fill=tk.X,
                                                                                                             pady=2)

        # Status
        st = tk.LabelFrame(self.sidebar, text="Status", bg="#2d2d2d", fg="white",
                           font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        st.pack(fill=tk.X, padx=10, pady=5)

        tk.Checkbutton(st, text="CMC habilitado",
                       variable=self.cmc_enabled,
                       bg="#2d2d2d", fg="white",
                       selectcolor="#404040").pack(anchor="w")



        self.lbl_passfail = tk.Label(st, text="RESULT: -", bg="#2d2d2d", fg="white", font=("Segoe UI", 12, "bold"))
        self.lbl_passfail.pack(anchor="w", pady=(0, 6))



        self.lbl_project = tk.Label(st, text="Projeto: novo_projeto", bg="#2d2d2d", fg="#00ff00", font=("Courier", 9))
        self.lbl_fps = tk.Label(st, text="FPS: 0.0", bg="#2d2d2d", fg="#00ff00", font=("Courier", 10))
        self.lbl_dec = tk.Label(st, text="Decode: 0.0 ms", bg="#2d2d2d", fg="#ffaa00", font=("Courier", 10))
        self.lbl_state = tk.Label(st, text="State: WAIT_PRESENT", bg="#2d2d2d", fg="white", font=("Courier", 10))
        self.lbl_cmc = tk.Label(st, text="CMC: -", bg="#2d2d2d", fg="#00ff00", font=("Courier", 10))
        self.lbl_cmc.pack(anchor="w")
        self.lbl_project.pack(anchor="w")
        self.lbl_fps.pack(anchor="w")
        self.lbl_dec.pack(anchor="w")
        self.lbl_state.pack(anchor="w")

        # Codes table
        codes = tk.LabelFrame(self.sidebar, text="Códigos (último trigger)", bg="#2d2d2d", fg="white",
                              font=("Segoe UI", 9, "bold"), padx=10, pady=10)
        codes.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        columns = ("ID", "Código", "ROI")
        self.tree = ttk.Treeview(codes, columns=columns, show="headings", height=10)
        for col in columns:
            self.tree.heading(col, text=col)
        self.tree.column("ID", width=40, anchor="center")
        self.tree.column("Código", width=260, anchor="w")
        self.tree.column("ROI", width=60, anchor="center")

        scr = tk.Scrollbar(codes, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=scr.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scr.pack(side=tk.RIGHT, fill=tk.Y)

        tk.Frame(self.sidebar, height=30, bg="#252525").pack()

    def _make_scrollable_sidebar(self, parent) -> tk.Frame:
        wrapper = tk.Frame(parent, bg="#252525")
        wrapper.pack(fill=tk.BOTH, expand=True)

        canvas = tk.Canvas(wrapper, bg="#252525", highlightthickness=0)
        vbar = tk.Scrollbar(wrapper, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vbar.set)

        vbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        inner = tk.Frame(canvas, bg="#252525")
        window_id = canvas.create_window((0, 0), window=inner, anchor="nw")

        def on_configure(event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfigure(window_id, width=canvas.winfo_width())

        inner.bind("<Configure>", on_configure)
        canvas.bind("<Configure>", on_configure)

        def _on_mousewheel(e):
            if e.delta != 0:
                canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")

        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        canvas.bind_all("<Button-4>", lambda e: canvas.yview_scroll(-1, "units"))
        canvas.bind_all("<Button-5>", lambda e: canvas.yview_scroll(1, "units"))

        return inner

    # ---------------- AOI / params ----------------
    def _safe_int(self, var, default=0, min_v=None, max_v=None):
        try:
            v = var.get() if hasattr(var, 'get') else var
            s = str(v).strip()
            m = re.match(r'^\s*([-+]?\d+)', s)
            if not m:
                return default
            x = int(m.group(1))
            if min_v is not None:
                x = max(min_v, x)
            if max_v is not None:
                x = min(max_v, x)
            return x
        except Exception:
            return default

    def _safe_float(self, var, default=0.0, min_v=None, max_v=None):
        try:
            v = var.get() if hasattr(var, 'get') else var
            s = str(v).strip().replace(',', '.')
            m = re.match(r'^\s*([-+]?\d+(?:\.\d+)?)', s)
            if not m:
                return default
            x = float(m.group(1))
            if min_v is not None:
                x = max(min_v, x)
            if max_v is not None:
                x = min(max_v, x)
            return x
        except Exception:
            return default

    def _refresh_runtime_cfg_from_ui(self):
        with self._cfg_lock:
            self._runtime_cfg['fps_limit'] = self._safe_int(self.fps_limit, 10, 1, 60)
            self._runtime_cfg['process_every_n'] = self._safe_int(self.process_every_n, 1, 1, 30)

    def _apply_panel_params_ui(self):
        x = self._safe_int(self.aoi_x, 0, 0, 100000)
        y = self._safe_int(self.aoi_y, 0, 0, 100000)
        w = self._safe_int(self.aoi_w, 0, 0, 100000)
        h = self._safe_int(self.aoi_h, 0, 0, 100000)
        if w <= 0 or h <= 0:
            return
        try:
            self.panel_detector.set_aoi(x, y, w, h)
        except Exception:
            pass
        try:
            p = self.panel_detector.params
            p.diff_threshold = int(self._safe_int(self.diff_thr, 20, 1, 255))
            p.occupancy_threshold = float(self._safe_float(self.occ_thr, 0.25, 0.0, 1.0))
            p.debounce_on = int(self._safe_int(self.deb_on, 3, 1, 200))
            p.debounce_off = int(self._safe_int(self.deb_off, 6, 1, 400))
        except Exception:
            pass

    def _apply_camera_params(self) -> None:
        exp = int(self.cam_exposure_us.get())
        for m in ("set_exposure", "set_exposure_us", "set_exposure_time", "set_exposure_time_us"):
            if hasattr(self.camera, m):
                try:
                    getattr(self.camera, m)(exp)
                    return
                except Exception:
                    pass

    def capture_bg(self):
        with self._lock:
            frame = self._shared.get("frame")
        if frame is None:
            messagebox.showwarning("BG", "Ainda não há frame da câmera.")
            return
        self._apply_panel_params_ui()
        ok = self.panel_detector.capture_background(frame)
        with self._lock:
            self._shared["panel_has_bg"] = bool(ok)
        if ok:
            messagebox.showinfo("BG", "✅ Background capturado (AOI vazia).")
        else:
            messagebox.showwarning("BG", "Falha ao capturar BG. Verifique AOI e se ela está vazia.")

    # ---------------- ROI editor ----------------

    def _next_roi_id(self) -> int:
        return (max([r.id for r in self.rois], default=0) + 1) if self.rois else 1

    def _select_roi_by_id(self, roi_id: Optional[int]) -> None:
        self.selected_roi_id = roi_id
        roi = next((r for r in self.rois if r.id == roi_id), None) if roi_id is not None else None
        if roi is None:
            self.roi_cx.set(0.0);
            self.roi_cy.set(0.0);
            self.roi_w.set(0.0);
            self.roi_h.set(0.0);
            self.roi_angle.set(0.0)
            return
        self.roi_cx.set(float(roi.cx))
        self.roi_cy.set(float(roi.cy))
        self.roi_w.set(float(roi.w))
        self.roi_h.set(float(roi.h))
        self.roi_angle.set(float(roi.angle))

    def apply_roi_fields(self) -> None:
        if self.selected_roi_id is None:
            messagebox.showwarning("ROI", "Nenhuma ROI selecionada.")
            return
        roi = next((r for r in self.rois if r.id == self.selected_roi_id), None)
        if roi is None:
            messagebox.showwarning("ROI", "ROI selecionada não existe.")
            return
        roi.cx = float(self.roi_cx.get())
        roi.cy = float(self.roi_cy.get())
        roi.w = max(1.0, float(self.roi_w.get()))
        roi.h = max(1.0, float(self.roi_h.get()))
        roi.angle = float(self.roi_angle.get())

    def delete_selected_roi(self) -> None:
        if self.selected_roi_id is None:
            return
        rid = int(self.selected_roi_id)
        self.rois = [r for r in self.rois if r.id != rid]
        self._select_roi_by_id(None)
        self._ensure_decode_pool(len(self.rois))

    def clear_all_rois(self) -> None:
        if not self.rois:
            return
        if not messagebox.askyesno("ROIs", "Remover TODAS as ROIs?"):
            return
        self.rois = []
        self._select_roi_by_id(None)
        self._ensure_decode_pool(1)

    # ---------------- UNIFIED PROJECT SAVE/LOAD ----------------

    def _bg_to_base64_png(self) -> Optional[str]:
        if not self.panel_detector.has_background():
            return None
        bg = self.panel_detector._bg
        if bg is None:
            return None
        ok, buf = cv2.imencode(".png", bg)
        if not ok:
            return None
        return base64.b64encode(buf.tobytes()).decode("ascii")

    def _bg_from_base64_png(self, s: str) -> bool:
        try:
            b = base64.b64decode(s.encode("ascii"))
            arr = np.frombuffer(b, dtype=np.uint8)
            bg = cv2.imdecode(arr, cv2.IMREAD_GRAYSCALE)
            if bg is None or bg.size == 0:
                return False
            self.panel_detector._bg = bg.copy()
            self.panel_detector.last_debug["has_bg"] = True
            return True
        except Exception:
            return False

    def save_unified_project(self) -> None:
        """Salva TUDO em um único arquivo JSON"""
        pname = simpledialog.askstring("Nome do Projeto",
                                       "Nome do projeto:",
                                       initialvalue=self.project_name)
        if not pname:
            return

        self.project_name = pname

        folder = "projects"
        os.makedirs(folder, exist_ok=True)

        path = filedialog.asksaveasfilename(
            title="Salvar Projeto Completo",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialdir=folder,
            initialfile=f"project_{pname}.json",
        )
        if not path:
            return

        self._apply_panel_params_ui()

        # Monta o dict completo com TUDO
        data = {
            "project_name": pname,
            "saved_at": datetime.now().strftime("%Y-%m-%d_%H-%M-%S"),
            "version": "2.0_unified",

            # Camera
            "camera": {
                "exposure_us": int(self.cam_exposure_us.get())
            },

            # Processing
            "processing": {
                "kernel_center": int(self.proc_kernel_center.get()),
                "thresh_c": int(self.proc_thresh_c.get())
            },

            # AOI
            "aoi": {
                "x": int(self.aoi_x.get()),
                "y": int(self.aoi_y.get()),
                "w": int(self.aoi_w.get()),
                "h": int(self.aoi_h.get())
            },

            # Trigger params
            "trigger": {
                "diff_threshold": int(self.diff_thr.get()),
                "occupancy_threshold": float(self.occ_thr.get()),
                "debounce_on": int(self.deb_on.get()),
                "debounce_off": int(self.deb_off.get())
            },

            # Decode params
            "decode": {
                "pad_px": int(self.dec_pad.get()),
                "invert": bool(self.dec_invert.get()),
                "timeout_fast": int(self.dec_timeout_fast.get()),
                "timeout_std": int(self.dec_timeout_std.get())
            },

            # Background
            "background_base64_png": self._bg_to_base64_png(),

            # ROIs
            "rois": [
                {
                    "id": int(r.id),
                    "cx": float(r.cx),
                    "cy": float(r.cy),
                    "w": float(r.w),
                    "h": float(r.h),
                    "angle": float(r.angle)
                }
                for r in self.rois
            ],
        }

        save_json(path, data)
        self.project_path = path
        self.lbl_project.config(text=f"Projeto: {pname}")

        messagebox.showinfo("Projeto Salvo",
                            f"✅ Projeto completo salvo:\n{path}\n\n"
                            f"Incluído:\n"
                            f"• Câmera (exposure)\n"
                            f"• Processing (kernel, thresh)\n"
                            f"• AOI e trigger\n"
                            f"• Decode params\n"
                            f"• Background\n"
                            f"• {len(self.rois)} ROIs")

    def load_unified_project(self) -> None:
        """Carrega TUDO de um único arquivo JSON"""
        path = filedialog.askopenfilename(
            title="Carregar Projeto Completo",
            filetypes=[("JSON", "*.json")],
            initialdir="projects"
        )
        if not path:
            return

        data = load_json(path)
        if not data:
            messagebox.showerror("Erro", "Falha ao carregar projeto.")
            return

        # Project info
        self.project_name = data.get("project_name", os.path.basename(path))
        self.project_path = path

        # Camera
        cam = data.get("camera", {})
        if cam:
            self.cam_exposure_us.set(int(cam.get("exposure_us", 8000)))

        # Processing
        proc = data.get("processing", {})
        if proc:
            self.proc_kernel_center.set(int(proc.get("kernel_center", 5)))
            self.proc_thresh_c.set(int(proc.get("thresh_c", 6)))

        self.project_processing = proc

        # AOI
        aoi = data.get("aoi", {})
        if aoi:
            self.aoi_x.set(int(aoi.get("x", 0)))
            self.aoi_y.set(int(aoi.get("y", 0)))
            self.aoi_w.set(int(aoi.get("w", 0)))
            self.aoi_h.set(int(aoi.get("h", 0)))

        # Trigger
        trig = data.get("trigger", {})
        if trig:
            self.diff_thr.set(int(trig.get("diff_threshold", 10)))
            self.occ_thr.set(float(trig.get("occupancy_threshold", 0.80)))
            self.deb_on.set(int(trig.get("debounce_on", 4)))
            self.deb_off.set(int(trig.get("debounce_off", 6)))

        # Decode
        dec = data.get("decode", {})
        if dec:
            self.dec_pad.set(int(dec.get("pad_px", 30)))
            self.dec_invert.set(bool(dec.get("invert", False)))
            self.dec_timeout_fast.set(int(dec.get("timeout_fast", 60)))
            self.dec_timeout_std.set(int(dec.get("timeout_std", 90)))

        # Background
        bg64 = data.get("background_base64_png")
        if bg64:
            ok = self._bg_from_base64_png(bg64)
            with self._lock:
                self._shared["panel_has_bg"] = bool(ok)

        # ROIs
        rois_data = data.get("rois", [])
        self.rois = []
        for r in rois_data:
            try:
                self.rois.append(ROI(
                    id=int(r.get("id", 1)),
                    cx=float(r.get("cx", 0)),
                    cy=float(r.get("cy", 0)),
                    w=float(r.get("w", 0)),
                    h=float(r.get("h", 0)),
                    angle=float(r.get("angle", 0.0))
                ))
            except Exception:
                pass

        self._ensure_decode_pool(len(self.rois))
        self._apply_panel_params_ui()

        if self.is_running:
            self._apply_camera_params()

        self.lbl_project.config(text=f"Projeto: {self.project_name}")

        messagebox.showinfo("Projeto Carregado",
                            f"✅ Projeto completo carregado:\n{self.project_name}\n\n"
                            f"Carregado:\n"
                            f"• Câmera (exposure={self.cam_exposure_us.get()}µs)\n"
                            f"• Processing (k={self.proc_kernel_center.get()}, c={self.proc_thresh_c.get()})\n"
                            f"• AOI: {self.aoi_w.get()}x{self.aoi_h.get()}\n"
                            f"• BG: {'✓' if bg64 else '✗'}\n"
                            f"• ROIs: {len(self.rois)}")

    # Mantém compatibilidade com config antiga
    def load_config(self, path: str, silent: bool = False):
        """Carrega config antiga (compatibilidade)"""
        if not os.path.exists(path):
            return
        try:
            self.load_unified_project()
        except Exception:
            pass

    # ---------------- Trigger control ----------------

    def rearm_trigger(self):
        self.state = "WAIT_PRESENT"
        print("🔁 Trigger rearmado (WAIT_PRESENT)")
        messagebox.showinfo("Trigger", "🔁 Trigger rearmado (WAIT_PRESENT).")

    def clear_debug(self):
        with self._lock:
            self._shared["last_trigger_debug"] = None
            self._shared["last_trigger_codes"] = []
        self.canvas_debug.delete("all")

    # ---------------- Live start/stop ----------------

    def toggle_config_view(self):
        show = bool(self.var_show_config.get())
        try:
            if show:
                if hasattr(self, '_p2_frame'):
                    self._p2_frame.pack(fill=tk.BOTH, expand=True)
                if hasattr(self, '_right_frame'):
                    self._right_frame.pack(fill=tk.BOTH, expand=False)
            else:
                if hasattr(self, '_p2_frame'):
                    self._p2_frame.pack_forget()
                if hasattr(self, '_right_frame'):
                    self._right_frame.pack_forget()
        except Exception:
            pass

    def start(self):
        if self.is_running:
            return

        if not self.camera.connect():
            messagebox.showerror("Erro", "Falha ao conectar câmera!")
            return

        self._apply_camera_params()
        self.camera.set_trigger_mode(False)
        self.camera.start_grabbing()

        self.stop_event.clear()
        self.is_running = True

        self.capture_thread = threading.Thread(target=self._capture_loop, daemon=True)
        self.capture_thread.start()

        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)

        print("✅ Modo live iniciado")

    def stop(self):
        if not self.is_running:
            return

        self.is_running = False
        self.stop_event.set()

        if self.capture_thread and self.capture_thread.is_alive():
            self.capture_thread.join(timeout=2.0)

        self.camera.stop_grabbing()
        self.camera.close()

        self.btn_start.config(state=tk.NORMAL)
        self.btn_stop.config(state=tk.DISABLED)

        print("⏸ Modo live parado")

    # ---------------- Capture loop ----------------

    def _capture_loop(self):
        times = []
        counter = 0

        while not self.stop_event.is_set():
            t0 = time.time()
            frame = self.camera.get_frame(timeout_ms=120)
            if frame is None:
                time.sleep(0.005)
                continue

            self._push_recent_frame(frame)

            counter += 1
            with self._cfg_lock:
                pe = int(self._runtime_cfg.get('process_every_n', 1))
            do_process = (counter % max(1, pe) == 0)

            if do_process:
                present = self.panel_detector.update(frame)
                occ = float(self.panel_detector.last_debug.get("occupancy", 0.0))
                mask = self.panel_detector.last_debug.get("mask", None)

                with self._lock:
                    self._shared["panel_occ"] = occ
                    self._shared["panel_present"] = bool(present)
                    self._shared["panel_has_bg"] = bool(self.panel_detector.has_background())
                    self._shared["last_mask_live"] = mask

                if self.state == "WAIT_PRESENT":
                    if present:
                        print(f"➡️ PRESENT entrou (occ={occ * 100:.1f}%)")
                        self._do_trigger_fire(frame, occ)
                        self.state = "WAIT_CLEAR"
                else:
                    if not present:
                        self.state = "WAIT_PRESENT"

            dt = time.time() - t0
            times.append(dt)
            if len(times) > 30:
                times.pop(0)
            fps = 1.0 / (np.mean(times) if times else 1e-6)

            with self._lock:
                self._shared["frame"] = frame
                self._shared["fps"] = fps

            with self._cfg_lock:
                fl = int(self._runtime_cfg.get('fps_limit', 10))
            target = 1.0 / max(1, fl)
            sleep_t = max(0.0, target - dt)
            if sleep_t > 0:
                time.sleep(sleep_t)

    # ---------------- Trigger fire ----------------

    def _do_trigger_fire(self, frame: np.ndarray, occ: float):
        if not self.rois:
            print(f"🔥 TRIGGER FIRE | occ={occ * 100:.1f}% | rois=0 (sem projeto)")
            with self._lock:
                self._shared["last_trigger_codes"] = []
            return

        tf, ts = self._clamp_timeouts()

        self.project_processing = {
            **(self.project_processing or {}),
            "kernel_center": int(self.proc_kernel_center.get()),
            "thresh_c": int(self.proc_thresh_c.get()),
        }

        decode_params = {
            "pad_px": int(self.dec_pad.get()),
            "timeout_fast": int(tf),
            "timeout_std": int(ts),
            "invert": bool(self.dec_invert.get()),
            "kernel_center": int(self.project_processing.get("kernel_center", 5)),
            "thresh_c": int(self.project_processing.get("thresh_c", 6)),
        }

        debug_mode = self.debug_mode.get()
        cols = max(1, int(self.mosaic_cols.get()))

        frames = self._get_recent_frames(k=3)
        if not frames:
            frames = [frame]

        self._ensure_decode_pool(len(self.rois))

        t_fire0 = time.time()
        ok_count = 0
        results_codes: List[Dict[str, Any]] = []
        tiles: List[np.ndarray] = []

        print(f"🔥 TRIGGER FIRE | occ={occ * 100:.1f}% | rois={len(self.rois)} | workers={self._decode_pool_workers}")

        futures = {}
        assert self.decode_pool is not None
        for roi in self.rois:
            futures[self.decode_pool.submit(self._decode_one_roi_bestframe, roi, frames, decode_params)] = roi

        temp_results: List[Dict[str, Any]] = []
        for fut in as_completed(futures):
            roi = futures[fut]
            try:
                r = fut.result()
            except Exception as e:
                r = {"roi_id": roi.id, "text": None, "ms": 0.0, "method": f"err:{e}", "raw": None, "proc": None}
            temp_results.append(r)

        temp_results.sort(key=lambda x: int(x.get("roi_id", 0)))

        for r in temp_results:
            text = r.get("text")
            if text:
                ok_count += 1

            results_codes.append({
                "roi_id": r["roi_id"],
                "text": text,
                "ms": float(r.get("ms", 0.0)),
                "method": r.get("method", "-")
            })

            raw_gray = r.get("raw")
            proc = r.get("proc")

            if debug_mode == "roi_raw":
                tile = self._tile_from_gray(raw_gray, title=f"ROI {r['roi_id']}", ok=bool(text),
                                            subtitle=("OK" if text else "NOK"))
            elif debug_mode == "roi_processed":
                if isinstance(proc, np.ndarray) and proc.ndim == 3:
                    proc = cv2.cvtColor(proc, cv2.COLOR_BGR2GRAY) if proc.shape[2] >= 3 else proc[:, :, 0]
                tile = self._tile_from_gray(proc if proc is not None else raw_gray,
                                            title=f"ROI {r['roi_id']}", ok=bool(text),
                                            subtitle=(text if text else "NOK"))
            else:
                tile = self._tile_from_gray(raw_gray, title=f"ROI {r['roi_id']}", ok=bool(text),
                                            subtitle=("OK" if text else "NOK"))

            tiles.append(tile)

        header = self._make_header_bar(f"TRIGGER | rois={len(self.rois)} | ok={ok_count}")
        mosaic = self._make_mosaic(tiles, cols=cols, pad=10, bg=(10, 10, 10))
        debug_img = self._vstack_images([header, mosaic])

        fire_ms = (time.time() - t_fire0) * 1000.0

        passed = (ok_count == len(self.rois))

        ts_tag = datetime.now().strftime("%Y-%m-%d_%H-%M-%S_%f")[:-3]
        artifact = self._save_trigger_artifacts(frame, results_codes, passed, ts_tag, fire_ms)

        with self._lock:
            self._shared["last_trigger_codes"] = results_codes
            self._shared["last_trigger_debug"] = debug_img
            self._shared["decode_ms"] = float(fire_ms)
            self._shared["last_passed"] = bool(passed)
            self._shared["last_artifact"] = artifact

        decoded_list = [r["text"] for r in results_codes if r.get("text")]
        if self.cmc_enabled.get() and decoded_list:
            if not self._cmc_ready.is_set():
                print("⚠️ CMC ainda não logado — descartando/enfileirando localmente conforme estratégia.")
            else:
                try:
                    if self.cmc_batch_mode.get():
                        self._cmc_queue.put_nowait(decoded_list)
                    else:
                        for s in decoded_list:
                            self._cmc_queue.put_nowait(s)
                    print(f"📥 Enfileirado p/ CMC: {decoded_list}")
                except Exception:
                    print("⚠️ Fila CMC cheia — descartando apontamento.")
        print(f"   decoded: {len(decoded_list)} {decoded_list} | fire={fire_ms:.1f}ms")

    def _save_trigger_artifacts(self, frame: np.ndarray, results_codes: List[Dict[str, Any]],
                                passed: bool, ts_tag: str, fire_ms: float) -> Optional[Dict[str, Any]]:
        try:
            base = self.project_name if self.project_name not in (None, "-", "novo_projeto") else "session"
            out_dir = os.path.join("captures", base)
            os.makedirs(out_dir, exist_ok=True)

            if frame.ndim == 2:
                bgr = cv2.cvtColor(frame, cv2.COLOR_GRAY2BGR)
            elif frame.ndim == 3 and frame.shape[2] == 1:
                bgr = cv2.cvtColor(frame[:, :, 0], cv2.COLOR_GRAY2BGR)
            else:
                bgr = frame.copy()

            text_by_id = {int(r.get("roi_id")): (r.get("text") or None) for r in results_codes}

            ann = bgr.copy()
            for roi in self.rois:
                ok = bool(text_by_id.get(int(roi.id)))
                color = (0, 220, 0) if ok else (0, 0, 255)
                box = roi.get_rect_points()
                cv2.polylines(ann, [box], True, color, 3)
                label = text_by_id.get(int(roi.id)) or "NOK"
                cv2.putText(ann, f"R{roi.id}: {label}"[:40], (int(roi.cx) + 6, int(roi.cy) - 6),
                            cv2.FONT_HERSHEY_SIMPLEX, 0.6, color, 2, cv2.LINE_AA)

            status_txt = "PASSED" if passed else "FAILED"
            cv2.rectangle(ann, (0, 0), (ann.shape[1], 55), (0, 0, 0), -1)
            cv2.putText(ann, f"{status_txt} | {ts_tag}", (10, 38), cv2.FONT_HERSHEY_SIMPLEX, 1.0,
                        (0, 220, 0) if passed else (0, 0, 255), 3, cv2.LINE_AA)

            img_path = os.path.join(out_dir, f"{ts_tag}_annotated.png")
            cv2.imwrite(img_path, ann)

            payload = {
                "timestamp": ts_tag,
                "project": base,
                "passed": bool(passed),
                "decode_ms": float(fire_ms),
                "results": [
                    {
                        "roi_id": int(r.id),
                        "text": text_by_id.get(int(r.id)),
                        "position": {"cx": float(r.cx), "cy": float(r.cy), "w": float(r.w), "h": float(r.h),
                                     "angle": float(r.angle)},
                    }
                    for r in self.rois
                ],
            }
            json_path = os.path.join(out_dir, f"{ts_tag}_decoded.json")
            save_json(json_path, payload)

            return {"dir": out_dir, "image": img_path, "json": json_path, "passed": bool(passed), "timestamp": ts_tag}
        except Exception as e:
            print(f"⚠️ Falha ao salvar artefatos: {e}")
            return None

    # ---------------- Drawing helpers ----------------

    @staticmethod
    def _make_header_bar(text: str, h: int = 70) -> np.ndarray:
        img = np.zeros((h, 900, 3), dtype=np.uint8)
        img[:] = (0, 0, 180)
        cv2.putText(img, text, (18, 48), cv2.FONT_HERSHEY_SIMPLEX, 1.1, (0, 255, 255), 6, cv2.LINE_AA)
        return img

    @staticmethod
    def _tile_from_gray(gray: Optional[np.ndarray], title: str, ok: bool, subtitle: str = "",
                        size=(420, 520)) -> np.ndarray:
        w, h = size
        img = np.zeros((h, w, 3), dtype=np.uint8)
        img[:] = (15, 15, 15)

        cv2.rectangle(img, (0, 0), (w - 1, 55), (0, 0, 180), -1)
        cv2.putText(img, title, (12, 35), cv2.FONT_HERSHEY_SIMPLEX, 0.9, (255, 255, 255), 2, cv2.LINE_AA)
        cv2.putText(img, "OK" if ok else "NOK", (12, 85), cv2.FONT_HERSHEY_SIMPLEX, 0.9,
                    (0, 220, 0) if ok else (0, 0, 255), 2, cv2.LINE_AA)

        if subtitle:
            cv2.putText(img, subtitle[:28], (12, 120), cv2.FONT_HERSHEY_SIMPLEX, 0.7,
                        (0, 220, 0) if ok else (200, 200, 200), 2, cv2.LINE_AA)

        if gray is None or not isinstance(gray, np.ndarray) or gray.size == 0:
            return img

        if gray.ndim != 2:
            gray = gray[:, :, 0]

        gh, gw = gray.shape[:2]
        target_h = h - 140
        scale = target_h / max(1, gh)
        new_w = int(gw * scale)
        new_h = int(gh * scale)
        if new_w < 10 or new_h < 10:
            return img

        g2 = cv2.resize(gray, (new_w, new_h), interpolation=cv2.INTER_NEAREST)
        g2 = cv2.cvtColor(g2, cv2.COLOR_GRAY2BGR)

        x0 = (w - new_w) // 2
        y0 = 135
        img[y0:y0 + new_h, x0:x0 + new_w] = g2
        return img

    @staticmethod
    def _make_mosaic(tiles: List[np.ndarray], cols: int = 2, pad: int = 10, bg=(10, 10, 10)) -> np.ndarray:
        if not tiles:
            out = np.zeros((500, 900, 3), dtype=np.uint8)
            out[:] = bg
            return out
        cols = max(1, int(cols))
        rows = int(np.ceil(len(tiles) / cols))
        th, tw = tiles[0].shape[:2]
        W = cols * tw + (cols + 1) * pad
        H = rows * th + (rows + 1) * pad
        out = np.zeros((H, W, 3), dtype=np.uint8)
        out[:] = bg
        for i, t in enumerate(tiles):
            r = i // cols
            c = i % cols
            x = pad + c * (tw + pad)
            y = pad + r * (th + pad)
            out[y:y + th, x:x + tw] = t
        return out

    @staticmethod
    def _vstack_images(imgs: List[np.ndarray]) -> np.ndarray:
        imgs = [i for i in imgs if isinstance(i, np.ndarray) and i.size > 0]
        if not imgs:
            out = np.zeros((400, 600, 3), dtype=np.uint8)
            return out
        w = max(i.shape[1] for i in imgs)
        fixed = []
        for im in imgs:
            if im.shape[1] != w:
                scale = w / im.shape[1]
                nh = int(im.shape[0] * scale)
                im = cv2.resize(im, (w, nh), interpolation=cv2.INTER_LINEAR)
            fixed.append(im)
        return np.vstack(fixed)

    # ---------------- Zoom/pan + ROI MOUSE EDITING ----------------

    def _canvas_to_image_xy(self, which: str, cx: int, cy: int):
        zp = self.zp_orig if which == "original" else self.zp_dbg
        s = float(zp.scale) if zp.scale > 0 else 1.0
        ix = (cx - float(zp.offx)) / s
        iy = (cy - float(zp.offy)) / s
        return ix, iy

    def start_select_aoi(self):
        if self._last_bgr_original is None:
            messagebox.showwarning("AOI", "Inicie o live para selecionar a AOI.")
            return
        self._aoi_select_active = True
        self._aoi_sel_start = None
        if self._aoi_sel_rect_id is not None:
            try:
                self.canvas_original.delete(self._aoi_sel_rect_id)
            except Exception:
                pass
            self._aoi_sel_rect_id = None

        messagebox.showinfo("AOI", "Modo AOI:\n\n• Clique e arraste para desenhar\n• Duplo-clique reseta zoom")

    def _bind_zoom_pan(self, canvas: tk.Canvas, zp: _ZoomPan, which: str):
        def _wheel(e):
            if self._get_last_image(which) is None:
                return "break"
            factor = 1.15 if e.delta > 0 else (1 / 1.15)
            self._zoom_at(zp, factor, e.x, e.y, which)
            return "break"

        def _wheel_linux_up(e):
            if self._get_last_image(which) is None:
                return "break"
            self._zoom_at(zp, 1.15, e.x, e.y, which)
            return "break"

        def _wheel_linux_down(e):
            if self._get_last_image(which) is None:
                return "break"
            self._zoom_at(zp, 1 / 1.15, e.x, e.y, which)
            return "break"

        def _btn_down(e):
            # ROI EDITOR - NOVO SISTEMA
            if which == "original" and self.roi_edit_mode.get() and self._last_bgr_original is not None:
                ix, iy = self._canvas_to_image_xy("original", e.x, e.y)

                ctrl = bool(e.state & 0x0004)  # Ctrl
                shift = bool(e.state & 0x0001)  # Shift
                alt = bool(e.state & 0x20000)  # Alt

                # Desenhar nova ROI (sem modificadores)
                if self.roi_draw_mode.get() and not ctrl and not shift and not alt:
                    self._roi_draw_start = (e.x, e.y)
                    if self._roi_draw_rect_id is not None:
                        try:
                            canvas.delete(self._roi_draw_rect_id)
                        except Exception:
                            pass
                    self._roi_draw_rect_id = canvas.create_rectangle(e.x, e.y, e.x, e.y, outline="#00ffff", width=3,
                                                                     dash=(6, 3))
                    return "break"

                # Selecionar/editar ROI existente
                chosen_roi = None
                for r in sorted(self.rois, key=lambda rr: rr.id):
                    if r.contains_point(ix, iy):
                        chosen_roi = r
                        break

                if chosen_roi is not None:
                    self._select_roi_by_id(chosen_roi.id)

                    # Ctrl: Mover
                    if ctrl:
                        self._roi_edit_action = 'move'
                        self._roi_edit_start_pos = (ix, iy)
                        self._roi_original_state = {
                            'cx': chosen_roi.cx,
                            'cy': chosen_roi.cy,
                            'w': chosen_roi.w,
                            'h': chosen_roi.h,
                            'angle': chosen_roi.angle
                        }
                    # Shift: Redimensionar (pelo canto mais próximo)
                    elif shift:
                        self._roi_edit_action = 'resize'
                        self._roi_edit_start_pos = (ix, iy)
                        self._roi_edit_corner_idx = chosen_roi.nearest_corner(ix, iy)
                        self._roi_original_state = {
                            'cx': chosen_roi.cx,
                            'cy': chosen_roi.cy,
                            'w': chosen_roi.w,
                            'h': chosen_roi.h,
                            'angle': chosen_roi.angle
                        }
                    # Alt: Rotacionar
                    elif alt:
                        self._roi_edit_action = 'rotate'
                        self._roi_edit_start_pos = (ix, iy)
                        self._roi_original_state = {
                            'cx': chosen_roi.cx,
                            'cy': chosen_roi.cy,
                            'w': chosen_roi.w,
                            'h': chosen_roi.h,
                            'angle': chosen_roi.angle
                        }

                    return "break"
                else:
                    self._select_roi_by_id(None)
                    return "break"

            # AOI selection
            if which == "original" and self._aoi_select_active:
                self._aoi_sel_start = (e.x, e.y)
                if self._aoi_sel_rect_id is not None:
                    try:
                        canvas.delete(self._aoi_sel_rect_id)
                    except Exception:
                        pass
                self._aoi_sel_rect_id = canvas.create_rectangle(
                    e.x, e.y, e.x, e.y, outline="#c000ff", width=4, dash=(8, 4)
                )
                return "break"

            # Pan
            zp._dragging = True
            zp._lastx = e.x
            zp._lasty = e.y
            return "break"

        def _btn_up(e):
            # ROI draw finish
            if which == "original" and self.roi_edit_mode.get() and self.roi_draw_mode.get() and self._roi_draw_start is not None:
                x0c, y0c = self._roi_draw_start
                x1c, y1c = e.x, e.y
                ix0, iy0 = self._canvas_to_image_xy("original", x0c, y0c)
                ix1, iy1 = self._canvas_to_image_xy("original", x1c, y1c)

                cx = float((ix0 + ix1) / 2.0)
                cy = float((iy0 + iy1) / 2.0)
                w = float(abs(ix1 - ix0))
                h = float(abs(iy1 - iy0))

                if self._last_bgr_original is not None:
                    img_h, img_w = self._last_bgr_original.shape[:2]
                    cx = float(np.clip(cx, 0, img_w - 1))
                    cy = float(np.clip(cy, 0, img_h - 1))
                    w = float(np.clip(w, 1, img_w))
                    h = float(np.clip(h, 1, img_h))

                if w >= 10 and h >= 10:
                    rid = self._next_roi_id()
                    self.rois.append(ROI(id=rid, cx=cx, cy=cy, w=w, h=h, angle=0.0))
                    self._select_roi_by_id(rid)
                    self._ensure_decode_pool(len(self.rois))

                self._roi_draw_start = None
                if self._roi_draw_rect_id is not None:
                    try:
                        canvas.delete(self._roi_draw_rect_id)
                    except Exception:
                        pass
                    self._roi_draw_rect_id = None
                return "break"

            # ROI edit finish
            if self._roi_edit_action is not None:
                self._roi_edit_action = None
                self._roi_edit_start_pos = None
                self._roi_edit_corner_idx = None
                self._roi_original_state = None
                self._select_roi_by_id(self.selected_roi_id)  # atualiza campos
                return "break"

            # AOI finish
            if which == "original" and self._aoi_select_active and self._aoi_sel_start is not None:
                x0c, y0c = self._aoi_sel_start
                x1c, y1c = e.x, e.y
                ix0, iy0 = self._canvas_to_image_xy("original", x0c, y0c)
                ix1, iy1 = self._canvas_to_image_xy("original", x1c, y1c)

                x = int(min(ix0, ix1))
                y = int(min(iy0, iy1))
                w = int(abs(ix1 - ix0))
                h = int(abs(iy1 - iy0))

                if self._last_bgr_original is not None:
                    img_h, img_w = self._last_bgr_original.shape[:2]
                    x = max(0, min(img_w - 1, x))
                    y = max(0, min(img_h - 1, y))
                    w = min(w, img_w - x)
                    h = min(h, img_h - y)

                if w >= 10 and h >= 10:
                    self.aoi_x.set(x);
                    self.aoi_y.set(y);
                    self.aoi_w.set(w);
                    self.aoi_h.set(h)
                    self._aoi_select_active = False
                    self._aoi_sel_start = None
                    if self._aoi_sel_rect_id is not None:
                        try:
                            canvas.delete(self._aoi_sel_rect_id)
                        except Exception:
                            pass
                        self._aoi_sel_rect_id = None
                    self.root.after(10, lambda: messagebox.showinfo("AOI", f"✅ AOI definida:\n({x},{y})  {w}x{h}"))
                else:
                    self._aoi_select_active = False
                    self._aoi_sel_start = None
                    if self._aoi_sel_rect_id is not None:
                        try:
                            canvas.delete(self._aoi_sel_rect_id)
                        except Exception:
                            pass
                        self._aoi_sel_rect_id = None
                    self.root.after(10, lambda: messagebox.showwarning("AOI", f"❌ Muito pequena: {w}x{h}"))

                return "break"

            zp._dragging = False
            return "break"

        def _motion(e):
            # ROI drawing feedback
            if which == "original" and self.roi_edit_mode.get() and self.roi_draw_mode.get() and self._roi_draw_start is not None:
                x0, y0 = self._roi_draw_start
                if self._roi_draw_rect_id is not None:
                    try:
                        canvas.coords(self._roi_draw_rect_id, x0, y0, e.x, e.y)
                    except Exception:
                        pass
                return "break"

            # ROI editing
            if self._roi_edit_action is not None and self.selected_roi_id is not None:
                roi = next((r for r in self.rois if r.id == self.selected_roi_id), None)
                if roi is not None and self._roi_original_state is not None and self._roi_edit_start_pos is not None:
                    ix, iy = self._canvas_to_image_xy("original", e.x, e.y)
                    start_x, start_y = self._roi_edit_start_pos

                    if self._roi_edit_action == 'move':
                        # Mover: translação simples
                        dx = ix - start_x
                        dy = iy - start_y
                        roi.cx = self._roi_original_state['cx'] + dx
                        roi.cy = self._roi_original_state['cy'] + dy

                    elif self._roi_edit_action == 'resize':
                        # Redimensionar: ajusta w/h mantendo centro aproximado
                        dx = ix - start_x
                        dy = iy - start_y
                        new_w = max(10.0, self._roi_original_state['w'] + abs(dx) * 2)
                        new_h = max(10.0, self._roi_original_state['h'] + abs(dy) * 2)
                        roi.w = new_w
                        roi.h = new_h

                    elif self._roi_edit_action == 'rotate':
                        # Rotacionar: baseado no ângulo do vetor centro->mouse
                        cx, cy = self._roi_original_state['cx'], self._roi_original_state['cy']
                        angle_rad = math.atan2(iy - cy, ix - cx)
                        angle_deg = math.degrees(angle_rad)
                        roi.angle = angle_deg

                    self._select_roi_by_id(roi.id)

                return "break"

            if which == "original" and self._aoi_select_active and self._aoi_sel_start is not None:
                x0, y0 = self._aoi_sel_start
                if self._aoi_sel_rect_id is not None:
                    try:
                        canvas.coords(self._aoi_sel_rect_id, x0, y0, e.x, e.y)
                    except Exception:
                        pass
                return "break"

            # Pan
            if not zp._dragging:
                return "break"
            dx = e.x - zp._lastx
            dy = e.y - zp._lasty
            zp._lastx = e.x
            zp._lasty = e.y
            zp.offx += dx
            zp.offy += dy
            self._redraw(which)
            return "break"

        def _reset(e):
            if which == "original" and self._aoi_select_active:
                return "break"
            zp.reset()
            self._redraw(which)
            return "break"

        canvas.bind("<MouseWheel>", _wheel)
        canvas.bind("<Button-4>", _wheel_linux_up)
        canvas.bind("<Button-5>", _wheel_linux_down)
        canvas.bind("<ButtonPress-1>", _btn_down)
        canvas.bind("<ButtonRelease-1>", _btn_up)
        canvas.bind("<B1-Motion>", _motion)
        canvas.bind("<Double-Button-1>", _reset)

    def _zoom_at(self, zp: _ZoomPan, factor: float, cx: int, cy: int, which: str):
        old = zp.scale
        zp.scale = old * factor
        zp.clamp()
        new = zp.scale
        ratio = (new / old) if old != 0 else 1.0
        zp.offx = cx - ratio * (cx - zp.offx)
        zp.offy = cy - ratio * (cy - zp.offy)
        self._redraw(which)

    def _get_last_image(self, which: str):
        return self._last_bgr_original if which == "original" else self._last_bgr_debug

    def _redraw(self, which: str):
        if which == "original":
            if self._last_bgr_original is not None:
                self._draw_on_canvas(self.canvas_original, self._last_bgr_original, which="original")
        else:
            if self._last_bgr_debug is not None:
                self._draw_on_canvas(self.canvas_debug, self._last_bgr_debug, which="debug")

    # ---------------- UI update loop ----------------

    def _schedule_ui(self):
        self._update_ui_once()
        self._ui_job = self.root.after(30, self._schedule_ui)

    def _update_ui_once(self):
        self._refresh_runtime_cfg_from_ui()
        self._apply_panel_params_ui()

        with self._lock:
            frame = self._shared.get("frame")
            fps = float(self._shared.get("fps", 0.0))
            dec_ms = float(self._shared.get("decode_ms", 0.0))
            occ = float(self._shared.get("panel_occ", 0.0))
            has_bg = bool(self._shared.get("panel_has_bg", False))
            present = bool(self._shared.get("panel_present", False))
            last_codes = list(self._shared.get("last_trigger_codes", []))
            last_debug = self._shared.get("last_trigger_debug", None)
            last_mask = self._shared.get("last_mask_live", None)
            last_passed_val = self._shared.get("last_passed", None)

        self.lbl_fps.config(text=f"FPS: {fps:.1f}")
        self.lbl_dec.config(text=f"Decode: {dec_ms:.1f} ms")
        self.lbl_state.config(text=f"State: {self.state}")

        if last_passed_val is None:
            self.lbl_passfail.config(text="RESULT: -", fg="white")
        else:
            last_passed = bool(last_passed_val)
            self.lbl_passfail.config(
                text=("RESULT: PASSED" if last_passed else "RESULT: FAILED"),
                fg=("#00ff00" if last_passed else "#ff4040"),
            )

        bg_txt = "sim" if has_bg else "não"
        pres_txt = "PRESENTE" if present else "vazio"
        self.lbl_occ.config(text=f"Ocupação: {occ * 100:.1f}% | BG: {bg_txt} | {pres_txt}")

        # table
        for it in self.tree.get_children():
            self.tree.delete(it)
        for i, r in enumerate(last_codes, 1):
            self.tree.insert("", "end", values=(i, r.get("text") or "", r.get("roi_id")))

        # ORIGINAL
        if frame is not None:
            if self.freeze.get():
                if not hasattr(self, "_frozen_frame") or self._frozen_frame is None:
                    self._frozen_frame = frame
                draw = self._frozen_frame
            else:
                self._frozen_frame = None
                draw = frame

            if draw.ndim == 2:
                orig = cv2.cvtColor(draw, cv2.COLOR_GRAY2BGR)
            elif draw.ndim == 3 and draw.shape[2] == 1:
                orig = cv2.cvtColor(draw[:, :, 0], cv2.COLOR_GRAY2BGR)
            else:
                orig = draw.copy()

            # AOI
            x, y, w, h = int(self.aoi_x.get()), int(self.aoi_y.get()), int(self.aoi_w.get()), int(self.aoi_h.get())
            if w > 1 and h > 1:
                cv2.rectangle(orig, (x, y), (x + w, y + h), (255, 0, 255), 16)
                cv2.putText(orig, f"AOI {occ * 100:.1f}%", (x + 20, y + 50),
                            cv2.FONT_HERSHEY_SIMPLEX, 1.5, (255, 0, 255), 2, cv2.LINE_AA)

            # ROIs overlay
            if self.show_overlay.get() and self.rois:
                for roi in self.rois:
                    box = roi.get_rect_points()
                    is_sel = (self.selected_roi_id == roi.id)
                    color = (0, 89, 255) if is_sel else (0, 255, 255)
                    thick = 8 if is_sel else 8
                    cv2.polylines(orig, [box], True, color, thick)
                    cv2.putText(orig, f"R{roi.id}", (int(roi.cx) + 2, int(roi.cy) - 2),
                                cv2.FONT_HERSHEY_SIMPLEX, 0.9, color, 2, cv2.LINE_AA)

                    # Marca os cantos da ROI selecionada (para debug de resize)
                    if is_sel:
                        corners = roi.get_corner_positions()
                        for cx, cy in corners:
                            cv2.circle(orig, (int(cx), int(cy)), 5, (255, 0, 255), -1)

            self._last_bgr_original = orig
            self._draw_on_canvas(self.canvas_original, orig, which="original")

        # DEBUG
        dbg_mode = self.debug_mode.get()
        dbg_img = None

        if dbg_mode == "trigger_mask":
            if isinstance(last_mask, np.ndarray):
                if last_mask.ndim == 2:
                    dbg_img = cv2.cvtColor(last_mask, cv2.COLOR_GRAY2BGR)
                else:
                    dbg_img = last_mask.copy()
                cv2.putText(dbg_img, "MASK LIVE", (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 1.0, (0, 255, 255), 2,
                            cv2.LINE_AA)

            if self.hold_last_trigger.get() and isinstance(last_debug, np.ndarray):
                dbg_img = last_debug
        else:
            if isinstance(last_debug, np.ndarray):
                dbg_img = last_debug
            elif isinstance(last_mask, np.ndarray):
                dbg_img = cv2.cvtColor(last_mask, cv2.COLOR_GRAY2BGR) if last_mask.ndim == 2 else last_mask.copy()

        if dbg_img is not None:
            self._last_bgr_debug = dbg_img
            self._draw_on_canvas(self.canvas_debug, dbg_img, which="debug")
        else:
            self.canvas_debug.delete("all")

    def _draw_on_canvas(self, canvas: tk.Canvas, bgr: np.ndarray, which: str):
        cw = canvas.winfo_width()
        ch = canvas.winfo_height()
        if cw < 2 or ch < 2:
            return

        zp = self.zp_orig if which == "original" else self.zp_dbg
        s = zp.scale
        ox = zp.offx
        oy = zp.offy

        M = np.array([[s, 0, ox],
                      [0, s, oy]], dtype=np.float32)
        img = cv2.warpAffine(bgr, M, (cw, ch), flags=cv2.INTER_LINEAR, borderValue=(32, 32, 32))

        rgb = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
        pil = Image.fromarray(rgb)
        imgtk = ImageTk.PhotoImage(pil)

        # preserva retângulos temporários
        preserve_aoi = None
        preserve_roi = None
        if which == "original" and self._aoi_select_active and self._aoi_sel_rect_id is not None:
            try:
                coords = canvas.coords(self._aoi_sel_rect_id)
                if len(coords) == 4:
                    preserve_aoi = coords
            except Exception:
                pass

        if which == "original" and self.roi_edit_mode.get() and self.roi_draw_mode.get() and self._roi_draw_rect_id is not None:
            try:
                coords = canvas.coords(self._roi_draw_rect_id)
                if len(coords) == 4:
                    preserve_roi = coords
            except Exception:
                pass

        canvas.delete("all")
        canvas.create_image(0, 0, anchor="nw", image=imgtk)

        if preserve_aoi is not None:
            self._aoi_sel_rect_id = canvas.create_rectangle(
                preserve_aoi[0], preserve_aoi[1], preserve_aoi[2], preserve_aoi[3],
                outline="#c000ff", width=4, dash=(8, 4)
            )

        if preserve_roi is not None:
            self._roi_draw_rect_id = canvas.create_rectangle(
                preserve_roi[0], preserve_roi[1], preserve_roi[2], preserve_roi[3],
                outline="#00ffff", width=3, dash=(6, 3)
            )

        if which == "original":
            self._img_tk_original = imgtk
        else:
            self._img_tk_debug = imgtk

    # ---------------- Run / close ----------------

    def run(self):
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.mainloop()

    def _on_close(self):
        self._cmc_stop.set()
        if self.is_running:
            self.stop()
        try:
            if self._ui_job is not None:
                self.root.after_cancel(self._ui_job)
        except Exception:
            pass

        try:
            if self.decode_pool is not None:
                self.decode_pool.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass

        self.root.destroy()


def main():
    print("=" * 70)
    print("  DataMatrix Reader - Live Trigger (IMPROVED)")
    print("  ✅ Edição de ROIs com mouse (arrastar/redimensionar/rotacionar)")
    print("  ✅ Salvamento UNIFICADO de projeto (tudo em um arquivo)")
    print("=" * 70)
    app = LiveModeTriggerGUI()
    app.run()


if __name__ == "__main__":
    main()