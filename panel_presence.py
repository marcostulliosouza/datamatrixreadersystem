#!/usr/bin/env python3
"""
Detecção de presença/ocupação de um painel dentro de uma AOI (Area Of Interest).

Estratégia:
- Captura um background (AOI vazia).
- Em runtime: diff = abs(gray - bg), binariza, mede occupancy (% de pixels diferentes).
- Usa debounce de frames para evitar falso-positivo.

✅ Correções:
- BUG: checagem de gray (era aoi_img.shape == 2) -> agora len(aoi_img.shape) == 2
- set_aoi NÃO invalida BG se a AOI não mudou (isso quebrava o trigger em live)
- Adicionado get_background_gray / set_background_gray para salvar/carregar BG no config
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple, Dict, Any
import cv2
import numpy as np


@dataclass
class PresenceParams:
    diff_threshold: int = 22
    occupancy_threshold: float = 0.80
    debounce_on: int = 4
    debounce_off: int = 6
    blur_ksize: int = 5
    morph_ksize: int = 5


class PanelPresenceDetector:
    def __init__(self, aoi: Tuple[int, int, int, int] = (0, 0, 0, 0), params: Optional[PresenceParams] = None):
        self.aoi = aoi  # (x,y,w,h)
        self.params = params or PresenceParams()


        self._bg_gray = None

        self._bg: Optional[np.ndarray] = None
        self._present: bool = False
        self._on_count: int = 0
        self._off_count: int = 0

        self.last_debug: Dict[str, Any] = {
            "occupancy": 0.0,
            "mask": None,
            "diff": None,
            "has_bg": False,
            "aoi": self.aoi,
        }

    # ---------- BG getters/setters (para salvar config) ----------

    def set_background_gray(self, bg_gray: np.ndarray) -> None:
        if bg_gray is None:
            self._bg = None
            self.last_debug["has_bg"] = False
            # reset states
            self._present = False
            self._on_count = 0
            self._off_count = 0
            return
        if bg_gray.ndim != 2:
            raise ValueError("Background precisa ser grayscale 2D")
        self._bg = bg_gray.copy()
        self.last_debug["has_bg"] = True

        # reset states (opcional, mas recomendado)
        self._present = False
        self._on_count = 0
        self._off_count = 0

    def get_background_gray(self) -> Optional[np.ndarray]:
        """
        Retorna o background (grayscale) salvo.
        - None se não existir BG
        - retorna cópia defensiva para não ser alterado fora
        """
        return None if self._bg is None else self._bg.copy()

    # ---------- AOI ----------

    def set_aoi(self, x: int, y: int, w: int, h: int) -> None:
        new_aoi = (int(x), int(y), int(w), int(h))

        # ✅ NÃO invalida BG se a AOI não mudou
        if new_aoi == self.aoi:
            return

        self.aoi = new_aoi
        self.last_debug["aoi"] = self.aoi

        # AOI mudou -> bg inválido
        self._bg = None
        self.last_debug["has_bg"] = False

        # reset states
        self._present = False
        self._on_count = 0
        self._off_count = 0

    def capture_background(self, frame_bgr: np.ndarray) -> bool:
        aoi_img = self._crop_aoi(frame_bgr)
        if aoi_img is None:
            return False

        if len(aoi_img.shape) == 2:
            gray = aoi_img
        else:
            # aoi_img pode ser 1 canal (HxWx1) ou 3 canais
            if aoi_img.ndim == 3 and aoi_img.shape[2] == 1:
                gray = aoi_img[:, :, 0]
            else:
                gray = cv2.cvtColor(aoi_img, cv2.COLOR_BGR2GRAY)

        self._bg = gray.copy()
        self.last_debug["has_bg"] = True
        return True

    def has_background(self) -> bool:
        return self._bg is not None

    def is_present(self) -> bool:
        return bool(self._present)

    def update(self, frame_bgr: np.ndarray) -> bool:
        """
        Atualiza estado e retorna present(bool).
        last_debug:
          - occupancy (0..1)
          - mask (uint8 0/255) no tamanho da AOI
          - diff (uint8)
        """
        aoi_img = self._crop_aoi(frame_bgr)
        if aoi_img is None:
            self.last_debug["occupancy"] = 0.0
            self.last_debug["mask"] = None
            self.last_debug["diff"] = None
            self._present = False
            self._on_count = 0
            self._off_count = 0
            self.last_debug["has_bg"] = self._bg is not None
            return False

        # ✅ BUG FIX: check de gray correto
        if len(aoi_img.shape) == 2:
            gray = aoi_img
        else:
            if aoi_img.ndim == 3 and aoi_img.shape[2] == 1:
                gray = aoi_img[:, :, 0]
            else:
                gray = cv2.cvtColor(aoi_img, cv2.COLOR_BGR2GRAY)

        # Se não tem bg, não decide presença
        if self._bg is None or self._bg.shape != gray.shape:
            edges = cv2.Canny(gray, 40, 120)
            occ = float(np.count_nonzero(edges)) / float(edges.size) if edges.size else 0.0
            self.last_debug["occupancy"] = occ
            self.last_debug["mask"] = edges
            self.last_debug["diff"] = None
            self.last_debug["has_bg"] = False
            return False

        self.last_debug["has_bg"] = True

        diff = cv2.absdiff(gray, self._bg)
        if self.params.blur_ksize >= 3 and self.params.blur_ksize % 2 == 1:
            diff = cv2.GaussianBlur(diff, (self.params.blur_ksize, self.params.blur_ksize), 0)

        _, mask = cv2.threshold(diff, int(self.params.diff_threshold), 255, cv2.THRESH_BINARY)

        k = int(self.params.morph_ksize)
        if k >= 3 and k % 2 == 1:
            ker = cv2.getStructuringElement(cv2.MORPH_RECT, (k, k))
            mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, ker, iterations=1)

        occ = float(np.count_nonzero(mask)) / float(mask.size) if mask.size else 0.0

        self.last_debug["occupancy"] = occ
        self.last_debug["mask"] = mask
        self.last_debug["diff"] = diff

        # Debounce
        if occ >= float(self.params.occupancy_threshold):
            self._on_count += 1
            self._off_count = 0
        else:
            self._off_count += 1
            self._on_count = 0

        if not self._present and self._on_count >= int(self.params.debounce_on):
            self._present = True
        elif self._present and self._off_count >= int(self.params.debounce_off):
            self._present = False

        return bool(self._present)

    def _crop_aoi(self, frame_bgr: np.ndarray) -> Optional[np.ndarray]:
        x, y, w, h = self.aoi
        if w <= 1 or h <= 1:
            return None

        H, W = frame_bgr.shape[:2]
        x = max(0, min(int(x), W - 1))
        y = max(0, min(int(y), H - 1))
        w = max(1, min(int(w), W - x))
        h = max(1, min(int(h), H - y))

        if w <= 1 or h <= 1:
            return None

        return frame_bgr[y:y+h, x:x+w]