#!/usr/bin/env python3
"""
Decoder DataMatrix - robusto e rápido

✅ Prioriza decode em grayscale (sem destruir ROI)
✅ Adiciona quiet zone (borda branca)
✅ Fallback: CLAHE -> OTSU -> Adaptive (+ invert)
"""

import cv2
import numpy as np
import time
from typing import Optional, Tuple
from dataclasses import dataclass
from pylibdmtx.pylibdmtx import decode as decode_dmtx


@dataclass
class DecoderResult:
    text: Optional[str]
    method: str
    processing_time: float
    processed_image: Optional[np.ndarray] = None


class DataMatrixDecoder:
    def __init__(self, use_neural: bool = False):
        self.use_neural = use_neural

    @staticmethod
    def _to_gray(img: np.ndarray) -> np.ndarray:
        if img.ndim == 2:
            return img
        if img.ndim == 3 and img.shape[2] == 1:
            return img[:, :, 0]
        if img.ndim == 3 and img.shape[2] == 3:
            return cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        if img.ndim == 3 and img.shape[2] == 4:
            return cv2.cvtColor(img, cv2.COLOR_BGRA2GRAY)
        return img[:, :, 0] if img.ndim == 3 else img

    @staticmethod
    def _add_border(img: np.ndarray, pad: int) -> np.ndarray:
        pad = int(max(0, pad))
        if pad == 0:
            return img
        return cv2.copyMakeBorder(img, pad, pad, pad, pad, cv2.BORDER_CONSTANT, value=255)

    @staticmethod
    def _try_decode(gray: np.ndarray, timeout_ms: int) -> Optional[str]:
        try:
            res = decode_dmtx(gray, timeout=int(timeout_ms))
            if res:
                return res[0].data.decode("utf-8")
        except Exception:
            return None
        return None

    def decode(self, image: np.ndarray, roi_size: Tuple[int, int] = None, filter_params: dict = None) -> DecoderResult:
        start = time.time()

        if filter_params is None:
            filter_params = {}
        pad_px = int(filter_params.get("pad_px", 30))
        timeout_fast = int(filter_params.get("timeout_fast", 60))
        timeout_std = int(filter_params.get("timeout_std", 90))
        invert_pref = bool(filter_params.get("invert", False))
        c_val = int(filter_params.get("thresh_c", 6))
        kernel_center = int(filter_params.get("kernel_center", 5))
        block_sizes = filter_params.get("block_sizes", [21, 31, 41])

        gray0 = self._to_gray(image)

        # resize opcional APENAS se explicitamente pedido (recomendado deixar None)
        if roi_size:
            gray0 = cv2.resize(gray0, roi_size, interpolation=cv2.INTER_CUBIC)

        # -------- NÍVEL 1: FAST (gray + border) --------
        for inv in ([invert_pref] + ([not invert_pref] if invert_pref is not None else [])):
            g = cv2.bitwise_not(gray0) if inv else gray0
            test = self._add_border(g, pad_px)
            txt = self._try_decode(test, timeout_fast)
            if txt:
                return DecoderResult(txt, "fast_gray", time.time() - start, processed_image=test)

        # -------- NÍVEL 2: CLAHE (ainda em gray) --------
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        g1 = clahe.apply(gray0)

        for inv in ([invert_pref, not invert_pref]):
            g = cv2.bitwise_not(g1) if inv else g1
            test = self._add_border(g, pad_px)
            txt = self._try_decode(test, timeout_std)
            if txt:
                return DecoderResult(txt, "clahe_gray", time.time() - start, processed_image=test)

        # -------- NÍVEL 3: binários (OTSU / Adaptive) --------
        # sharpen leve
        k = np.array([[0, -1, 0],
                      [-1, kernel_center, -1],
                      [0, -1, 0]], dtype=np.float32)
        sharp = cv2.filter2D(g1, -1, k)

        # OTSU
        _, otsu = cv2.threshold(sharp, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        for bin_img in [otsu, cv2.bitwise_not(otsu)]:
            test = self._add_border(bin_img, pad_px)
            txt = self._try_decode(test, timeout_std)
            if txt:
                return DecoderResult(txt, "otsu", time.time() - start, processed_image=test)

        # Adaptive
        for block in block_sizes:
            block = int(block)
            if block < 3:
                continue
            if block % 2 == 0:
                block += 1
            try:
                thr = cv2.adaptiveThreshold(sharp, 255, cv2.ADAPTIVE_THRESH_MEAN_C,
                                            cv2.THRESH_BINARY, block, c_val)
            except Exception:
                continue

            for bin_img in [thr, cv2.bitwise_not(thr)]:
                test = self._add_border(bin_img, pad_px)
                txt = self._try_decode(test, timeout_std)
                if txt:
                    return DecoderResult(txt, f"adaptive_{block}", time.time() - start, processed_image=test)

        return DecoderResult(None, "failed", time.time() - start, processed_image=self._add_border(g1, pad_px))


class ImagePreprocessor:
    @staticmethod
    def extract_roi(image: np.ndarray, cx: float, cy: float, w: float, h: float, angle: float = 0.0,
                    padding_factor: float = 0.6) -> Optional[np.ndarray]:
        try:
            pad = int(max(w, h) * padding_factor)
            x1 = max(0, int(cx - pad))
            y1 = max(0, int(cy - pad))
            x2 = min(image.shape[1], int(cx + pad))
            y2 = min(image.shape[0], int(cy + pad))

            chunk = image[y1:y2, x1:x2]
            if chunk.size == 0:
                return None

            M = cv2.getRotationMatrix2D((cx - x1, cy - y1), angle, 1.0)
            rotated = cv2.warpAffine(chunk, M, (chunk.shape[1], chunk.shape[0]))

            roi = cv2.getRectSubPix(rotated, (int(w), int(h)), (cx - x1, cy - y1))
            return roi
        except Exception:
            return None
