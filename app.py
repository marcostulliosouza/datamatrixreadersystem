#!/usr/bin/env python3
"""
CMControl — DataMatrix Reader
Aplicação unificada: Login → Menu → Configuração (câmera/ROI/AOI) → Produção

Estrutura:
  App            — router Tk (troca de telas via grid)
  AppState       — estado compartilhado entre telas
  LoginPage      — autenticação simples
  MenuPage       — seleção de modo
  ConfigPage     — configuração completa (câmera, ROI, AOI, decode, MQTT)
  ProductionPage — produção: carrega projeto, inicia engine, mostra resultados
"""

from __future__ import annotations

import base64, threading, time, math, os
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from typing import Optional, Dict, Any, List

import cv2
import numpy as np
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
from PIL import Image, ImageTk
from collections import deque

from camera_controller import BaslerCameraController
from decoder import DataMatrixDecoder, ImagePreprocessor
from panel_presence import PanelPresenceDetector, PresenceParams
from live_config import load_json, save_json
import cmcontrol_mqtt
from cmcontrol_mqtt import CmControlMqttClient


# ══════════════════════════════════════════════════════════════════
#  PALETA & CONSTANTES
# ══════════════════════════════════════════════════════════════════

BG_DEEP   = "#0a0c10"
BG_PANEL  = "#111318"
BG_CARD   = "#181c24"
BG_HOVER  = "#1e2330"
BORDER    = "#252b3b"
BORDER_LT = "#2e3650"

ACCENT    = "#00e5ff"
ACCENT2   = "#7c3aed"
GREEN     = "#00ff88"
RED       = "#ff3b5c"
YELLOW    = "#f59e0b"
MUTED     = "#4a5568"
TEXT_PRI  = "#e8eaf0"
TEXT_SEC  = "#8892a4"
TEXT_DIM  = "#4a5568"

FONT_MONO  = ("Consolas", 10)
FONT_SM    = ("Segoe UI", 10)
FONT_LBL   = ("Segoe UI", 9)
FONT_BOLD  = ("Segoe UI", 9, "bold")


# ══════════════════════════════════════════════════════════════════
#  HELPERS DE UI
# ══════════════════════════════════════════════════════════════════

def _apply_ttk_style(root):
    s = ttk.Style(root)
    s.theme_use("clam")
    s.configure("Treeview", background=BG_CARD, fieldbackground=BG_CARD,
                foreground=TEXT_PRI, rowheight=26, borderwidth=0, font=FONT_MONO)
    s.configure("Treeview.Heading", background=BG_PANEL, foreground=TEXT_DIM,
                relief="flat", font=FONT_BOLD)
    s.map("Treeview", background=[("selected", ACCENT2)],
          foreground=[("selected", "#fff")])
    s.configure("Vertical.TScrollbar", background=BORDER,
                troughcolor=BG_CARD, borderwidth=0, arrowsize=10)
    s.configure("TEntry", fieldbackground=BG_HOVER, foreground=TEXT_PRI,
                insertcolor=ACCENT, borderwidth=0, relief="flat", padding=6)


def _btn(parent, text, command=None, style="ghost", padx=14, pady=7, width=None):
    pal = {
        "primary": (ACCENT,    BG_DEEP,   ACCENT),
        "success": (GREEN,     BG_DEEP,   "#00cc6a"),
        "danger" : (RED,       "#fff",    "#cc2244"),
        "warn"   : (YELLOW,    BG_DEEP,   "#c97f00"),
        "violet" : (ACCENT2,   "#fff",    "#5b21b6"),
        "ghost"  : (BORDER_LT, TEXT_SEC,  BG_HOVER),
        "subtle" : (BG_CARD,   TEXT_SEC,  BG_HOVER),
        "disabled": (MUTED,    TEXT_DIM,  MUTED),
    }

    bg, fg, hbg = pal.get(style, pal["ghost"])

    kw = dict(text=text, bg=bg, fg=fg, font=FONT_BOLD,
              padx=padx, pady=pady, cursor="hand2", relief="flat",
              activebackground=hbg, activeforeground=fg)
    if width:
        kw["width"] = width

    b = tk.Label(parent, **kw)

    # guarda estado
    b._base_bg = bg
    b._hover_bg = hbg
    b._base_fg = fg
    b._enabled = True
    b._command = command

    def _enter(_):
        if b._enabled:
            b.config(bg=b._hover_bg)
    def _leave(_):
        b.config(bg=b._base_bg)
    def _click(_):
        if b._enabled and b._command:
            b._command()

    b.bind("<Enter>", _enter)
    b.bind("<Leave>", _leave)
    b.bind("<Button-1>", _click)

    def set_style(new_style: str):
        bg2, fg2, hbg2 = pal.get(new_style, pal["ghost"])
        b._base_bg = bg2
        b._hover_bg = hbg2
        b._base_fg = fg2
        b.config(bg=bg2, fg=fg2)

    def set_enabled(enabled: bool):
        b._enabled = bool(enabled)
        if b._enabled:
            b.config(cursor="hand2")
        else:
            b.config(cursor="arrow")

    b.set_style = set_style
    b.set_enabled = set_enabled

    return b


def _section(parent, title, bg=BG_CARD):
    outer = tk.Frame(parent, bg=bg, highlightbackground=BORDER, highlightthickness=1)
    outer.pack(fill="x", padx=8, pady=3)
    head = tk.Frame(outer, bg=BG_PANEL)
    head.pack(fill="x")
    tk.Label(head, text=title, bg=BG_PANEL, fg=TEXT_DIM,
             font=FONT_BOLD).pack(side="left", padx=10, pady=5)
    body = tk.Frame(outer, bg=bg, padx=10, pady=7)
    body.pack(fill="x")
    return body


def _row(parent, bg=BG_CARD):
    f = tk.Frame(parent, bg=bg)
    f.pack(fill="x", pady=2)
    return f


def _lbl(parent, text, bg=BG_CARD, fg=TEXT_SEC):
    return tk.Label(parent, text=text, bg=bg, fg=fg, font=FONT_LBL)


def _spin(parent, var, from_, to, width=6, inc=1):
    return tk.Spinbox(parent, from_=from_, to=to, textvariable=var,
                      width=width, increment=inc,
                      bg=BG_HOVER, fg=TEXT_PRI, relief="flat",
                      buttonbackground=BORDER_LT,
                      insertbackground=ACCENT,
                      highlightthickness=0, font=FONT_MONO)


def _entry(parent, var, width=8):
    return tk.Entry(parent, textvariable=var, width=width,
                    bg=BG_HOVER, fg=TEXT_PRI, relief="flat",
                    insertbackground=ACCENT,
                    highlightthickness=1,
                    highlightcolor=ACCENT,
                    highlightbackground=BORDER,
                    font=FONT_MONO)


def _chk(parent, text, var, bg=BG_CARD):
    return tk.Checkbutton(parent, text=text, variable=var,
                          bg=bg, fg=TEXT_SEC, selectcolor=BG_HOVER,
                          activebackground=bg, activeforeground=TEXT_PRI,
                          font=FONT_LBL)


def _radio(parent, text, var, val, bg=BG_CARD):
    return tk.Radiobutton(parent, text=text, variable=var, value=val,
                          bg=bg, fg=TEXT_SEC, selectcolor=BG_HOVER,
                          activebackground=bg, activeforeground=TEXT_PRI,
                          font=FONT_LBL)


def _topbar(parent, title, title_color=ACCENT, back_cmd=None, back_label="← Menu"):
    bar = tk.Frame(parent, bg=BG_PANEL, height=50,
                   highlightbackground=BORDER_LT, highlightthickness=1)
    bar.pack(fill="x")
    bar.pack_propagate(False)

    if back_cmd:
        _btn(bar, back_label, command=back_cmd,
             style="ghost", padx=12, pady=6).pack(side="left", padx=8, pady=8)

    tk.Label(bar, text="DM", bg=BG_PANEL, fg=ACCENT,
             font=("Segoe UI", 15, "bold")).pack(side="left", padx=(4, 0), pady=8)
    tk.Label(bar, text="DataMatrix Ready System", bg=BG_PANEL, fg=TEXT_PRI,
             font=("Segoe UI", 9, "bold")).pack(side="left", pady=8, padx=(3, 12))
    tk.Label(bar, text="│", bg=BG_PANEL, fg=BORDER_LT,
             font=("Segoe UI", 14)).pack(side="left")
    tk.Label(bar, text=title, bg=BG_PANEL, fg=title_color,
             font=FONT_BOLD).pack(side="left", padx=10)

    return bar


def _scrollable(parent, bg=BG_DEEP):
    wrap = tk.Frame(parent, bg=bg)
    wrap.pack(fill="both", expand=True)

    cv = tk.Canvas(wrap, bg=bg, highlightthickness=0)
    sb = ttk.Scrollbar(wrap, orient="vertical", command=cv.yview)
    cv.configure(yscrollcommand=sb.set)
    sb.pack(side="right", fill="y")
    cv.pack(side="left", fill="both", expand=True)

    inner = tk.Frame(cv, bg=bg)
    wid = cv.create_window((0, 0), window=inner, anchor="nw")

    def _cfg(e=None):
        cv.configure(scrollregion=cv.bbox("all"))
        cv.itemconfigure(wid, width=cv.winfo_width())
    inner.bind("<Configure>", _cfg)
    cv.bind("<Configure>", _cfg)

    def _wheel(e):
        if e.delta:
            cv.yview_scroll(int(-e.delta / 120), "units")

    def _wheel_linux_up(e):
        cv.yview_scroll(-1, "units")

    def _wheel_linux_down(e):
        cv.yview_scroll(1, "units")

    for w in (cv, inner):
        w.bind("<MouseWheel>", _wheel)
        w.bind("<Button-4>", _wheel_linux_up)
        w.bind("<Button-5>", _wheel_linux_down)

    return inner

def _env_has_api_creds() -> bool:
    try:
        base_cfg = cmcontrol_mqtt.load_config_from_env()
        u = (getattr(base_cfg, "api_user", None) or "").strip()
        p = (getattr(base_cfg, "api_pass", None) or "").strip()
        return bool(u and p)
    except Exception:
        return False

def _canvas_stop_overlay(canvas: tk.Canvas, title="STOPPED", subtitle="Clique em Iniciar para voltar"):
    canvas.delete("all")
    w = max(2, canvas.winfo_width())
    h = max(2, canvas.winfo_height())

    # fundo preto
    canvas.create_rectangle(0, 0, w, h, fill="#000000", outline="")

    # texto central
    canvas.create_text(w // 2, h // 2 - 18, text=title,
                       fill="#ffffff", font=("Segoe UI", 36, "bold"))
    canvas.create_text(w // 2, h // 2 + 22, text=subtitle,
                       fill="#8892a4", font=("Segoe UI", 12, "bold"))

# ══════════════════════════════════════════════════════════════════
#  ROI DATACLASS
# ══════════════════════════════════════════════════════════════════

@dataclass
class ROI:
    id: int
    cx: float; cy: float; w: float; h: float; angle: float = 0.0

    def contains_point(self, x, y, tol=8.0):
        pts = self.get_rect_points().astype(np.float32)
        return cv2.pointPolygonTest(pts, (float(x), float(y)), True) >= -tol

    def get_rect_points(self):
        box = cv2.boxPoints(((self.cx, self.cy), (self.w, self.h), self.angle))
        return box.astype(np.int32)

    def get_corner_positions(self):
        box = self.get_rect_points()
        return [(float(box[i][0]), float(box[i][1])) for i in range(4)]

    def nearest_corner(self, x, y):
        corners = self.get_corner_positions()
        dists = [math.sqrt((x-cx)**2 + (y-cy)**2) for cx, cy in corners]
        return int(np.argmin(dists))


@dataclass
class _ZoomPan:
    scale: float = 1.0
    offx: float = 0.0
    offy: float = 0.0
    _dragging: bool = False
    _lastx: int = 0
    _lasty: int = 0
    min_scale: float = 0.2
    max_scale: float = 8.0

    def reset(self):
        self.scale = 1.0; self.offx = 0.0; self.offy = 0.0


# ══════════════════════════════════════════════════════════════════
#  ESTADO GLOBAL
# ══════════════════════════════════════════════════════════════════

class AppState:
    def __init__(self):
        self.user: Optional[Dict] = None
        self.project_path: Optional[str] = None
        self.project_data: Optional[Dict] = None

        # CMControl (ÚNICO cliente global: criado no Login e reutilizado)
        self.cmc: Optional[CmControlMqttClient] = None
        self.cmc_ready = False

        # Engine compartilhado
        self.camera:         Optional[BaslerCameraController] = None
        self.decoder:        Optional[DataMatrixDecoder] = None
        self.panel_detector: Optional[PanelPresenceDetector] = None
        self.rois:           List[ROI] = []

        # Resultados do último trigger (para ProductionPage exibir)
        self.last_passed:    Optional[bool] = None
        self.last_codes:     List[Dict] = []
        self.last_debug_img: Optional[np.ndarray] = None

        self.skip_auto_login_once = False

    def reset_session(self):
        """Zera tudo que não deve ficar salvo após logout."""
        self.user = None

        # projeto/produção/config (estado "do último usuário")
        self.project_path = None
        self.project_data = None
        self.rois = []

        self.camera = None
        self.decoder = None
        self.panel_detector = None

        self.last_passed = None
        self.last_codes = []
        self.last_debug_img = None

        # CMC
        self.cmc = None
        self.cmc_ready = False

# ══════════════════════════════════════════════════════════════════
#  LOG
# ══════════════════════════════════════════════════════════════════
class DailyLog:
    def __init__(self, base_dir="logs"):
        self.base_dir = base_dir
        self._lock = threading.Lock()
        os.makedirs(self.base_dir, exist_ok=True)

    def _path_today(self) -> str:
        d = datetime.now().strftime("%Y-%m-%d")
        return os.path.join(self.base_dir, f"{d}.log")

    def write_line(self, line: str):
        # linha única (sempre com timestamp)
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self._lock:
            with open(self._path_today(), "a", encoding="utf-8") as f:
                f.write(f"[{ts}] {line}\n")

    def write_block(self, title: str, lines: list[str]):
        self.write_line(f"--- {title} ---")
        for ln in lines:
            self.write_line(ln)
        self.write_line(f"--- /{title} ---")

# ══════════════════════════════════════════════════════════════════
#  ROUTER
# ══════════════════════════════════════════════════════════════════

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("DataMatrix Reader System")
        self.geometry("1440x870")
        self.minsize(1100, 700)
        self.configure(bg=BG_DEEP)
        _apply_ttk_style(self)

        self.state = AppState()

        self._current = None

        container = tk.Frame(self, bg=BG_DEEP)
        container.pack(fill="both", expand=True)
        container.grid_rowconfigure(0, weight=1)
        container.grid_columnconfigure(0, weight=1)

        self.frames: Dict[str, tk.Frame] = {}
        for F in (LoginPage, MenuPage, ConfigPage, ProductionPage):
            frame = F(parent=container, app=self)
            self.frames[F.__name__] = frame
            frame.grid(row=0, column=0, sticky="nsew")

        self.show("LoginPage")
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def on_show(self):
        pass

    def on_hide(self):
        pass

    def show(self, name: str):
        # chama on_hide da tela atual
        if self._current:
            fcur = self.frames[self._current]
            if hasattr(fcur, "on_hide"):
                try:
                    fcur.on_hide()
                except:
                    pass

        # mostra a próxima
        self.frames[name].tkraise()
        self._current = name

        if hasattr(self.frames[name], "on_show"):
            self.frames[name].on_show()

    def _on_close(self):
        # fecha cmc no exit do app
        if messagebox.askyesno("Fechar", "Deseja fechar o programa?"):
            if self.state.cmc:
                try:
                    self.state.cmc.disconnect()
                except Exception:
                    pass
                self.state.cmc = None
            self.destroy()


# ══════════════════════════════════════════════════════════════════
#  LOGIN
# ══════════════════════════════════════════════════════════════════

class LoginPage(tk.Frame):
    def __init__(self, parent, app: App):
        super().__init__(parent, bg=BG_DEEP)
        self.app = app
        self._build()

    def _build(self):
        self._bg_canvas = tk.Canvas(self, bg=BG_DEEP, highlightthickness=0)
        self._bg_canvas.place(relwidth=1, relheight=1)
        self.bind("<Configure>", self._draw_bg)

        panel = tk.Frame(self, bg=BG_PANEL,
                         highlightbackground=BORDER_LT, highlightthickness=1)
        panel.place(relx=0.5, rely=0.5, anchor="center", width=420)

        tk.Frame(panel, bg=ACCENT, height=3).pack(fill="x")

        inner = tk.Frame(panel, bg=BG_PANEL, padx=40, pady=38)
        inner.pack(fill="both")

        tk.Label(inner, text="DM", bg=BG_PANEL, fg=ACCENT,
                 font=("Segoe UI", 38, "bold")).pack(anchor="w")
        tk.Label(inner, text="DataMatrix Reader System", bg=BG_PANEL, fg=TEXT_PRI,
                 font=("Segoe UI", 12, "bold")).pack(anchor="w")
        tk.Label(inner, text="Autentique com dados do CMControl", bg=BG_PANEL,
                 fg=TEXT_DIM, font=FONT_LBL).pack(anchor="w", pady=(2, 30))

        self.var_user = tk.StringVar()
        self.var_pass = tk.StringVar()
        e_user = self._field(inner, "USUÁRIO", self.var_user, False)
        e_pass = self._field(inner, "SENHA",   self.var_pass, True)

        self.lbl_err = tk.Label(inner, text="", bg=BG_PANEL, fg=RED, font=FONT_LBL)
        self.lbl_err.pack(anchor="w", pady=(6, 0))

        _btn(inner, "  ENTRAR  →", command=self.do_login,
             style="primary", padx=0, pady=10).pack(fill="x", pady=(14, 0))

        tk.Label(inner, text="v3.0 · Acesso Restrito",
                 bg=BG_PANEL, fg=TEXT_DIM, font=FONT_LBL).pack(pady=(22, 0))
        e_user.bind("<Return>", lambda e: self.do_login())
        e_pass.bind("<Return>", lambda e: self.do_login())
        # self.bind_all("<Return>", lambda e: self.do_login())

    def _field(self, parent, label, var, password):
        tk.Label(parent, text=label, bg=BG_PANEL, fg=TEXT_DIM,
                 font=("Segoe UI", 8, "bold")).pack(anchor="w", pady=(0, 3))
        e = tk.Entry(parent, textvariable=var, show="●" if password else "",
                     bg=BG_HOVER, fg=TEXT_PRI, relief="flat",
                     insertbackground=ACCENT, font=FONT_SM,
                     highlightthickness=1, highlightcolor=ACCENT,
                     highlightbackground=BORDER)
        e.pack(fill="x", pady=(0, 14), ipady=6)
        return e

    def _draw_bg(self, e=None):
        c = self._bg_canvas
        c.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        for x in range(0, w, 52):
            for y in range(0, h, 52):
                c.create_oval(x-1, y-1, x+1, y+1, fill="#12161e", outline="")
        c.create_oval(w-200, h-200, w+120, h+120, outline="#1a2035", width=1)
        c.create_oval(w-300, h-300, w+220, h+220, outline="#131825", width=1)

    def _try_login(self, u: str, p: str) -> bool:
        """Tenta logar no CMControl e, se OK, salva no state e retorna True."""
        try:
            base_cfg = cmcontrol_mqtt.load_config_from_env()

            cfg = cmcontrol_mqtt.CmControlConfig(
                device_addr=base_cfg.device_addr,
                broker_host=base_cfg.broker_host,
                broker_port=base_cfg.broker_port,
                mqtt_user=base_cfg.mqtt_user,
                mqtt_pass=base_cfg.mqtt_pass,
                api_user=u,
                api_pass=p,
                token_renew_margin_s=base_cfg.token_renew_margin_s,
                connect_timeout_s=base_cfg.connect_timeout_s,
            )

            # se já tinha um cmc global, derruba antes
            if self.app.state.cmc:
                try:
                    self.app.state.cmc.disconnect()
                except Exception:
                    pass
                self.app.state.cmc = None
                self.app.state.cmc_ready = False

            cmc = CmControlMqttClient(cfg)
            cmc.connect()
            cmc.ensure_login(timeout_s=15)

            # guarda globalmente (única instância)
            self.app.state.user = {"username": u, "password": p}
            self.app.state.cmc = cmc
            self.app.state.cmc_ready = True
            return True

        except Exception as e:
            self.lbl_err.config(text=f"❌ Login inválido: {str(e)[:120]}")
            return False

    def do_login(self):
        u = self.var_user.get().strip()
        p = self.var_pass.get()

        if not u or not p:
            self.lbl_err.config(text="⚠  Preencha usuário e senha.")
            return

        self.lbl_err.config(text="Validando credenciais no CMControl...")
        self.update_idletasks()

        if self._try_login(u, p):
            self.lbl_err.config(text="")
            self.app.show("MenuPage")

    def on_show(self):
        # ✅ se veio de logout: não auto-logar e limpa campos
        if getattr(self.app.state, "skip_auto_login_once", False):
            self.app.state.skip_auto_login_once = False

            self.var_user.set("")
            self.var_pass.set("")
            self.lbl_err.config(text="")
            self.update_idletasks()
            return

        # auto-login normal se env tiver credenciais
        try:
            base_cfg = cmcontrol_mqtt.load_config_from_env()
            u = (getattr(base_cfg, "api_user", None) or "").strip()
            p = (getattr(base_cfg, "api_pass", None) or "").strip()
        except Exception:
            u, p = "", ""

        if u and p:
            self.lbl_err.config(text="Auto-login (env) no CMControl...")
            self.update_idletasks()
            self.var_user.set(u)
            self.var_pass.set(p)

            if self._try_login(u, p):
                self.lbl_err.config(text="")
                self.app.show("MenuPage")
        else:
            # se não tem env, deixa tela limpa
            self.var_user.set("")
            self.var_pass.set("")
            self.lbl_err.config(text="")

# ══════════════════════════════════════════════════════════════════
#  MENU
# ══════════════════════════════════════════════════════════════════

class MenuPage(tk.Frame):
    def __init__(self, parent, app: App):
        super().__init__(parent, bg=BG_DEEP)
        self.app = app
        self._build()

    def _build(self):
        bar = tk.Frame(self, bg=BG_PANEL, height=50,
                       highlightbackground=BORDER_LT, highlightthickness=1)
        bar.pack(fill="x")
        bar.pack_propagate(False)

        tk.Label(bar, text="DM", bg=BG_PANEL, fg=ACCENT,
                 font=("Segoe UI", 16, "bold")).pack(side="left", padx=(18, 0), pady=10)
        tk.Label(bar, text="DataMatrix Reader System", bg=BG_PANEL, fg=TEXT_PRI,
                 font=("Segoe UI", 9, "bold")).pack(side="left", padx=(4, 0), pady=10)

        self.lbl_user = tk.Label(bar, text="", bg=BG_PANEL, fg=TEXT_SEC, font=FONT_LBL)
        self.lbl_user.pack(side="right", padx=16)
        _btn(bar, "Sair", command=self.logout,
             style="ghost", padx=10, pady=5).pack(side="right", padx=8, pady=10)

        center = tk.Frame(self, bg=BG_DEEP)
        center.pack(expand=True, fill="both")

        tk.Label(center, text="SELECIONE O MODO DE OPERAÇÃO",
                 bg=BG_DEEP, fg=TEXT_DIM,
                 font=("Segoe UI", 9, "bold")).pack(pady=(56, 32))

        cards_row = tk.Frame(center, bg=BG_DEEP)
        cards_row.pack()

        self._mode_card(cards_row,
            icon="🏭", title="PRODUÇÃO",
            desc="Carrega projeto salvo\ne inicia leitura em tempo real",
            color=GREEN, cmd=lambda: self.app.show("ProductionPage"), col=0)

        self._mode_card(cards_row,
            icon="⚙", title="CONFIGURAÇÃO",
            desc="Câmera · ROI/AOI · Decode\nMQTT · Salvar/Carregar projeto",
            color=ACCENT, cmd=lambda: self.app.show("ConfigPage"), col=1)

    def _mode_card(self, parent, icon, title, desc, color, cmd, col):
        outer = tk.Frame(parent, bg=BG_CARD,
                         highlightbackground=BORDER, highlightthickness=1,
                         cursor="hand2")
        outer.grid(row=0, column=col, padx=22)

        tk.Frame(outer, bg=color, height=3).pack(fill="x")

        inner = tk.Frame(outer, bg=BG_CARD, padx=52, pady=44)
        inner.pack()

        tk.Label(inner, text=icon, bg=BG_CARD, fg=color,
                 font=("Segoe UI", 44)).pack()
        tk.Label(inner, text=title, bg=BG_CARD, fg=TEXT_PRI,
                 font=("Segoe UI", 17, "bold")).pack(pady=(12, 6))
        tk.Label(inner, text=desc, bg=BG_CARD, fg=TEXT_SEC,
                 font=FONT_SM, justify="center").pack()

        btn_style = "primary" if color == ACCENT else "success"
        _btn(inner, f"Entrar →", command=cmd,
             style=btn_style, padx=14, pady=8).pack(pady=(28, 0), fill="x")

        def _enter(e): outer.config(highlightbackground=color)
        def _leave(e): outer.config(highlightbackground=BORDER)
        def _click(e): cmd()

        for w in [outer, inner] + list(inner.winfo_children()):
            w.bind("<Enter>", _enter)
            w.bind("<Leave>", _leave)
            w.bind("<Button-1>", _click)

    def on_show(self):
        u = self.app.state.user
        self.lbl_user.config(text=f"●  {u['username']}" if u else "")

    def logout(self):
        # 1) desconecta cmc
        cmc = self.app.state.cmc
        if cmc:
            try:
                cmc.disconnect()
            except Exception:
                pass

        # 2) zera sessão inteira
        self.app.state.reset_session()

        # 3) limpa o label do menu (evita “ficar o último” se voltar pra tela)
        self.lbl_user.config(text="")

        # 4) regra pedida
        if _env_has_api_creds():
            if messagebox.askyesno("Sair", "Deseja sair do programa?"):
                self.app._on_close()  # type: ignore
            return

        if messagebox.askyesno("Logout", "Deseja fazer logout do programa?"):
            # impede auto-login logo após logout
            self.app.state.skip_auto_login_once = True
            self.app.show("LoginPage")


# ══════════════════════════════════════════════════════════════════
#  ENGINE
# ══════════════════════════════════════════════════════════════════

class Engine:
    """
    Encapsula o loop de captura + trigger + decode.
    """
    def __init__(self,
                 camera: BaslerCameraController,
                 decoder: DataMatrixDecoder,
                 panel_detector: PanelPresenceDetector):
        self.camera = camera
        self.decoder = decoder
        self.panel_detector = panel_detector

        self.rois: List[ROI] = []
        self.decode_params: Dict[str, Any] = {}

        self._stop_evt = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._pool: Optional[ThreadPoolExecutor] = None

        self._recent: deque = deque(maxlen=6)
        self._recent_lock = threading.Lock()

        self.state = "WAIT_PRESENT"

        self.on_frame = None
        self.on_trigger_result = None
        self.on_occupancy = None
        self.on_state_change = None

        self.fps_limit = 12
        self.process_every_n = 1

        # Delay antes do trigger (para evitar borrão na esteira)
        self.trigger_delay_ms = 0
        self._present_since = None

        self.mosaic_cols = 3

        self._pool_workers = 0

    def start(self, exposure_us: int = 8000) -> bool:
        if self._thread and self._thread.is_alive():
            return True
        if not self.camera.connect():
            return False
        try:
            self.camera.set_exposure(exposure_us)
        except Exception:
            pass
        self.camera.set_trigger_mode(False)
        self.camera.start_grabbing()
        self._stop_evt.clear()
        self._ensure_pool()
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()
        return True

    def stop(self):
        self._stop_evt.set()
        if self._thread:
            self._thread.join(timeout=3)
        self.camera.stop_grabbing()
        self.camera.close()
        if self._pool:
            self._pool.shutdown(wait=False, cancel_futures=True)
            self._pool = None

    def rearm(self):
        self.state = "WAIT_PRESENT"
        if self.on_state_change:
            self.on_state_change(self.state)

    def _ensure_pool(self):
        desired = max(1, min(len(self.rois) if self.rois else 1, os.cpu_count() or 4))
        if self._pool is None or desired != self._pool_workers:
            # recria pool se mudou
            if self._pool:
                try:
                    self._pool.shutdown(wait=False, cancel_futures=True)
                except Exception:
                    pass
            self._pool = ThreadPoolExecutor(max_workers=desired)
            self._pool_workers = desired

    @staticmethod
    def _sharpness(gray):
        return float(cv2.Laplacian(gray, cv2.CV_64F).var())

    def _best_gray(self, roi: ROI, frames):
        best, best_s = None, -1.0
        for fr in frames:
            roi_img = ImagePreprocessor.extract_roi(
                fr, roi.cx, roi.cy, roi.w, roi.h, roi.angle)
            if roi_img is None or roi_img.size == 0:
                continue
            g = roi_img if roi_img.ndim == 2 else \
                cv2.cvtColor(roi_img, cv2.COLOR_BGR2GRAY) if roi_img.shape[2] >= 3 \
                else roi_img[:, :, 0]
            s = self._sharpness(g)
            if s > best_s:
                best_s = s; best = g
        return best

    def _decode_roi(self, roi, frames):
        t0 = time.time()
        gray = self._best_gray(roi, frames)
        if gray is None:
            return {"roi_id": roi.id, "text": None, "ms": 0, "raw": None, "proc": None}
        r1 = self.decoder.decode(gray, filter_params=self.decode_params)
        r = r1
        if not r1.text:
            p2 = {**self.decode_params, "invert": not self.decode_params.get("invert", False)}
            r2 = self.decoder.decode(gray, filter_params=p2)
            if r2.text:
                r = r2
        return {"roi_id": roi.id, "text": r.text, "ms": (time.time()-t0)*1000,
                "raw": gray, "proc": r.processed_image}

    def _fire_trigger(self, frame):
        if not self.rois:
            if self.on_trigger_result:
                self.on_trigger_result([], None, False, 0)
            return

        with self._recent_lock:
            frames = list(self._recent)[-3:] or [frame]

        t0 = time.time()
        futures = {self._pool.submit(self._decode_roi, roi, frames): roi
                   for roi in self.rois}
        results = []
        for fut in as_completed(futures):
            try:
                results.append(fut.result())
            except Exception:
                roi = futures[fut]
                results.append({"roi_id": roi.id, "text": None, "ms": 0, "raw": None, "proc": None})
        results.sort(key=lambda x: x["roi_id"])

        ok = sum(1 for r in results if r["text"])
        passed = (ok == len(self.rois))
        fire_ms = (time.time()-t0)*1000

        tiles = [self._make_tile(r) for r in results]
        dbg = self._mosaic(tiles, cols=int(getattr(self, 'mosaic_cols', 3)))

        if self.on_trigger_result:
            self.on_trigger_result(results, dbg, passed, fire_ms)

    def _make_tile(self, r, size=(360, 440)):
        w, h = size

        img = np.zeros((h, w, 3), np.uint8)
        img[:] = (15, 15, 15)

        cv2.rectangle(img, (0, 0), (w - 1, 44), (0, 0, 140), -1)

        ok = bool(r.get("text"))
        cv2.putText(img, f"ROI {r.get('roi_id', '?')}", (10, 30),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.85, (255, 255, 255), 2)
        cv2.putText(img, "OK" if ok else "NOK", (10, 72),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.85,
                    (0, 220, 0) if ok else (0, 0, 255), 2)

        # pega imagem de preview (proc > raw)
        gray = r.get("proc")
        if gray is None:
            gray = r.get("raw")

        if isinstance(gray, np.ndarray) and gray.size > 0:
            # garante 2D
            if gray.ndim == 3:
                gray = gray[:, :, 0]
            elif gray.ndim != 2:
                gray = np.squeeze(gray)
                if gray.ndim != 2:
                    gray = None

        if isinstance(gray, np.ndarray) and gray.size > 0:
            # área disponível no tile
            avail_h = h - 110
            avail_w = w - 20  # margem lateral

            gh, gw = gray.shape[:2]
            if gh > 0 and gw > 0:
                sc = min(avail_h / gh, avail_w / gw)  # cabe em altura e largura
                nw = max(1, int(gw * sc))
                nh = max(1, int(gh * sc))

                if nw >= 4 and nh >= 4:
                    g2 = cv2.resize(gray, (nw, nh), interpolation=cv2.INTER_NEAREST)
                    g2 = cv2.cvtColor(g2, cv2.COLOR_GRAY2BGR)

                    x0 = max(0, (w - nw) // 2)
                    y0 = 100

                    # corte defensivo
                    x1 = min(w, x0 + nw)
                    y1 = min(h, y0 + nh)
                    g2 = g2[:(y1 - y0), :(x1 - x0)]

                    img[y0:y1, x0:x1] = g2

        txt = r.get("text")
        if txt:
            cv2.putText(img, str(txt)[:26], (10, h - 14),
                        cv2.FONT_HERSHEY_SIMPLEX, 0.55, (0, 220, 0), 1)

        return img

    @staticmethod
    def _mosaic(tiles, cols=3, pad=8):
        if not tiles:
            return np.zeros((300,600,3), np.uint8)
        cols = min(cols, len(tiles))
        rows = math.ceil(len(tiles)/cols)
        th, tw = tiles[0].shape[:2]
        W = cols*tw + (cols+1)*pad
        H = rows*th + (rows+1)*pad
        out = np.zeros((H, W, 3), np.uint8)
        for i, t in enumerate(tiles):
            r, c = i//cols, i%cols
            x = pad + c*(tw+pad); y = pad + r*(th+pad)
            out[y:y+th, x:x+tw] = t
        return out

    def _loop(self):
        times = []
        counter = 0

        while not self._stop_evt.is_set():
            t0 = time.time()

            frame = self.camera.get_frame(timeout_ms=120)
            if frame is None:
                time.sleep(0.005)
                continue

            # guarda frame puro (sem timestamp)
            with self._recent_lock:
                self._recent.append(frame.copy())

            counter += 1
            if counter % max(1, self.process_every_n) == 0:
                present = self.panel_detector.update(frame)
                occ = float(self.panel_detector.last_debug.get("occupancy", 0))
                hasbg = bool(self.panel_detector.has_background())

                cb_occ = self.on_occupancy
                if cb_occ and not self._stop_evt.is_set():
                    cb_occ(occ, hasbg, present)

                delay_s = max(0.0, float(getattr(self, "trigger_delay_ms", 0)) / 1000.0)

                if self.state == "WAIT_PRESENT":
                    if present:
                        # entrou presente → marca início e vai aguardar estabilizar
                        self._present_since = time.time()
                        self.state = "WAIT_STABLE" if delay_s > 0 else "TRIGGERED"

                        cb_state = self.on_state_change
                        if cb_state and not self._stop_evt.is_set():
                            cb_state(self.state)

                        if delay_s <= 0:
                            # sem delay: dispara imediatamente
                            self._fire_trigger(frame)
                            self.state = "WAIT_CLEAR"
                            cb_state = self.on_state_change
                            if cb_state and not self._stop_evt.is_set():
                                cb_state(self.state)
                    else:
                        self._present_since = None

                elif self.state == "WAIT_STABLE":
                    if not present:
                        # perdeu presença antes de estabilizar → cancela
                        self._present_since = None
                        self.state = "WAIT_PRESENT"
                        cb_state = self.on_state_change
                        if cb_state and not self._stop_evt.is_set():
                            cb_state(self.state)
                    else:
                        # ainda presente → espera completar delay
                        if self._present_since is None:
                            self._present_since = time.time()
                        if (time.time() - self._present_since) >= delay_s:
                            self.state = "TRIGGERED"
                            cb_state = self.on_state_change
                            if cb_state and not self._stop_evt.is_set():
                                cb_state(self.state)

                            self._fire_trigger(frame)

                            self.state = "WAIT_CLEAR"
                            cb_state = self.on_state_change
                            if cb_state and not self._stop_evt.is_set():
                                cb_state(self.state)

                elif self.state == "WAIT_CLEAR" and not present:
                    self._present_since = None
                    self.state = "WAIT_PRESENT"
                    cb_state = self.on_state_change
                    if cb_state and not self._stop_evt.is_set():
                        cb_state(self.state)


            dt = time.time() - t0
            times.append(dt)
            if len(times) > 30:
                times.pop(0)
            fps = 1.0 / (np.mean(times) if times else 1e-6)

            # chama UMA vez só
            cb = self.on_frame
            if cb and not self._stop_evt.is_set():
                cb(frame, fps)

            sleep_t = max(0.0, (1.0 / max(1, self.fps_limit)) - dt)
            if sleep_t > 0:
                time.sleep(sleep_t)


# ══════════════════════════════════════════════════════════════════
#  CONFIG PAGE
# ══════════════════════════════════════════════════════════════════

class ConfigPage(tk.Frame):
    def __init__(self, parent, app: App):
        super().__init__(parent, bg=BG_DEEP)
        self.app = app
        self.engine: Optional[Engine] = None
        self._loaded_bg = None

        self._last_exposure_us = None
        self._last_exposure_apply_t = 0.0

        self.trigger_delay_ms = tk.IntVar(value=150)

        self._active = False
        self._run_id = 0

        self.cam_exposure    = tk.IntVar(value=8000)
        self.fps_limit       = tk.IntVar(value=12)
        self.proc_every_n    = tk.IntVar(value=1)
        self.proc_kernel     = tk.IntVar(value=5)
        self.proc_thresh_c   = tk.IntVar(value=6)

        self.aoi_x = tk.IntVar(value=0); self.aoi_y = tk.IntVar(value=0)
        self.aoi_w = tk.IntVar(value=0); self.aoi_h = tk.IntVar(value=0)
        self.diff_thr  = tk.IntVar(value=10)
        self.occ_thr   = tk.DoubleVar(value=0.80)
        self.deb_on    = tk.IntVar(value=4)
        self.deb_off   = tk.IntVar(value=6)

        self.dec_pad         = tk.IntVar(value=30)
        self.dec_invert      = tk.BooleanVar(value=False)
        self.dec_t_fast      = tk.IntVar(value=60)
        self.dec_t_std       = tk.IntVar(value=90)
        self.debug_mode      = tk.StringVar(value="roi_processed")
        self.hold_trigger    = tk.BooleanVar(value=True)
        self.mosaic_cols     = tk.IntVar(value=3)
        self.show_overlay    = tk.BooleanVar(value=True)
        self.paused          = tk.BooleanVar(value=False)

        # ✅ CMC switches (apenas UI)
        self.cmc_enabled     = tk.BooleanVar(value=True)
        self.cmc_batch       = tk.BooleanVar(value=True)

        # ROI editor state
        self.rois: List[ROI] = []
        self.selected_roi_id: Optional[int] = None
        self.roi_edit_mode   = tk.BooleanVar(value=False)
        self.roi_draw_mode   = tk.BooleanVar(value=False)
        self.roi_cx = tk.DoubleVar(); self.roi_cy = tk.DoubleVar()
        self.roi_w  = tk.DoubleVar(); self.roi_h  = tk.DoubleVar()
        self.roi_angle = tk.DoubleVar()

        # AOI selection
        self._aoi_active = False
        self._aoi_start  = None
        self._aoi_curr   = None

        # ROI draw
        self._roi_draw_start = None
        self._roi_draw_curr  = None

        # ROI edit
        self._roi_action = None
        self._roi_start_pos = None
        self._roi_orig  = None
        self._roi_corner_idx = None

        # zoom/pan
        self.zp_orig = _ZoomPan()
        self.zp_dbg  = _ZoomPan()

        # shared state
        self._lock = threading.Lock()
        self._shared: Dict[str, Any] = {
            "frame": None, "fps": 0.0, "dec_ms": 0.0,
            "occ": 0.0, "has_bg": False, "present": False,
            "codes": [], "debug_img": None,
            "passed": None, "state": "WAIT_PRESENT",
            "total": 0, "ok_count": 0, "fail_count": 0
        }
        self._img_orig_tk = None
        self._img_dbg_tk  = None
        self._last_bgr_orig = None
        self._last_bgr_dbg  = None
        self._paused_frame  = None
        self._project_name  = "novo_projeto"

        self._build()
        self._ui_job = None
        self._schedule_ui()

        # logger simples
        self._hist = []  # lista de (ts, tag, msg)
        self._hist_max = 200

        self._last_exp_warn_t = 0.0

    def _hist_add(self, tag: str, msg: str):
        ts = datetime.now().strftime("%H:%M:%S")
        self._hist.append((ts, tag, msg))
        if len(self._hist) > self._hist_max:
            self._hist = self._hist[-self._hist_max:]

    def _hist_dump(self):
        with self._lock:
            return "\n".join([f"[{ts}] {tag}: {msg}" for ts, tag, msg in self._hist])

    def on_hide(self):
        # para engine/camera
        self._active = False
        self._run_id += 1
        self.stop_engine()

    def stop_engine(self):
        eng = self.engine
        self._active = False
        self._run_id += 1
        if not eng:
            return

        eng.on_frame = None
        eng.on_trigger_result = None
        eng.on_occupancy = None
        eng.on_state_change = None

        self.paused.set(False)
        self._paused_frame = None
        try:
            self.btn_pause.config(text="⏸  Pause")
        except Exception:
            pass

        try:
            eng.stop()
        except Exception:
            pass

        self.engine = None
        with self._lock:
            self._shared["frame"] = None
            self._shared["debug_img"] = None
            self._shared["passed"] = None
            self._shared["state"] = "STOPPED"

        self.after(0, lambda: _canvas_stop_overlay(self.canvas_original, "STOPPED", "Clique em Iniciar"))
        # self.after(0, lambda: _canvas_stop_overlay(self.canvas_debug, "STOPPED", "Clique em Iniciar"))
        # self.btn_start.set_style("success") # Type: ignore
        # self.btn_start.set_enabled(True) # Type: ignore
        # self.btn_stop.set_style("disabled") # Type: ignore
        # self.btn_stop.set_enabled(False) # Type: ignore

    # ── SHOW ────────────────────────────────────────────────────
    def on_show(self):
        # atualiza label CMC conforme estado global
        self._active = True
        self._run_id += 1
        cmc = self.app.state.cmc
        if cmc and self.app.state.cmc_ready:
            self.lbl_cmc.config(text="CMC: logado", fg=GREEN)
        elif cmc:
            self.lbl_cmc.config(text="CMC: conectado", fg=YELLOW)
        else:
            self.lbl_cmc.config(text="CMC: offline", fg=TEXT_DIM)

    # ── BUILD ────────────────────────────────────────────────────
    def _build(self):
        bar = _topbar(self, "MODO CONFIGURAÇÃO",
                      back_cmd=lambda: self.app.show("MenuPage"))

        _btn(bar, "💾  Salvar Projeto",
             command=self.save_project, style="primary",
             padx=12, pady=5).pack(side="right", padx=6, pady=10)
        _btn(bar, "📂  Carregar",
             command=self.load_project, style="ghost",
             padx=12, pady=5).pack(side="right", padx=2, pady=10)
        _btn(bar, "🔁  Trigger Manual",
             command=self.rearm, style="warn",
             padx=10, pady=5).pack(side="right", padx=2, pady=10)

        self.lbl_project = tk.Label(bar, text="● novo_projeto",
                                    bg=BG_PANEL, fg=TEXT_DIM, font=FONT_LBL)
        self.lbl_project.pack(side="right", padx=14)

        body = tk.Frame(self, bg=BG_DEEP)
        body.pack(fill="both", expand=True, padx=8, pady=8)

        vid_col = tk.Frame(body, bg=BG_DEEP)
        vid_col.pack(side="left", fill="both", expand=True, padx=(0, 6))

        orig_wrap = tk.Frame(vid_col, bg=BG_CARD,
                             highlightbackground=BORDER, highlightthickness=1)
        orig_wrap.pack(fill="both", expand=True, pady=(0, 4))
        orig_h = tk.Frame(orig_wrap, bg=BG_PANEL)
        orig_h.pack(fill="x")
        tk.Label(orig_h, text="ORIGINAL  ·  AOI (roxo) + ROIs (ciano)",
                 bg=BG_PANEL, fg=TEXT_DIM, font=FONT_BOLD).pack(side="left", padx=10, pady=5)
        self.lbl_fps = tk.Label(orig_h, text="FPS: –",
                                bg=BG_PANEL, fg=ACCENT, font=FONT_MONO)
        self.lbl_fps.pack(side="right", padx=10)
        self.canvas_original = tk.Canvas(orig_wrap, bg="#090b0f", highlightthickness=0)
        self.canvas_original.pack(fill="both", expand=True, padx=4, pady=4)

        DBG_H = 240
        dbg_wrap = tk.Frame(vid_col, bg=BG_CARD,
                            highlightbackground=BORDER, highlightthickness=1, height=DBG_H)
        dbg_wrap.pack(fill="x", expand=False)
        dbg_wrap.pack_propagate(False)

        dbg_h = tk.Frame(dbg_wrap, bg=BG_PANEL)
        dbg_h.pack(fill="x")
        tk.Label(dbg_h, text="DEBUG  ·  último trigger / mask",
                 bg=BG_PANEL, fg=TEXT_DIM, font=FONT_BOLD).pack(side="left", padx=10, pady=5)
        self.lbl_dec = tk.Label(dbg_h, text="Decode: – ms",
                                bg=BG_PANEL, fg=YELLOW, font=FONT_MONO)
        self.lbl_dec.pack(side="right", padx=10)

        self.canvas_debug = tk.Canvas(dbg_wrap, bg="#090b0f", highlightthickness=0)
        self.canvas_debug.pack(fill="both", expand=True, padx=4, pady=4)

        self._bind_zoom_pan(self.canvas_original, self.zp_orig, "original")
        self._bind_zoom_pan(self.canvas_debug, self.zp_dbg, "debug")

        bbar = tk.Frame(vid_col, bg=BG_PANEL,
                        highlightbackground=BORDER, highlightthickness=1)
        bbar.pack(fill="x", pady=(4, 0))

        self.btn_start = _btn(bbar, "▶  Iniciar", command=self.start_engine,
                              style="success", padx=14, pady=6)
        self.btn_stop  = _btn(bbar, "⏹  Parar",   command=self.stop_engine,
                              style="danger",  padx=14, pady=6)
        self.btn_start.pack(side="left", padx=8, pady=6)
        self.btn_stop.pack(side="left", padx=4, pady=6)

        # self.btn_stop.set_style("disabled") # Type: ignore
        # self.btn_stop.set_enabled(False) #Type: ignore

        self.btn_pause = _btn(bbar, "⏸  Pause", command=self.toggle_pause,
                              style="primary", padx=12, pady=6)
        self.btn_pause.pack(side="left", padx=8, pady=6)

        _chk(bbar, "Overlay", self.show_overlay, bg=BG_PANEL).pack(side="left", padx=10)

        tk.Label(bbar, text="FPS lim:", bg=BG_PANEL,
                 fg=TEXT_DIM, font=FONT_LBL).pack(side="left", padx=(14, 3))
        _spin(bbar, self.fps_limit, 1, 30, width=4).pack(side="left")
        tk.Label(bbar, text="Proc/N:", bg=BG_PANEL,
                 fg=TEXT_DIM, font=FONT_LBL).pack(side="left", padx=(10, 3))
        _spin(bbar, self.proc_every_n, 1, 10, width=4).pack(side="left")

        sb_outer = tk.Frame(body, bg=BG_DEEP, width=390)
        sb_outer.pack(side="right", fill="y")
        sb_outer.pack_propagate(False)
        self.sidebar = _scrollable(sb_outer, bg=BG_DEEP)

        self._build_status_card()
        self._build_debug_section()
        self._build_camera_section()
        self._build_roi_section()
        self._build_trigger_section()
        self._build_decode_section()
        self._build_cmc_section()

        hist_body = _section(self.sidebar, "HISTÓRICO")
        self.txt_hist = tk.Text(hist_body, height=8, bg=BG_CARD, fg=TEXT_SEC,
                                font=FONT_MONO, relief="flat",
                                insertbackground=ACCENT, state="disabled")
        self.txt_hist.pack(fill="x")
        tk.Frame(self.sidebar, bg=BG_DEEP, height=24).pack()

    def toggle_pause(self):
        now = not bool(self.paused.get())
        self.paused.set(now)

        if now:
            # congelar frame atual
            with self._lock:
                fr = self._shared.get("frame")
            self._paused_frame = fr.copy() if isinstance(fr, np.ndarray) else None
            self.btn_pause.config(text="▶  Resume")
            self._hist_add("UI", "PAUSE (preview congelado)")
        else:
            self._paused_frame = None
            self.btn_pause.config(text="⏸  Pause")
            self._hist_add("UI", "RESUME")
        self._hist_refresh_text()

    def _hist_refresh_text(self):
        if not hasattr(self, "txt_hist"):
            return
        self.txt_hist.config(state="normal")
        self.txt_hist.delete("1.0", "end")
        for ts, tag, msg in self._hist[-120:]:
            self.txt_hist.insert("end", f"[{ts}] {tag}: {msg}\n")
        self.txt_hist.config(state="disabled")
        self.txt_hist.see("end")

    def _build_status_card(self):
        c = tk.Frame(self.sidebar, bg=BG_CARD,
                     highlightbackground=BORDER, highlightthickness=1)
        c.pack(fill="x", padx=8, pady=(4, 6))
        self._status_bar = tk.Frame(c, bg=MUTED, height=3)
        self._status_bar.pack(fill="x")
        inner = tk.Frame(c, bg=BG_CARD, padx=12, pady=10)
        inner.pack(fill="x")
        self.lbl_passfail = tk.Label(inner, text="–", bg=BG_CARD,
                                     fg=MUTED, font=("Segoe UI", 20, "bold"))
        self.lbl_passfail.pack(side="left")
        r = tk.Frame(inner, bg=BG_CARD)
        r.pack(side="right")
        self.lbl_state = tk.Label(r, text="State: WAIT_PRESENT",
                                  bg=BG_CARD, fg=TEXT_DIM, font=FONT_MONO)
        self.lbl_state.pack(anchor="e")
        self.lbl_cmc = tk.Label(r, text="CMC: –",
                                bg=BG_CARD, fg=TEXT_DIM, font=FONT_MONO)
        self.lbl_cmc.pack(anchor="e")
        self.lbl_occ = tk.Label(c, text="Ocupação: –% | BG: – | –",
                                bg=BG_CARD, fg=TEXT_SEC, font=FONT_LBL)
        self.lbl_occ.pack(anchor="w", padx=12, pady=(0, 8))

    def _build_debug_section(self):
        body = _section(self.sidebar, "DEBUG")
        modes = tk.Frame(body, bg=BG_CARD)
        modes.pack(fill="x")
        for t, v in [("Mask", "trigger_mask"),
                     ("RAW", "roi_raw"),
                     ("Processed", "roi_processed")]:
            _radio(modes, t, self.debug_mode, v).pack(side="left", padx=6)
        r = _row(body)
        _chk(r, "Hold último trigger", self.hold_trigger).pack(side="left")
        r2 = _row(body)
        _lbl(r2, "Cols mosaico:").pack(side="left", padx=(0,6))
        _spin(r2, self.mosaic_cols, 1, 8, width=4).pack(side="left")
        _btn(r2, "🧹 Limpar", command=self.clear_debug,
             style="subtle", padx=8, pady=4).pack(side="right")

    def _build_camera_section(self):
        body = _section(self.sidebar, "CÂMERA")
        r = _row(body)
        _lbl(r, "Exposição (µs):").pack(side="left", padx=(0,8))
        _spin(r, self.cam_exposure, 100, 200000, width=8, inc=100).pack(side="left")

    def _build_roi_section(self):
        body = _section(self.sidebar, "EDITOR DE ROIs  ·  mouse no canvas")

        mr = _row(body)
        _chk(mr, "Editar",  self.roi_edit_mode).pack(side="left")
        _chk(mr, "Desenhar",self.roi_draw_mode).pack(side="left", padx=10)
        _btn(mr, "🗑 Remover", command=self.delete_roi,
             style="danger", padx=8, pady=4).pack(side="right")

        ff = tk.Frame(body, bg=BG_CARD)
        ff.pack(fill="x", pady=(6,0))
        for i, (lbl, var) in enumerate([("cx", self.roi_cx), ("cy", self.roi_cy),
                                         ("w",  self.roi_w),  ("h",  self.roi_h),
                                         ("∠",  self.roi_angle)]):
            cell = tk.Frame(ff, bg=BG_CARD)
            cell.grid(row=i//3, column=i%3, padx=4, pady=3, sticky="w")
            tk.Label(cell, text=lbl, bg=BG_CARD, fg=TEXT_DIM,
                     font=FONT_LBL).pack(anchor="w")
            _entry(cell, var, width=8).pack()

        ar = _row(body)
        _btn(ar, "✅ Aplicar ROI", command=self.apply_roi_fields,
             style="primary", padx=10, pady=6).pack(side="left", fill="x",
                                                     expand=True, padx=(0,3))
        _btn(ar, "🧹 Limpar Tudo", command=self.clear_rois,
             style="ghost", padx=10, pady=6).pack(side="right", fill="x", expand=True)

    def _build_trigger_section(self):


        body = _section(self.sidebar, "TRIGGER  ·  AOI")

        aoi_row = tk.Frame(body, bg=BG_CARD)
        aoi_row.pack(fill="x", pady=(0,6))
        for lbl, var in [("x", self.aoi_x), ("y", self.aoi_y),
                         ("w", self.aoi_w), ("h", self.aoi_h)]:
            c = tk.Frame(aoi_row, bg=BG_CARD)
            c.pack(side="left", padx=4)
            tk.Label(c, text=lbl, bg=BG_CARD, fg=TEXT_DIM,
                     font=FONT_LBL).pack(anchor="w")
            _entry(c, var, width=6).pack()

        ab = tk.Frame(body, bg=BG_CARD)
        ab.pack(fill="x", pady=4)
        _btn(ab, "🟣 Selecionar AOI", command=self.start_select_aoi,
             style="violet", padx=10, pady=6).pack(side="left", fill="x",
                                                    expand=True, padx=(0,3))
        _btn(ab, "📸 Capturar BG", command=self.capture_bg,
             style="success", padx=10, pady=6).pack(side="right", fill="x", expand=True)

        r = _row(body)
        _lbl(r, "Diff:").pack(side="left", padx=(0,4))
        _spin(r, self.diff_thr, 5, 80, width=5).pack(side="left")
        _lbl(r, "Occ:").pack(side="left", padx=(12,4))
        _spin(r, self.occ_thr, 0.05, 0.99, width=6, inc=0.01).pack(side="left")

        r2 = _row(body)
        _lbl(r2, "Deb ON:").pack(side="left", padx=(0,4))
        _spin(r2, self.deb_on, 1, 30, width=4).pack(side="left")
        _lbl(r2, "OFF:").pack(side="left", padx=(10,4))
        _spin(r2, self.deb_off, 1, 60, width=4).pack(side="left")

        r3 = _row(body)
        _lbl(r3, "Delay trigger (ms):").pack(side="left", padx=(0,4))
        _spin(r3, self.trigger_delay_ms, 0, 2000, width=6, inc=10).pack(side="left")

    def _build_decode_section(self):
        body = _section(self.sidebar, "DECODE")
        r = _row(body)
        _lbl(r, "Pad (px):").pack(side="left", padx=(0,4))
        _spin(r, self.dec_pad, 0, 80, width=5).pack(side="left")
        _chk(r, "Invert", self.dec_invert).pack(side="left", padx=14)
        r2 = _row(body)
        _lbl(r2, "T fast:").pack(side="left", padx=(0,4))
        _spin(r2, self.dec_t_fast, 20, 400, width=5).pack(side="left")
        _lbl(r2, "T std:").pack(side="left", padx=(12,4))
        _spin(r2, self.dec_t_std, 40, 600, width=5).pack(side="left")

    def _build_cmc_section(self):
        body = _section(self.sidebar, "CMControl MQTT")
        r = _row(body)
        _chk(r, "Habilitado", self.cmc_enabled).pack(side="left")
        _chk(r, "Batch mode", self.cmc_batch).pack(side="left", padx=12)

    # ── ENGINE ───────────────────────────────────────────────────
    def _make_engine(self) -> Engine:
        camera  = BaslerCameraController()
        decoder = DataMatrixDecoder(use_neural=True)
        pd      = PanelPresenceDetector(aoi=(0,0,0,0), params=PresenceParams())
        eng     = Engine(camera, decoder, pd)
        eng.rois = self.rois
        eng.decode_params = self._decode_params()
        eng.fps_limit = int(self.fps_limit.get())
        eng.process_every_n = int(self.proc_every_n.get())

        eng.on_frame           = self._cb_frame
        eng.on_trigger_result  = self._cb_trigger
        eng.on_occupancy       = self._cb_occupancy
        eng.on_state_change    = self._cb_state

        eng.trigger_delay_ms = int(self.trigger_delay_ms.get())

        self.app.state.camera  = camera
        self.app.state.decoder = decoder
        self.app.state.panel_detector = pd
        return eng

    def _decode_params(self):
        return {
            "pad_px": int(self.dec_pad.get()),
            "invert": bool(self.dec_invert.get()),
            "timeout_fast": max(20, int(self.dec_t_fast.get())),
            "timeout_std":  max(40, int(self.dec_t_std.get())),
            "kernel_center": int(self.proc_kernel.get()),
            "thresh_c": int(self.proc_thresh_c.get()),
        }

    def _apply_aoi(self):
        x = int(self.aoi_x.get())
        y = int(self.aoi_y.get())
        w = int(self.aoi_w.get())
        h = int(self.aoi_h.get())

        if self.engine:
            # detecta AOI antiga vs nova antes de aplicar
            old_aoi = tuple(getattr(self.engine.panel_detector, "aoi", (0, 0, 0, 0)))
            new_aoi = (x, y, w, h)

            if w > 0 and h > 0:
                self.engine.panel_detector.set_aoi(x, y, w, h)

            # ✅ se AOI mudou, BG salvo fica inválido
            if new_aoi != old_aoi:
                self._loaded_bg = None
                with self._lock:
                    self._shared["has_bg"] = False

        # params
        try:
            if self.engine:
                p = self.engine.panel_detector.params
                p.diff_threshold = int(self.diff_thr.get())
                p.occupancy_threshold = float(self.occ_thr.get())
                p.debounce_on = int(self.deb_on.get())
                p.debounce_off = int(self.deb_off.get())
        except Exception:
            pass

    def start_engine(self):
        if self.engine:
            return

        self._active = True
        self._run_id += 1

        eng = self._make_engine()
        self.engine = eng

        # aplica AOI/parametros
        self._apply_aoi()

        # aplica BG carregado do projeto (se existir)
        if self._loaded_bg is not None:
            eng.panel_detector.set_background_gray(self._loaded_bg)
            with self._lock:
                self._shared["has_bg"] = True

        # inicia câmera/loop
        if not eng.start(exposure_us=int(self.cam_exposure.get())):
            messagebox.showerror("Erro", "Falha ao conectar câmera!")
            self.engine = None
            return

        # self.btn_start.set_style("disabled") # type: ignore
        # self.btn_start.set_enabled(False) # type: ignore
        # self.btn_stop.set_style("danger") # type: ignore
        # self.btn_stop.set_enabled(True)# type: ignore

    def rearm(self):
        if self.engine:
            self.engine.rearm()

    def capture_bg(self):
        if not self.engine:
            messagebox.showwarning("BG", "Inicie o engine primeiro.")
            return
        with self._lock:
            frame = self._shared.get("frame")
        if frame is None:
            messagebox.showwarning("BG", "Sem frame da câmera.")
            return

        self._apply_aoi()
        ok = self.engine.panel_detector.capture_background(frame)

        with self._lock:
            self._shared["has_bg"] = ok

        if ok:
            # guarda BG na ConfigPage para salvar mesmo se engine parar
            self._loaded_bg = self.engine.panel_detector.get_background_gray()

            messagebox.showinfo("BG", "✅ Background capturado.")
        else:
            messagebox.showwarning("BG", "Falha. Verifique AOI.")

    # ── Callbacks (thread → shared) ───────────────────────────────
    def _cb_frame(self, frame, fps):
        with self._lock:
            self._shared["frame"] = frame
            self._shared["fps"] = fps

        eng = self.engine
        if not eng:
            return
        try:
            exp = int(self.cam_exposure.get())
            now = time.time()
            if (self._last_exposure_us != exp) and (now - self._last_exposure_apply_t > 0.25):
                # algumas câmeras aceitam set_exposure durante grabbing
                eng.camera.set_exposure(exp)
                self._last_exposure_us = exp
                self._last_exposure_apply_t = now
        except Exception:
            now = time.time()
            if now - self._last_exp_warn_t > 2.0:
                self._last_exp_warn_t = now
                self._hist_add("CAM", "SDK não permite set_exposure ao vivo.")
                self.after(0, self._hist_refresh_text)

        eng.trigger_delay_ms = int(self.trigger_delay_ms.get())
        eng.fps_limit = int(self.fps_limit.get())
        eng.process_every_n = int(self.proc_every_n.get())
        eng.rois = self.rois
        eng.decode_params = self._decode_params()
        eng.mosaic_cols = int(self.mosaic_cols.get())

        try:
            self._apply_aoi()
        except Exception:
            pass

    def _cb_trigger(self, codes, dbg_img, passed, dec_ms):
        with self._lock:
            self._shared["codes"] = codes
            self._shared["debug_img"] = dbg_img
            self._shared["passed"] = passed
            self._shared["dec_ms"] = dec_ms
            self._shared["total"] += 1
            if passed:
                self._shared["ok_count"] += 1
            else:
                self._shared["fail_count"] += 1

        roi_stat = {}
        for r in codes:
            rid = int(r.get("roi_id", 0))
            txt = r.get("text")
            roi_stat[rid] = {"text": txt, "decode_ok": bool(txt), "cmc_ok": None, "cmc_reason": ""}

        with self._lock:
            self._shared["roi_stat"] = roi_stat

        decoded = [r.get("text") for r in codes if r.get("text")]
        decoded = list(dict.fromkeys(decoded))  # evita duplicados mantendo ordem

        passed_decode = bool(passed)

        cmc = self.app.state.cmc
        needs_cmc = bool(self._active and self.cmc_enabled.get() and decoded and cmc)

        with self._lock:
            # se vai apontar, o resultado final ainda não está pronto
            if needs_cmc:
                self._shared["passed"] = None  # mostra "aguardando CMC"
                self._shared["pending_final"] = True
            else:
                self._shared["passed"] = passed_decode
                self._shared["pending_final"] = False

        self._hist_add("TRG", f"{'PASS' if passed else 'FAIL'} | codes={len(decoded)} | {dec_ms:.0f}ms")
        self.after(0, self._hist_refresh_text)

        cmc = self.app.state.cmc
        if not (self._active and self.cmc_enabled.get() and decoded and cmc):
            return

        run_id = self._run_id  # trava a sessão (evita thread antiga escrevendo depois)

        # só pra log/UI
        payload = list(decoded) if self.cmc_batch.get() else str(decoded[0])

        if isinstance(payload, list):
            preview = f"{len(payload)} seriais (1 a 1): {payload[0][:40]}..."
            self._hist_add("CMC", f"→ Enviando {preview}")
        else:
            self._hist_add("CMC", f"→ Enviando 1 serial: {payload}")
        self.after(0, self._hist_refresh_text)

        def _ap(payload_local):
            if (not self._active) or (self._run_id != run_id):
                return

            try:
                cmc.ensure_login(timeout_s=15)
                if (not self._active) or (self._run_id != run_id):
                    return

                seriais = payload_local if isinstance(payload_local, list) else [payload_local]
                all_ok = True
                for serial in seriais:
                    if (not self._active) or (self._run_id != run_id):
                        return

                    resp = cmc.apontar(serial, timeout_s=15)

                    r = cmc.apontamento_result(resp)
                    if not r["ok"]:
                        all_ok = False
                    if r["ok"]:
                        self.after(0, lambda s=serial, rr=r["reason"]:
                        self._hist_add("CMC", f"✅ {rr} | serial={s}"))
                    else:
                        self.after(0, lambda s=serial, rr=r["reason"], dd=r["detail"]:
                        self._hist_add("CMC", f"❌ {rr}: {dd} | serial={s}"))

                    # opcional: delay pra não saturar broker/API
                    time.sleep(0.05)

                final_passed = bool(passed_decode and all_ok)

                def _set_final():
                    if self._shared.get("pending_final", False):
                        if final_passed:
                            self._shared["ok_count"] += 1
                        else:
                            self._shared["fail_count"] += 1
                        self._shared["pending_final"] = False
                self.after(0, _set_final)

            except Exception as e:
                msg = str(e)[:180]
                self.after(0, lambda m=msg: self._hist_add("CMC", f"❌ Exceção: {m}"))
            finally:
                self.after(0, self._hist_refresh_text)

        threading.Thread(target=_ap, args=(payload,), daemon=True).start()

    def _cb_occupancy(self, occ, has_bg, present):
        with self._lock:
            self._shared["occ"]     = occ
            self._shared["has_bg"]  = has_bg
            self._shared["present"] = present

    def _cb_state(self, state):
        with self._lock:
            self._shared["state"] = state

    # ── Project save/load ────────────────────────────────────────
    def _project_dict(self) -> dict:
        bg64 = None

        # 1) tenta pegar bg do engine
        bg = None
        if self.engine and self.engine.panel_detector.has_background():
            bg = self.engine.panel_detector.get_background_gray()

        # 2) fallback: último bg carregado/capturado
        if bg is None and self._loaded_bg is not None:
            bg = self._loaded_bg

        # 3) fallback: reaproveita do projeto atual (se existir)
        if bg is None and self.app.state.project_data:
            bg64 = self.app.state.project_data.get("background_base64_png")

        if bg is not None and bg64 is None:
            ok, buf = cv2.imencode(".png", bg)
            if ok:
                bg64 = base64.b64encode(buf.tobytes()).decode()

        return {
            "project_name": self._project_name,
            "saved_at": datetime.now().strftime("%Y-%m-%d_%H-%M-%S"),
            "version": "3.0",
            "ui": {"mosaic_cols": int(self.mosaic_cols.get())},
            "camera":     {"exposure_us": int(self.cam_exposure.get())},
            "processing": {"kernel_center": int(self.proc_kernel.get()),
                           "thresh_c": int(self.proc_thresh_c.get())},
            "aoi": {"x": int(self.aoi_x.get()), "y": int(self.aoi_y.get()),
                    "w": int(self.aoi_w.get()), "h": int(self.aoi_h.get())},
            "trigger": {"diff_threshold": int(self.diff_thr.get()),
                        "occupancy_threshold": float(self.occ_thr.get()),
                        "debounce_on": int(self.deb_on.get()),
                        "debounce_off": int(self.deb_off.get())},
            "decode": {"pad_px": int(self.dec_pad.get()),
                       "invert": bool(self.dec_invert.get()),
                       "timeout_fast": int(self.dec_t_fast.get()),
                       "timeout_std":  int(self.dec_t_std.get())},
            "background_base64_png": bg64,
            "rois": [{"id": r.id, "cx": r.cx, "cy": r.cy,
                      "w": r.w,  "h": r.h, "angle": r.angle}
                     for r in self.rois],
        }

    def _load_project_dict(self, data: dict):
        self._project_name = data.get("project_name", "projeto")
        cam  = data.get("camera", {})
        proc = data.get("processing", {})
        aoi  = data.get("aoi", {})
        trig = data.get("trigger", {})
        dec  = data.get("decode", {})
        ui = data.get("ui", {})

        self.cam_exposure.set(int(cam.get("exposure_us", 8000)))
        self.proc_kernel.set(int(proc.get("kernel_center", 5)))
        self.proc_thresh_c.set(int(proc.get("thresh_c", 6)))
        self.aoi_x.set(int(aoi.get("x",0))); self.aoi_y.set(int(aoi.get("y",0)))
        self.aoi_w.set(int(aoi.get("w",0))); self.aoi_h.set(int(aoi.get("h",0)))
        self.diff_thr.set(int(trig.get("diff_threshold", 10)))
        self.occ_thr.set(float(trig.get("occupancy_threshold", 0.80)))
        self.deb_on.set(int(trig.get("debounce_on", 4)))
        self.deb_off.set(int(trig.get("debounce_off", 6)))
        self.dec_pad.set(int(dec.get("pad_px", 30)))
        self.dec_invert.set(bool(dec.get("invert", False)))
        self.dec_t_fast.set(int(dec.get("timeout_fast", 60)))
        self.dec_t_std.set(int(dec.get("timeout_std", 90)))
        self.mosaic_cols.set(int(ui.get("mosaic_cols", 3)))

        self.rois = []
        for r in data.get("rois", []):
            self.rois.append(ROI(id=int(r["id"]), cx=float(r["cx"]),
                                 cy=float(r["cy"]), w=float(r["w"]),
                                 h=float(r["h"]),  angle=float(r.get("angle",0))))

        bg64 = data.get("background_base64_png")
        self._loaded_bg = None
        if bg64:
            try:
                b = base64.b64decode(bg64)
                arr = np.frombuffer(b, np.uint8)
                bg = cv2.imdecode(arr, cv2.IMREAD_GRAYSCALE)
                if bg is not None:
                    self._loaded_bg = bg
            except Exception:
                self._loaded_bg = None
        with self._lock:
            self._shared["has_bg"] = (self._loaded_bg is not None)

        # se o engine estiver rodando, aplica imediatamente
        if self.engine and self._loaded_bg is not None:
            self.engine.panel_detector.set_background_gray(self._loaded_bg)
        self.lbl_project.config(text=f"● {self._project_name}", fg=ACCENT)
        self.app.state.project_data = data
        self.app.state.rois = self.rois

    def save_project(self):
        proj = self._project_dict()
        if not proj.get("background_base64_png"):
            if not messagebox.askyesno("Sem BG", "Projeto está sem Background. Salvar mesmo assim?"):
                return
        name = simpledialog.askstring("Projeto", "Nome:", initialvalue=self._project_name)
        if not name:
            return
        self._project_name = name
        os.makedirs("projects", exist_ok=True)
        path = filedialog.asksaveasfilename(
            title="Salvar Projeto", defaultextension=".json",
            filetypes=[("JSON","*.json")], initialdir="projects",
            initialfile=f"project_{name}.json")
        if not path:
            return
        save_json(path, self._project_dict())
        self.app.state.project_path = path
        self.lbl_project.config(text=f"● {name}", fg=ACCENT)
        messagebox.showinfo("Salvo", f"✅ Projeto salvo:\n{path}")

    def load_project(self):
        path = filedialog.askopenfilename(
            title="Carregar Projeto",
            filetypes=[("JSON","*.json")], initialdir="projects")
        if not path:
            return
        data = load_json(path)
        if not data:
            messagebox.showerror("Erro", "Falha ao ler arquivo.")
            return
        self._load_project_dict(data)
        self.app.state.project_path = path
        messagebox.showinfo("Carregado", f"✅ {self._project_name} carregado.")

    # ── ROI helpers ──────────────────────────────────────────────

    def _next_roi_id(self):
        return max([r.id for r in self.rois], default=0) + 1

    def _select_roi(self, roi_id):
        self.selected_roi_id = roi_id
        roi = next((r for r in self.rois if r.id == roi_id), None)
        if roi:
            self.roi_cx.set(roi.cx); self.roi_cy.set(roi.cy)
            self.roi_w.set(roi.w);   self.roi_h.set(roi.h)
            self.roi_angle.set(roi.angle)

    def apply_roi_fields(self):
        roi = next((r for r in self.rois if r.id == self.selected_roi_id), None)
        if not roi:
            return
        roi.cx=float(self.roi_cx.get()); roi.cy=float(self.roi_cy.get())
        roi.w=max(1,float(self.roi_w.get())); roi.h=max(1,float(self.roi_h.get()))
        roi.angle=float(self.roi_angle.get())

    def delete_roi(self):
        if self.selected_roi_id is None:
            return
        self.rois = [r for r in self.rois if r.id != self.selected_roi_id]
        self.selected_roi_id = None

    def clear_rois(self):
        if self.rois and messagebox.askyesno("ROIs","Remover todas?"):
            self.rois = []; self.selected_roi_id = None

    def clear_debug(self):
        with self._lock:
            self._shared["debug_img"] = None
        self.canvas_debug.delete("all")

    # ── AOI selection ────────────────────────────────────────────
    def start_select_aoi(self):
        if self._last_bgr_orig is None:
            messagebox.showwarning("AOI","Inicie o engine primeiro.")
            return
        self._aoi_active = True
        self._aoi_start  = None
        self._aoi_curr   = None
        messagebox.showinfo("AOI","Clique e arraste no canvas ORIGINAL para definir a AOI.")

    # ── Zoom/pan + ROI mouse editing ─────────────────────────────
    def _canvas_to_img(self, which, cx, cy):
        zp = self.zp_orig if which == "original" else self.zp_dbg
        s  = zp.scale if zp.scale > 0 else 1.0
        return (cx - zp.offx) / s, (cy - zp.offy) / s

    def _bind_zoom_pan(self, canvas, zp, which):
        def _wheel(e):
            f = 1.15 if e.delta > 0 else 1/1.15
            old = zp.scale
            zp.scale = float(np.clip(old*f, zp.min_scale, zp.max_scale))
            r = zp.scale/old
            zp.offx = e.x - r*(e.x - zp.offx)
            zp.offy = e.y - r*(e.y - zp.offy)
            self._redraw(which); return "break"

        def _press(e):
            ix, iy = self._canvas_to_img(which, e.x, e.y)
            ctrl  = bool(e.state & 0x0004)
            shift = bool(e.state & 0x0001)
            alt   = bool(e.state & 0x20000)

            if which == "original" and self.roi_edit_mode.get():
                if self.roi_draw_mode.get() and not ctrl and not shift and not alt:
                    self._roi_draw_start = (e.x, e.y)
                    self._roi_draw_curr = (e.x, e.y)
                    return "break"
                for r in self.rois:
                    if r.contains_point(ix, iy):
                        self._select_roi(r.id)
                        self._roi_orig = {"cx":r.cx,"cy":r.cy,"w":r.w,"h":r.h,"angle":r.angle}
                        self._roi_start_pos = (ix, iy)
                        if ctrl:   self._roi_action = "move"
                        elif shift:
                            self._roi_action = "resize"
                            self._roi_corner_idx = r.nearest_corner(ix, iy)
                        elif alt:  self._roi_action = "rotate"
                        return "break"
                self.selected_roi_id = None
                return "break"

            if which == "original" and self._aoi_active:
                self._aoi_start = (e.x, e.y)
                self._aoi_curr  = (e.x, e.y)
                return "break"

            zp._dragging = True; zp._lastx = e.x; zp._lasty = e.y
            return "break"

        def _motion(e):
            if which == "original" and self.roi_draw_mode.get() and self._roi_draw_start:
                # x0, y0 = self._roi_draw_start
                self._roi_draw_curr = (e.x, e.y)
                return "break"

            if self._roi_action and self.selected_roi_id is not None:
                roi = next((r for r in self.rois if r.id == self.selected_roi_id), None)
                if roi and self._roi_orig and self._roi_start_pos:
                    ix, iy = self._canvas_to_img(which, e.x, e.y)
                    sx, sy = self._roi_start_pos
                    dx, dy = ix-sx, iy-sy
                    if self._roi_action == "move":
                        roi.cx = self._roi_orig["cx"] + dx
                        roi.cy = self._roi_orig["cy"] + dy
                    elif self._roi_action == "resize":
                        roi.w = max(10, self._roi_orig["w"] + abs(dx)*2)
                        roi.h = max(10, self._roi_orig["h"] + abs(dy)*2)
                    elif self._roi_action == "rotate":
                        roi.angle = math.degrees(math.atan2(
                            iy - self._roi_orig["cy"], ix - self._roi_orig["cx"]))
                    self._select_roi(roi.id)
                return "break"

            if which == "original" and self._aoi_active and self._aoi_start:
                self._aoi_curr = (e.x, e.y)
                return "break"

            if zp._dragging:
                zp.offx += e.x - zp._lastx; zp.offy += e.y - zp._lasty
                zp._lastx = e.x; zp._lasty = e.y
                self._redraw(which)
            return "break"

        def _release(e):
            ix, iy = self._canvas_to_img(which, e.x, e.y)

            if which == "original" and self.roi_draw_mode.get() and self._roi_draw_start:
                x0c, y0c = self._roi_draw_start
                x1c, y1c = e.x, e.y

                ix0, iy0 = self._canvas_to_img(which, x0c, y0c)
                ix1, iy1 = self._canvas_to_img(which, x1c, y1c)

                w = abs(ix1 - ix0);
                h = abs(iy1 - iy0)
                if w >= 10 and h >= 10:
                    rid = self._next_roi_id()
                    self.rois.append(ROI(id=rid, cx=(ix0 + ix1) / 2, cy=(iy0 + iy1) / 2,
                                         w=w, h=h, angle=0.0))
                    self._select_roi(rid)

                self._roi_draw_start = None
                self._roi_draw_curr = None
                return "break"

            if self._roi_action:
                self._roi_action = None; self._roi_start_pos = None
                self._roi_orig = None;   self._roi_corner_idx = None
                return "break"

            if which == "original" and self._aoi_active and self._aoi_start:
                x0c, y0c = self._aoi_start
                ix0, iy0 = self._canvas_to_img(which, x0c, y0c)
                x = int(min(ix0,ix)); y = int(min(iy0,iy))
                w = int(abs(ix-ix0)); h = int(abs(iy-iy0))
                if w >= 10 and h >= 10:
                    self.aoi_x.set(x); self.aoi_y.set(y)
                    self.aoi_w.set(w); self.aoi_h.set(h)
                    self._apply_aoi()
                self._aoi_start = None
                self._aoi_curr = None
                self._aoi_active = False
                return "break"

            zp._dragging = False
            return "break"

        def _reset(e):
            zp.reset(); self._redraw(which); return "break"

        canvas.bind("<MouseWheel>", _wheel)
        canvas.bind("<ButtonPress-1>",   _press)
        canvas.bind("<ButtonRelease-1>", _release)
        canvas.bind("<B1-Motion>",       _motion)
        canvas.bind("<Double-Button-1>", _reset)

    def _redraw(self, which):
        bgr = self._last_bgr_orig if which == "original" else self._last_bgr_dbg
        if bgr is not None:
            self._draw_on_canvas(self.canvas_original if which=="original"
                                 else self.canvas_debug, bgr, which)

    def _draw_on_canvas(self, canvas, bgr, which):
        cw, ch = canvas.winfo_width(), canvas.winfo_height()
        if cw < 2 or ch < 2:
            return
        zp = self.zp_orig if which == "original" else self.zp_dbg
        M = np.array([[zp.scale,0,zp.offx],[0,zp.scale,zp.offy]], np.float32)
        img = cv2.warpAffine(bgr, M, (cw, ch),
                             flags=cv2.INTER_LINEAR, borderValue=(18,20,28))
        rgb = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
        imgtk = ImageTk.PhotoImage(Image.fromarray(rgb))
        canvas.delete("all")
        canvas.create_image(0, 0, anchor="nw", image=imgtk)
        if which == "original":
            self._img_orig_tk = imgtk
        else:
            self._img_dbg_tk = imgtk

        if self.paused.get():
            c = self.canvas_original
            w = c.winfo_width()
            h = c.winfo_height()
            c.create_rectangle(0, 0, w, 42, fill="#000000", outline="")
            c.create_text(14, 21, anchor="w", text="PAUSED", fill="#f59e0b",
                          font=("Segoe UI", 12, "bold"))

    # ── UI update loop ────────────────────────────────────────────
    def _schedule_ui(self):
        self._update_ui()
        self._ui_job = self.after(30, self._schedule_ui)

    def _update_ui(self):
        with self._lock:
            frame     = self._shared.get("frame")
            fps       = float(self._shared.get("fps", 0))
            dec_ms    = float(self._shared.get("dec_ms", 0))
            occ       = float(self._shared.get("occ", 0))
            has_bg    = bool(self._shared.get("has_bg", False))
            present   = bool(self._shared.get("present", False))
            dbg_img   = self._shared.get("debug_img")
            passed    = self._shared.get("passed")
            state_str = self._shared.get("state", "WAIT_PRESENT")

        if frame is None and state_str == "STOPPED":
            _canvas_stop_overlay(self.canvas_original, "STOPPED", "Clique em Iniciar")
            # _canvas_stop_overlay(self.canvas_debug, "STOPPED", "Clique em Iniciar")
            return

        self.lbl_fps.config(text=f"FPS: {fps:.1f}")
        self.lbl_dec.config(text=f"Decode: {dec_ms:.0f} ms")
        self.lbl_state.config(text=f"State: {state_str}")
        self.lbl_occ.config(
            text=f"Occ: {occ*100:.1f}%  BG: {'✓' if has_bg else '✗'}  "
                 f"{'PRESENTE' if present else 'vazio'}")

        if passed is None:
            self.lbl_passfail.config(text="–", fg=MUTED)
            self._status_bar.config(bg=MUTED)
        elif passed:
            self.lbl_passfail.config(text="PASSED", fg=GREEN)
            self._status_bar.config(bg=GREEN)
        else:
            self.lbl_passfail.config(text="FAILED", fg=RED)
            self._status_bar.config(bg=RED)

        # draw original
        if frame is not None:
            if self.paused.get():
                if self._paused_frame is None and frame is not None:
                    self._paused_frame = frame.copy()
                draw = self._paused_frame
            else:
                draw = frame
                self._paused_frame = None

            # ✅ agora draw nunca será None aqui
            orig = cv2.cvtColor(draw, cv2.COLOR_GRAY2BGR) if draw.ndim == 2 else draw.copy()
            if self.roi_draw_mode.get() and self._roi_draw_start and self._roi_draw_curr:
                x0c, y0c = self._roi_draw_start
                x1c, y1c = self._roi_draw_curr
                ix0, iy0 = self._canvas_to_img("original", x0c, y0c)
                ix1, iy1 = self._canvas_to_img("original", x1c, y1c)
                x0, y0 = int(min(ix0, ix1)), int(min(iy0, iy1))
                x1, y1 = int(max(ix0, ix1)), int(max(iy0, iy1))

                # retângulo "tracejado" simples (segmentado) — opcional
                step = 14
                for x in range(x0, x1, step):
                    cv2.line(orig, (x, y0), (min(x + step // 2, x1), y0), (0, 255, 0), 3)
                    cv2.line(orig, (x, y1), (min(x + step // 2, x1), y1), (0, 255, 0), 3)
                for y in range(y0, y1, step):
                    cv2.line(orig, (x0, y), (x0, min(y + step // 2, y1)), (0, 255, 0), 3)
                    cv2.line(orig, (x1, y), (x1, min(y + step // 2, y1)), (0, 255, 0), 3)

                cv2.putText(orig, "Desenhando ROI...", (x0 + 8, max(30, y0 - 10)),
                            cv2.FONT_HERSHEY_SIMPLEX, 0.9, (0, 255, 0), 2)
            # AOI overlay (fixa)
            ax, ay, aw, ah = (int(self.aoi_x.get()), int(self.aoi_y.get()),
                              int(self.aoi_w.get()), int(self.aoi_h.get()))
            if aw > 1 and ah > 1:
                cv2.rectangle(orig, (ax,ay), (ax+aw,ay+ah), (255,0,255), 10)
                cv2.putText(orig, f"AOI {occ*100:.0f}%",
                            (ax+12, ay+40), cv2.FONT_HERSHEY_SIMPLEX,
                            1.2, (255,0,255), 2)

            # ✅ AOI preview durante seleção (não some mais)
            if self._aoi_active and self._aoi_start and self._aoi_curr:
                x0c, y0c = self._aoi_start
                x1c, y1c = self._aoi_curr
                ix0, iy0 = self._canvas_to_img("original", x0c, y0c)
                ix1, iy1 = self._canvas_to_img("original", x1c, y1c)
                x = int(min(ix0, ix1)); y = int(min(iy0, iy1))
                w = int(abs(ix1 - ix0)); h = int(abs(iy1 - iy0))
                if w > 2 and h > 2:
                    cv2.rectangle(orig, (x,y), (x+w,y+h), (255,0,255), 6)
                    cv2.putText(orig, "Selecionando AOI...", (x+10, max(30,y-10)),
                                cv2.FONT_HERSHEY_SIMPLEX, 1.0, (255,0,255), 2)

            # ROI overlay
            if self.show_overlay.get():
                for roi in self.rois:
                    sel = (roi.id == self.selected_roi_id)
                    col = (0,180,255) if sel else (0,255,255)
                    cv2.polylines(orig, [roi.get_rect_points()], True, col, 6)
                    cv2.putText(orig, f"R{roi.id}",
                                (int(roi.cx)+4, int(roi.cy)-4),
                                cv2.FONT_HERSHEY_SIMPLEX, 0.8, col, 2)
                    if sel:
                        for cx_, cy_ in roi.get_corner_positions():
                            cv2.circle(orig,(int(cx_),int(cy_)),6,(255,0,255),-1)

            self._last_bgr_orig = orig
            self._draw_on_canvas(self.canvas_original, orig, "original")

        # draw debug
        if dbg_img is not None and isinstance(dbg_img, np.ndarray):
            self._last_bgr_dbg = dbg_img
            self._draw_on_canvas(self.canvas_debug, dbg_img, "debug")


# ══════════════════════════════════════════════════════════════════
#  PRODUCTION PAGE
# ══════════════════════════════════════════════════════════════════

class ProductionPage(tk.Frame):
    def __init__(self, parent, app: App):
        super().__init__(parent, bg=BG_DEEP)
        self.app = app

        # ✅ FIX: vars CMC existem aqui também (você usava e não existia)
        self.cmc_enabled = tk.BooleanVar(value=True)
        self.cmc_batch   = tk.BooleanVar(value=True)

        self._active = False
        self._run_id = 0

        self._engine: Optional[Engine] = None
        self._lock = threading.Lock()
        self._shared: Dict[str, Any] = {
            "frame": None, "fps": 0.0, "dec_ms": 0.0,
            "occ": 0.0, "has_bg": False, "present": False,
            "codes": [], "debug_img": None, "passed": None,
            "state": "WAIT_PRESENT", "total": 0, "ok_count": 0, "fail_count": 0,
        }
        self._img_tk   = None
        self._img_dbg  = None
        self._last_bgr = None
        self._last_dbg = None
        self._zp = _ZoomPan()
        self._build()
        self._ui_job = self.after(40, self._schedule_ui)

        self._hist = deque(maxlen=600)

        self._log = DailyLog(base_dir="logs")

    def _hist_add(self, level: str, msg: str):
        ts = datetime.now().strftime("%H:%M:%S")
        line = f"[{ts}] [{level}] {msg}"
        with self._lock:
            self._hist.append(line)

        # log em arquivo por data
        u = (self.app.state.user or {}).get("username", "—")
        proj = (self.app.state.project_data or {}).get("project_name", "—")
        self._log.write_line(f"HIST | user={u} | project={proj} | {line}")

    def _hist_refresh_text(self):
        with self._lock:
            text = "\n".join(self._hist)

        self.txt_hist.config(state="normal")
        self.txt_hist.delete("1.0", "end")
        self.txt_hist.insert("end", text + ("\n" if text else ""))
        self.txt_hist.config(state="disabled")
        self.txt_hist.see("end")

    def on_hide(self):
        self._active = False
        self._run_id += 1
        self.stop_prod()

    def stop_prod(self):
        eng = self._engine
        self._active = False
        self._run_id += 1
        if not eng:
            return

        eng.on_frame = None
        eng.on_trigger_result = None
        eng.on_occupancy = None
        eng.on_state_change = None

        u = (self.app.state.user or {}).get("username", "—")
        proj = (self.app.state.project_data or {}).get("project_name", "—")
        with self._lock:
            okc = self._shared.get("ok_count", 0)
            failc = self._shared.get("fail_count", 0)
            total = self._shared.get("total", 0)
        self._log.write_line(f"SESSION END | user={u} | project={proj} | total={total} ok={okc} fail={failc}")

        try:
            eng.stop()
        except Exception:
            pass

        self._engine = None
        self._cam_dot.config(fg=MUTED)

        # limpa frame e desenha overlay STOP
        with self._lock:
            self._shared["frame"] = None
            self._shared["codes"] = []
            self._shared["passed"] = None
            self._shared["state"] = "STOPPED"

        self.after(0, lambda: _canvas_stop_overlay(self.canvas_live, "STOPPED", "Carregue projeto / clique em Iniciar"))

    def _build(self):
        bar = _topbar(self, "MODO PRODUÇÃO",
                      title_color=GREEN,
                      back_cmd=lambda: self._go_menu())

        _btn(bar, "▶  Iniciar", command=self.start_prod,
             style="success", padx=12, pady=5).pack(side="right", padx=4, pady=10)
        _btn(bar, "⏹  Parar",   command=self.stop_prod,
             style="danger",  padx=12, pady=5).pack(side="right", padx=4, pady=10)
        _btn(bar, "🔁  Trigger Manual", command=self.rearm,
             style="warn",    padx=10, pady=5).pack(side="right", padx=4, pady=10)
        _btn(bar, "📂  Carregar Projeto", command=self.load_project,
             style="ghost",   padx=10, pady=5).pack(side="right", padx=4, pady=10)

        self.lbl_proj = tk.Label(bar, text="Nenhum projeto",
                                 bg=BG_PANEL, fg=TEXT_DIM, font=FONT_LBL)
        self.lbl_proj.pack(side="right", padx=14)

        body = tk.Frame(self, bg=BG_DEEP)
        body.pack(fill="both", expand=True, padx=8, pady=8)

        vid = tk.Frame(body, bg=BG_CARD,
                       highlightbackground=BORDER, highlightthickness=1)
        vid.pack(side="left", fill="both", expand=True, padx=(0,8))

        vid_h = tk.Frame(vid, bg=BG_PANEL)
        vid_h.pack(fill="x")

        self._cam_dot = tk.Label(vid_h, text="●", bg=BG_PANEL, fg=MUTED,
                                 font=("Segoe UI",10))
        self._cam_dot.pack(side="left", padx=(10,4), pady=6)
        tk.Label(vid_h, text="LIVE", bg=BG_PANEL, fg=TEXT_DIM,
                 font=FONT_BOLD).pack(side="left")
        self.lbl_fps = tk.Label(vid_h, text="", bg=BG_PANEL,
                                fg=ACCENT, font=FONT_MONO)
        self.lbl_dec = tk.Label(vid_h, text="Decode: – ms",
                                bg=BG_PANEL, fg=YELLOW, font=FONT_MONO)
        self.lbl_dec.pack(side="right", padx=12)

        self.lbl_fps.pack(side="right", padx=12)

        self.canvas_live = tk.Canvas(vid, bg="#090b0f", highlightthickness=0)
        self.canvas_live.pack(fill="both", expand=True, padx=4, pady=4)

        # dbg_wrap = tk.Frame(vid, bg=BG_CARD,
        #                     highlightbackground=BORDER, highlightthickness=1)
        # dbg_wrap.pack(fill="x", padx=0, pady=(4, 0))
        #
        # dbg_h2 = tk.Frame(dbg_wrap, bg=BG_PANEL)
        # dbg_h2.pack(fill="x")
        #
        # tk.Label(dbg_h2, text="DEBUG  ·  último trigger",
        #          bg=BG_PANEL, fg=TEXT_DIM, font=FONT_BOLD
        # ).pack(side="left", padx=10, pady=5)
        #
        # self.lbl_dec = tk.Label(dbg_h2, text="Decode: –",
        #                         bg=BG_PANEL, fg=YELLOW, font=FONT_MONO)
        # self.lbl_dec.pack(side="right", padx=10)
        #
        # self.canvas_debug = tk.Canvas(dbg_wrap, bg="#090b0f",
        #                               highlightthickness=0, height=220)
        # self.canvas_debug.pack(fill="x", padx=4, pady=4)

        right = tk.Frame(body, bg=BG_DEEP, width=360)
        right.pack(side="right", fill="y")
        right.pack_propagate(False)

        status_c = tk.Frame(right, bg=BG_CARD,
                            highlightbackground=BORDER, highlightthickness=1)
        status_c.pack(fill="x", padx=6, pady=(0,6))
        self._status_bar = tk.Frame(status_c, bg=MUTED, height=4)
        self._status_bar.pack(fill="x")
        status_i = tk.Frame(status_c, bg=BG_CARD, padx=14, pady=12)
        status_i.pack(fill="x")

        self.lbl_result = tk.Label(status_i, text="AGUARDANDO",
                                   bg=BG_CARD, fg=MUTED,
                                   font=("Segoe UI", 24, "bold"))
        self.lbl_result.pack(anchor="w")
        self.lbl_state = tk.Label(status_i, text="State: WAIT_PRESENT",
                                  bg=BG_CARD, fg=TEXT_DIM, font=FONT_MONO)
        self.lbl_state.pack(anchor="w")
        self.lbl_occ = tk.Label(status_c, text="Occ: –%  BG: –",
                                bg=BG_CARD, fg=TEXT_SEC, font=FONT_LBL)
        self.lbl_occ.pack(anchor="w", padx=14, pady=(0,8))

        cmc_body = _section(right, "CMControl MQTT")
        r = _row(cmc_body)
        _chk(r, "Habilitado", self.cmc_enabled, bg=BG_CARD).pack(side="left")
        _chk(r, "Batch mode", self.cmc_batch, bg=BG_CARD).pack(side="left", padx=12)

        cnt = tk.Frame(right, bg=BG_DEEP)
        cnt.pack(fill="x", padx=6, pady=(0,6))
        self._cnt_widgets = {}
        for i, (lbl, color, key) in enumerate([
            ("OK",    GREEN,    "ok_count"),
            ("FAIL",  RED,      "fail_count"),
            ("TOTAL", TEXT_SEC, "total"),
        ]):
            c = tk.Frame(cnt, bg=BG_CARD,
                         highlightbackground=BORDER, highlightthickness=1)
            c.grid(row=0, column=i, sticky="ew", padx=(0 if i==0 else 4, 0))
            cnt.grid_columnconfigure(i, weight=1)
            inner = tk.Frame(c, bg=BG_CARD, padx=8, pady=8)
            inner.pack()
            tk.Label(inner, text=lbl, bg=BG_CARD, fg=TEXT_DIM,
                     font=("Segoe UI", 8, "bold")).pack(anchor="w")
            v = tk.Label(inner, text="0", bg=BG_CARD, fg=color,
                         font=("Segoe UI", 20, "bold"))
            v.pack(anchor="w")
            self._cnt_widgets[key] = v

        tbl_body = _section(right, "LEITURAS — último trigger")
        cols = ("ROI", "Código", "Decode", "Apont.", "Motivo", "ms")
        self.tree = ttk.Treeview(tbl_body, columns=cols, show="headings", height=8)

        self.tree.bind("<Double-Button-1>", lambda e: self.open_readings_popup())

        self.tree.heading("ROI", text="ROI")
        self.tree.heading("Código", text="Código")
        self.tree.heading("Decode", text="Decode")
        self.tree.heading("Apont.", text="Apont.")
        self.tree.heading("Motivo", text="Motivo")
        self.tree.heading("ms", text="ms")

        self.tree.column("ROI", width=20, anchor="center")
        self.tree.column("Código", width=80, anchor="w")
        self.tree.column("Decode", width=70, anchor="center")
        self.tree.column("Apont.", width=70, anchor="center")
        self.tree.column("Motivo", width=80, anchor="w")
        self.tree.column("ms", width=55, anchor="center")
        scr = ttk.Scrollbar(tbl_body, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scr.set)
        self.tree.pack(side="left", fill="both", expand=True)
        scr.pack(side="right", fill="y")
        self.tree.tag_configure("ok",   foreground=GREEN)
        self.tree.tag_configure("fail", foreground=RED)

        actions = tk.Frame(tbl_body, bg=BG_CARD)
        actions.pack(fill="x", pady=(0, 6))

        _btn(actions, "🔎 Expandir", command=self.open_readings_popup,
             style="ghost", padx=10, pady=5).pack(side="left")

        _btn(actions, "📋 Copiar", command=self.copy_readings_text,
             style="ghost", padx=10, pady=5).pack(side="left", padx=6)

        _btn(actions, "💾 Exportar .txt", command=self.export_readings_txt,
             style="primary", padx=10, pady=5).pack(side="right")

        hist_body = _section(right, "HISTÓRICO")
        h_actions = tk.Frame(hist_body, bg=BG_CARD)
        h_actions.pack(fill="x", pady=(0, 6))

        _btn(h_actions, "🔎 Expandir", command=self.open_history_popup,
             style="ghost", padx=10, pady=5).pack(side="left")

        _btn(h_actions, "📋 Copiar", command=self.copy_history_text,
             style="ghost", padx=10, pady=5).pack(side="left", padx=6)

        _btn(h_actions, "💾 Exportar .txt", command=self.export_history_txt,
             style="primary", padx=10, pady=5).pack(side="right")
        self.txt_hist = tk.Text(hist_body, height=8, bg=BG_CARD, fg=TEXT_SEC,
                                font=FONT_MONO, relief="flat",
                                insertbackground=ACCENT, state="disabled")
        self.txt_hist.pack(fill="x")

    def _readings_rows(self):
        # retorna uma lista de tuplas igual ao que você mostra na tree
        with self._lock:
            codes = list(self._shared.get("codes", []))
            roi_stat = dict(self._shared.get("roi_stat", {}) or {})
            cmc_needed = bool(self._shared.get("cmc_needed", False))

        rows = []
        for r in codes:
            rid = int(r.get("roi_id", 0))
            st = roi_stat.get(rid, {})
            txt = st.get("text") or "—"

            dec_ok = bool(st.get("decode_ok"))
            dec_str = "OK" if dec_ok else "NOK"

            if not cmc_needed:
                cmc_str = "—"
                motivo = ""
            else:
                cmc_ok = st.get("cmc_ok", None)
                if cmc_ok is None:
                    cmc_str = "..."
                    motivo = "Aguardando CMControl"
                else:
                    cmc_str = "OK" if cmc_ok else "NOK"
                    motivo = (st.get("cmc_reason") or "")
                    det = (st.get("cmc_detail") or "")
                    if det and not cmc_ok:
                        motivo = f"{motivo}: {det}" if motivo else det

            ms = f"{float(r.get('ms', 0)):.0f}"
            rows.append((f"R{rid}", txt, dec_str, cmc_str, motivo, ms))
        return rows

    def _readings_text(self) -> str:
        rows = self._readings_rows()
        if not rows:
            return "Sem dados do último trigger.\n"

        header = ["ROI", "Código", "Decode", "Apont.", "Motivo", "ms"]
        lines = ["\t".join(header)]
        for row in rows:
            lines.append("\t".join([str(x) for x in row]))
        return "\n".join(lines) + "\n"

    def copy_readings_text(self):
        text = self._readings_text()
        self.clipboard_clear()
        self.clipboard_append(text)

    def export_readings_txt(self):
        text = self._readings_text()
        path = filedialog.asksaveasfilename(
            title="Exportar leituras do último trigger",
            defaultextension=".txt",
            filetypes=[("TXT", "*.txt")],
            initialfile=f"leituras_{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}.txt"
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        messagebox.showinfo("Exportado", f"✅ Arquivo salvo:\n{path}")

    def open_readings_popup(self):
        win = tk.Toplevel(self)
        win.title("Leituras — Último trigger (Expandido)")
        win.geometry("1100x650")
        win.configure(bg=BG_DEEP)

        top = tk.Frame(win, bg=BG_PANEL, highlightbackground=BORDER_LT, highlightthickness=1)
        top.pack(fill="x")

        tk.Label(top, text="Leituras — Último trigger", bg=BG_PANEL, fg=TEXT_PRI,
                 font=("Segoe UI", 11, "bold")).pack(side="left", padx=12, pady=10)

        _btn(top, "📋 Copiar", command=lambda: (win.clipboard_clear(), win.clipboard_append(self._readings_text())),
             style="ghost", padx=10, pady=5).pack(side="right", padx=6, pady=8)

        _btn(top, "💾 Exportar .txt", command=self.export_readings_txt,
             style="primary", padx=10, pady=5).pack(side="right", padx=6, pady=8)

        # tabela grande
        body = tk.Frame(win, bg=BG_DEEP, padx=10, pady=10)
        body.pack(fill="both", expand=True)

        cols = ("ROI", "Código", "Decode", "Apont.", "Motivo", "ms")
        tv = ttk.Treeview(body, columns=cols, show="headings")
        for c in cols:
            tv.heading(c, text=c)

        tv.column("ROI", width=70, anchor="center")
        tv.column("Código", width=260, anchor="w")
        tv.column("Decode", width=90, anchor="center")
        tv.column("Apont.", width=90, anchor="center")
        tv.column("Motivo", width=470, anchor="w")
        tv.column("ms", width=80, anchor="center")

        scr = ttk.Scrollbar(body, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=scr.set)
        tv.pack(side="left", fill="both", expand=True)
        scr.pack(side="right", fill="y")

        # popula com os dados atuais
        for row in self._readings_rows():
            tv.insert("", "end", values=row)

    def _history_text(self) -> str:
        with self._lock:
            return "\n".join(list(self._hist)) + ("\n" if len(self._hist) else "")

    def copy_history_text(self):
        text = self._history_text()
        self.clipboard_clear()
        self.clipboard_append(text)

    def export_history_txt(self):
        text = self._history_text()
        path = filedialog.asksaveasfilename(
            title="Exportar histórico",
            defaultextension=".txt",
            filetypes=[("TXT", "*.txt")],
            initialfile=f"historico_{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}.txt"
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        messagebox.showinfo("Exportado", f"✅ Arquivo salvo:\n{path}")

    def open_history_popup(self):
        win = tk.Toplevel(self)
        win.title("Histórico (Expandido)")
        win.geometry("1100x650")
        win.configure(bg=BG_DEEP)

        top = tk.Frame(win, bg=BG_PANEL, highlightbackground=BORDER_LT, highlightthickness=1)
        top.pack(fill="x")

        tk.Label(top, text="Histórico", bg=BG_PANEL, fg=TEXT_PRI,
                 font=("Segoe UI", 11, "bold")).pack(side="left", padx=12, pady=10)

        _btn(top, "📋 Copiar", command=lambda: (win.clipboard_clear(), win.clipboard_append(self._history_text())),
             style="ghost", padx=10, pady=5).pack(side="right", padx=6, pady=8)

        _btn(top, "💾 Exportar .txt", command=self.export_history_txt,
             style="primary", padx=10, pady=5).pack(side="right", padx=6, pady=8)

        body = tk.Frame(win, bg=BG_DEEP, padx=10, pady=10)
        body.pack(fill="both", expand=True)

        txt = tk.Text(body, bg=BG_CARD, fg=TEXT_SEC, font=FONT_MONO,
                      relief="flat", insertbackground=ACCENT)
        scr = ttk.Scrollbar(body, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=scr.set)

        txt.pack(side="left", fill="both", expand=True)
        scr.pack(side="right", fill="y")

        txt.insert("1.0", self._history_text())

    def _go_menu(self):
        self.stop_prod()
        self.app.show("MenuPage")

    def on_show(self):
        pd = self.app.state.project_data
        if pd:
            self.lbl_proj.config(text=f"● {pd.get('project_name','?')}", fg=ACCENT)

    def load_project(self):
        path = filedialog.askopenfilename(
            title="Carregar Projeto",
            filetypes=[("JSON","*.json")], initialdir="projects")
        if not path:
            return
        data = load_json(path)
        if not data:
            messagebox.showerror("Erro","Falha ao ler arquivo."); return
        self.app.state.project_path = path
        self.app.state.project_data = data

        cfg_page = self.app.frames.get("ConfigPage")
        if cfg_page:
            cfg_page._load_project_dict(data)

        self.lbl_proj.config(text=f"● {data.get('project_name','?')}", fg=ACCENT)
        messagebox.showinfo("Projeto", f"✅ {data.get('project_name')} carregado.")
        u = (self.app.state.user or {}).get("username", "—")
        proj = data.get("project_name", "—")
        self._log.write_line(f"PROJECT LOADED | user={u} | project={proj} | path={path}")

    def _build_engine_from_project(self) -> Optional[Engine]:
        data = self.app.state.project_data
        if not data:
            messagebox.showwarning("Projeto","Carregue um projeto primeiro.")
            return None

        camera  = BaslerCameraController()
        decoder = DataMatrixDecoder(use_neural=True)
        pd      = PanelPresenceDetector(aoi=(0,0,0,0), params=PresenceParams())
        eng     = Engine(camera, decoder, pd)

        ui = data.get("ui", {})
        eng.mosaic_cols = int(ui.get("mosaic_cols", 3))

        eng.rois = []
        for r in data.get("rois", []):
            eng.rois.append(ROI(id=int(r["id"]), cx=float(r["cx"]),
                                cy=float(r["cy"]), w=float(r["w"]),
                                h=float(r["h"]),  angle=float(r.get("angle",0))))
        self.app.state.rois = eng.rois

        dec = data.get("decode", {})
        proc = data.get("processing", {})
        eng.decode_params = {
            "pad_px":        int(dec.get("pad_px",30)),
            "invert":        bool(dec.get("invert",False)),
            "timeout_fast":  int(dec.get("timeout_fast",60)),
            "timeout_std":   int(dec.get("timeout_std",90)),
            "kernel_center": int(proc.get("kernel_center",5)),
            "thresh_c":      int(proc.get("thresh_c",6)),
        }

        aoi = data.get("aoi", {})
        if aoi.get("w",0) > 0:
            pd.set_aoi(int(aoi["x"]), int(aoi["y"]),
                       int(aoi["w"]), int(aoi["h"]))
        trig = data.get("trigger", {})
        p = pd.params
        p.diff_threshold      = int(trig.get("diff_threshold",10))
        p.occupancy_threshold = float(trig.get("occupancy_threshold",0.80))
        p.debounce_on         = int(trig.get("debounce_on",4))
        p.debounce_off        = int(trig.get("debounce_off",6))

        bg64 = data.get("background_base64_png")
        if bg64:
            arr = np.frombuffer(base64.b64decode(bg64), np.uint8)
            bg = cv2.imdecode(arr, cv2.IMREAD_GRAYSCALE)
            if bg is not None:
                pd.set_background_gray(bg)

        eng.on_frame          = self._cb_frame
        eng.on_trigger_result = self._cb_trigger
        eng.on_occupancy      = self._cb_occupancy
        eng.on_state_change   = self._cb_state

        exp = int(data.get("camera", {}).get("exposure_us", 8000))
        if not eng.start(exposure_us=exp):
            messagebox.showerror("Erro","Falha ao conectar câmera!")
            return None

        return eng

    def start_prod(self):
        if self._engine:
            return
        self._engine = self._build_engine_from_project()
        if self._engine:
            self._active = True
            self._run_id += 1
            self._cam_dot.config(fg=GREEN)
            u = (self.app.state.user or {}).get("username", "—")
            proj = (self.app.state.project_data or {}).get("project_name", "—")
            self._log.write_line(f"SESSION START | user={u} | project={proj}")

    def rearm(self):
        if self._engine:
            self._engine.rearm()

    def _cb_frame(self, frame, fps):
        eng = self._engine
        if not eng:
            return

        with self._lock:
            self._shared["frame"] = frame
            self._shared["fps"] = fps

    def _cb_trigger(self, codes, dbg_img, passed, dec_ms):
        # ---- prepara dados base ----
        decoded = [r.get("text") for r in codes if r.get("text")]
        decoded = list(dict.fromkeys(decoded))  # sem duplicados
        passed_decode = bool(passed)

        cmc = self.app.state.cmc
        needs_cmc = bool(self._active and self.cmc_enabled.get() and decoded and cmc)

        with self._lock:
            self._shared["codes"] = codes
            self._shared["debug_img"] = dbg_img
            self._shared["dec_ms"] = dec_ms

            self._shared["total"] += 1

            if needs_cmc:
                self._shared["passed"] = None
                self._shared["pending_final"] = True
            else:
                self._shared["passed"] = passed_decode
                self._shared["pending_final"] = False
                if passed_decode:
                    self._shared["ok_count"] += 1
                else:
                    self._shared["fail_count"] += 1

        # ---- status por ROI ----
        roi_stat = {}
        for r in codes:
            rid = int(r.get("roi_id", 0))
            txt = r.get("text")
            roi_stat[rid] = {
                "text": txt,
                "decode_ok": bool(txt),
                "cmc_ok": None,  # None = não aplicável ou pendente
                "cmc_reason": "",
                "cmc_detail": ""
            }

        u = (self.app.state.user or {}).get("username", "—")
        proj = (self.app.state.project_data or {}).get("project_name", "—")

        with self._lock:
            self._shared["roi_stat"] = roi_stat
            self._shared["cmc_needed"] = needs_cmc

            total = int(self._shared.get("total", 0))
            okc = int(self._shared.get("ok_count", 0))
            failc = int(self._shared.get("fail_count", 0))
            cmc_needed = bool(self._shared.get("cmc_needed", False))
            roi_stat_snap = dict(self._shared.get("roi_stat", {}) or {})

            lines = []
            lines.append(
                f"user={u} | project={proj} | trigger_total={total} | ok={okc} fail={failc} | cmc_needed={cmc_needed}")
            lines.append(f"decode_passed={bool(passed_decode)} | decoded_codes={len(decoded)}")

            # detalhe por ROI
            for rid in sorted(roi_stat_snap.keys()):
                st = roi_stat_snap[rid]
                txt = st.get("text") or "—"
                dec_ok = st.get("decode_ok")
                cmc_ok = st.get("cmc_ok")
                reason = (st.get("cmc_reason") or "")
                detail = (st.get("cmc_detail") or "")

                if not dec_ok:
                    lines.append(f"ROI {rid}: DECODE=NOK | code={txt}")
                else:
                    if not cmc_needed:
                        lines.append(f"ROI {rid}: DECODE=OK | CMC=— | code={txt}")
                    else:
                        if cmc_ok is None:
                            lines.append(f"ROI {rid}: DECODE=OK | CMC=PENDING | code={txt}")
                        elif cmc_ok:
                            lines.append(f"ROI {rid}: DECODE=OK | CMC=OK | code={txt} | reason={reason}")
                        else:
                            lines.append(
                                f"ROI {rid}: DECODE=OK | CMC=NOK | code={txt} | reason={reason} | detail={detail}")

            self._log.write_block("TRIGGER", lines)

        if not (self._active and self.cmc_enabled.get() and decoded and cmc):
            return

        run_id = self._run_id

        # só pra log/UI
        payload = list(decoded) if self.cmc_batch.get() else str(decoded[0])

        if isinstance(payload, list):
            self._hist_add("CMC", f"→ Enviando {len(payload)} seriais (1 a 1): {payload[0][:40]}...")
        else:
            self._hist_add("CMC", f"→ Enviando 1 serial: {payload}")
        self.after(0, self._hist_refresh_text)

        def _ap(payload_local):
            if (not self._active) or (self._run_id != run_id) or (self._engine is None):
                return
            try:
                cmc.ensure_login(timeout_s=15)
                if (not self._active) or (self._run_id != run_id) or (self._engine is None):
                    return

                seriais = payload_local if isinstance(payload_local, list) else [payload_local]
                all_ok = True
                for serial in seriais:
                    if (not self._active) or (self._run_id != run_id) or (self._engine is None):
                        return

                    resp = cmc.apontar(serial, timeout_s=15)

                    r = cmc.apontamento_result(resp)

                    def _upd_roi_stat(serial_local=serial, rr=r):
                        with self._lock:
                            roi_stat_local = self._shared.get("roi_stat", {})
                            for rid, st in roi_stat_local.items():
                                if st.get("text") == serial_local:
                                    st["cmc_ok"] = bool(rr.get("ok"))
                                    st["cmc_reason"] = str(rr.get("reason") or "")
                                    st["cmc_detail"] = str(rr.get("detail") or "")
                            self._shared["roi_stat"] = roi_stat_local

                    self.after(0, _upd_roi_stat)

                    if not r["ok"]:
                        all_ok = False
                    if r["ok"]:
                        self.after(0, lambda s=serial, rr=r["reason"]:
                        self._hist_add("CMC", f"✅ {rr} | serial={s}"))
                    else:
                        self.after(0, lambda s=serial, rr=r["reason"], dd=r["detail"]:
                        self._hist_add("CMC", f"❌ {rr}: {dd} | serial={s}"))

                    # opcional: pequeno delay pra não saturar (ajuste se precisar)
                    time.sleep(0.05)
                with self._lock:
                    roi_stat_final = dict(self._shared.get("roi_stat", {}) or {})

                final_passed = bool(passed_decode and all_ok)

                lines = [f"user={u} | project={proj} | all_ok={all_ok} | final_passed={final_passed}"]
                for rid in sorted(roi_stat_final.keys()):
                    st = roi_stat_final[rid]
                    code = st.get("text") or "—"
                    dec_ok = bool(st.get("decode_ok"))
                    cmc_ok = st.get("cmc_ok", None)
                    reason = st.get("cmc_reason") or ""
                    detail = st.get("cmc_detail") or ""

                    if not dec_ok:
                        lines.append(f"ROI {rid}: DECODE=NOK | code={code}")
                    else:
                        if cmc_ok is None:
                            lines.append(f"ROI {rid}: DECODE=OK | CMC=? | code={code}")
                        elif cmc_ok:
                            lines.append(f"ROI {rid}: DECODE=OK | CMC=OK | code={code} | reason={reason}")
                        else:
                            lines.append(
                                f"ROI {rid}: DECODE=OK | CMC=NOK | code={code} | reason={reason} | detail={detail}")

                self._log.write_block("CMC_FINAL", lines)

                def _set_final():
                    with self._lock:
                        self._shared["passed"] = final_passed
                        self._shared["cmc_all_ok"] = all_ok

                        if self._shared.get("pending_final", False):
                            if final_passed:
                                self._shared["ok_count"] += 1
                            else:
                                self._shared["fail_count"] += 1
                            self._shared["pending_final"] = False

                    self._hist_refresh_text()

                self.after(0, _set_final)

            except Exception as e:
                msg = str(e)[:180]

                def _fail_final():
                    with self._lock:
                        self._shared["passed"] = False

                        if self._shared.get("pending_final", False):
                            self._shared["fail_count"] += 1
                            self._shared["pending_final"] = False

                    self._hist_add("CMC", f"❌ Exceção: {msg}")
                    self._hist_refresh_text()

                self.after(0, _fail_final)
            finally:
                self.after(0, self._hist_refresh_text)

        threading.Thread(target=_ap, args=(payload,), daemon=True).start()

    def _cb_occupancy(self, occ, has_bg, present):
        with self._lock:
            self._shared["occ"]     = occ
            self._shared["has_bg"]  = has_bg
            self._shared["present"] = present

    def _cb_state(self, state):
        with self._lock:
            self._shared["state"] = state

    def _schedule_ui(self):
        self._update_ui()
        self._ui_job = self.after(40, self._schedule_ui)

    def _update_ui(self):
        with self._lock:
            frame    = self._shared.get("frame")
            fps      = float(self._shared.get("fps", 0))
            dec_ms   = float(self._shared.get("dec_ms", 0))
            occ      = float(self._shared.get("occ", 0))
            has_bg   = bool(self._shared.get("has_bg", False))
            present  = bool(self._shared.get("present", False))
            codes    = list(self._shared.get("codes", []))
            # dbg_img  = self._shared.get("debug_img")
            passed   = self._shared.get("passed")
            state    = self._shared.get("state", "WAIT_PRESENT")
            total    = self._shared.get("total", 0)
            ok_c     = self._shared.get("ok_count", 0)
            fail_c   = self._shared.get("fail_count", 0)

            frame = self._shared.get("frame")
            state = self._shared.get("state", "WAIT_PRESENT")

        if frame is None and state == "STOPPED":
            _canvas_stop_overlay(self.canvas_live, "STOPPED", "Clique em Iniciar para voltar")
            # opcional: limpa tabela para não confundir
            for i in self.tree.get_children():
                self.tree.delete(i)
            return

        self.lbl_fps.config(text=f"{fps:.0f} FPS")
        self.lbl_dec.config(text=f"Decode: {dec_ms:.0f} ms")
        self.lbl_state.config(text=f"State: {state}")
        self.lbl_occ.config(
            text=f"Occ: {occ*100:.0f}%  BG: {'✓' if has_bg else '✗'}  "
                 f"{'PRESENTE' if present else 'vazio'}")

        self._cnt_widgets["total"].config(text=str(total))
        self._cnt_widgets["ok_count"].config(text=str(ok_c))
        self._cnt_widgets["fail_count"].config(text=str(fail_c))

        if passed is None:
            self.lbl_result.config(text="APONTANDO", fg=MUTED)
            self._status_bar.config(bg=MUTED)
        elif passed:
            self.lbl_result.config(text="PASSED", fg=GREEN)
            self._status_bar.config(bg=GREEN)
        else:
            self.lbl_result.config(text="FAILED", fg=RED)
            self._status_bar.config(bg=RED)

        for i in self.tree.get_children():
            self.tree.delete(i)
        roi_stat = {}
        cmc_needed = False
        with self._lock:
            roi_stat = dict(self._shared.get("roi_stat", {}) or {})
            cmc_needed = bool(self._shared.get("cmc_needed", False))

        for r in codes:
            rid = int(r.get("roi_id", 0))
            st = roi_stat.get(rid, {})
            txt = st.get("text") or "—"

            dec_ok = bool(st.get("decode_ok"))
            dec_str = "OK" if dec_ok else "NOK"

            # apontamento
            if not cmc_needed:
                cmc_str = "—"
                motivo = ""
                row_ok = dec_ok
            else:
                cmc_ok = st.get("cmc_ok", None)
                if cmc_ok is None:
                    cmc_str = "..."
                    motivo = "Aguardando CMControl"
                    row_ok = False  # ainda não é OK final
                else:
                    cmc_str = "OK" if cmc_ok else "NOK"
                    motivo = (st.get("cmc_reason") or "")
                    det = (st.get("cmc_detail") or "")
                    if det and not cmc_ok:
                        motivo = f"{motivo}: {det}" if motivo else det
                    row_ok = bool(dec_ok and cmc_ok)

            self.tree.insert(
                "", "end",
                values=(f"R{rid}", txt, dec_str, cmc_str, motivo[:120], f"{r.get('ms', 0):.0f}"),
                tags=("ok" if row_ok else "fail",)
            )

        if frame is not None:
            orig = cv2.cvtColor(frame, cv2.COLOR_GRAY2BGR) \
                if frame.ndim == 2 else frame.copy()
            roi_stat = {}
            cmc_needed = False
            present_now = bool(present)

            with self._lock:
                roi_stat = dict(self._shared.get("roi_stat", {}) or {})
                cmc_needed = bool(self._shared.get("cmc_needed", False))

            for roi in (self.app.state.rois or []):
                # padrão
                col = (0, 255, 255)  # ciano

                if present_now:
                    st = roi_stat.get(int(roi.id), {})
                    dec_ok = bool(st.get("decode_ok"))

                    if not dec_ok:
                        col = (0, 0, 255)  # vermelho
                    else:
                        if not cmc_needed:
                            col = (0, 255, 0)  # verde
                        else:
                            cmc_ok = st.get("cmc_ok", None)
                            if cmc_ok is None:
                                col = (0, 255, 255)  # amarelo (BGR: (0,255,255))
                            else:
                                col = (0, 255, 0) if cmc_ok else (0, 0, 255)

                cv2.polylines(orig, [roi.get_rect_points()], True, col, 6)
                cv2.putText(orig, f"R{roi.id}",
                            (int(roi.cx) + 4, int(roi.cy) - 4),
                            cv2.FONT_HERSHEY_SIMPLEX, 0.85, col, 2)
                # cv2.putText(orig, f"R{roi.id}",
                #             (int(roi.cx)+4, int(roi.cy)-4),
                #             cv2.FONT_HERSHEY_SIMPLEX, 0.8, (0,255,255), 2)
            self._last_bgr = orig
            self._draw_canvas(self.canvas_live, orig, "live")

        # if dbg_img is not None:
        #     self._last_dbg = dbg_img
        #     self._draw_canvas(self.canvas_debug, dbg_img, "dbg")

    def _draw_canvas(self, canvas, bgr, which):
        cw = canvas.winfo_width(); ch = canvas.winfo_height()
        if cw < 2 or ch < 2:
            return
        scale = min(cw/max(1,bgr.shape[1]), ch/max(1,bgr.shape[0]))
        nw = int(bgr.shape[1]*scale); nh = int(bgr.shape[0]*scale)
        resized = cv2.resize(bgr, (nw, nh), interpolation=cv2.INTER_LINEAR)
        rgb = cv2.cvtColor(resized, cv2.COLOR_BGR2RGB)
        imgtk = ImageTk.PhotoImage(Image.fromarray(rgb))
        canvas.delete("all")
        x0 = (cw-nw)//2; y0 = (ch-nh)//2
        canvas.create_image(x0, y0, anchor="nw", image=imgtk)
        if which == "live":
            self._img_tk  = imgtk
        else:
            self._img_dbg = imgtk


# ══════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    App().mainloop()