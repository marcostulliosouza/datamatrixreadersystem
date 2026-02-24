import json
import time
import base64
import threading
from dataclasses import dataclass
from datetime import datetime
from typing import Union, List, Optional, Dict, Any, Callable

import paho.mqtt.client as mqtt
from dotenv import load_dotenv
from pathlib import Path
import os
import uuid

BASE_DIR = Path(__file__).resolve().parent
ENV_PATH = BASE_DIR / ".env"

# ============================================================
# CONFIG / ENV
# ============================================================

SerialInput = Union[str, List[str]]

def now_ts() -> int:
    return int(time.time())


def b64(text: str) -> str:
    return base64.b64encode(text.encode()).decode()


def env_int(name: str, default: int) -> int:
    v = os.getenv(name)
    if v is None or v.strip() == "":
        return default
    return int(v)

def env_str(name: str, default: str = "") -> str:
    v = os.getenv(name)
    if v is None:
        return default
    return v.strip()


def require_env(name: str) -> str:
    v = os.getenv(name, "").strip()
    if not v:
        raise ValueError(f"Variável de ambiente obrigatória ausente: {name}")
    return v


@dataclass(frozen=True)
class CmControlConfig:
    # Dispositivo / MQTT
    device_addr: str
    broker_host: str
    broker_port: int
    mqtt_user: str
    mqtt_pass: str

    # API (basic auth para oauth2/login)
    api_user: str = ""
    api_pass: str = ""

    # Ajustes
    token_renew_margin_s: int = 600  # renova 10 min antes
    connect_timeout_s: int = 10


def load_config_from_env() -> CmControlConfig:
    load_dotenv(ENV_PATH)

    return CmControlConfig(
        device_addr=require_env("CMC_DEVICE_ADDR"),
        broker_host=require_env("CMC_BROKER_HOST"),
        broker_port=env_int("CMC_BROKER_PORT", 1883),
        mqtt_user=require_env("CMC_MQTT_USER"),
        mqtt_pass=require_env("CMC_MQTT_PASS"),
        api_user=env_str("CMC_API_USER", ""),
        api_pass=env_str("CMC_API_PASS", ""),
        token_renew_margin_s=env_int("CMC_TOKEN_RENEW_MARGIN_S", 600),
        connect_timeout_s=env_int("CMC_CONNECT_TIMEOUT_S", 10),
    )


# ============================================================
# CLIENTE REUTILIZÁVEL
# ============================================================

class CmControlMqttClient:
    """
    Cliente MQTT CmControl com login OAuth2 via MQTT+REST.
    - Conecta no broker, publica state online, responde ping/state.
    - Faz login e mantém token (renova quando necessário).
    - Expõe métodos para validar rota e apontar serial (com evidência base64 opcional).
    - Faz logout e state offline no shutdown.
    """

    def __init__(self, cfg: CmControlConfig):
        self.cfg = cfg

        # ACK de apontamento (para conseguir "esperar" a resposta)
        self._ap_event = threading.Event()
        self._last_apontamento_payload: Optional[Dict[str, Any]] = None

        # Callback mais informativo (opcional)
        self.on_apontamento_response: Optional[Callable[[Dict[str, Any]], None]] = None

        self._client: Optional[mqtt.Client] = None
        self._lock = threading.Lock()

        self._access_token: Optional[str] = None
        self._token_expiration_ts: Optional[int] = None

        self._last_apontamento_error: Optional[str] = None
        self._last_login_error: Optional[str] = None

        self._connected_event = threading.Event()
        self._login_event = threading.Event()

        # Callbacks externos (opcionais)
        self.on_login_ok: Optional[Callable[[], None]] = None
        self.on_login_error: Optional[Callable[[str], None]] = None
        self.on_apontamento_ok: Optional[Callable[[], None]] = None
        self.on_apontamento_error: Optional[Callable[[str], None]] = None

    # -------------------------
    # Helpers
    # -------------------------

    def topic(self, path: str) -> str:
        return f"br/com/cmcontrol/dispositivo/{self.cfg.device_addr}/{path}"

    def _publish(self, path: str, payload: Dict[str, Any]) -> None:
        if not self._client:
            raise RuntimeError("MQTT client não inicializado. Chame connect().")
        self._client.publish(self.topic(path), json.dumps(payload))

    def _api_basic_auth(self) -> str:
        if not self.cfg.api_user or not self.cfg.api_pass:
            raise RuntimeError("CMC api_user/api_pass não definidos (login da UI não foi aplicado).")
        return b64(f"{self.cfg.api_user}:{self.cfg.api_pass}")

    def is_token_valid(self) -> bool:
        with self._lock:
            if not self._access_token or not self._token_expiration_ts:
                return False
            return now_ts() < (self._token_expiration_ts - self.cfg.token_renew_margin_s)

    def get_token(self) -> Optional[str]:
        with self._lock:
            return self._access_token

    @staticmethod
    def _normalize_seriais(seriais: SerialInput) -> List[str]:
        if isinstance(seriais, str):
            s = seriais.strip()
            return [s] if s else []
        # lista/iterável
        out = []
        for x in seriais:
            if x is None:
                continue
            sx = str(x).strip()
            if sx:
                out.append(sx)
        return out
    # -------------------------
    # Payloads
    # -------------------------

    def payload_login(self, bearer: bool = False) -> Dict[str, Any]:
        # Primeiro login usa Basic; renovação pode usar Bearer (se o backend suportar)
        auth = f"Bearer {self._access_token}" if (bearer and self._access_token) else f"Basic {self._api_basic_auth()}"
        return {"request": {"headers": {"Authorization": auth}, "type": "GET"}}

    def payload_logout(self) -> Dict[str, Any]:
        token = self.get_token()
        return {"request": {"headers": {"Authorization": f"Bearer {token}"}, "type": "GET"}}

    def payload_validar_rota(self, serial: str) -> Dict[str, Any]:
        token = self.get_token()
        return {
            "request": {"headers": {"Authorization": f"Bearer {token}"}, "type": "POST"},
            "data": {
                "enderecoDispositivo": self.cfg.device_addr,
                "ciclo": "VALIDAR_ROTA",
                "apontamentos": [{"ok": True, "seriais": [{"codigo": serial}]}],
            },
        }

    def payload_apontamento_real(self, serial: str, evidencias: Optional[list] = None) -> Dict[str, Any]:
        token = self.get_token()
        apont = {"ok": True, "seriais": [{"codigo": serial}]}
        if evidencias:
            apont["evidencias"] = evidencias

        return {
            "request": {"headers": {"Authorization": f"Bearer {token}"}, "type": "POST"},
            "data": {
                "enderecoDispositivo": self.cfg.device_addr,
                "apontamentos": [apont],
            },
        }

    def payload_apontamento(self, seriais: SerialInput, evidencias: Optional[list] = None) -> Dict[str, Any]:
        """
        Monta payload igual ao exemplo:
        {
          "enderecoDispositivo": "...",
          "apontamentos": [{
             "ok": true,
             "seriais": [{"codigo": "..."} ...]
          }]
        }
        """
        token = self.get_token()
        codigos = self._normalize_seriais(seriais)
        if not codigos:
            raise ValueError("Lista de seriais vazia.")

        seriais_obj = [{"codigo": c} for c in codigos]

        apont = {"ok": True, "seriais": seriais_obj}
        if evidencias:
            apont["evidencias"] = evidencias

        return {
            "request": {"headers": {"Authorization": f"Bearer {token}"}, "type": "POST"},
            "data": {
                "enderecoDispositivo": self.cfg.device_addr,
                "apontamentos": [apont],
            },
        }

    # -------------------------
    # MQTT callbacks
    # -------------------------
    def _on_disconnect(self, client, userdata, rc):
        if rc == 0:
            print("ℹ️ MQTT desconectou (normal) rc=0")
        else:
            print(f"❌ MQTT desconectou rc={rc}")

    def _on_connect(self, client, userdata, flags, rc):
        self._connected_event.set()

        subs = [
            "get/ping",
            "get/state",
            "get/rest/oauth2/login",
            "get/rest/oauth2/logout",
            "get/rest/api/v1/setup.apontamento",
        ]
        for s in subs:
            client.subscribe(self.topic(s))

        # online
        self._publish("set/state", {"state": "1"})

    def _on_message(self, client, userdata, msg):
        t = msg.topic
        try:
            payload = json.loads(msg.payload.decode())
        except Exception:
            return

        # ping
        if t.endswith("/get/ping"):
            self._publish("set/pong", {"timestamp": now_ts()})
            return

        # state
        if t.endswith("/get/state"):
            self._publish("set/state", {"state": "1"})
            return

        # login response
        if t.endswith("/get/rest/oauth2/login"):
            # alguns servidores mandam status como "200"
            status = payload.get("status")
            try:
                status_i = int(status)
            except Exception:
                status_i = None

            if status_i == 200:
                # pode vir access_token no root ou dentro de response/data dependendo do backend
                token = payload.get("access_token")
                expires_in_min = payload.get("expires_in")

                if token is None:
                    token = (payload.get("response") or {}).get("access_token") or (payload.get("data") or {}).get(
                        "access_token")
                if expires_in_min is None:
                    expires_in_min = (payload.get("response") or {}).get("expires_in") or (
                                payload.get("data") or {}).get("expires_in")

                if not token:
                    self._last_login_error = "Login retornou 200 mas access_token não veio no payload."
                    self._login_event.set()
                    if self.on_login_error:
                        self.on_login_error(self._last_login_error)
                    return

                with self._lock:
                    self._access_token = token
                    self._token_expiration_ts = now_ts() + int(expires_in_min or 60) * 60

                self._last_login_error = None
                self._login_event.set()
                if self.on_login_ok:
                    self.on_login_ok()
            else:
                err = payload.get("log") or payload.get("message") or f"Login falhou. status={status}"
                self._last_login_error = err
                self._login_event.set()
                if self.on_login_error:
                    self.on_login_error(err)
            return

        # apontamento response
        if t.endswith("/get/rest/api/v1/setup.apontamento"):
            self._last_apontamento_payload = payload
            self._ap_event.set()

            # callback "raw" (se quiser ver o payload completo no GUI)
            if self.on_apontamento_response:
                try:
                    self.on_apontamento_response(payload)
                except Exception:
                    pass

            status = payload.get("status")
            ok = (status == 200) or (status == "200")

            if not ok:
                err = payload.get("log", "Erro desconhecido no apontamento")
                self._last_apontamento_error = err
                if self.on_apontamento_error:
                    self.on_apontamento_error(err)
            else:
                self._last_apontamento_error = None
                if self.on_apontamento_ok:
                    self.on_apontamento_ok()
            return

        # logout response
        if t.endswith("/get/rest/oauth2/logout"):
            # opcional: logar payload
            return
    def _publish_and_wait_apontamento(self, payload: Dict[str, Any], timeout_s: int) -> Dict[str, Any]:
        self._ap_event.clear()
        self._last_apontamento_payload = None
        self._publish("set/rest/api/v1/setup.apontamento", payload)

        if not self._ap_event.wait(timeout=timeout_s):
            raise TimeoutError("Timeout esperando resposta do apontamento (setup.apontamento).")

        return self._last_apontamento_payload or {}

    # -------------------------
    # Lifecycle
    # -------------------------

    def connect(self) -> None:
        # limpa antes de tudo (reconexões)
        self._connected_event.clear()
        self._login_event.clear()
        client_id = f"{self.cfg.device_addr}-{uuid.uuid4().hex[:8]}"
        self._client = mqtt.Client(client_id=client_id)
        self._client.username_pw_set(self.cfg.mqtt_user, self.cfg.mqtt_pass)

        self._client.on_connect = self._on_connect
        self._client.on_message = self._on_message
        self._client.on_disconnect = self._on_disconnect

        self._client.connect(self.cfg.broker_host, self.cfg.broker_port)
        self._client.loop_start()

        if not self._connected_event.wait(timeout=self.cfg.connect_timeout_s):
            raise TimeoutError("Timeout conectando no broker MQTT.")

    def ensure_login(self, timeout_s: int = 10) -> None:
        if self.is_token_valid():
            return

        bearer = self.get_token() is not None
        self._last_login_error = None
        self._login_event.clear()

        # print("Auth mode:", "Bearer" if bearer else "Basic")

        self._publish("set/rest/oauth2/login", self.payload_login(bearer=bearer))
        if not self._login_event.wait(timeout=timeout_s):
            raise TimeoutError("Timeout esperando resposta do login OAuth2 via MQTT.")

        if self._last_login_error:
            raise RuntimeError(f"Login inválido: {self._last_login_error}")

        if not self.is_token_valid():
            raise RuntimeError("Login retornou, mas token não ficou válido.")

    def disconnect(self) -> None:
        if not self._client:
            return

        # logout se tiver token
        if self.get_token():
            try:
                self._publish("set/rest/oauth2/logout", self.payload_logout())
                time.sleep(1)
            except Exception:
                pass

        # offline
        try:
            self._publish("set/state", {"state": "0"})
            time.sleep(0.5)
        except Exception:
            pass

        self._client.loop_stop()
        self._client.disconnect()
        self._client = None

    def __enter__(self):
        self.connect()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.disconnect()

    # -------------------------
    # Operações (reutilizáveis)
    # -------------------------

    def validar_rota(self, serial: str, timeout_s: int = 10) -> Dict[str, Any]:
        self.ensure_login(timeout_s=timeout_s)
        self._last_apontamento_error = None
        return self._publish_and_wait_apontamento(self.payload_validar_rota(serial), timeout_s=timeout_s)

    def apontar(self, seriais: SerialInput, evidencias: Optional[list] = None, timeout_s: int = 10) -> Dict[str, Any]:
        self.ensure_login(timeout_s=timeout_s)
        self._last_apontamento_error = None
        return self._publish_and_wait_apontamento(self.payload_apontamento(seriais, evidencias=evidencias),
                                                  timeout_s=timeout_s)
    def apontar_um_a_um(self, seriais: List[str], evidencias: Optional[list] = None, timeout_s: int = 10,
                        delay_s: float = 0.3) -> None:
        """
        Faz N requests, um serial por vez (para teste).
        """
        codigos = self._normalize_seriais(seriais)
        for c in codigos:
            self.apontar(c, evidencias=evidencias, timeout_s=timeout_s)
            time.sleep(max(0.0, float(delay_s)))

    def get_last_apontamento_error(self) -> Optional[str]:
        return self._last_apontamento_error
