"""
Módulo de controle da câmera Basler
Gerencia conexão, configuração e captura de imagens
"""

import pypylon.pylon as pylon
import numpy as np
from typing import Optional, Dict, Any
import time
import traceback

class BaslerCameraController:
    """Controlador para câmera Basler usando PyPylon"""

    def __init__(self):
        self.camera: Optional[pylon.InstantCamera] = None
        self.converter = pylon.ImageFormatConverter()
        self.converter.OutputPixelFormat = pylon.PixelType_Mono8
        self.converter.OutputBitAlignment = pylon.OutputBitAlignment_MsbAligned
        self.is_connected = False
        self.is_grabbing = False

        # Parâmetros padrão
        self.default_config = {
            'exposure_us': 20000,
            'gain': 0.0,
            'pixel_format': 'Mono12',
            'trigger_mode': False
        }

    def connect(self, max_retries: int = 3) -> bool:
        """
        Conecta à primeira câmera Basler disponível

        Returns:
            bool: True se conectado com sucesso
        """
        try:


            tl_factory = pylon.TlFactory.GetInstance()
            devices = tl_factory.EnumerateDevices()

            if not devices:
                print("❌ Nenhuma câmera Basler encontrada")
                return False

            self.camera = pylon.InstantCamera(tl_factory.CreateFirstDevice())
            self.camera.Open()

            # Configuração inicial
            self._apply_default_config()

            model = self.camera.GetDeviceInfo().GetModelName()
            print(f"✅ Câmera conectada: {model}")
            self.is_connected = True
            return True

        except Exception as e:

            print(f"❌ Erro ao conectar câmera: {e}")
            return False

    def _apply_default_config(self):
        """Aplica configurações padrão à câmera"""
        try:
            # Formato de pixel
            try:
                self.camera.PixelFormat.SetValue(self.default_config['pixel_format'])
            except:
                print("  Mono12 não disponível, usando formato padrão")

            # Desabilita auto-exposure e auto-gain
            self.camera.ExposureAuto.SetValue("Off")
            self.camera.GainAuto.SetValue("Off")

            # Define valores
            self.set_exposure(self.default_config['exposure_us'])
            self.set_gain(self.default_config['gain'])

            # Modo de aquisição
            self.camera.AcquisitionMode.SetValue("Continuous")

        except Exception as e:
            print(f"  Erro ao aplicar config padrão: {e}")

    def start_grabbing(self):
        """Inicia captura contínua de imagens"""
        if self.camera and not self.camera.IsGrabbing():
            self.camera.StartGrabbing(pylon.GrabStrategy_LatestImageOnly)
            self.is_grabbing = True

    def stop_grabbing(self):
        """Para captura de imagens"""
        if self.camera and self.camera.IsGrabbing():
            self.camera.StopGrabbing()
            self.is_grabbing = False

    def get_frame(self, timeout_ms: int = 50) -> Optional[np.ndarray]:
        """
        Captura um frame da câmera

        Args:
            timeout_ms: Timeout em milissegundos

        Returns:
            numpy array com a imagem ou None se falhar
        """
        if not self.camera or not self.camera.IsGrabbing():
            return None

        try:
            # grab = self.camera.RetrieveResult(timeout_ms, pylon.TimeoutHandling_Return)
            #
            # if grab.GrabSucceeded():
            #     image = self.converter.Convert(grab)
            #     img_array = image.GetArray()
            #     grab.Release()
            #     return np.asarray(img_array, dtype=np.uint8)
            # else:
            #     grab.Release()
            #     return None

            grab = self.camera.RetrieveResult(timeout_ms, pylon.TimeoutHandling_Return)

            if not grab or not grab.IsValid():
                return None

            if not grab.GrabSucceeded():
                grab.Release()
                return None

            image = self.converter.Convert(grab)
            img_array = image.GetArray()
            grab.Release()
            return img_array

        except Exception as e:
            print(f"  Erro ao capturar frame: {e}")
            return None

    def capture_single_frame(self, timeout_ms: int = 5000) -> Optional[np.ndarray]:
        """
        Captura um único frame (usado para produção)

        Args:
            timeout_ms: Timeout em milissegundos

        Returns:
            numpy array com a imagem ou None se falhar
        """
        if not self.camera:
            return None

        try:
            was_grabbing = self.camera.IsGrabbing()

            if not was_grabbing:
                self.camera.StartGrabbing(1)

            grab = self.camera.RetrieveResult(timeout_ms, pylon.TimeoutHandling_ThrowException)

            if grab.GrabSucceeded():
                image = self.converter.Convert(grab)
                img_array = image.GetArray()
                grab.Release()
                return np.asarray(img_array, dtype=np.uint8)
            else:
                grab.Release()
                return None

        except Exception as e:
            print(f"❌ Erro ao capturar frame único: {e}")
            return None

    def set_exposure(self, value_us: float) -> bool:
        """
        Define tempo de exposição

        Args:
            value_us: Exposição em microssegundos

        Returns:
            bool: True se aplicado com sucesso
        """
        if not self.camera or not self.camera.IsOpen():
            return False

        try:
            min_exp = self.camera.ExposureTime.GetMin()
            max_exp = self.camera.ExposureTime.GetMax()
            val = max(min_exp, min(float(value_us), max_exp))
            self.camera.ExposureTime.SetValue(val)
            return True
        except Exception as e:
            print(f" Erro ao definir exposure: {e}")
            return False

    def set_gain(self, value: float) -> bool:
        """
        Define ganho da câmera

        Args:
            value: Ganho em dB

        Returns:
            bool: True se aplicado com sucesso
        """
        if not self.camera or not self.camera.IsOpen():
            return False

        try:
            min_gain = self.camera.Gain.GetMin()
            max_gain = self.camera.Gain.GetMax()
            val = max(min_gain, min(float(value), max_gain))
            self.camera.Gain.SetValue(val)
            return True
        except Exception as e:
            print(f"  Erro ao definir gain: {e}")
            return False

    def set_trigger_mode(self, enabled: bool):
        """
        Configura modo de trigger

        Args:
            enabled: True para software trigger, False para free run
        """
        if not self.camera or not self.camera.IsOpen():
            return

        was_grabbing = self.camera.IsGrabbing()
        if was_grabbing:
            self.camera.StopGrabbing()

        if enabled:
            self.camera.TriggerMode.SetValue("On")
            self.camera.TriggerSource.SetValue("Software")
        else:
            self.camera.TriggerMode.SetValue("Off")

        if was_grabbing:
            self.camera.StartGrabbing(pylon.GrabStrategy_LatestImageOnly)

    def execute_software_trigger(self):
        """Executa trigger via software"""
        if self.camera and self.camera.IsOpen():
            try:
                if self.camera.TriggerMode.GetValue() == "On":
                    self.camera.TriggerSoftware.Execute()
            except Exception as e:
                print(f"  Erro ao executar trigger: {e}")

    def get_camera_info(self) -> Dict[str, Any]:
        """
        Retorna informações da câmera

        Returns:
            Dicionário com informações
        """
        if not self.camera or not self.camera.IsOpen():
            return {}

        try:
            return {
                'model': self.camera.GetDeviceInfo().GetModelName(),
                'serial': self.camera.GetDeviceInfo().GetSerialNumber(),
                'exposure': self.camera.ExposureTime.GetValue(),
                'gain': self.camera.Gain.GetValue(),
                'pixel_format': self.camera.PixelFormat.GetValue(),
                'trigger_mode': self.camera.TriggerMode.GetValue()
            }
        except:
            return {}

    def close(self):
        """Fecha conexão com a câmera"""
        if self.camera:
            if self.camera.IsGrabbing():
                self.camera.StopGrabbing()
            self.camera.Close()
            self.is_connected = False
            print(" Câmera desconectada")