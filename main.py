import tkinter as tk
from tkinter import ttk
import subprocess
import json
import traceback
import tkinter.messagebox as msgbox
import os
from PIL import Image, ImageTk, ImageSequence
import threading
import logging
import sys
import shutil

IMAGEIO_AVAILABLE = False
try:
    import imageio
    IMAGEIO_AVAILABLE = True
except ImportError:
    print("警告：未找到 imageio 庫。GIF 動畫的持續時間可能不準確，或無法播放。")
    print("請嘗試安裝： pip install imageio")

# --- 全局路徑設定 (基於 main.py 的位置) ---
MAIN_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
GIF_DIR = os.path.join(MAIN_SCRIPT_DIR, "gif")

# --- .minecraft 相關路徑 ---
MINECRAFT_CORE_DIR = os.path.join(MAIN_SCRIPT_DIR, ".minecraft")
PLAYER_DATA_DIR = os.path.join(MINECRAFT_CORE_DIR, "playerdata")
PLAYER_JSON_PATH = os.path.join(PLAYER_DATA_DIR, "player.json")
GAME_PY_PATH = os.path.join(MINECRAFT_CORE_DIR, "game.py")

# --- 確保相關資料夾存在 ---
os.makedirs(MINECRAFT_CORE_DIR, exist_ok=True)
os.makedirs(PLAYER_DATA_DIR, exist_ok=True)
os.makedirs(GIF_DIR, exist_ok=True)
LAUNCHER_LOG_DIR = os.path.join(MAIN_SCRIPT_DIR, "log")
os.makedirs(LAUNCHER_LOG_DIR, exist_ok=True)

# --- 主啟動器日誌設定 ---
launcher_log_file = os.path.join(LAUNCHER_LOG_DIR, "main_launcher.log")
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(module)s.%(funcName)s:%(lineno)d - %(message)s',
    handlers=[
        logging.FileHandler(launcher_log_file, mode='w', encoding='utf-8'),
        logging.StreamHandler()
    ]
)

class AnimatedGIF:
    def __init__(self, master, path, position=(0, 0), size=None,
                 speed_multiplier=1.0, default_bg_color="white",
                 loop=True, on_animation_loop_complete=None, force_smooth_delay_ms=None):
        self.master = master
        self.path = path
        self.position = position
        self.size = size
        self.speed_multiplier = float(speed_multiplier) if speed_multiplier > 0 else 1.0
        self.default_bg_color = default_bg_color
        self.loop = loop
        self.on_animation_loop_complete = on_animation_loop_complete
        self.force_smooth_delay_ms = force_smooth_delay_ms

        self.canvas = None
        self.canvas_width = 0
        self.canvas_height = 0

        self.tk_frames = []
        self.delay = []
        self.adjusted_delay = []
        self.idx = 0
        self.image_id = None
        self.cancel_id = None
        self.total_duration_ms = 0
        self.is_playing = False

        self._load_gif()

    def _load_gif(self):
        if not os.path.exists(self.path):
            logging.error(f"AnimatedGIF({self.path}): GIF 檔案未找到。")
            self.tk_frames = []
            return

        self.tk_frames = []
        self.delay = []
        self.adjusted_delay = []
        self.total_duration_ms = 0

        try:
            resample_filter = Image.LANCZOS
            if hasattr(Image, 'Resampling'):
                resample_filter = Image.Resampling.LANCZOS

            logging.debug(f"AnimatedGIF({self.path}): Attempting to load frames. Forced delay: {self.force_smooth_delay_ms}ms")

            min_frame_delay = 20

            if IMAGEIO_AVAILABLE:
                logging.debug(f"AnimatedGIF({self.path}): Loading with imageio.")
                gif_reader = imageio.get_reader(self.path)
                for i, frame_data in enumerate(gif_reader):
                    pil_image = Image.fromarray(frame_data).convert("RGBA")
                    if self.size: pil_image = pil_image.resize(self.size, resample_filter)

                    photo_image = ImageTk.PhotoImage(pil_image)
                    self.tk_frames.append(photo_image)

                    try:
                        original_frame_delay_ms = 0
                        if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0:
                            original_frame_delay_ms = self.force_smooth_delay_ms
                        else:
                            raw_duration_val = gif_reader.get_meta_data(i)['duration']
                            logging.debug(f"AnimatedGIF({self.path}): imageio raw_duration_val for frame {i}: {raw_duration_val}")
                            original_frame_delay_ms = int(raw_duration_val * 10)

                        if original_frame_delay_ms <= 0: original_frame_delay_ms = 100

                        self.delay.append(original_frame_delay_ms)
                        current_adjusted_delay = int(original_frame_delay_ms / self.speed_multiplier)
                        if current_adjusted_delay < min_frame_delay:
                            current_adjusted_delay = min_frame_delay

                        self.adjusted_delay.append(current_adjusted_delay)
                        self.total_duration_ms += original_frame_delay_ms

                    except (KeyError, IndexError, TypeError, ValueError) as e_dur:
                        logging.warning(f"AnimatedGIF({self.path}): Error getting duration from imageio for frame {i}: {e_dur}. Using default.")
                        fallback_delay = self.force_smooth_delay_ms if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 else 100
                        self.delay.append(fallback_delay)
                        self.adjusted_delay.append(max(min_frame_delay, int(fallback_delay / self.speed_multiplier)))
                        self.total_duration_ms += fallback_delay
                if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 and self.tk_frames:
                     logging.info(f"AnimatedGIF({self.path}): All frames used forced delay of {self.force_smooth_delay_ms}ms.")
                gif_reader.close()
            else: # Using PIL
                logging.debug(f"AnimatedGIF({self.path}): Loading with PIL/Pillow.")
                with Image.open(self.path) as img:
                    for frame_idx, frame_pil in enumerate(ImageSequence.Iterator(img)):
                        pil_frame_rgba = frame_pil.copy().convert("RGBA")
                        if self.size:
                            pil_frame_rgba = pil_frame_rgba.resize(self.size, resample_filter)

                        photo_image = ImageTk.PhotoImage(pil_frame_rgba)
                        self.tk_frames.append(photo_image)

                        try:
                            original_frame_delay_ms = 0
                            if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0:
                                original_frame_delay_ms = self.force_smooth_delay_ms
                            else:
                                original_frame_delay_ms = frame_pil.info.get('duration', 100)

                            if original_frame_delay_ms <= 0: original_frame_delay_ms = 100
                            self.delay.append(original_frame_delay_ms)

                            current_adjusted_delay = int(original_frame_delay_ms / self.speed_multiplier)
                            if current_adjusted_delay < min_frame_delay:
                                current_adjusted_delay = min_frame_delay

                            self.adjusted_delay.append(current_adjusted_delay)
                            self.total_duration_ms += original_frame_delay_ms
                        except Exception as e_pil_dur:
                            logging.warning(f"AnimatedGIF({self.path}): Error getting duration from PIL for frame {frame_idx}: {e_pil_dur}. Using default.")
                            fallback_delay = self.force_smooth_delay_ms if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 else 100
                            self.delay.append(fallback_delay)
                            self.adjusted_delay.append(max(min_frame_delay, int(fallback_delay / self.speed_multiplier)))
                            self.total_duration_ms += fallback_delay
                    if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 and self.tk_frames:
                        logging.info(f"AnimatedGIF({self.path}): All frames used forced delay of {self.force_smooth_delay_ms}ms.")

            if not self.tk_frames:
                 logging.error(f"AnimatedGIF({self.path}): No frames loaded, tk_frames is empty.")
            else:
                delay_source_info = "forced" if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 else "original"
                logging.info(f"AnimatedGIF({self.path}): Loaded {len(self.tk_frames)} frames. "
                             f"Delays used ({delay_source_info}, first 5): {self.delay[:5]}. "
                             f"Adjusted Delays (first 5): {self.adjusted_delay[:5]}. "
                             f"Total duration (based on delays list): {sum(self.delay)}ms. "
                             f"Total duration for anim (adj): {sum(self.adjusted_delay)}ms.")
                if len(self.tk_frames) != len(self.delay) or len(self.tk_frames) != len(self.adjusted_delay):
                    logging.critical(f"AnimatedGIF({self.path}): Mismatch in frame/delay list lengths! This is a bug.")
                    list_len = len(self.tk_frames)
                    default_delay_val = self.force_smooth_delay_ms if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 else 100
                    default_adjusted = max(min_frame_delay, int(default_delay_val / self.speed_multiplier))
                    self.delay = (self.delay + [default_delay_val] * list_len)[:list_len]
                    self.adjusted_delay = (self.adjusted_delay + [default_adjusted] * list_len)[:list_len]


        except FileNotFoundError:
            logging.error(f"AnimatedGIF({self.path}): GIF 檔案未找到。")
            self.tk_frames = []
        except Exception as e:
            logging.error(f"AnimatedGIF({self.path}): 載入 GIF 時發生錯誤: {e}", exc_info=True)
            self.tk_frames = []

    def setup_canvas(self, canvas_width, canvas_height):
        self.canvas_width = canvas_width
        self.canvas_height = canvas_height
        self.canvas = tk.Canvas(self.master, width=self.canvas_width, height=self.canvas_height,
                                highlightthickness=0, bg=self.default_bg_color)

    def _animate(self):
        if not self.is_playing or not self.tk_frames or not self.canvas or not self.canvas.winfo_exists():
            self.is_playing = False
            return

        if self.image_id:
            try: self.canvas.delete(self.image_id)
            except tk.TclError: pass
            self.image_id = None

        try:
            current_frame_tk = self.tk_frames[self.idx]
            img_width = current_frame_tk.width()
            img_height = current_frame_tk.height()
        except IndexError:
            logging.error(f"AnimatedGIF({self.path}): IndexError in _animate. idx={self.idx}, len(tk_frames)={len(self.tk_frames)}")
            self.stop_animation()
            return

        x = (self.canvas_width - img_width) // 2
        y = (self.canvas_height - img_height) // 2
        self.image_id = self.canvas.create_image(x, y, image=current_frame_tk, anchor=tk.NW)
        if self.canvas: self.canvas.current_display_ref = current_frame_tk

        self.idx += 1
        if self.idx >= len(self.tk_frames):
            logging.debug(f"AnimatedGIF({self.path}): Reached end of sequence (idx={self.idx}, len={len(self.tk_frames)}).")
            if self.on_animation_loop_complete:
                logging.debug(f"AnimatedGIF({self.path}): Calling on_animation_loop_complete.")
                self.master.after(0, self.on_animation_loop_complete)

            if self.loop:
                self.idx = 0
                logging.debug(f"AnimatedGIF({self.path}): Looping back to frame 0.")
            else:
                self.is_playing = False
                logging.debug(f"AnimatedGIF({self.path}): Animation finished (not looping). Stop scheduling.")
                return

        if self.is_playing:
            try:
                current_delay_for_next_frame = self.adjusted_delay[self.idx]
            except IndexError:
                logging.warning(f"AnimatedGIF({self.path}): IndexError for adjusted_delay. idx={self.idx}, len={len(self.adjusted_delay)}. Using default.")
                min_frame_delay = 20
                default_delay_val = self.force_smooth_delay_ms if self.force_smooth_delay_ms and self.force_smooth_delay_ms > 0 else 100
                current_delay_for_next_frame = max(min_frame_delay, int(default_delay_val / self.speed_multiplier))

            self.cancel_id = self.master.after(current_delay_for_next_frame, self._animate)
        else:
            logging.debug(f"AnimatedGIF({self.path}): Not scheduling next frame as is_playing is False.")


    def start_animation(self):
        if not self.canvas: logging.error(f"AnimatedGIF({self.path}): Canvas 未設定。"); return
        if not self.tk_frames: logging.error(f"AnimatedGIF({self.path}): tk_frames 為空。"); return
        if self.is_playing:
            logging.debug(f"AnimatedGIF({self.path}): start_animation called but already playing.")
            return

        self.stop_animation_internal()
        self.is_playing = True
        self.idx = 0

        if self.image_id and self.canvas.winfo_exists():
             try: self.canvas.delete(self.image_id)
             except tk.TclError: pass
        self.image_id = None

        logging.debug(f"AnimatedGIF({self.path}): Starting animation. Loop: {self.loop}. First adjusted delay: {self.adjusted_delay[0] if self.adjusted_delay else 'N/A'}")
        self._animate()

    def stop_animation_internal(self):
        if self.cancel_id:
            self.master.after_cancel(self.cancel_id)
            self.cancel_id = None
        if self.canvas and hasattr(self.canvas, 'current_display_ref'):
            try: del self.canvas.current_display_ref
            except AttributeError: pass

    def stop_animation(self):
        logging.debug(f"AnimatedGIF({self.path}): stop_animation called (public).")
        self.is_playing = False
        self.stop_animation_internal()

    def hide(self):
        if self.canvas: self.canvas.place_forget()

    def show(self, **place_options):
        if self.canvas:
            if 'width' not in place_options: place_options['width'] = self.canvas_width
            if 'height' not in place_options: place_options['height'] = self.canvas_height
            self.canvas.place(**place_options)

    def unload(self):
        logging.info(f"AnimatedGIF({self.path}): Unloading frames and stopping animation.")
        self.stop_animation()
        self.tk_frames = []
        self.delay = []
        self.adjusted_delay = []
        if self.canvas and self.image_id:
            try: self.canvas.delete(self.image_id)
            except tk.TclError: pass
            self.image_id = None
        self.on_animation_loop_complete = None


class GameLauncher:
    def __init__(self, master):
        self.master = master
        self.master.title("MineCraft啟動器")
        self.master.geometry("800x600")
        self.master.configure(bg="#2E2E2E")

        self.is_tkinter_fullscreen = True
        self.master.attributes("-fullscreen", self.is_tkinter_fullscreen)

        self.master.bind("<F11>", self.toggle_tkinter_fullscreen)
        self.master.bind("<Escape>", self.escape_tkinter_fullscreen)

        self.minecraft_bg_canvas = None
        self.minecraft_gif_player = None
        self.loading_label = None
        self.progress_bar = None
        self.buttons_frame = None
        self.version_label = None

        self._setup_ui_elements()
        self.master.after(100, self._start_launcher_animation_sequence)

    def toggle_tkinter_fullscreen(self, event=None):
        self.is_tkinter_fullscreen = not self.is_tkinter_fullscreen
        self.master.attributes("-fullscreen", self.is_tkinter_fullscreen)

    def escape_tkinter_fullscreen(self, event=None):
        if self.is_tkinter_fullscreen:
            self.is_tkinter_fullscreen = False
            self.master.attributes("-fullscreen", self.is_tkinter_fullscreen)

    def _setup_ui_elements(self):
        minecraft_gif_path = os.path.join(GIF_DIR, "minecraft_background_animation.gif")

        FORCED_MC_DELAY = 80

        logging.info(f"Setting up Minecraft GIF with forced delay: {FORCED_MC_DELAY}ms")
        self.minecraft_gif_player = AnimatedGIF(self.master, minecraft_gif_path,
                                                size=(1920, 1080), default_bg_color="#2E2E2E",
                                                loop=True,
                                                speed_multiplier=1.0,
                                                force_smooth_delay_ms=FORCED_MC_DELAY)
        if self.minecraft_gif_player.tk_frames:
            self.minecraft_gif_player.setup_canvas(1920, 1080)
            self.minecraft_bg_canvas = self.minecraft_gif_player.canvas
        else: logging.warning(f"Minecraft GIF player for {minecraft_gif_path} has no frames.")

        self.loading_label = tk.Label(self.master, text="正在準備遊戲...", font=("Arial", 12), fg="white", bg="#2E2E2E")
        self.progress_bar = ttk.Progressbar(self.master, orient="horizontal", length=300, mode="determinate")
        
        self.buttons_frame = tk.Frame(self.master, bg="#2E2E2E")
        tk.Label(self.buttons_frame, text="MINECRAFT", font=("Arial", 64, "bold"), fg="#E0E0E0", bg="#2E2E2E").pack(pady=(0, 5))
        tk.Label(self.buttons_frame, text="選擇遊戲模式", font=("Arial", 20, "bold"), fg="#E0E0E0", bg="#2E2E2E").pack(pady=20)
        
        style = ttk.Style()
        try: style.theme_use('clam')
        except tk.TclError: logging.warning("Clam theme not available.")
        style.configure("Grey.TButton", background="#555555", foreground="#FFFFFF", relief=tk.FLAT, padding=(10, 6), font=('Segoe UI', 10, 'bold'), borderwidth=0)
        style.map("Grey.TButton", background=[('active', '#6E6E6E'), ('pressed', '#4A4A4A'), ('disabled', '#3C3C3C')], foreground=[('active', '#FFFFFF'), ('pressed', '#E0E0E0'), ('disabled', '#777777')], relief=[('pressed', tk.SUNKEN), ('!pressed', tk.FLAT)])
        ttk.Button(self.buttons_frame, text="生存模式", command=lambda: self.start_game_thread("survival"), style="Grey.TButton", width=55).pack(pady=12)
        ttk.Button(self.buttons_frame, text="創造模式", command=lambda: self.start_game_thread("creative"), style="Grey.TButton", width=55).pack(pady=12)
        ttk.Button(self.buttons_frame, text="退出", command=self.on_quit, style="Grey.TButton", width=55).pack(pady=12)

        self.version_label = tk.Label(self.master, text="MineCraft Beta2.0", font=("Arial", 12), fg="white", bg="#2E2E2E")

    def on_quit(self):
        logging.info("GameLauncher: Quit button pressed.")
        if self.minecraft_gif_player: self.minecraft_gif_player.unload()
        self.master.quit()

    def _hide_all_stages(self):
        if self.minecraft_gif_player: self.minecraft_gif_player.hide()
        if self.loading_label: self.loading_label.place_forget()
        if self.progress_bar: self.progress_bar.place_forget()
        if self.buttons_frame: self.buttons_frame.place_forget()
        if self.version_label: self.version_label.place_forget()

    def _start_launcher_animation_sequence(self):
        self._hide_all_stages()
        self._show_minecraft_background()

    def _show_minecraft_background(self):
        logging.info("Showing Minecraft background.")
        self._hide_all_stages()

        if self.minecraft_gif_player and self.minecraft_gif_player.tk_frames and self.minecraft_bg_canvas:
            logging.info(f"Showing Minecraft background animation (looping). Expected loop duration: {sum(self.minecraft_gif_player.adjusted_delay)}ms")
            self.minecraft_gif_player.show(x=0, y=0, relwidth=1, relheight=1)
            self.minecraft_gif_player.start_animation()
        else:
            logging.warning("Minecraft background animation cannot be shown.")
            self.master.configure(bg="#2E2E2E")

        self.loading_label.place(relx=0.5, rely=0.75, anchor=tk.CENTER)
        self.progress_bar.place(relx=0.5, rely=0.8, anchor=tk.CENTER)
        self._simulate_loading()

    def _simulate_loading(self, current_progress=0):
        if current_progress <= 100:
            self.progress_bar['value'] = current_progress
            self.master.after(30, lambda: self._simulate_loading(current_progress + 2))
        else:
            self._show_main_buttons()

    def _show_main_buttons(self):
        if self.loading_label: self.loading_label.place_forget()
        if self.progress_bar: self.progress_bar.place_forget()
        if self.minecraft_gif_player and self.minecraft_gif_player.tk_frames and \
           self.minecraft_bg_canvas and not self.minecraft_bg_canvas.winfo_viewable():
            self.minecraft_gif_player.show(x=0, y=0, relwidth=1, relheight=1)
            if not self.minecraft_gif_player.is_playing:
                self.minecraft_gif_player.start_animation()
        self.buttons_frame.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
        if self.version_label:
            self.version_label.place(relx=0.01, rely=0.99, anchor='sw')
        self._re_enable_buttons_and_ui(force_show_buttons_frame=False)

    def start_game_thread(self, selected_mode):
        logging.info(f"GameLauncher: Attempting to start game in '{selected_mode}' mode.")
        if self.buttons_frame:
            for widget in self.buttons_frame.winfo_children():
                if isinstance(widget, ttk.Button): widget.state(['disabled'])
        if self.loading_label:
            self.loading_label.config(text=f"正在準備啟動 {selected_mode} 模式...")
            self.loading_label.place(relx=0.5, rely=0.85, anchor=tk.CENTER)
        thread = threading.Thread(target=self._start_game_logic, args=(selected_mode,))
        thread.daemon = True
        thread.start()

    def _start_game_logic(self, selected_mode):
        player_data = {}
        resolved_python_exe = None
        python_exe_aliases_to_try = ["python", "python3"]
        try:
            if os.path.exists(PLAYER_JSON_PATH):
                try:
                    with open(PLAYER_JSON_PATH, "r", encoding="utf-8") as f:
                        content = f.read()
                        if content.strip(): player_data = json.loads(content)
                        else: player_data = {}
                except json.JSONDecodeError:
                    logging.warning(f"{PLAYER_JSON_PATH} 格式錯誤。")
                    player_data = {}
                except Exception as e:
                    logging.error(f"讀取 {PLAYER_JSON_PATH} 錯誤: {e}", exc_info=True)
                    player_data = {}
            else:
                logging.info(f"{PLAYER_JSON_PATH} 未找到。")
                player_data = {}
            player_data["mode"] = selected_mode
            player_data.setdefault("position", [0.5, 15.0, 0.5])
            player_data.setdefault("rotation", [0.0, 0.0])
            player_data.setdefault("inventory_counts", {})
            player_data.setdefault("hotbar_keys", [None] * 9)
            player_data.setdefault("main_inventory_view_cache", [None] * (9 * 6))
            player_data.setdefault("current_hotbar_index", 0)
            player_data.setdefault("hp", 20)
            player_data.setdefault("hunger", 20)
            with open(PLAYER_JSON_PATH, "w", encoding="utf-8") as f:
                json.dump(player_data, f, indent=2, ensure_ascii=False)
            logging.info(f"Player data for mode '{selected_mode}' saved to {PLAYER_JSON_PATH}")
            python_exe_found = False
            version_check_timeout = 5
            for alias in python_exe_aliases_to_try:
                try:
                    proc_version_check = subprocess.run([alias, "--version"], check=True, capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=version_check_timeout)
                    potential_exe_path = shutil.which(alias)
                    if not potential_exe_path: potential_exe_path = alias
                    resolved_python_exe = potential_exe_path
                    python_exe_found = True
                    logging.info(f"Using Python alias '{alias}' (resolved to: {resolved_python_exe}). Version: {proc_version_check.stdout.strip()}")
                    break
                except (FileNotFoundError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
                    logging.warning(f"Python alias '{alias}' not found, version check failed, or timed out ({version_check_timeout}s): {e}. Trying next alias if available.")
            if not python_exe_found or not resolved_python_exe:
                logging.error(f"No suitable Python interpreter found after trying: {python_exe_aliases_to_try}.", exc_info=True)
                if self.master.winfo_exists():
                    self.master.after(0, lambda: msgbox.showerror("啟動失敗", f"找不到可用的 Python 解譯器 (嘗試過: {', '.join(python_exe_aliases_to_try)})。\n請確保 Python 已安裝並在 PATH 中，且能正常執行。"))
                self._re_enable_after_error()
                return
            pyglet_check_timeout = 10
            logging.info(f"Checking for pyglet using: '{resolved_python_exe}' with timeout {pyglet_check_timeout}s...")
            try:
                check_script = "import pyglet; print(f'Pyglet {pyglet.version} imported successfully')"
                clean_env = os.environ.copy()
                vars_to_remove_for_subprocess = ['PYTHONPATH', 'PYTHONDEVMODE', 'PYTHONDEBUG', 'DEBUGPY_LAUNCHER_PORT', 'DEBUGPY_SOCKET_PATH']
                if 'PYTHONPATH' in clean_env:
                    paths = clean_env['PYTHONPATH'].split(os.pathsep)
                    clean_env['PYTHONPATH'] = os.pathsep.join([p for p in paths if 'debugpy' not in p.lower() and 'pydevd' not in p.lower()])
                    if not clean_env['PYTHONPATH']: del clean_env['PYTHONPATH']
                for var in vars_to_remove_for_subprocess:
                     if var in clean_env and var != 'PYTHONPATH': del clean_env[var]
                startupinfo = None
                if os.name == 'nt':
                    startupinfo = subprocess.STARTUPINFO()
                    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                pyglet_check_proc = subprocess.run(
                    [resolved_python_exe, "-c", check_script], check=True, capture_output=True, text=True,
                    encoding='utf-8', errors='replace', timeout=pyglet_check_timeout, env=clean_env, startupinfo=startupinfo)
                logging.info(f"Pyglet check successful for '{resolved_python_exe}'. Output: {pyglet_check_proc.stdout.strip()}")
            except subprocess.CalledProcessError as e_pyglet_import:
                error_output = e_pyglet_import.stderr.strip() if e_pyglet_import.stderr else "N/A"
                stdout_output = e_pyglet_import.stdout.strip() if e_pyglet_import.stdout else "N/A"
                logging.error(f"Pyglet library import failed in '{resolved_python_exe}' environment. Stdout: {stdout_output}, Stderr: {error_output}", exc_info=True)
                if self.master.winfo_exists():
                    self.master.after(0, lambda: msgbox.showerror("依賴項缺失",
                        f"執行遊戲所需的 'pyglet' 函式庫在 '{resolved_python_exe}' 環境中匯入失敗。\n\n"
                        f"錯誤詳情 (stderr):\n{error_output[:300]}...\n\n"
                        f"請確認 'pyglet' 已正確安裝於此 Python 環境。\n嘗試安裝指令：\n'{resolved_python_exe} -m pip install pyglet'"))
                self._re_enable_after_error()
                return
            except subprocess.TimeoutExpired:
                logging.error(f"Checking for pyglet with '{resolved_python_exe}' timed out after {pyglet_check_timeout}s.")
                if self.master.winfo_exists():
                    self.master.after(0, lambda: msgbox.showerror("檢查超時",
                        f"使用 Python 解譯器:\n'{resolved_python_exe}'\n檢查 'pyglet' 函式庫時發生超時 ({pyglet_check_timeout} 秒)。\n\n"
                        f"這可能表示 Python 解譯器啟動緩慢，或 'pyglet' 匯入耗時較長。\n請嘗試在您的終端機 (命令提示字元) 中手動執行以下指令並觀察耗時：\n"
                        f"\"{resolved_python_exe}\" -c \"import pyglet; print('Pyglet imported')\"\n\n"
                        f"如果手動執行也緩慢、失敗或無回應，請檢查您的 Python 環境、pyglet 安裝，或是否有防毒軟體等程式影響。"))
                self._re_enable_after_error()
                return
            except FileNotFoundError:
                logging.error(f"Python interpreter '{resolved_python_exe}' not found when checking for pyglet (should have been caught earlier).")
                if self.master.winfo_exists():
                     self.master.after(0, lambda: msgbox.showerror("啟動失敗", f"找不到 Python 解譯器 '{resolved_python_exe}'。"))
                self._re_enable_after_error()
                return
            if self.master.winfo_exists(): self.master.after(0, self.master.withdraw)
            cmd_to_run = [resolved_python_exe, GAME_PY_PATH, f"--mode={selected_mode}"]
            logging.info(f"Running game: {' '.join(cmd_to_run)} in CWD: {MINECRAFT_CORE_DIR}")
            process = subprocess.Popen(cmd_to_run, cwd=MINECRAFT_CORE_DIR, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding='utf-8', errors='replace', env=clean_env, startupinfo=startupinfo)
            stdout, stderr = process.communicate()
            logging.info(f"Game process finished. Return code: {process.returncode}")
            if stdout: logging.info(f"Game stdout:\n{stdout.strip()}")
            if stderr:
                logging.error(f"Game stderr:\n{stderr.strip()}")
                if self.master.winfo_exists() and process.returncode != 0:
                     self.master.after(0, lambda: msgbox.showerror("遊戲錯誤", f"遊戲執行錯誤 (Code {process.returncode}).\n詳情請見 .minecraft/log/game.log 及 log/main_launcher.log。\n\n錯誤輸出:\n{stderr.strip()[:500]}..."))
        except FileNotFoundError as fnf_err:
            logging.error(f"啟動失敗 (FileNotFoundError for Popen): {fnf_err}", exc_info=True)
            if self.master.winfo_exists():
                py_exe_to_report = resolved_python_exe if resolved_python_exe else ", ".join(python_exe_aliases_to_try)
                self.master.after(0, lambda: msgbox.showerror("啟動失敗", f"找不到 Python 解譯器 ('{py_exe_to_report}') 或遊戲檔案 ({GAME_PY_PATH}).\n請檢查檔案路徑和 Python 安裝。\n錯誤: {fnf_err}"))
        except Exception as e:
            logging.error(f"啟動遊戲時發生未預期例外: {e}", exc_info=True)
            if self.master.winfo_exists():
                self.master.after(0, lambda: msgbox.showerror("啟動失敗", f"啟動遊戲時發生未預期錯誤：\n{e}\n\n{traceback.format_exc()}"))
        finally:
            logging.info("Game logic thread completing.")
            if hasattr(self.master, 'winfo_exists') and self.master.winfo_exists():
                if not self.master.winfo_viewable(): self.master.after(0, self.master.deiconify)
                self.master.after(50, lambda: self._re_enable_buttons_and_ui(force_show_buttons_frame=True))
            logging.info("Launcher UI restoration scheduled/completed.")

    def _re_enable_after_error(self):
        if hasattr(self.master, 'winfo_exists') and self.master.winfo_exists():
            self.master.after(10, lambda: self._re_enable_buttons_and_ui(force_show_buttons_frame=True))

    def _re_enable_buttons_and_ui(self, force_show_buttons_frame=False):
        def _task():
            if self.buttons_frame and self.buttons_frame.winfo_exists():
                 for widget in self.buttons_frame.winfo_children():
                    if isinstance(widget, ttk.Button) and widget.winfo_exists():
                        if 'disabled' in widget.state(): widget.state(['!disabled'])
            if self.loading_label and self.loading_label.winfo_exists(): self.loading_label.place_forget()
            if force_show_buttons_frame:
                if self.buttons_frame and self.buttons_frame.winfo_exists():
                     if not self.buttons_frame.winfo_viewable(): self.buttons_frame.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
            if hasattr(self.master, 'update_idletasks') and self.master.winfo_exists(): self.master.update_idletasks()
        if hasattr(self.master, 'winfo_exists') and self.master.winfo_exists(): self.master.after(100, _task)

if __name__ == "__main__":
    root = tk.Tk()
    minecraft_gif_abs_path = os.path.join(GIF_DIR, "minecraft_background_animation.gif")
    if not os.path.exists(minecraft_gif_abs_path): msgbox.showwarning("資源缺失", f"找不到背景動畫:\n{minecraft_gif_abs_path}")
    app = GameLauncher(root)
    root.mainloop()
    logging.info("Application mainloop finished.")