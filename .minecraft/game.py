import os
import json
import math
import logging
import random
import time
import sys

import pyglet
import pyglet.gl as gl

from pyglet.window import mouse, key
MAIN_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

GAME_LOG_DIR = os.path.join(MAIN_SCRIPT_DIR, "log")
os.makedirs(GAME_LOG_DIR, exist_ok=True)
game_log_file = os.path.join(GAME_LOG_DIR, "game.log")

# --- 使用簡潔且穩定的日誌設定 ---
if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(module)s.%(funcName)s:%(lineno)d - %(message)s',
        handlers=[
            logging.FileHandler(game_log_file, mode='w', encoding='utf-8'),
            logging.StreamHandler(sys.stdout) 
        ]
    )
else:
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(module)s.%(funcName)s:%(lineno)d - %(message)s',
        handlers=[
            logging.FileHandler(game_log_file, mode='w', encoding='utf-8')
        ]
    )
# --------------------------------

def gluPerspective(fovY, aspect, zNear, zFar):
    fH = math.tan(math.radians(fovY) / 2) * zNear
    fW = fH * aspect
    gl.glFrustum(-fW, fW, -fH, fH, zNear, zFar)

class Game:
    def __init__(self, window):
        self.window = window
        logging.info("遊戲引擎初始化開始...")
        self.world_batch = pyglet.graphics.Batch()
        self.held_block_batch = pyglet.graphics.Batch()
        self.breaking_effect_batch = pyglet.graphics.Batch()
        self.pause_menu = False
        self.show_keybinding_menu = False
        self.key_to_rebind = None
        
        self.keybindings = {
            "forward": key.W, "backward": key.S, "left": key.A, "right": key.D,
            "jump": key.SPACE, "sprint": key.Q, "sneak": key.LSHIFT,
            "inventory": key.E,
            "attack": mouse.LEFT,
            "place": mouse.RIGHT,
            "pick_block": mouse.MIDDLE,
            "chat": key.T,
            "command": key.RETURN
        }
        self.keybinding_labels = {} 
        self.conflicting_actions = set()

        self.keys = None
        # 新增滑鼠按鈕狀態追蹤
        self.mouse_btn_state = set() 

        try:
            key_handler_instance = pyglet.window.key.KeyStateHandler()
            window.push_handlers(key_handler_instance)
            self.keys = key_handler_instance
            logging.info("KeyStateHandler initialized and pushed successfully in Game.__init__.")
        except Exception as e:
            logging.critical(f"CRITICAL ERROR during KeyStateHandler initialization or push_handlers in Game.__init__: {e}", exc_info=True)
        
        if self.keys is None:
            logging.error("CRITICAL FAILURE in Game.__init__: self.keys IS STRICTLY NONE after initialization attempt!")
        
        self.world = {}
        self.generated_chunks = set()
        self.chunk_load_distance = 4
        self.chunk_size = 16

        self.texture_groups = {}
        self.textures = {}
        self.break_texture_groups = []
        
        self.recipes = {}
        self.show_crafting_table_ui = False
        self.inventory_crafting_grid = [None] * 4 
        self.inventory_crafting_result = None
        self.crafting_table_grid = [None] * 9
        self.crafting_table_result = None
        self.load_recipes()

        self.position = [0.5, 15.0, 0.5]
        self.rotation = [0.0, 0.0]
        self.velocity = [0.0, 0.0, 0.0]
        self.on_ground = False
        self.mode = "survival"
        self.hp = 20; self.max_hp = 20
        self.hunger = 20; self.max_hunger = 20

        self.inventory_cols = 9
        self.inventory_rows = 3
        self.hotbar_size = 9
        self.max_stack_size = 64
        
        self.hotbar = [None] * self.hotbar_size
        self.main_inventory = [None] * (self.inventory_cols * self.inventory_rows)
        
        self.current_hotbar_index = 0
        self.selected_block = None
        self.player_id = "BlueYuTW"

        self.inventory_selected_item_info = None
        
        self.mouse_x = 0; self.mouse_y = 0
        self.mouse_left_is_pressed = False
        
        self.last_click_time = 0.0
        self.last_click_info = None 
        self.double_click_threshold = 0.3

        self.game_hotbar_slot_size = 40; self.game_hotbar_padding = 5

        self.arm_display_offset = [0.35, -0.45, -0.6]; self.original_arm_offset_y = self.arm_display_offset[1]
        self.held_block_offset = [0.45, -0.35, -0.5]; self.held_block_scale = 0.2

        self.arm_swing_active = False; self.arm_swing_start_time = 0; self.arm_swing_duration = 0.25

        self.breaking_block_pos = None; self.breaking_block_start_time = 0
        self.breaking_block_stage = 0
        self.break_time_map = {
            "dirt": 0.5, "grass_block": 0.6, "sand": 0.5, "gravel": 0.6,
            "oak_log": 2.0, "oak_leaves": 0.2, "stone": 1.5, "cobblestone": 2.0,
            "coal_ore": 3.0, "iron_ore": 3.0, "gold_ore": 3.0, "diamond_ore": 3.0,
            "lapis_ore": 3.0, "oak_planks": 2.0, "birch_log": 2.0, "birch_leaves": 0.2,
            "crafting_table": 2.5, "birch_planks": 2.0,
        }
        
        self.valid_give_items = set(self.break_time_map.keys())
        self.valid_give_items.update(["oak_planks", "birch_planks", "crafting_table"])

        self.chat_active = False
        self.chat_input = ""
        self.chat_label = pyglet.text.Label("", x=10, y=10, font_size=14, color=(255, 255, 255, 255))
        self.ignore_next_text = False

        # --- [Tab 補全相關變數] ---
        self.tab_matches = []      
        self.tab_index = 0         
        self.tab_prefix = ""       
        # -------------------------
        
        self.chat_feedback_messages = []
        self.chat_feedback_duration = 7.0
        self.chat_feedback_y_start = 40
        self.chat_feedback_spacing = 20

        self.tooltip_label = None
        self.tooltip_bg_batch = None

        self.texture_base_path = os.path.join(MAIN_SCRIPT_DIR, "assets", "minecraft", "textures", "block")
        
        self.texture_map = {
            "grass_block_top": "grass_block_top", "grass_block_side": "grass_block_side",
            "grass_block_bottom": "dirt", "dirt": "dirt", "stone": "stone",
            "cobblestone": "cobblestone", "oak_planks": "oak_planks", "sand": "sand",
            "gravel": "gravel", "gold_ore": "gold_ore", "iron_ore": "iron_ore",
            "coal_ore": "coal_ore", "diamond_ore": "diamond_ore", "lapis_ore": "lapis_ore",
            "oak_log_top": "oak_log_top", "oak_log_side": "oak_log", "oak_leaves": "oak_leaves",
            "birch_log_top": "birch_log_top", "birch_log_side": "birch_log", "birch_leaves": "birch_leaves",
            "crafting_table_top": "crafting_table_top", "crafting_table_side": "crafting_table_side",
            "crafting_table_front": "crafting_table_front",
            "birch_planks": "birch_planks",
        }
        self.load_textures_and_groups()

        player_data_loaded_successfully = False
        player_data_file_path = os.path.join(MAIN_SCRIPT_DIR, "playerdata", "player.json")
        os.makedirs(os.path.dirname(player_data_file_path), exist_ok=True)
        try:
            with open(player_data_file_path, "r", encoding='utf-8') as f: data = json.load(f)
            self.mode = data.get("mode", self.mode)
            self.player_id = data.get("player_id", "BlueYuTW")
            loaded_pos_raw = data.get("position", self.position)
            self.position = [float(p) for p in loaded_pos_raw] if isinstance(loaded_pos_raw, list) and len(loaded_pos_raw) == 3 else self.position
            loaded_rot_raw = data.get("rotation", self.rotation)
            self.rotation = [float(r) for r in loaded_rot_raw] if isinstance(loaded_rot_raw, list) and len(loaded_rot_raw) == 2 else self.rotation
            if "hotbar" in data and "main_inventory" in data:
                self.hotbar = data.get("hotbar", self.hotbar)
                self.main_inventory = data.get("main_inventory", self.main_inventory)
                self.inventory_crafting_grid = data.get("inventory_crafting_grid", self.inventory_crafting_grid)
                self.crafting_table_grid = data.get("crafting_table_grid", self.crafting_table_grid)
            else:
                logging.warning("舊版玩家存檔格式，將初始化新的物品欄。")
                self._initial_populate_inventory_slots()
            self.current_hotbar_index = data.get("current_hotbar_index", self.current_hotbar_index)
            player_data_loaded_successfully = True
            logging.info(f"Player data loaded from {player_data_file_path}.")
        except FileNotFoundError:
            logging.warning(f"{player_data_file_path} 未找到. 將初始化新的玩家狀態。")
            self._initial_populate_inventory_slots()
        except json.JSONDecodeError as e:
            logging.error(f"解碼 {player_data_file_path} 失敗: {e}. 將初始化新的玩家狀態。", exc_info=True)
            self._initial_populate_inventory_slots()
        except Exception as e:
            logging.error(f"讀取 {player_data_file_path} 時發生其他錯誤: {e}. 將初始化新的玩家狀態。", exc_info=True)
            self._initial_populate_inventory_slots()

        if not player_data_loaded_successfully: 
            logging.info("玩家數據未載入或損壞，已使用預設物品欄初始化。")
        
        self.check_crafting_recipe('inventory')
        self.check_crafting_recipe('crafting_table')


        self.show_inventory = False
        self._update_mouse_exclusivity()

        self.gravity = -20.0; self.jump_force = 8.0
        self.normal_move_speed = 5.0; self.sprint_speed_multiplier = 1.6
        self.sneak_speed_multiplier = 0.5; self.fly_speed = 10.0
        self.player_height = 1.8; self.sneak_camera_offset_y = 0.25
        self.is_sprinting = False; self.is_sneaking = False; self.is_flying_creative = False
        self.last_space_press_time = 0; self.double_tap_time = 0.3
        self.chunk_dirty = True

        self.last_jump_time = 0; self.jump_cooldown = 0.3

        self.skin_texture = None
        self.arm_vertex_list = None
        skin_path = os.path.join(MAIN_SCRIPT_DIR, 'assets', 'skins', 'BlueYuTW.png')
        try:
            if os.path.exists(skin_path):
                self.skin_image = pyglet.image.load(skin_path)
                self.skin_texture = self.skin_image.get_texture()
                self.create_right_arm_geometry()
            else:
                logging.warning(f"皮膚檔案不存在: {skin_path}，將不顯示手臂。")
        except Exception as e:
            logging.error(f"載入皮膚或創建手臂模型時出錯: {e}", exc_info=True)

        self.load_world()
        self.ensure_player_on_surface() 
        self.update_selected_block_from_hotbar()

        self.hp_label = pyglet.text.Label(f"HP: {self.hp}/{self.max_hp}", x=10, y=window.height - 30, color=(255,0,0,255))
        self.hunger_label = pyglet.text.Label(f"Hunger: {self.hunger}/{self.max_hunger}", x=10, y=window.height - 60, color=(255,165,0,255))
        self.pos_label = pyglet.text.Label("", x=10, y=10, color=(255,255,255,255), width=window.width - 20, multiline=False)
        
        self.load_keybindings()
        logging.info("遊戲引擎初始化完成。")
        def render_player_avatar(self, x, y, scale=2.0, facing="front"):
            """
            在指定座標 x, y 以 scale 繪製玩家角色（正面/背面），皮膚分割為頭、身體、手、腳。
            facing: "front" 顯示正面，"back" 顯示背面（鏡像）。
            """
            if not hasattr(self, 'skin_image') or self.skin_image is None:
                return
            img = self.skin_image
            # Minecraft 皮膚預設 64x64
            # 區塊座標參考 https://minecraft.wiki/w/Skin
            # 頭部正面: (8,8,8,8) 背面: (24,8,8,8)
            # 身體正面: (20,20,8,12) 背面: (32,20,8,12)
            # 左手正面: (36,52,4,12) 背面: (52,52,4,12)
            # 右手正面: (44,20,4,12) 背面: (52,20,4,12)
            # 左腳正面: (20,52,4,12) 背面: (28,52,4,12)
            # 右腳正面: (4,20,4,12) 背面: (12,20,4,12)
            # 只顯示正面/背面，不做 3D 旋轉
            def blit_part(sx, sy, sw, sh, dx, dy, dw, dh, mirror=False):
                region = img.get_region(sx, sy, sw, sh)
                if mirror:
                    region = region.get_transform(flip_x=True)
                region.blit(dx, dy, width=dw, height=dh)
            # 頭部
            head_w, head_h = 8*scale, 8*scale
            head_x, head_y = x + 12*scale, y + 40*scale
            if facing == "front":
                blit_part(8, 8, 8, 8, head_x, head_y, head_w, head_h)
            else:
                blit_part(24, 8, 8, 8, head_x, head_y, head_w, head_h)
            # 身體
            body_w, body_h = 8*scale, 12*scale
            body_x, body_y = x + 12*scale, y + 28*scale
            if facing == "front":
                blit_part(20, 20, 8, 12, body_x, body_y, body_w, body_h)
            else:
                blit_part(32, 20, 8, 12, body_x, body_y, body_w, body_h)
            # 左手
            arm_w, arm_h = 4*scale, 12*scale
            left_arm_x, left_arm_y = x + 8*scale, y + 28*scale
            if facing == "front":
                blit_part(36, 52, 4, 12, left_arm_x, left_arm_y, arm_w, arm_h)
            else:
                blit_part(52, 52, 4, 12, left_arm_x, left_arm_y, arm_w, arm_h)
            # 右手
            right_arm_x = x + 20*scale
            if facing == "front":
                blit_part(44, 20, 4, 12, right_arm_x, left_arm_y, arm_w, arm_h)
            else:
                blit_part(52, 20, 4, 12, right_arm_x, left_arm_y, arm_w, arm_h)
            # 左腳
            leg_w, leg_h = 4*scale, 12*scale
            left_leg_x, left_leg_y = x + 12*scale, y + 16*scale
            if facing == "front":
                blit_part(20, 52, 4, 12, left_leg_x, left_leg_y, leg_w, leg_h)
            else:
                blit_part(28, 52, 4, 12, left_leg_x, left_leg_y, leg_w, leg_h)
            # 右腳
            right_leg_x = x + 16*scale
            if facing == "front":
                blit_part(4, 20, 4, 12, right_leg_x, left_leg_y, leg_w, leg_h)
            else:
                blit_part(12, 20, 4, 12, right_leg_x, left_leg_y, leg_w, leg_h)
    
    def _get_binding_name(self, code):
        if code == mouse.LEFT: return "滑鼠左鍵"
        if code == mouse.RIGHT: return "滑鼠右鍵"
        if code == mouse.MIDDLE: return "滑鼠中鍵"
        if code == 8: return "滑鼠側鍵 4"
        if code == 16: return "滑鼠側鍵 5"
        
        try:
            return key.symbol_string(code)
        except (ValueError, KeyError):
            return "未知按鍵"

    def is_action_pressed(self, action_name):
        binding_code = self.keybindings.get(action_name)
        if binding_code is None:
            return False
        if self.keys and self.keys.get(binding_code, False):
            return True
        if binding_code in self.mouse_btn_state:
            return True
        return False

    def load_keybindings(self):
        path = os.path.join(MAIN_SCRIPT_DIR,"settings","keybindings.json")
        try:
            with open(path, "r") as f:
                loaded_keys = json.load(f)
                for action, key_code in loaded_keys.items():
                    if action in self.keybindings:
                        self.keybindings[action] = key_code
            logging.info(f"從 {path} 載入按鍵設定。")
        except FileNotFoundError:
            logging.info(f"按鍵設定檔案 {path} 未找到，使用預設值。")
        except Exception as e:
            logging.error(f"讀取按鍵設定時發生錯誤: {e}", exc_info=True)
        self.check_key_conflicts()

    def save_keybindings(self):
        path = os.path.join(MAIN_SCRIPT_DIR,"settings", "keybindings.json")
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                json.dump(self.keybindings, f, indent=4)
            logging.info(f"按鍵設定已儲存至 {path}。")
        except Exception as e:
            logging.error(f"儲存按鍵設定失敗: {e}", exc_info=True)

    def check_key_conflicts(self):
        self.conflicting_actions.clear()
        key_to_actions = {}
        for action, key_code in self.keybindings.items():
            if key_code not in key_to_actions:
                key_to_actions[key_code] = []
            key_to_actions[key_code].append(action)
        
        for key_code, actions in key_to_actions.items():
            if len(actions) > 1:
                for action in actions:
                    self.conflicting_actions.add(action)

    def add_chat_feedback(self, message_text, color=(255, 255, 255, 255)):
        label = pyglet.text.Label(
            message_text,
            font_name='Microsoft JhengHei',
            x=10,
            y=0,
            font_size=14,
            color=color
        )
        expiry_time = time.time() + self.chat_feedback_duration
        self.chat_feedback_messages.append({'label': label, 'expiry': expiry_time})
        if len(self.chat_feedback_messages) > 10:
            self.chat_feedback_messages.pop(0)

    def draw_chat_feedback(self):
        current_y = self.chat_feedback_y_start
        if self.chat_active:
            current_y += 40

        for message in reversed(self.chat_feedback_messages):
            message['label'].y = current_y
            time_left = message['expiry'] - time.time()
            if time_left < 1.0:
                opacity = int(max(0, time_left) * 255)
                original_color = list(message['label'].color)
                original_color[3] = opacity
                message['label'].color = tuple(original_color)

            message['label'].draw()
            current_y += self.chat_feedback_spacing

    def _update_mouse_exclusivity(self):
        should_be_exclusive = not self.show_inventory and not self.pause_menu and not self.chat_active and not self.show_crafting_table_ui and not self.show_keybinding_menu
        if self.window._exclusive_mouse != should_be_exclusive:
            try:
                self.window.set_exclusive_mouse(should_be_exclusive)
            except Exception as e:
                logging.error(f"Error setting mouse exclusivity to {should_be_exclusive}: {e}", exc_info=True)

    def _initial_populate_inventory_slots(self):
        logging.info("Performing initial population of inventory for a new game state.")
        self.hotbar = [None] * self.hotbar_size
        self.main_inventory = [None] * (self.inventory_cols * self.inventory_rows)
        self.inventory_crafting_grid = [None] * 4
        self.crafting_table_grid = [None] * 9
        self.current_hotbar_index = 0
        logging.info(f"  Initialized empty hotbar: {self.hotbar}")
        logging.info(f"  Initialized empty main inventory: {self.main_inventory}")
    
    def add_item_to_inventory(self, item_id, count_to_add):
        for slot in self.hotbar:
            if slot and slot['id'] == item_id and slot['count'] < self.max_stack_size:
                can_add = self.max_stack_size - slot['count']
                add_amount = min(count_to_add, can_add)
                slot['count'] += add_amount
                count_to_add -= add_amount
                if count_to_add == 0: return True
        
        for slot in self.main_inventory:
            if slot and slot['id'] == item_id and slot['count'] < self.max_stack_size:
                can_add = self.max_stack_size - slot['count']
                add_amount = min(count_to_add, can_add)
                slot['count'] += add_amount
                count_to_add -= add_amount
                if count_to_add == 0: return True

        if count_to_add > 0:
            for i in range(len(self.hotbar)):
                if self.hotbar[i] is None:
                    add_amount = min(count_to_add, self.max_stack_size)
                    self.hotbar[i] = {'id': item_id, 'count': add_amount}
                    count_to_add -= add_amount
                    if count_to_add == 0: return True

        if count_to_add > 0:
            for i in range(len(self.main_inventory)):
                if self.main_inventory[i] is None:
                    add_amount = min(count_to_add, self.max_stack_size)
                    self.main_inventory[i] = {'id': item_id, 'count': add_amount}
                    count_to_add -= add_amount
                    if count_to_add == 0: return True
        
        if count_to_add > 0:
            logging.warning(f"物品欄已滿！無法添加 {count_to_add} 個 {item_id}。")
            return False
        return True

    def _refresh_inventory_display_layout(self): 
        self.update_selected_block_from_hotbar()

    def update_selected_block_from_hotbar(self):
        old_selected = self.selected_block
        current_item_slot = self.hotbar[self.current_hotbar_index]

        if current_item_slot and current_item_slot['count'] > 0:
            self.selected_block = current_item_slot['id']
        else:
            if current_item_slot and current_item_slot['count'] <= 0:
                self.hotbar[self.current_hotbar_index] = None
            self.selected_block = None
        
        if old_selected != self.selected_block: 
            self.rebuild_held_block_geometry()

    def create_right_arm_geometry(self):
        arm_w, arm_h, arm_d = 0.15, 0.5, 0.15; ax, ay, az = 0.0, -arm_h / 2, -arm_d / 2
        A, B, C, D = (ax, ay, az), (ax + arm_w, ay, az), (ax + arm_w, ay, az + arm_d), (ax, ay, az + arm_d)
        E, F, G, H = (ax, ay + arm_h, az), (ax + arm_w, ay + arm_h, az), (ax + arm_w, ay + arm_h, az + arm_d), (ax, ay + arm_h, az + arm_d)
        v_list = [*D, *C, *G, *H, *B, *A, *E, *F, *A, *D, *H, *E, *C, *B, *F, *G, *H, *G, *F, *E, *A, *B, *C, *D]
        sw, sh = 64.0, 64.0; uv_defs = [(40,20,4,12),(48,20,4,12),(44,20,4,12),(52,20,4,12),(44,16,4,4),(48,16,4,4)]; tc_list = []
        for xuv,yuv,wuv,huv in uv_defs: u0,v0_img,u1,v1_img=xuv/sw,(yuv+huv)/sh,(xuv+wuv)/sw,yuv/sh; v0_gl,v1_gl=1.0-v0_img,1.0-v1_img; tc_list.extend([u0,v0_gl,u1,v0_gl,u1,v1_gl,u0,v1_gl])
        self.arm_vertex_list = pyglet.graphics.vertex_list(24, ('v3f/static', v_list), ('t2f/static', tc_list))

    def draw_first_person_arm(self):
        if self.show_inventory or self.pause_menu or not self.skin_texture or not self.arm_vertex_list or self.selected_block: return
        gl.glMatrixMode(gl.GL_MODELVIEW); gl.glPushMatrix(); gl.glLoadIdentity()
        current_arm_y_offset = self.original_arm_offset_y
        if self.arm_swing_active:
            elapsed = time.time() - self.arm_swing_start_time
            if elapsed >= self.arm_swing_duration: self.arm_swing_active = False
            else: progress = elapsed/self.arm_swing_duration; current_arm_y_offset = self.original_arm_offset_y - (math.sin(math.pi * progress) * 0.15)
        gl.glTranslatef(self.arm_display_offset[0], current_arm_y_offset, self.arm_display_offset[2]); gl.glRotatef(90.0, 1.0, 0.0, 0.0)
        if self.arm_swing_active:
            progress = (time.time() - self.arm_swing_start_time) / self.arm_swing_duration
            if progress < 1.0: gl.glRotatef(-math.sin(progress * math.pi) * 30, 0, 0, 1)
        gl.glPushAttrib(gl.GL_DEPTH_BUFFER_BIT | gl.GL_LIGHTING_BIT | gl.GL_ENABLE_BIT); gl.glDisable(gl.GL_DEPTH_TEST); gl.glDisable(gl.GL_LIGHTING)
        gl.glEnable(self.skin_texture.target); gl.glBindTexture(self.skin_texture.target, self.skin_texture.id)
        gl.glTexParameteri(self.skin_texture.target, gl.GL_TEXTURE_MAG_FILTER, gl.GL_NEAREST); gl.glTexParameteri(self.skin_texture.target, gl.GL_TEXTURE_MIN_FILTER, gl.GL_NEAREST)
        self.arm_vertex_list.draw(gl.GL_QUADS); gl.glDisable(self.skin_texture.target); gl.glPopAttrib(); gl.glPopMatrix()

    def trigger_arm_swing_animation(self):
        if not self.arm_swing_active: self.arm_swing_active = True; self.arm_swing_start_time = time.time()

    def get_block_face_vertices(self, world_x, world_y, world_z, face_index, scale=1.0, center_offset=(0.0,0.0,0.0), rotation=0):
        # rotation: 0, 1, 2, 3 (0, 90, 180, 270 degrees clockwise)
        
        s = scale
        cx, cy, cz = center_offset[0]*s, center_offset[1]*s, center_offset[2]*s
        
        v = [
            (0-cx, 0-cy, 0-cz), (s-cx, 0-cy, 0-cz), (s-cx, s-cy, 0-cz), (0-cx, s-cy, 0-cz),
            (0-cx, 0-cy, s-cz), (s-cx, 0-cy, s-cz), (s-cx, s-cy, s-cz), (0-cx, s-cy, s-cz)
        ]
        
        p = [(vx+world_x, vy+world_y, vz+world_z) for vx, vy, vz in v]
        
        # 標準紋理座標 (BL, BR, TR, TL)
        base_tc = [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0)]
        
        # 根據 rotation 旋轉紋理座標順序
        # 旋轉貼圖相當於循環移動這四個點
        tc_quad = base_tc[rotation:] + base_tc[:rotation]

        standard_faces_vertex_indices = [
            (p[1], p[5], p[6], p[2]), # right
            (p[4], p[0], p[3], p[7]), # left
            (p[3], p[2], p[6], p[7]), # top
            (p[4], p[5], p[1], p[0]), # bottom
            (p[4], p[5], p[6], p[7]), # back (actually front in some contexts)
            (p[1], p[0], p[3], p[2])  # front
        ]
        
        selected_face_v_coords = standard_faces_vertex_indices[face_index]
        final_vertices = []
        for vc in selected_face_v_coords:
            final_vertices.extend(vc)
            
        final_tex_coords = []
        for tcp in tc_quad:
            final_tex_coords.extend(tcp)
            
        return final_vertices, final_tex_coords

    def rebuild_held_block_geometry(self):
        self.held_block_batch = pyglet.graphics.Batch();
        if not self.selected_block: return
        block_type_id = self.selected_block; default_texture_key = "stone"; texture_keys_for_faces = [default_texture_key] * 6
        if block_type_id == "grass_block": texture_keys_for_faces = ["grass_block_side","grass_block_side","grass_block_top","grass_block_bottom","grass_block_side","grass_block_side"]
        elif block_type_id == "oak_log": texture_keys_for_faces = ["oak_log_side","oak_log_side","oak_log_top","oak_log_top","oak_log_side","oak_log_side"]
        elif block_type_id == "birch_log": texture_keys_for_faces = ["birch_log_side","birch_log_side","birch_log_top","birch_log_top","birch_log_side","birch_log_side"]
        elif block_type_id == "crafting_table": texture_keys_for_faces = ["crafting_table_side", "crafting_table_side", "crafting_table_top", "oak_planks", "crafting_table_front", "crafting_table_side"]
        elif block_type_id == "oak_leaves" or block_type_id == "birch_leaves": texture_keys_for_faces = [block_type_id] * 6
        elif block_type_id in self.texture_map: texture_keys_for_faces = [block_type_id] * 6
        elif block_type_id in self.texture_groups: texture_keys_for_faces = [block_type_id] * 6 
        vertex_texture_groups = [];
        for tex_key in texture_keys_for_faces: tex_group = self.texture_groups.get(tex_key, self.texture_groups.get(default_texture_key)); vertex_texture_groups.append(tex_group)
        scale = self.held_block_scale
        for face_idx in range(6):
            if vertex_texture_groups[face_idx]:
                # 手持物品不需要隨機旋轉，傳入 0
                v, tc = self.get_block_face_vertices(0,0,0,face_idx,scale=scale,center_offset=(0.5,0.5,0.5), rotation=0)
                self.held_block_batch.add(4,gl.GL_QUADS,vertex_texture_groups[face_idx],('v3f/static',v),('t2f/static',tc))

    def draw_held_block(self):
        if self.show_inventory or self.pause_menu or not self.selected_block: return
        gl.glMatrixMode(gl.GL_MODELVIEW); gl.glPushMatrix(); gl.glLoadIdentity()
        gl.glTranslatef(self.held_block_offset[0],self.held_block_offset[1],self.held_block_offset[2]); gl.glRotatef(-30,1,0,0); gl.glRotatef(45,0,1,0)
        if self.arm_swing_active:
            elapsed = time.time() - self.arm_swing_start_time
            if elapsed < self.arm_swing_duration: gl.glRotatef(-math.sin((elapsed/self.arm_swing_duration)*math.pi)*20,1,0,1)
        gl.glPushAttrib(gl.GL_DEPTH_BUFFER_BIT|gl.GL_LIGHTING_BIT|gl.GL_POLYGON_BIT|gl.GL_TEXTURE_BIT|gl.GL_ENABLE_BIT)
        gl.glDisable(gl.GL_DEPTH_TEST); gl.glDisable(gl.GL_LIGHTING); gl.glEnable(gl.GL_TEXTURE_2D)
        if self.selected_block == "oak_leaves" or self.selected_block == "birch_leaves" or self.selected_block == "birch_planks":
            gl.glEnable(gl.GL_BLEND); gl.glBlendFunc(gl.GL_SRC_ALPHA,gl.GL_ONE_MINUS_SRC_ALPHA)
        self.held_block_batch.draw()
        if self.selected_block == "oak_leaves" or self.selected_block == "birch_leaves" or self.selected_block == "birch_planks":
            gl.glDisable(gl.GL_BLEND)
        gl.glPopAttrib(); gl.glPopMatrix()

    def ensure_player_on_surface(self):
        if not self.world: return
        if self.mode == "creative" and self.position[1] > -10 and not self.is_flying_creative: 
            if self.position[1] < -20: 
                self.position[1] = 15.0; self.velocity = [0,0,0]; return
        
        player_x_block, player_z_block = math.floor(self.position[0]), math.floor(self.position[2])
        player_foot_y_int = math.floor(self.position[1])
        player_head_y_int = math.floor(self.position[1] + self.player_height - 0.01) 
        
        stuck_in_block = False
        non_solid_blocks = {"oak_leaves", "birch_leaves"}
        if (player_x_block, player_foot_y_int, player_z_block) in self.world and \
           self.world.get((player_x_block, player_foot_y_int, player_z_block)) not in non_solid_blocks:
            stuck_in_block = True
        if (player_x_block, player_head_y_int, player_z_block) in self.world and \
           self.world.get((player_x_block, player_head_y_int, player_z_block)) not in non_solid_blocks:
           if self.position[1] + self.player_height - 0.01 < player_head_y_int + 1.0:
               stuck_in_block = True
        
        if self.position[1] < -5 and self.mode == "survival": 
            stuck_in_block = True

        if stuck_in_block:
            logging.warning(f"Player stuck or out of bounds at {self.position}. Attempting to find safe spot.")
            search_x, search_z = player_x_block, player_z_block
            found_safe_spot = False
            start_search_y = math.floor(self.position[1]) + 5 
            for y_candidate_feet in range(start_search_y, -10, -1): 
                block_below_pos = (search_x, y_candidate_feet - 1, search_z)
                standing_spot_pos = (search_x, y_candidate_feet, search_z) 
                head_spot_pos = (search_x, y_candidate_feet + 1, search_z) 

                block_type_below = self.world.get(block_below_pos)
                block_type_standing = self.world.get(standing_spot_pos)
                block_type_head = self.world.get(head_spot_pos)

                if block_type_below and block_type_below not in non_solid_blocks and \
                   (not block_type_standing or block_type_standing in non_solid_blocks) and \
                   (not block_type_head or block_type_head in non_solid_blocks):
                    self.position = [search_x + 0.5, float(y_candidate_feet), search_z + 0.5]
                    self.velocity = [0,0,0]
                    if self.mode == "survival": self.on_ground = True
                    logging.info(f"Moved player to safe spot: {self.position}")
                    found_safe_spot = True
                    break
            
            if not found_safe_spot:
                self.position = [self.position[0], 30.0, self.position[2]] 
                self.velocity = [0,0,0]
                self.on_ground = False 
                logging.warning(f"Could not find safe spot nearby, moved player to default height: {self.position}")

                new_foot_y = math.floor(self.position[1])
                new_head_y = math.floor(self.position[1] + self.player_height - 0.01)
                if ( (math.floor(self.position[0]), new_foot_y, math.floor(self.position[2])) in self.world and \
                     self.world.get((math.floor(self.position[0]), new_foot_y, math.floor(self.position[2]))) not in non_solid_blocks ) or \
                   ( (math.floor(self.position[0]), new_head_y, math.floor(self.position[2])) in self.world and \
                     self.world.get((math.floor(self.position[0]), new_head_y, math.floor(self.position[2]))) not in non_solid_blocks ):
                    self.position[1] += 5.0 
                    logging.warning("Still stuck after default height, pushed further up.")


    def load_textures_and_groups(self):
        for texture_key_mapped, texture_filename_mapped in self.texture_map.items():
            full_path = os.path.join(self.texture_base_path, f"{texture_filename_mapped}.png"); texture_key_to_store = texture_key_mapped
            if os.path.exists(full_path):
                try:
                    image = pyglet.image.load(full_path); texture = image.get_texture(); gl.glBindTexture(texture.target, texture.id)
                    gl.glTexParameteri(texture.target,gl.GL_TEXTURE_MIN_FILTER,gl.GL_NEAREST); gl.glTexParameteri(texture.target,gl.GL_TEXTURE_MAG_FILTER,gl.GL_NEAREST)
                    if "leaves" in texture_filename_mapped: gl.glTexParameteri(texture.target,gl.GL_TEXTURE_WRAP_S,gl.GL_CLAMP_TO_EDGE); gl.glTexParameteri(texture.target,gl.GL_TEXTURE_WRAP_T,gl.GL_CLAMP_TO_EDGE)
                    gl.glBindTexture(texture.target,0); self.textures[texture_key_to_store]=texture; self.texture_groups[texture_key_to_store]=pyglet.graphics.TextureGroup(texture)
                except Exception as e: logging.error(f"載入材質 {full_path} 或建立 TextureGroup for '{texture_key_to_store}' 失敗: {e}", exc_info=True)
            else:
                logging.warning(f"材質檔案 {full_path} for key '{texture_key_to_store}' (mapped from '{texture_filename_mapped}') 不存在. Creating dummy texture.")
                try:
                    from PIL import Image, ImageDraw; base_color = (128,0,128,255)
                    if texture_filename_mapped == "birch_planks": base_color = (220, 200, 150, 255)
                    elif texture_filename_mapped == "birch_log": base_color = (215, 215, 215, 255)
                    elif texture_filename_mapped == "birch_log_top": base_color = (225, 225, 225, 255)
                    elif texture_filename_mapped == "birch_leaves": base_color = (128, 180, 128, 128)
                    elif texture_filename_mapped == "crafting_table_top": base_color = (180, 140, 100, 255)
                    elif texture_filename_mapped == "crafting_table_side": base_color = (160, 120, 80, 255)
                    elif texture_filename_mapped == "crafting_table_front": base_color = (160, 120, 80, 255)
                    elif texture_filename_mapped=="coal_ore": base_color=(50,50,50,255)
                    elif texture_filename_mapped=="diamond_ore": base_color=(100,200,250,255)
                    elif texture_filename_mapped == "lapis_lazuli_ore": base_color = (50, 50, 200, 255)
                    elif texture_filename_mapped == "iron_ore": base_color = (210, 150, 120, 255)
                    elif texture_filename_mapped == "gold_ore": base_color = (255, 220, 50, 255)
                    elif texture_filename_mapped == "oak_log_top": base_color = (180, 150, 100, 255)
                    elif texture_filename_mapped == "oak_log": base_color = (101, 67, 33, 255)
                    elif texture_filename_mapped == "oak_leaves": base_color = (50, 150, 50, 128)
                    elif texture_filename_mapped == "grass_block_top": base_color = (30, 200, 50, 255)
                    elif texture_filename_mapped == "grass_block_side": base_color = (130, 90, 60, 255)
                    elif texture_filename_mapped == "dirt": base_color = (130, 90, 60, 255)
                    elif texture_filename_mapped == "stone": base_color = (128, 128, 128, 255)
                    elif texture_filename_mapped == "cobblestone": base_color = (120, 120, 120, 255)
                    elif texture_filename_mapped == "oak_planks": base_color = (200, 160, 100, 255)
                    elif texture_filename_mapped == "sand": base_color = (240, 230, 140, 255)
                    elif texture_filename_mapped == "gravel": base_color = (160, 160, 160, 255)
                    img_pil = Image.new('RGBA',(16,16),color=base_color); draw = ImageDraw.Draw(img_pil)
                    if "leaves" in texture_filename_mapped:
                        for _ in range(random.randint(25,55)): x_rand,y_rand=random.randint(0,15),random.randint(0,15); alpha=0 if random.random()<0.7 else random.randint(10,70); draw.point((x_rand,y_rand),fill=(base_color[0],base_color[1],base_color[2],alpha))
                    if texture_filename_mapped in ["stone","cobblestone","gravel","dirt","grass_block_side", "birch_log"]:
                        num_dots = random.randint(15,30)
                        if texture_filename_mapped == "birch_log":
                            for _ in range(num_dots):
                                x_r, y_r = random.randint(0,15), random.randint(0,15)
                                shade = random.randint(-40, 40)
                                if random.random() < 0.2:
                                    draw.rectangle([(x_r, y_r), (x_r+1, y_r+2)], fill=(40+shade, 40+shade, 40+shade, 255))
                        else:
                            for _ in range(num_dots): x_rand,y_rand=random.randint(0,15),random.randint(0,15); shade_offset=random.randint(-20,20); new_color=(max(0,min(255,base_color[0]+shade_offset)),max(0,min(255,base_color[1]+shade_offset)),max(0,min(255,base_color[2]+shade_offset)),255); draw.point((x_rand,y_rand),fill=new_color)
                    if texture_filename_mapped == "crafting_table_top":
                        draw.rectangle([(2,2),(6,6)], fill=(150,110,70,255))
                        draw.rectangle([(10,2),(14,6)], fill=(150,110,70,255))
                    elif texture_filename_mapped == "crafting_table_front":
                        draw.rectangle([(2,8),(6,12)], fill=(130,90,50,255))
                    
                    os.makedirs(os.path.dirname(full_path),exist_ok=True); img_pil.save(full_path)
                    image=pyglet.image.load(full_path); texture=image.get_texture(); gl.glBindTexture(texture.target,texture.id)
                    gl.glTexParameteri(texture.target,gl.GL_TEXTURE_MIN_FILTER,gl.GL_NEAREST); gl.glTexParameteri(texture.target,gl.GL_TEXTURE_MAG_FILTER,gl.GL_NEAREST)
                    if "leaves" in texture_filename_mapped: gl.glTexParameteri(texture.target,gl.GL_TEXTURE_WRAP_S,gl.GL_CLAMP_TO_EDGE); gl.glTexParameteri(texture.target,gl.GL_TEXTURE_WRAP_T,gl.GL_CLAMP_TO_EDGE)
                    gl.glBindTexture(texture.target,0); self.textures[texture_key_to_store]=texture; self.texture_groups[texture_key_to_store]=pyglet.graphics.TextureGroup(texture)
                except ImportError: logging.warning(f"Pillow (PIL) not installed. Cannot create dummy texture for {full_path}.")
                except Exception as e_dummy: logging.error(f"Error creating dummy texture {full_path}: {e_dummy}", exc_info=True)
        self.break_texture_groups = []
        for i in range(10):
            fp = os.path.join(self.texture_base_path, f"destroy_stage_{i}.png")
            if os.path.exists(fp):
                try:
                    img=pyglet.image.load(fp); tex=img.get_texture(); gl.glBindTexture(tex.target,tex.id)
                    gl.glTexParameteri(tex.target,gl.GL_TEXTURE_MIN_FILTER,gl.GL_NEAREST); gl.glTexParameteri(tex.target,gl.GL_TEXTURE_MAG_FILTER,gl.GL_NEAREST)
                    gl.glTexParameteri(tex.target,gl.GL_TEXTURE_WRAP_S,gl.GL_CLAMP_TO_EDGE); gl.glTexParameteri(tex.target,gl.GL_TEXTURE_WRAP_T,gl.GL_CLAMP_TO_EDGE)
                    gl.glBindTexture(tex.target,0); self.break_texture_groups.append(pyglet.graphics.TextureGroup(tex))
                except Exception as e_break: logging.error(f"Error loading break texture {fp}: {e_break}", exc_info=True); self.break_texture_groups.append(None)
            else: logging.warning(f"Break texture {fp} not found."); self.break_texture_groups.append(None)

    def rebuild_world_geometry(self):
        if not self.chunk_dirty: return
        if not self.world: self.chunk_dirty = False; return
        self.world_batch = pyglet.graphics.Batch(); render_distance_blocks = 32 
        px_floor,py_floor,pz_floor = map(math.floor, self.position)
        non_solid_blocks = {"oak_leaves", "birch_leaves"}
        
        # 定義需要隨機旋轉材質的方塊類型
        rotatable_blocks = {
            "grass_block", "dirt", "sand", "stone", "oak_leaves", "birch_leaves", 
            "gravel", "coal_ore", "iron_ore", "gold_ore", "diamond_ore", "lapis_ore"
        }

        for (x,y,z), block_type_in_world in self.world.items():
            if not (abs(x-px_floor)<render_distance_blocks and \
                    abs(y-py_floor)<render_distance_blocks+20 and \
                    abs(z-pz_floor)<render_distance_blocks): 
                continue
            
            is_transparent_block = (block_type_in_world in non_solid_blocks) 

            for face_index_standard, (dx_normal,dy_normal,dz_normal) in enumerate([(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]):
                neighbor_x,neighbor_y,neighbor_z = x+dx_normal,y+dy_normal,z+dz_normal
                neighbor_block_type = self.world.get((neighbor_x,neighbor_y,neighbor_z))
                
                should_draw_face = False
                if not neighbor_block_type: 
                    should_draw_face = True
                elif is_transparent_block and (neighbor_block_type != block_type_in_world and neighbor_block_type is not None):
                    should_draw_face = True
                elif not is_transparent_block and (neighbor_block_type in non_solid_blocks): 
                    should_draw_face = True

                if should_draw_face:
                    texture_key_for_face = None
                    if block_type_in_world=="grass_block":
                        if face_index_standard==2: texture_key_for_face="grass_block_top"      
                        elif face_index_standard==3: texture_key_for_face="grass_block_bottom"  
                        else: texture_key_for_face="grass_block_side"                         
                    elif block_type_in_world=="oak_log":
                        if face_index_standard==2 or face_index_standard==3: texture_key_for_face="oak_log_top"
                        else: texture_key_for_face="oak_log_side"
                    elif block_type_in_world=="birch_log":
                        if face_index_standard==2 or face_index_standard==3: texture_key_for_face="birch_log_top"
                        else: texture_key_for_face="birch_log_side"
                    elif block_type_in_world == "crafting_table":
                        if face_index_standard == 2: texture_key_for_face = "crafting_table_top"
                        elif face_index_standard == 3: texture_key_for_face = "oak_planks"
                        elif face_index_standard == 4: texture_key_for_face = "crafting_table_front"
                        else: texture_key_for_face = "crafting_table_side"
                    elif block_type_in_world in non_solid_blocks: 
                        texture_key_for_face=block_type_in_world
                    elif block_type_in_world in self.texture_map: 
                        texture_key_for_face=block_type_in_world
                    else: 
                        texture_key_for_face="stone" 
                    
                    texture_group_for_face = self.texture_groups.get(texture_key_for_face, self.texture_groups.get("stone"))
                    
                    # 計算隨機旋轉
                    rotation = 0
                    should_rotate = False
                    
                    # 草地只有頂部會旋轉，樹葉和其他自然方塊全旋轉
                    if block_type_in_world == "grass_block":
                        if face_index_standard == 2: # Top face
                            should_rotate = True
                    elif block_type_in_world in rotatable_blocks:
                        should_rotate = True
                    
                    if should_rotate:
                        # 根據座標計算一個固定的隨機數 (Hash)
                        # 使用位元運算可以加快速度
                        # (x * 質數1 + y * 質數2 + z * 質數3)
                        # 這樣同一個位置的方塊旋轉角度永遠固定
                        h = int(x * 521 + y * 97 + z * 643)
                        rotation = h % 4

                    if texture_group_for_face:
                        v,tc = self.get_block_face_vertices(x,y,z,face_index_standard,scale=1.0,center_offset=(0,0,0), rotation=rotation)
                        self.world_batch.add(4,gl.GL_QUADS,texture_group_for_face,('v3f/static',v),('t2f/static',tc))
        self.chunk_dirty = False

    def generate_tree(self, xt, ys, zt, tree_type="oak"):
        non_solid_blocks = {"oak_leaves", "birch_leaves"}
        log_type = f"{tree_type}_log"
        leaves_type = f"{tree_type}_leaves"
        
        can_grow=True
        for i in range(-1,2): 
            for j in range(-1,2):
                if i==0 and j==0: continue 
                check_pos_ground=(xt+i,ys-1,zt+j)
                block_on_ground=self.world.get(check_pos_ground)
                if block_on_ground and block_on_ground not in ["grass_block", "dirt"] and block_on_ground not in non_solid_blocks:
                    can_grow=False; break
                for k_up in range(5): 
                    check_pos_air=(xt+i,ys+k_up,zt+j)
                    block_in_air=self.world.get(check_pos_air)
                    if block_in_air and block_in_air not in non_solid_blocks: 
                        can_grow=False; break
                if not can_grow: break
            if not can_grow: break
        
        if not (self.world.get((xt,ys-1,zt)) in ["grass_block","dirt"]): 
            can_grow=False
        
        if not can_grow: return False

        trunk_height=random.randint(4,6); placed_logs=[]
        for i in range(trunk_height):
            log_pos=(xt,ys+i,zt)
            if self.world.get(log_pos) and self.world.get(log_pos) not in [None] and self.world.get(log_pos) not in non_solid_blocks:
                for plog_pos in placed_logs: self.world.pop(plog_pos,None) 
                return False
            self.world[log_pos]=log_type; placed_logs.append(log_pos)

        leaf_y_base=ys+trunk_height-2 
        leaf_height_layers=random.randint(3,4) 
        for leaf_y_offset in range(leaf_height_layers):
            current_y=leaf_y_base+leaf_y_offset
            radius=1 if (leaf_y_offset==leaf_height_layers-1 and leaf_height_layers>1) else 2 
            if leaf_height_layers==1: radius=1 

            for leaf_x_offset in range(-radius,radius+1):
                for leaf_z_offset in range(-radius,radius+1):
                    if leaf_x_offset==0 and leaf_z_offset==0 and current_y < ys + trunk_height: continue
                    if radius==2 and abs(leaf_x_offset)==2 and abs(leaf_z_offset)==2 and random.random()<0.5: continue
                    if radius==2 and (abs(leaf_x_offset)==2 or abs(leaf_z_offset)==2) and \
                       (abs(leaf_x_offset)!=abs(leaf_z_offset)) and random.random()<0.2: continue

                    leaf_pos=(xt+leaf_x_offset,current_y,zt+leaf_z_offset)
                    existing_block_at_leaf_pos=self.world.get(leaf_pos)
                    if not existing_block_at_leaf_pos or existing_block_at_leaf_pos in non_solid_blocks:
                        self.world[leaf_pos]=leaves_type
        return True

    def generate_chunk(self, chunk_x, chunk_z):
        base_y_level = 8
        ores_to_generate = [
            ("coal_ore", 0, base_y_level - 1, 80), ("iron_ore", 2, base_y_level - 3, 50),
            ("gold_ore", 4, base_y_level - 5, 15), ("lapis_ore", 4, base_y_level - 5, 10),
            ("diamond_ore", 5, base_y_level - 6, 5)
        ]
        
        start_x, start_z = chunk_x * self.chunk_size, chunk_z * self.chunk_size
        
        for dx in range(self.chunk_size):
            for dz in range(self.chunk_size):
                x_coord, z_coord = start_x + dx, start_z + dz
                self.world[(x_coord, 0, z_coord)] = "stone"
                for y_offset in range(1, base_y_level - 4): self.world[(x_coord, y_offset, z_coord)] = "stone"
                for y_offset in range(base_y_level - 4, base_y_level): self.world[(x_coord, y_offset, z_coord)] = "dirt"
                self.world[(x_coord, base_y_level, z_coord)] = "grass_block"

                for y_ore_check in range(1, base_y_level - 1):
                    if self.world.get((x_coord, y_ore_check, z_coord)) == "stone":
                        for ore_type, min_d, max_d, rarity in ores_to_generate:
                            if min_d <= y_ore_check <= max_d and random.randint(1, 1000) <= rarity:
                                self.world[(x_coord, y_ore_check, z_coord)] = ore_type
                                break
        
        if random.random() < 0.15: 
            for _ in range(random.randint(1, 3)):
                x_tree, z_tree = start_x + random.randint(2, self.chunk_size-3), start_z + random.randint(2, self.chunk_size-3)
                if self.world.get((x_tree, base_y_level, z_tree)) == "grass_block":
                    tree_type = "birch" if random.random() < 0.3 else "oak" 
                    self.generate_tree(x_tree, base_y_level + 1, z_tree, tree_type=tree_type)

        logging.info(f"Generated chunk at ({chunk_x}, {chunk_z})")

    def _manage_world_chunks(self):
        player_chunk_x = math.floor(self.position[0] / self.chunk_size)
        player_chunk_z = math.floor(self.position[2] / self.chunk_size)
        
        new_chunks_generated = False
        for cx in range(player_chunk_x - self.chunk_load_distance, player_chunk_x + self.chunk_load_distance + 1):
            for cz in range(player_chunk_z - self.chunk_load_distance, player_chunk_z + self.chunk_load_distance + 1):
                if (cx, cz) not in self.generated_chunks:
                    self.generate_chunk(cx, cz)
                    self.generated_chunks.add((cx, cz))
                    new_chunks_generated = True
        
        if new_chunks_generated:
            self.chunk_dirty = True


    def load_world(self):
        self.init_world_file()
        world_file_path = os.path.join(MAIN_SCRIPT_DIR, "worlds", "world.json")
        try:
            with open(world_file_path, "r", encoding='utf-8') as f: content = f.read()
            data = json.loads(content) if content.strip() else {}
            
            if isinstance(data, dict):
                self.world = {tuple(map(int, k.split(','))): v for k, v in data.items()}
                if self.world:
                    for x, y, z in self.world.keys():
                        self.generated_chunks.add((math.floor(x / self.chunk_size), math.floor(z / self.chunk_size)))
                    logging.info(f"World data loaded. {len(self.world)} blocks, {len(self.generated_chunks)} chunks.")
            else: logging.warning(f"World data format error. Starting fresh.")
        except (json.JSONDecodeError, FileNotFoundError, Exception) as e:
            logging.error(f"Error reading world file {world_file_path}: {e}. Starting fresh.", exc_info=True)
        self.chunk_dirty = True

    def init_world_file(self):
        path=os.path.join(MAIN_SCRIPT_DIR,"worlds","world.json"); os.makedirs(os.path.dirname(path),exist_ok=True)
        if not os.path.exists(path) or os.path.getsize(path)==0:
            try:
                with open(path,"w",encoding='utf-8') as f: json.dump({},f); logging.info(f"Initialized empty world file at {path}")
            except IOError as e: logging.error(f"Error initializing world file {path}: {e}", exc_info=True)

    def save_game(self):
        world_file_path=os.path.join(MAIN_SCRIPT_DIR,"worlds","world.json"); player_data_file_path=os.path.join(MAIN_SCRIPT_DIR,"playerdata","player.json")
        os.makedirs(os.path.dirname(world_file_path),exist_ok=True); os.makedirs(os.path.dirname(player_data_file_path),exist_ok=True)
        try:
            world_serializable={f"{k[0]},{k[1]},{k[2]}":v for k,v in self.world.items()}
            with open(world_file_path,"w",encoding='utf-8') as f: json.dump(world_serializable,f,indent=2,ensure_ascii=False)
            
            self._return_held_and_crafting_items()

            player_data={
                "player_id": self.player_id,
                "mode": self.mode, 
                "position": [round(p, 2) for p in self.position],
                "rotation": [round(r, 2) for r in self.rotation],
                "hotbar": self.hotbar,
                "main_inventory": self.main_inventory,
                "inventory_crafting_grid": self.inventory_crafting_grid,
                "crafting_table_grid": self.crafting_table_grid,
                "current_hotbar_index": self.current_hotbar_index
            }
            with open(player_data_file_path,"w",encoding='utf-8') as f: json.dump(player_data,f,indent=2,ensure_ascii=False)
            logging.info(f"Game saved. World ({len(world_serializable)} blocks) to {world_file_path}. Player data to {player_data_file_path}")
        except Exception as e: logging.error(f"儲存遊戲失敗:{e}", exc_info=True)


    def rebuild_breaking_effect(self):
        self.breaking_effect_batch=pyglet.graphics.Batch()
        if self.breaking_block_pos and self.break_texture_groups and 0<=self.breaking_block_stage<len(self.break_texture_groups):
            texture_group=self.break_texture_groups[self.breaking_block_stage]
            if texture_group:
                x,y,z = self.breaking_block_pos
                for face_idx in range(6): 
                    v,tc=self.get_block_face_vertices(x-0.001,y-0.001,z-0.001,face_idx,scale=1.002, rotation=0) 
                    self.breaking_effect_batch.add(4,gl.GL_QUADS,texture_group,('v3f/static',v),('t2f/static',tc))

    def draw_breaking_effect(self):
        if self.breaking_block_pos and self.breaking_effect_batch:
            gl.glEnable(gl.GL_BLEND); gl.glBlendFunc(gl.GL_SRC_ALPHA,gl.GL_ONE_MINUS_SRC_ALPHA)
            self.breaking_effect_batch.draw()
            gl.glDisable(gl.GL_BLEND)

    def check_collision_bbox(self, pos_x, pos_y, pos_z):
        player_width, non_solid_blocks = 0.6, {"oak_leaves", "birch_leaves"}
        min_x,max_x = pos_x - player_width/2, pos_x + player_width/2
        min_y,max_y = pos_y, pos_y + self.player_height 
        min_z,max_z = pos_z - player_width/2, pos_z + player_width/2

        for ix in range(math.floor(min_x),math.ceil(max_x)):
            for iy in range(math.floor(min_y),math.ceil(max_y)):
                for iz in range(math.floor(min_z),math.ceil(max_z)):
                    block_type=self.world.get((ix,iy,iz))
                    if block_type and block_type not in non_solid_blocks:
                        block_min_x,block_max_x=ix,ix+1
                        block_min_y,block_max_y=iy,iy+1
                        block_min_z,block_max_z=iz,iz+1
                        if (min_x<block_max_x and max_x>block_min_x and \
                            min_y<block_max_y and max_y>block_min_y and \
                            min_z<block_max_z and max_z>block_min_z):
                            return True 
        return False 

    def get_selected_block_type(self): return self.selected_block

    def get_target_block(self, max_distance=8):
        eye_y_offset=self.player_height*0.85 
        if self.is_sneaking and self.mode=="survival": 
            eye_y_offset-=self.sneak_camera_offset_y
        
        eye_x,eye_y,eye_z = self.position[0], self.position[1]+eye_y_offset, self.position[2]
        
        yaw,pitch = self.rotation[0], self.rotation[1]
        rad_yaw,rad_pitch = math.radians(yaw), math.radians(pitch)
        
        dx_view, dy_view, dz_view = math.cos(rad_pitch) * -math.sin(rad_yaw), math.sin(rad_pitch), math.cos(rad_pitch) * -math.cos(rad_yaw)

        step_size, last_air_block_coord = 0.05, None

        for i in range(int(max_distance/step_size)+1): 
            current_x, current_y, current_z = eye_x + dx_view*i*step_size, eye_y + dy_view*i*step_size, eye_z + dz_view*i*step_size
            block_pos_tuple=(math.floor(current_x),math.floor(current_y),math.floor(current_z))

            if block_pos_tuple in self.world: 
                face_hit=[0,0,0] 
                if last_air_block_coord:
                    diff_x, diff_y, diff_z = last_air_block_coord[0]-block_pos_tuple[0], last_air_block_coord[1]-block_pos_tuple[1], last_air_block_coord[2]-block_pos_tuple[2]
                    if abs(diff_x) > abs(diff_y) and abs(diff_x) > abs(diff_z): face_hit[0]=int(math.copysign(1, diff_x))
                    elif abs(diff_y) > abs(diff_z): face_hit[1]=int(math.copysign(1, diff_y))
                    else: face_hit[2]=int(math.copysign(1, diff_z))
                else: 
                    frac_x, frac_y, frac_z = current_x - block_pos_tuple[0] - 0.5, current_y - block_pos_tuple[1] - 0.5, current_z - block_pos_tuple[2] - 0.5
                    abs_fx,abs_fy,abs_fz=abs(frac_x),abs(frac_y),abs(frac_z)
                    if abs_fx>abs_fy and abs_fx>abs_fz: face_hit[0]=1 if frac_x<0 else -1
                    elif abs_fy>abs_fz: face_hit[1]=1 if frac_y<0 else -1
                    else: face_hit[2]=1 if frac_z<0 else -1
                
                if face_hit==[0,0,0]: face_hit=[0,1,0] 
                return block_pos_tuple,tuple(face_hit)
            
            last_air_block_coord=block_pos_tuple 
        return None 

    def sort_main_inventory(self):
        if not self.show_inventory: return

        logging.info("Sorting and consolidating main inventory...")
        item_counts = {}

        for slot in self.main_inventory:
            if slot:
                item_id = slot['id']
                count = slot['count']
                item_counts[item_id] = item_counts.get(item_id, 0) + count
        
        self.main_inventory = [None] * len(self.main_inventory)

        sorted_ids = sorted(item_counts.keys())
        
        current_slot_index = 0
        for item_id in sorted_ids:
            total_count = item_counts[item_id]
            while total_count > 0:
                if current_slot_index >= len(self.main_inventory):
                    logging.error("排序時發生錯誤：物品太多放不回物品欄！")
                    return

                count_to_place = min(total_count, self.max_stack_size)
                self.main_inventory[current_slot_index] = {'id': item_id, 'count': count_to_place}
                
                total_count -= count_to_place
                current_slot_index += 1

        logging.info("Inventory sorted and consolidated.")
        self._refresh_inventory_display_layout()

    def parse_command(self, command_text):
        parts = command_text.strip().lower().split()
        if not parts: return

        cmd = parts[0]
        args = parts[1:]
        error_color = (255, 100, 100, 255)
        player_id_lower = self.player_id.lower()

        if cmd == "/tp":
            coords_args = []
            target_valid = False

            if len(args) == 4:
                if args[0] == '@s' or args[0] == player_id_lower:
                    coords_args = args[1:]
                    target_valid = True
            elif len(args) == 3:
                coords_args = args
                target_valid = True

            if target_valid and len(coords_args) == 3:
                try:
                    final_coords = []
                    for i, coord_str in enumerate(coords_args):
                        base_val = self.position[i]
                        if coord_str.startswith('~'):
                            offset_str = coord_str[1:]
                            if not offset_str:
                                final_coords.append(base_val)
                            else:
                                offset = float(offset_str)
                                final_coords.append(base_val + offset)
                        else:
                            final_coords.append(float(coord_str))
                    
                    x, y, z = final_coords
                    self.position = [x, y, z]
                    self.velocity = [0.0, 0.0, 0.0]
                    self.on_ground = False
                    self.chunk_dirty = True
                    self.add_chat_feedback(f"已將 {self.player_id} 傳送至 {x:.1f}, {y:.1f}, {z:.1f}")
                    self.ensure_player_on_surface()
                except ValueError:
                    self.add_chat_feedback("無效的 /tp 座標。請使用數字或 ~[offset] 格式。", color=error_color)
            else:
                self.add_chat_feedback("無效的 /tp 指令。用法: /tp [<target>] <x> <y> <z>", color=error_color)
        
        elif cmd == "/gamemode":
            target_valid = False
            if len(args) == 1:
                target_valid = True
            elif len(args) == 2 and (args[1] == '@s' or args[1] == player_id_lower):
                target_valid = True

            if target_valid:
                new_mode = args[0]
                if new_mode in ["survival", "creative"]:
                    self.mode = new_mode
                    self.add_chat_feedback(f"為 {self.player_id} 將遊戲模式設為 {self.mode.capitalize()}")
                    if self.mode == "creative":
                        self.velocity = [0, 0, 0]
                        self.is_sprinting = False; self.is_sneaking = False; self.is_flying_creative = False
                        self.on_ground = False
                    else:
                        self.is_sprinting = False; self.is_sneaking = False; self.is_flying_creative = False
                        self.on_ground = False
                    self.chunk_dirty = True
                else:
                    self.add_chat_feedback(f"無效的遊戲模式 '{new_mode}'。請使用 'survival' 或 'creative'。", color=error_color)
            else:
                self.add_chat_feedback("無效的 /gamemode 指令。用法: /gamemode <mode> [<target>]", color=error_color)
        
        elif cmd == "/give":
            if len(args) >= 2 and (args[0] == '@s' or args[0] == player_id_lower):
                item_id_raw = args[1]
                item_id = item_id_raw.replace("minecraft:", "")

                count = 1
                if len(args) > 2:
                    try:
                        requested_count = int(args[2])
                        count = max(1, min(requested_count, 32768))
                        if requested_count > 32768:
                            self.add_chat_feedback(f"請求的數量 {requested_count} 超過上限 32768，將給予 32768 個。", color=(255, 255, 100, 255))
                        elif requested_count < 1:
                            self.add_chat_feedback(f"請求的數量 {requested_count} 小於下限 1，將給予 1 個。", color=(255, 255, 100, 255))
                    except ValueError:
                        self.add_chat_feedback(f"無效的數量 '{args[2]}'。必須是數字。將給予 1 個。", color=error_color)
                
                if item_id in self.valid_give_items:
                    self.add_item_to_inventory(item_id, count)
                    self.add_chat_feedback(f"給予 {self.player_id} {count} 個 '{item_id}'")
                else:
                    self.add_chat_feedback(f"未知的物品 ID: '{item_id}'", color=error_color)
            else:
                self.add_chat_feedback("用法: /give <target> <item_id> [數量]", color=error_color)
        
        elif cmd == "/clear":
            target_valid = False
            if len(args) == 0:
                target_valid = True
            elif len(args) == 1 and (args[0] == '@s' or args[0] == player_id_lower):
                target_valid = True

            if target_valid:
                self.hotbar = [None] * self.hotbar_size
                self.main_inventory = [None] * (self.inventory_cols * self.inventory_rows)
                self.update_selected_block_from_hotbar()
                self.add_chat_feedback(f"已清除玩家 {self.player_id} 的物品欄。")
            else:
                self.add_chat_feedback(f"無效的目標選擇器 '{args[0]}'", color=error_color)

        else:
            self.add_chat_feedback(f"未知或無效的指令: '{command_text.split()[0]}'", color=error_color)

    def _return_held_and_crafting_items(self):
        if self.inventory_selected_item_info:
            held_item = self.inventory_selected_item_info
            self.add_item_to_inventory(held_item['id'], held_item['count'])
            self.inventory_selected_item_info = None

        for i, item_slot in enumerate(self.inventory_crafting_grid):
            if item_slot:
                self.add_item_to_inventory(item_slot['id'], item_slot['count'])
                self.inventory_crafting_grid[i] = None
        
        for i, item_slot in enumerate(self.crafting_table_grid):
            if item_slot:
                self.add_item_to_inventory(item_slot['id'], item_slot['count'])
                self.crafting_table_grid[i] = None
        
        self.check_crafting_recipe('inventory')
        self.check_crafting_recipe('crafting_table')

    def on_text(self, text):
        if self.ignore_next_text:
            self.ignore_next_text = False
            return

        if self.chat_active:
            if text and text not in ('\r', '\n', '\t'): # 防止 Tab 鍵輸入字元
                self.chat_input += text
                self.chat_label.text = self.chat_input + "_"
                # 重置 Tab 補全狀態
                self.tab_matches = []
                self.tab_index = 0
    
    def on_key_press(self, symbol, modifiers):
        # 切換人稱視角（三段式）
        if symbol == self.keybindings.get("toggle_third_person"):
            if self.camera_mode == "first":
                self.camera_mode = "third_back"
            elif self.camera_mode == "third_back":
                self.camera_mode = "third_front"
            else:
                self.camera_mode = "first"
            logging.info(f"切換視角: {self.camera_mode}")
            return pyglet.event.EVENT_HANDLED
        if self.show_keybinding_menu and self.key_to_rebind:
            if symbol == key.ESCAPE:
                self.key_to_rebind = None
                return pyglet.event.EVENT_HANDLED

            key_name = self._get_binding_name(symbol)
            action_name_zh = {
                "forward": "前進", "backward": "後退", "left": "向左", "right": "向右",
                "jump": "跳躍", "sprint": "奔跑", "sneak": "潛行",
                "inventory": "物品欄",
                "attack": "攻擊/破壞", "place": "使用/放置", "pick_block": "選取方塊",
                "chat": "開啟聊天", "command": "開啟指令",
            }.get(self.key_to_rebind, self.key_to_rebind)
            logging.info(f"按鍵綁定已更新: {action_name_zh} -> {key_name} (code: {symbol})")
            self.keybindings[self.key_to_rebind] = symbol
            self.key_to_rebind = None
            self.check_key_conflicts()
            self.save_keybindings()
            return pyglet.event.EVENT_HANDLED

        if self.chat_active:
            if symbol == key.TAB:
                # [Tab 自動補全邏輯]
                if self.tab_matches:
                    # 如果已經在補全模式中，切換下一個
                    self.tab_index = (self.tab_index + 1) % len(self.tab_matches)
                    new_word = self.tab_matches[self.tab_index]
                    self.chat_input = self.tab_prefix + new_word
                    self.chat_label.text = self.chat_input + "_"
                    return pyglet.event.EVENT_HANDLED

                # 開始新的補全搜尋
                parts = self.chat_input.split(' ')
                if len(parts) < 2: return pyglet.event.EVENT_HANDLED 
                
                if parts[0] != "/give": return pyglet.event.EVENT_HANDLED
                
                # 判斷當前輸入狀態
                # 1. "/give " -> 列出所有物品
                # 2. "/give oa" -> 搜尋 oa 開頭
                # 3. "/give @s oa" -> 搜尋 oa 開頭
                
                last_word = parts[-1]
                if self.chat_input.endswith(' '):
                    query = ""
                    self.tab_prefix = self.chat_input
                else:
                    query = last_word
                    self.tab_prefix = self.chat_input[:-len(query)]
                
                matches = [item for item in self.valid_give_items if item.startswith(query)]
                
                if matches:
                    self.tab_matches = sorted(matches)
                    self.tab_index = 0
                    self.chat_input = self.tab_prefix + self.tab_matches[0]
                    self.chat_label.text = self.chat_input + "_"

                return pyglet.event.EVENT_HANDLED

            elif symbol == key.ENTER or symbol == key.RETURN:
                if self.chat_input:
                    if self.chat_input.startswith('/'):
                        self.parse_command(self.chat_input)
                    else:
                        chat_message = f"<{self.player_id}> {self.chat_input}"
                        self.add_chat_feedback(chat_message)
                
                self.chat_active = False
                self.chat_input = ""
                self.tab_matches = [] # 重置
                self._update_mouse_exclusivity()
                self.chat_label.text = ""
            elif symbol == key.BACKSPACE:
                self.chat_input = self.chat_input[:-1]
                self.chat_label.text = self.chat_input + "_"
                self.tab_matches = [] # 重置
            elif symbol == key.ESCAPE:
                self.chat_active = False
                self.chat_input = ""
                self.tab_matches = [] # 重置
                self._update_mouse_exclusivity()
                self.chat_label.text = ""
            return pyglet.event.EVENT_HANDLED

        current_time = time.time()
        ui_interaction_key_pressed = False 

        if symbol == pyglet.window.key.F11:
            self.window.set_fullscreen(not self.window.fullscreen)
            logging.info(f"Fullscreen toggled to: {self.window.fullscreen}")
            self.hp_label.y = self.window.height - 30
            self.hunger_label.y = self.window.height - 60
            return pyglet.event.EVENT_HANDLED
        
        is_chat_key = symbol == self.keybindings.get('chat')
        is_command_key = symbol == self.keybindings.get('command')
        if not is_command_key and self.keybindings.get('command') == key.RETURN and symbol == key.ENTER:
            is_command_key = True

        if not self.show_inventory and not self.pause_menu and not self.show_crafting_table_ui and not self.chat_active:
            if is_chat_key and 'chat' not in self.conflicting_actions:
                self.chat_active = True
                self.chat_input = ""
                self.chat_label.text = self.chat_input + "_"
                self._update_mouse_exclusivity()
                self.ignore_next_text = True 
                return pyglet.event.EVENT_HANDLED
            if is_command_key and 'command' not in self.conflicting_actions:
                self.chat_active = True
                self.chat_input = "/"
                self.chat_label.text = self.chat_input + "_"
                self._update_mouse_exclusivity()
                self.ignore_next_text = True 
                return pyglet.event.EVENT_HANDLED

        if symbol == pyglet.window.key.ESCAPE:
            ui_interaction_key_pressed = True
            if self.show_keybinding_menu:
                self.show_keybinding_menu = False
                self.pause_menu = True
                self.key_to_rebind = None
            elif self.show_inventory or self.show_crafting_table_ui:
                self.show_inventory = False
                self.show_crafting_table_ui = False
                self._return_held_and_crafting_items()
            elif self.pause_menu: self.pause_menu = False
            else: self.pause_menu = True
        
        elif symbol == self.keybindings.get('inventory') and 'inventory' not in self.conflicting_actions:
            if not self.pause_menu and not self.show_keybinding_menu:
                ui_interaction_key_pressed = True
                if self.show_crafting_table_ui:
                    self.show_crafting_table_ui = False
                    self._return_held_and_crafting_items()
                else:
                    self.show_inventory = not self.show_inventory
                    if not self.show_inventory:
                        self._return_held_and_crafting_items()
                logging.info(f"Inventory key pressed. show_inventory: {self.show_inventory}, show_crafting_table_ui: {self.show_crafting_table_ui}")

        if ui_interaction_key_pressed:
            self._update_mouse_exclusivity()
            return pyglet.event.EVENT_HANDLED
        
        if symbol == pyglet.window.key.R:
            if self.show_inventory and not self.pause_menu:
                self.sort_main_inventory()
                return pyglet.event.EVENT_HANDLED

        if self.pause_menu or self.show_inventory or self.show_crafting_table_ui:
            return pyglet.event.EVENT_HANDLED 
        
        if symbol == self.keybindings.get('sprint') and 'sprint' not in self.conflicting_actions:
            if not self.is_sneaking:
                self.is_sprinting = True
            
        elif symbol == self.keybindings.get('jump') and 'jump' not in self.conflicting_actions:
            if self.mode == "survival" and self.on_ground:
                if current_time - self.last_jump_time > self.jump_cooldown:
                    self.velocity[1] = self.jump_force
                    self.on_ground = False 
                    self.last_jump_time = current_time
            elif self.mode == "creative":
                if not self.is_flying_creative and self.on_ground: 
                    if current_time - self.last_jump_time > self.jump_cooldown:
                         self.velocity[1] = self.jump_force
                         self.on_ground = False
                         self.last_jump_time = current_time
                elif current_time - self.last_space_press_time < self.double_tap_time: 
                    self.is_flying_creative = not self.is_flying_creative
                    logging.info(f"Creative flying toggled: {self.is_flying_creative}")
                    if not self.is_flying_creative: 
                        self.on_ground = False 
                        if self.check_collision_bbox(self.position[0], self.position[1] - 0.01, self.position[2]):
                            self.on_ground = True
                            self.velocity[1] = 0 
                self.last_space_press_time = current_time
        
        elif pyglet.window.key._1 <= symbol <= pyglet.window.key._9:
            self.current_hotbar_index = symbol - pyglet.window.key._1
            self.update_selected_block_from_hotbar()

    def on_key_release(self, symbol, modifiers):
        if self.show_inventory or self.pause_menu or self.show_crafting_table_ui: return
        if symbol == self.keybindings.get('sprint'): 
            self.is_sprinting = False

    def on_mouse_motion(self, x, y, dx, dy):
        self.mouse_x,self.mouse_y = x,y
        if self.window._exclusive_mouse:
            sensitivity = 0.15
            self.rotation[0]-=dx*sensitivity
            self.rotation[1]+=dy*sensitivity
            self.rotation[1]=max(-89.9,min(89.9,self.rotation[1]))

    def on_mouse_scroll(self, x, y, scroll_x, scroll_y):
        if self.show_inventory or self.pause_menu or self.chat_active or self.show_crafting_table_ui or not self.hotbar: return
        if scroll_y > 0: self.current_hotbar_index = (self.current_hotbar_index - 1 + self.hotbar_size) % self.hotbar_size
        elif scroll_y < 0: self.current_hotbar_index = (self.current_hotbar_index + 1) % self.hotbar_size
        self.update_selected_block_from_hotbar()

    def on_mouse_release(self, x, y, button, modifiers):
        self.mouse_btn_state.discard(button) 

        if self.show_inventory or self.pause_menu or self.chat_active or self.show_crafting_table_ui or self.show_keybinding_menu: return 
        
        if button == self.keybindings.get('attack'):
            self.mouse_left_is_pressed = False
            if self.breaking_block_pos: 
                self.breaking_block_pos=None
                self.breaking_block_stage=0
                self.breaking_effect_batch=pyglet.graphics.Batch() 
        
        if button == self.keybindings.get('sprint'):
            self.is_sprinting = False

    def update(self, dt):
        if self.chat_feedback_messages:
            current_time = time.time()
            self.chat_feedback_messages = [msg for msg in self.chat_feedback_messages if msg['expiry'] > current_time]

        if self.pause_menu or self.show_keybinding_menu: return 
        if dt > 0.1: dt = 0.1

        self._update_tooltip()
        
        self._manage_world_chunks()

        old_player_chunk_x = math.floor(self.position[0] / self.chunk_size)
        old_player_chunk_z = math.floor(self.position[2] / self.chunk_size)

        if not self.chat_active and not self.show_inventory and not self.show_crafting_table_ui:
            dx_input, dz_input = 0.0, 0.0
            dy_input_creative_fly = 0.0
            current_speed = self.normal_move_speed

            self.is_sneaking = False
            if self.on_ground and not self.is_flying_creative:
                 if 'sneak' not in self.conflicting_actions:
                    self.is_sneaking = self.is_action_pressed('sneak')

            if not self.show_inventory: 
                if self.mode == "survival":
                    if self.is_sneaking: 
                        current_speed *= self.sneak_speed_multiplier
                        self.is_sprinting = False 
                    elif self.is_sprinting and self.on_ground and 'forward' not in self.conflicting_actions and self.is_action_pressed('forward'): 
                        current_speed *= self.sprint_speed_multiplier
                    elif self.is_sprinting and not (self.on_ground and 'forward' not in self.conflicting_actions and self.is_action_pressed('forward')):
                        self.is_sprinting = False 
                elif self.mode == "creative":
                    if self.is_sneaking and not self.is_flying_creative:
                         current_speed *= self.sneak_speed_multiplier
                         self.is_sprinting = False
                    else:
                         current_speed = self.fly_speed
                         if self.is_sprinting: current_speed *= self.sprint_speed_multiplier
                
                strafe_yaw_rad = math.radians(self.rotation[0])
                sin_yaw, cos_yaw = math.sin(strafe_yaw_rad), math.cos(strafe_yaw_rad)
                temp_dx, temp_dz = 0.0, 0.0
                if 'forward' not in self.conflicting_actions and self.is_action_pressed('forward'): temp_dx -= sin_yaw; temp_dz -= cos_yaw
                if 'backward' not in self.conflicting_actions and self.is_action_pressed('backward'): temp_dx += sin_yaw; temp_dz += cos_yaw
                if 'left' not in self.conflicting_actions and self.is_action_pressed('left'): temp_dx -= cos_yaw; temp_dz += sin_yaw
                if 'right' not in self.conflicting_actions and self.is_action_pressed('right'): temp_dx += cos_yaw; temp_dz -= sin_yaw
                
                move_len = math.sqrt(temp_dx**2 + temp_dz**2)
                if move_len > 0: 
                    dx_input = (temp_dx/move_len)*current_speed*dt
                    dz_input = (temp_dz/move_len)*current_speed*dt
                
                if self.mode == "creative" and self.is_flying_creative:
                    if 'jump' not in self.conflicting_actions and self.is_action_pressed('jump'): dy_input_creative_fly += current_speed * dt
                    if 'sneak' not in self.conflicting_actions and self.is_action_pressed('sneak'): 
                        dy_input_creative_fly -= current_speed * dt
            
            player_width = 0.6
            
            next_pos_x = self.position[0] + dx_input
            if self.is_sneaking and self.on_ground:
                check_x = next_pos_x + math.copysign(player_width / 2, dx_input) if dx_input != 0 else next_pos_x
                block_below_x_pos = (math.floor(check_x), math.floor(self.position[1] - 0.1), math.floor(self.position[2]))
                if block_below_x_pos not in self.world:
                    dx_input = 0
                    next_pos_x = self.position[0]
            
            if not self.check_collision_bbox(next_pos_x, self.position[1], self.position[2]):
                self.position[0] = next_pos_x
            
            next_pos_z = self.position[2] + dz_input
            if self.is_sneaking and self.on_ground:
                check_z = next_pos_z + math.copysign(player_width / 2, dz_input) if dz_input != 0 else next_pos_z
                block_below_z_pos = (math.floor(self.position[0]), math.floor(self.position[1] - 0.1), math.floor(check_z))
                if block_below_z_pos not in self.world:
                    dz_input = 0
                    next_pos_z = self.position[2]

            if not self.check_collision_bbox(self.position[0], self.position[1], next_pos_z):
                self.position[2] = next_pos_z


            if self.mode == "creative" and self.is_flying_creative:
                self.on_ground = False 
                self.velocity[1] = 0   
                
                next_pos_y_fly = self.position[1] + dy_input_creative_fly
                if not self.check_collision_bbox(self.position[0], next_pos_y_fly, self.position[2]):
                    self.position[1] = next_pos_y_fly
                else: 
                    if dy_input_creative_fly < 0: 
                        self.position[1] = math.floor(next_pos_y_fly) + 1.0 
                        if self.check_collision_bbox(self.position[0], self.position[1] - 0.01, self.position[2]):
                            self.is_flying_creative = False 
                            self.on_ground = True
                    elif dy_input_creative_fly > 0: 
                        self.position[1] = math.floor(next_pos_y_fly + self.player_height) - self.player_height - 0.01 
            else: 
                self.velocity[1] += self.gravity * dt
                self.velocity[1] = max(self.velocity[1], -50.0) 
                
                next_pos_y_normal = self.position[1] + self.velocity[1] * dt
                self.on_ground = False 

                if not self.check_collision_bbox(self.position[0], next_pos_y_normal, self.position[2]):
                    self.position[1] = next_pos_y_normal
                else: 
                    if self.velocity[1] <= 0: 
                        self.position[1] = math.floor(next_pos_y_normal) + 1.0 
                        self.on_ground = True
                        self.velocity[1] = 0 
                    elif self.velocity[1] > 0: 
                        self.position[1] = math.floor(next_pos_y_normal + self.player_height) - self.player_height - 0.01
                        self.velocity[1] = 0 

        if self.breaking_block_pos and not self.show_inventory and not self.pause_menu and not self.show_crafting_table_ui:
            block_type_at_breaking_pos = self.world.get(self.breaking_block_pos)
            if block_type_at_breaking_pos:
                required_time = self.break_time_map.get(block_type_at_breaking_pos, 3.0) 
                elapsed_time = time.time() - self.breaking_block_start_time
                
                current_target_info = self.get_target_block(max_distance=5) 
                if not self.mouse_left_is_pressed or \
                   not current_target_info or \
                   current_target_info[0] != self.breaking_block_pos or \
                   self.world.get(self.breaking_block_pos) != block_type_at_breaking_pos:
                    self.breaking_block_pos = None; self.breaking_block_stage = 0; self.rebuild_breaking_effect() 
                elif elapsed_time >= required_time: 
                    self.world.pop(self.breaking_block_pos)
                    self.trigger_arm_swing_animation()
                    if self.mode == "survival": 
                        self.add_item_to_inventory(block_type_at_breaking_pos, 1)
                        logging.info(f"Broke {block_type_at_breaking_pos}, added to inventory.")
                    self.chunk_dirty = True
                    self.breaking_block_pos = None; self.breaking_block_stage = 0; self.rebuild_breaking_effect() 
                    self.update_selected_block_from_hotbar() 
                else: 
                    self.breaking_block_stage = min(9, math.floor((elapsed_time / required_time) * 10))
                    self.rebuild_breaking_effect()
            else: 
                self.breaking_block_pos = None; self.breaking_block_stage = 0; self.rebuild_breaking_effect()
        elif self.breaking_block_pos: 
            self.breaking_block_pos = None; self.breaking_block_stage = 0; self.rebuild_breaking_effect()

        if self.mode == "survival" and self.position[1] < -60: 
            logging.warning("Player fell out of the world in survival mode. Resetting position.")
            self.position = [self.position[0], 30.0, self.position[2]] 
            self.velocity = [0,0,0]; self.on_ground = False
            self.ensure_player_on_surface() 
            self.chunk_dirty = True 
        
        new_player_chunk_x = math.floor(self.position[0] / self.chunk_size)
        new_player_chunk_z = math.floor(self.position[2] / self.chunk_size)
        if new_player_chunk_x != old_player_chunk_x or new_player_chunk_z != old_player_chunk_z:
            self.chunk_dirty = True
        
        sneak_status = " Sneaking" if self.is_sneaking else ""
        sprint_status = " Sprinting" if self.is_sprinting else ""
        fly_status = " Flying" if self.mode=="creative" and self.is_flying_creative else ""
        self.pos_label.text = (f"Pos:({self.position[0]:.1f},{self.position[1]:.1f},{self.position[2]:.1f}) R:({self.rotation[0]:.0f},{self.rotation[1]:.0f}) Ground:{self.on_ground} Mode:{self.mode}{sneak_status}{sprint_status}{fly_status} V_Y:{self.velocity[1]:.1f}")
        if self.mode == "survival": 
            self.hp_label.text = f"HP:{self.hp}/{self.max_hp}"
            self.hunger_label.text = f"Hunger:{self.hunger}/{self.max_hunger}"

    def get_camera_position(self):
        eye_y_offset = self.player_height * 0.85
        if self.is_sneaking and self.mode == "survival":
            eye_y_offset -= self.sneak_camera_offset_y
        
        player_eye_x = self.position[0]
        player_eye_y = self.position[1] + eye_y_offset
        player_eye_z = self.position[2]
        
        return (player_eye_x, player_eye_y, player_eye_z)

    def setup_3d(self):
        w,h=self.window.get_size()
        sky_color=(0.5,0.7,0.95,1.0)
        gl.glClearColor(*sky_color)
        gl.glEnable(gl.GL_TEXTURE_2D)
        gl.glEnable(gl.GL_FOG)
        gl.glFogi(gl.GL_FOG_MODE,gl.GL_LINEAR)
        gl.glFogfv(gl.GL_FOG_COLOR,(gl.GLfloat*4)(*sky_color))
        gl.glFogf(gl.GL_FOG_START,20.0)
        gl.glFogf(gl.GL_FOG_END,80.0)
        gl.glEnable(gl.GL_DEPTH_TEST)
        gl.glDisable(gl.GL_CULL_FACE)
        gl.glEnable(gl.GL_ALPHA_TEST)
        gl.glAlphaFunc(gl.GL_GREATER,0.5)
        gl.glViewport(0,0,w,h)
        gl.glMatrixMode(gl.GL_PROJECTION)
        gl.glLoadIdentity()
        gluPerspective(65,w/h if h>0 else 1,0.1,200)
        gl.glMatrixMode(gl.GL_MODELVIEW)
        gl.glLoadIdentity()

        gl.glRotatef(-self.rotation[1],1.0,0.0,0.0)
        gl.glRotatef(-self.rotation[0],0.0,1.0,0.0)

        cam_x, cam_y, cam_z = self.get_camera_position()
        gl.glTranslatef(-cam_x, -cam_y, -cam_z)

    def setup_2d(self):
        w,h=self.window.get_size(); gl.glDisable(gl.GL_DEPTH_TEST); gl.glDisable(gl.GL_CULL_FACE); gl.glDisable(gl.GL_FOG); gl.glDisable(gl.GL_ALPHA_TEST)
        gl.glEnable(gl.GL_BLEND); gl.glBlendFunc(gl.GL_SRC_ALPHA,gl.GL_ONE_MINUS_SRC_ALPHA)
        gl.glMatrixMode(gl.GL_PROJECTION); gl.glLoadIdentity(); gl.gluOrtho2D(0,w,0,h)
        gl.glMatrixMode(gl.GL_MODELVIEW); gl.glLoadIdentity()

    def _draw_text_with_shadow(self, text, x, y, font_size, color=(255,255,255,255), shadow_color=(60,60,60,255), anchor_x='right', anchor_y='bottom', bold=True):
        # Draw shadow
        pyglet.text.Label(text, font_size=font_size, x=x+1, y=y-1, anchor_x=anchor_x, anchor_y=anchor_y, color=shadow_color, bold=bold).draw()
        # Draw main text
        pyglet.text.Label(text, font_size=font_size, x=x, y=y, anchor_x=anchor_x, anchor_y=anchor_y, color=color, bold=bold).draw()

    def _draw_item_texture_in_slot(self, item_id, x, y, size):
        if not item_id: return
        
        texture_key = item_id
        if item_id == "grass_block": texture_key = "grass_block_top"
        elif item_id == "oak_log": texture_key = "oak_log_side"
        elif item_id == "birch_log": texture_key = "birch_log_side"
        elif item_id == "crafting_table": texture_key = "crafting_table_top"
        
        texture_group = self.texture_groups.get(texture_key)
        if not texture_group: return

        texture = texture_group.texture
        gl.glEnable(texture.target)
        gl.glBindTexture(texture.target, texture.id)
        
        inset = size * 0.1
        texture.blit(x + inset, y + inset, width=size - 2 * inset, height=size - 2 * inset)
        
        gl.glDisable(texture.target)

    def draw_inventory(self):
        batch = pyglet.graphics.Batch()
        scale = 2.0
        base_w, base_h = 176, 166
        total_width, total_height = base_w * scale, base_h * scale
        x_start = (self.window.width - total_width) / 2
        y_start = (self.window.height - total_height) / 2

        bg_color = (198, 198, 198, 255)
        batch.add(4, gl.GL_QUADS, None, ('v2f', (x_start, y_start, x_start + total_width, y_start, x_start + total_width, y_start + total_height, x_start, y_start + total_height)), ('c4B', bg_color * 4))
        slot_size = 18 * scale
        inv_base_x = x_start + (8 * scale)
        hotbar_y = y_start + (8 * scale)
        main_inv_y_start = hotbar_y + slot_size + (4 * scale)

        for i in range(self.hotbar_size):
            x = inv_base_x + i * slot_size
            self._draw_slot(batch, x, hotbar_y, slot_size)
        
        for row in range(self.inventory_rows):
            for col in range(self.inventory_cols):
                x = inv_base_x + col * slot_size
                y = main_inv_y_start + (2 - row) * slot_size
                self._draw_slot(batch, x, y, slot_size)
            
        # 裝備欄（頭、身、褲、鞋）
        armor_x = inv_base_x
        armor_y_start = y_start + total_height - (26 * scale)
        for i in range(4):
            y = armor_y_start - i * slot_size
            self._draw_slot(batch, armor_x, y, slot_size)

        # 合成格（2x2）
        craft_base_x = x_start + 88 * scale
        craft_base_y = y_start + total_height - (70 * scale)
        for i in range(4):
            row, col = divmod(i, 2)
            x = craft_base_x + col * slot_size
            y = craft_base_y + (1-row) * slot_size
            self._draw_slot(batch, x, y, slot_size)

        # 合成結果格與箭頭（保留箭頭與結果格，移除副手與綠色書）
        arrow_y_center = craft_base_y + slot_size / 2
        arrow_x = craft_base_x + (2 * slot_size) + (6 * scale)
        arrow_w, arrow_h = 22 * scale, 15 * scale
        shaft_h = 7 * scale; shaft_w = 15 * scale
        arrow_color_tuple = (139, 139, 139, 255) * 4
        shaft_y = arrow_y_center - shaft_h / 2
        batch.add(4, gl.GL_QUADS, None, ('v2f', (arrow_x, shaft_y, arrow_x + shaft_w, shaft_y, arrow_x + shaft_w, shaft_y + shaft_h, arrow_x, shaft_y + shaft_h)), ('c4B', arrow_color_tuple))
        batch.add(3, gl.GL_TRIANGLES, None, ('v2f', (arrow_x + shaft_w, arrow_y_center - arrow_h/2, arrow_x + shaft_w, arrow_y_center + arrow_h/2, arrow_x + arrow_w, arrow_y_center)), ('c4B', arrow_color_tuple[:3*4]))

        result_x = arrow_x + arrow_w + (6 * scale)
        result_y = arrow_y_center - (slot_size / 2)
        self._draw_slot(batch, result_x, result_y, slot_size)
        
        batch.draw()

        for i, item_slot in enumerate(self.hotbar):
            if item_slot:
                x = inv_base_x + i * slot_size
                self._draw_item_texture_in_slot(item_slot['id'], x, hotbar_y, slot_size)
                if item_slot['count'] > 1:
                    self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=hotbar_y+2)
        
        for i, item_slot in enumerate(self.main_inventory):
            if item_slot:
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = main_inv_y_start + (2-row) * slot_size
                self._draw_item_texture_in_slot(item_slot['id'], x, y, slot_size)
                if item_slot['count'] > 1:
                    self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=y+2)

        for i, item_slot in enumerate(self.inventory_crafting_grid):
            if item_slot:
                row, col = divmod(i, 2)
                x = craft_base_x + col * slot_size
                y = craft_base_y + (1-row) * slot_size
                self._draw_item_texture_in_slot(item_slot['id'], x, y, slot_size)
                if item_slot['count'] > 1:
                    self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=y+2)

        res_item, res_count = self.inventory_crafting_result if self.inventory_crafting_result else (None, 0)
        if res_item:
            self._draw_item_texture_in_slot(res_item, result_x, result_y, slot_size)
            if res_count > 1:
                self._draw_text_with_shadow(str(res_count), font_size=10*scale, x=result_x+slot_size-2, y=result_y+2)

        title_color = (64, 64, 64, 255)
        pyglet.text.Label("合成", font_name='Microsoft JhengHei', font_size=10*scale, x=craft_base_x, y=y_start + total_height - 28*scale, color=title_color).draw()

    def draw_crafting_table_ui(self, is_crafting_table_ui=True):
        batch = pyglet.graphics.Batch()
        
        scale = 2.0
        base_w, base_h = 176, 166
        total_width, total_height = base_w * scale, base_h * scale
        x_start = (self.window.width - total_width) / 2
        y_start = (self.window.height - total_height) / 2

        bg_color = (198, 198, 198, 255)
        batch.add(4, gl.GL_QUADS, None, ('v2f', (x_start, y_start, x_start + total_width, y_start, x_start + total_width, y_start + total_height, x_start, y_start + total_height)), ('c4B', bg_color * 4))
        
        slot_size = 18 * scale
        
        inv_base_x = x_start + 8 * scale
        inv_base_y_main = y_start + 8 * scale + 1 * (slot_size + 0)
        for i in range(len(self.main_inventory)):
            row, col = divmod(i, self.inventory_cols)
            x = inv_base_x + col * slot_size
            y = inv_base_y_main + (2-row) * slot_size 
            self._draw_slot(batch, x, y, slot_size)

        inv_base_y_hotbar = y_start + 8 * scale
        for i in range(len(self.hotbar)):
            x = inv_base_x + i * slot_size
            y = inv_base_y_hotbar
            self._draw_slot(batch, x, y, slot_size)

        craft_base_x = x_start + 30 * scale
        craft_base_y = y_start + total_height - 70 * scale
        for i in range(9):
            row, col = divmod(i, 3)
            x = craft_base_x + col * slot_size
            y = craft_base_y + (2-row) * slot_size
            self._draw_slot(batch, x, y, slot_size)

        arrow_y_center = craft_base_y + slot_size
        arrow_x, _ = x_start + 90 * scale, y_start + total_height - 52 * scale
        arrow_w, arrow_h = 22 * scale, 15 * scale
        shaft_h = 7 * scale; shaft_w = 15 * scale
        arrow_color_tuple = (139, 139, 139, 255) * 4
        shaft_y = arrow_y_center - shaft_h / 2
        batch.add(4, gl.GL_QUADS, None, ('v2f', (arrow_x, shaft_y, arrow_x + shaft_w, shaft_y, arrow_x + shaft_w, shaft_y + shaft_h, arrow_x, shaft_y + shaft_h)), ('c4B', arrow_color_tuple))
        batch.add(3, gl.GL_TRIANGLES, None, ('v2f', (arrow_x + shaft_w, arrow_y_center - arrow_h/2, arrow_x + shaft_w, arrow_y_center + arrow_h/2, arrow_x + arrow_w, arrow_y_center)), ('c4B', arrow_color_tuple[:3*4]))

        result_x, result_y = x_start + 124 * scale, y_start + total_height - 58 * scale
        self._draw_slot(batch, result_x, result_y, slot_size)
        
        batch.draw()

        for i in range(len(self.main_inventory)):
            item_slot = self.main_inventory[i]
            if item_slot:
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = inv_base_y_main + (2-row) * slot_size 
                self._draw_item_texture_in_slot(item_slot['id'], x, y, slot_size)
                if item_slot['count'] > 1:
                    self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=y+2)

        for i in range(len(self.hotbar)):
            item_slot = self.hotbar[i]
            if item_slot:
                x = inv_base_x + i * slot_size
                y = inv_base_y_hotbar
                self._draw_item_texture_in_slot(item_slot['id'], x, y, slot_size)
                if item_slot['count'] > 1:
                    self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=y+2)

        if is_crafting_table_ui:
            craft_base_x = x_start + 30 * scale
            craft_base_y = y_start + total_height - 70 * scale
            for i in range(9):
                item_slot = self.crafting_table_grid[i]
                if item_slot:
                    row, col = divmod(i, 3)
                    x = craft_base_x + col * slot_size
                    y = craft_base_y + (2-row) * slot_size
                    self._draw_item_texture_in_slot(item_slot['id'], x, y, slot_size)
                    if item_slot['count'] > 1:
                        self._draw_text_with_shadow(str(item_slot['count']), font_size=10*scale, x=x+slot_size-2, y=y+2)

            res_item, res_count = self.crafting_table_result if self.crafting_table_result else (None, 0)
            if res_item:
                result_x, result_y = x_start + 124 * scale, y_start + total_height - 58 * scale
                self._draw_item_texture_in_slot(res_item, result_x, result_y, slot_size)
                if res_count > 1:
                    self._draw_text_with_shadow(str(res_count), font_size=10*scale, x=result_x+slot_size-2, y=result_y+2)
        
        title_color = (64, 64, 64, 255)
        if is_crafting_table_ui:
            pyglet.text.Label("製作", font_name='Microsoft JhengHei', font_size=10*scale, x=x_start + 28*scale, y=y_start + base_h*scale - 18, color=title_color).draw()
        
        pyglet.text.Label("物品欄", font_name='Microsoft JhengHei', font_size=10*scale, x=x_start + 8*scale, y=y_start + 84*scale - 14, color=title_color).draw()

    def draw_hotbar(self):
        slot_sz,padding,num_slots=self.game_hotbar_slot_size,self.game_hotbar_padding,self.hotbar_size
        total_width=(slot_sz*num_slots)+(padding*(num_slots-1))
        start_x,start_y=(self.window.width-total_width)//2,padding+5 
        
        for i in range(num_slots):
            slot_x=start_x+i*(slot_sz+padding)
            item_slot = self.hotbar[i]
            
            is_selected=(i==self.current_hotbar_index)
            
            bg_color=(10,10,10,100)
            gl.glPushAttrib(gl.GL_CURRENT_BIT); gl.glColor4ub(*bg_color)
            pyglet.graphics.draw(4,gl.GL_QUADS,('v2f',(slot_x,start_y,slot_x+slot_sz,start_y,
                                                      slot_x+slot_sz,start_y+slot_sz,slot_x,start_y+slot_sz)))
            gl.glPopAttrib()

            if item_slot:
                item_id = item_slot['id']
                count = item_slot['count']
                if count > 0:
                    self._draw_item_texture_in_slot(item_id, slot_x, start_y, slot_sz)
                    if count > 1:
                        self._draw_text_with_shadow(str(count),x=slot_x+slot_sz-2,y=start_y+2, font_size=10)
            
            gl.glPushAttrib(gl.GL_LINE_BIT|gl.GL_CURRENT_BIT)
            if is_selected:
                gl.glLineWidth(2.5) 
                gl.glColor3ub(240,240,240)
            else:
                gl.glLineWidth(1.5)
                gl.glColor3ub(90,90,90) 
            pyglet.graphics.draw(4,gl.GL_LINE_LOOP,('v2f',(slot_x-1,start_y-1,slot_x+slot_sz+1,start_y-1,
                                                         slot_x+slot_sz+1,start_y+slot_sz+1,slot_x-1,start_y+slot_sz+1)))
            gl.glPopAttrib()
            
    def draw_chat_input(self):
        w, h = self.window.get_size()
        chat_height = 40
        gl.glPushAttrib(gl.GL_CURRENT_BIT)
        gl.glColor4f(0, 0, 0, 0.5) 
        pyglet.graphics.draw(4, gl.GL_QUADS, ('v2f', (0, 0, w, 0, w, chat_height, 0, chat_height)))
        gl.glPopAttrib()
        self.chat_label.y = chat_height // 2
        self.chat_label.anchor_y = 'center'
        self.chat_label.draw()

    def draw_pause_menu(self):
        w,h=self.window.get_size()
        gl.glPushAttrib(gl.GL_CURRENT_BIT); gl.glColor4ub(0,0,0,150)
        pyglet.graphics.draw(4,gl.GL_QUADS,('v2f',(0,0,w,0,w,h,0,h))); gl.glPopAttrib()
        
        button_width,button_height,button_spacing=300,60,20
        total_buttons_height = 3 * button_height + 2 * button_spacing
        start_y = h // 2 + total_buttons_height // 2 - button_height
        
        continue_x, continue_y = w//2 - button_width//2, start_y
        keys_x, keys_y = w//2 - button_width//2, continue_y - button_height - button_spacing
        exit_x, exit_y = w//2 - button_width//2, keys_y - button_height - button_spacing

        gl.glPushAttrib(gl.GL_CURRENT_BIT); gl.glColor4ub(80,80,80,220) 
        pyglet.graphics.draw(4,gl.GL_QUADS,('v2f',(continue_x,continue_y, continue_x+button_width,continue_y, continue_x+button_width,continue_y+button_height, continue_x,continue_y+button_height)))
        pyglet.graphics.draw(4,gl.GL_QUADS,('v2f',(keys_x,keys_y, keys_x+button_width,keys_y, keys_x+button_width,keys_y+button_height, keys_x,keys_y+button_height)))
        pyglet.graphics.draw(4,gl.GL_QUADS,('v2f',(exit_x,exit_y, exit_x+button_width,exit_y, exit_x+button_width,exit_y+button_height, exit_x,exit_y+button_height)))
        gl.glPopAttrib()
        
        pyglet.text.Label("繼續遊玩",x=w//2,y=continue_y+button_height//2, anchor_x='center',anchor_y='center', font_name='Microsoft JhengHei',font_size=20,color=(255,255,255,255)).draw()
        pyglet.text.Label("修改按鍵",x=w//2,y=keys_y+button_height//2, anchor_x='center',anchor_y='center', font_name='Microsoft JhengHei',font_size=20,color=(255,255,255,255)).draw()
        pyglet.text.Label("儲存並退出",x=w//2,y=exit_y+button_height//2, anchor_x='center',anchor_y='center', font_name='Microsoft JhengHei',font_size=20,color=(255,255,255,255)).draw()

    def draw_keybinding_menu(self):
        w, h = self.window.get_size()
        gl.glPushAttrib(gl.GL_CURRENT_BIT); gl.glColor4ub(0, 0, 0, 180)
        pyglet.graphics.draw(4, gl.GL_QUADS, ('v2f', (0, 0, w, 0, w, h, 0, h))); gl.glPopAttrib()
        
        pyglet.text.Label("修改按鍵", x=w//2, y=h - 60, anchor_x='center', font_name='Microsoft JhengHei', font_size=24, color=(255, 255, 255, 255)).draw()
        if self.key_to_rebind:
            pyglet.text.Label("請按下鍵盤按鍵或滑鼠按鍵以設定，按 ESC 取消", x=w//2, y=h - 100, anchor_x='center', font_name='Microsoft JhengHei', font_size=16, color=(255, 255, 100, 255)).draw()
        else:
            pyglet.text.Label("點擊按鍵名稱以修改，按 ESC 返回", x=w//2, y=h - 100, anchor_x='center', font_name='Microsoft JhengHei', font_size=16, color=(200, 200, 200, 255)).draw()

        action_map_zh = {
            "forward": "前進", "backward": "後退", "left": "向左", "right": "向右",
            "jump": "跳躍", "sprint": "奔跑", "sneak": "潛行",
            "inventory": "物品欄",
            "attack": "攻擊/破壞", "place": "使用/放置", "pick_block": "選取方塊",
            "chat": "開啟聊天", "command": "開啟指令",
            "toggle_third_person": "切換第三人稱視角"
        }
        
        self.keybinding_labels.clear()
        
        start_y = h - 180
        spacing = 45
        
        action_order = [
            "forward", "backward", "left", "right", "jump", "sprint", "sneak",
            "inventory", "attack", "place", "pick_block", "chat", "command", "toggle_third_person"
        ]
        
        for i, action in enumerate(action_order):
            if action not in self.keybindings: continue
            y = start_y - i * spacing
            pyglet.text.Label(action_map_zh.get(action, action), x=w//2 - 250, y=y, anchor_x='left', font_name='Microsoft JhengHei', font_size=18, color=(255, 255, 255, 255)).draw()
            
            key_code = self.keybindings[action]
            key_name = self._get_binding_name(key_code)
            
            is_conflicting = action in self.conflicting_actions
            is_rebinding = self.key_to_rebind == action

            if is_rebinding:
                key_text = "> ??? <"
                color = (255, 255, 100, 255)
            elif is_conflicting:
                key_text = key_name
                color = (255, 80, 80, 255)
            else:
                key_text = key_name
                color = (255, 255, 255, 255)

            key_label = pyglet.text.Label(key_text, x=w//2 + 200, y=y, anchor_x='center', font_name='Consolas', font_size=18, color=color, bold=True)
            key_label.draw()
            
            label_width = key_label.content_width + 40
            label_height = key_label.content_height + 10
            self.keybinding_labels[action] = (key_label.x - label_width / 2, y - label_height / 2, label_width, label_height)

    def on_mouse_press(self, x_click, y_click, button, modifiers):
        # 支援滑鼠按鍵切換人稱
        if not self.show_keybinding_menu and button == self.keybindings.get('toggle_third_person'):
            if self.camera_mode == "first":
                self.camera_mode = "third_back"
            elif self.camera_mode == "third_back":
                self.camera_mode = "third_front"
            else:
                self.camera_mode = "first"
            logging.info(f"滑鼠按鍵切換視角: {self.camera_mode}")
            return pyglet.event.EVENT_HANDLED
        # 支援自訂按鍵流程偵測滑鼠按鍵
        if self.show_keybinding_menu and self.key_to_rebind:
            key_name = self._get_binding_name(button)
            action_name_zh = {
                "forward": "前進", "backward": "後退", "left": "向左", "right": "向右",
                "jump": "跳躍", "sprint": "奔跑", "sneak": "潛行",
                "inventory": "物品欄",
                "attack": "攻擊/破壞", "place": "使用/放置", "pick_block": "選取方塊",
                "chat": "開啟聊天", "command": "開啟指令",
                "toggle_third_person": "切換第三人稱視角"
            }.get(self.key_to_rebind, self.key_to_rebind)
            logging.info(f"按鍵綁定已更新: {action_name_zh} -> {key_name} (code: {button})")
            self.keybindings[self.key_to_rebind] = button
            self.key_to_rebind = None
            self.check_key_conflicts()
            self.save_keybindings()
            return pyglet.event.EVENT_HANDLED

        if not self.show_keybinding_menu:
            self.mouse_btn_state.add(button)
            # ...原本的檢查邏輯...
            current_time = time.time()
            if button == self.keybindings.get('sprint') and 'sprint' not in self.conflicting_actions:
                if not self.is_sneaking:
                    self.is_sprinting = True
            elif button == self.keybindings.get('jump') and 'jump' not in self.conflicting_actions:
                # 滑鼠綁定的跳躍邏輯
                if self.mode == "survival" and self.on_ground:
                    if current_time - self.last_jump_time > self.jump_cooldown:
                        self.velocity[1] = self.jump_force
                        self.on_ground = False 
                        self.last_jump_time = current_time
                elif self.mode == "creative":
                    if not self.is_flying_creative and self.on_ground: 
                        if current_time - self.last_jump_time > self.jump_cooldown:
                             self.velocity[1] = self.jump_force
                             self.on_ground = False
                             self.last_jump_time = current_time
                    elif current_time - self.last_space_press_time < self.double_tap_time: 
                        self.is_flying_creative = not self.is_flying_creative
                        logging.info(f"Creative flying toggled: {self.is_flying_creative}")
                        if not self.is_flying_creative: 
                            self.on_ground = False 
                            if self.check_collision_bbox(self.position[0], self.position[1] - 0.01, self.position[2]):
                                self.on_ground = True
                                self.velocity[1] = 0 
                    self.last_space_press_time = current_time

        if self.show_keybinding_menu:
            if self.key_to_rebind:
                if button not in (mouse.SCROLL_UP, mouse.SCROLL_DOWN):
                    button_name = self._get_binding_name(button)
                    action_name_zh = {
                        "forward": "前進", "backward": "後退", "left": "向左", "right": "向右",
                        "jump": "跳躍", "sprint": "奔跑", "sneak": "潛行",
                        "inventory": "物品欄",
                        "attack": "攻擊/破壞", "place": "使用/放置", "pick_block": "選取方塊",
                        "chat": "開啟聊天", "command": "開啟指令",
                    }.get(self.key_to_rebind, self.key_to_rebind)
                    logging.info(f"按鍵綁定已更新: {action_name_zh} -> {button_name} (code: {button})")
                    self.keybindings[self.key_to_rebind] = button
                    self.key_to_rebind = None
                    self.check_key_conflicts()
                    self.save_keybindings()
                else:
                    logging.info("滾輪按鍵無法綁定，請使用其他按鍵")
                return pyglet.event.EVENT_HANDLED
            elif button == mouse.LEFT:
                for action, (lx, ly, lw, lh) in self.keybinding_labels.items():
                    if lx <= x_click < lx + lw and ly <= y_click < ly + lh:
                        self.key_to_rebind = action
                        return pyglet.event.EVENT_HANDLED
            return pyglet.event.EVENT_HANDLED

        if self.show_inventory or self.show_crafting_table_ui:
            ui_type = 'crafting_table' if self.show_crafting_table_ui else 'inventory'
            self._handle_inventory_click(x_click, y_click, ui_type, button)
            return pyglet.event.EVENT_HANDLED

        if self.chat_active:
            return pyglet.event.EVENT_HANDLED

        if button == self.keybindings.get('pick_block') and 'pick_block' not in self.conflicting_actions:
            target_info = self.get_target_block()
            if not target_info: return pyglet.event.EVENT_HANDLED

            block_pos, _ = target_info
            target_block_type = self.world.get(block_pos)
            if not target_block_type: return pyglet.event.EVENT_HANDLED

            current_slot_item = self.hotbar[self.current_hotbar_index]
            if current_slot_item and current_slot_item['id'] == target_block_type:
                return pyglet.event.EVENT_HANDLED

            found_location = None
            for i, slot in enumerate(self.hotbar):
                if slot and slot['id'] == target_block_type:
                    found_location = ('hotbar', i)
                    break
            
            if not found_location:
                for i, slot in enumerate(self.main_inventory):
                    if slot and slot['id'] == target_block_type:
                        found_location = ('main', i)
                        break

            if found_location:
                source_type, source_index = found_location
                source_list = self.hotbar if source_type == 'hotbar' else self.main_inventory
                
                item_from_source = source_list[source_index]
                item_from_dest = self.hotbar[self.current_hotbar_index]
                
                source_list[source_index] = item_from_dest
                self.hotbar[self.current_hotbar_index] = item_from_source
                
                self.update_selected_block_from_hotbar()
                return pyglet.event.EVENT_HANDLED

            if self.mode == "creative":
                old_item_in_hotbar = self.hotbar[self.current_hotbar_index]
                self.hotbar[self.current_hotbar_index] = {'id': target_block_type, 'count': 1}
                
                if old_item_in_hotbar:
                    if self.main_inventory[0] is None:
                        self.main_inventory[0] = old_item_in_hotbar
                    elif self.main_inventory[0]['id'] == old_item_in_hotbar['id'] and \
                         self.main_inventory[0]['count'] + old_item_in_hotbar['count'] <= self.max_stack_size:
                        self.main_inventory[0]['count'] += old_item_in_hotbar['count']
                    else:
                        self.add_item_to_inventory(old_item_in_hotbar['id'], old_item_in_hotbar['count'])

                self.update_selected_block_from_hotbar()
            
            return pyglet.event.EVENT_HANDLED

        if button == self.keybindings.get('attack') and 'attack' not in self.conflicting_actions:
             self.mouse_left_is_pressed=True
        
        if self.pause_menu: 
            w, h = self.window.get_size()
            btn_w, btn_h, btn_sp = 300, 60, 20
            total_buttons_height = 3 * btn_h + 2 * btn_sp
            start_y = h // 2 + total_buttons_height // 2 - btn_h
            
            cx1, cy1 = w//2 - btn_w//2, start_y
            cx2, cy2 = cx1 + btn_w, cy1 + btn_h

            kx1, ky1 = w//2 - btn_w//2, cy1 - btn_h - btn_sp
            kx2, ky2 = kx1 + btn_w, ky1 + btn_h

            ex1, ey1 = w//2 - btn_w//2, ky1 - btn_h - btn_sp
            ex2, ey2 = ex1 + btn_w, ey1 + btn_h
            
            if cx1 <= x_click <= cx2 and cy1 <= y_click <= cy2: 
                self.pause_menu=False
                self._update_mouse_exclusivity() 
                return pyglet.event.EVENT_HANDLED
            elif kx1 <= x_click <= kx2 and ky1 <= y_click <= ky2:
                self.pause_menu = False
                self.show_keybinding_menu = True
                self._update_mouse_exclusivity()
                return pyglet.event.EVENT_HANDLED
            elif ex1 <= x_click <= ex2 and ey1 <= y_click <= ey2: 
                self.save_game()
                logging.info("「儲存並退出」按鈕被按下，準備結束 Pyglet 應用程式。")
                pyglet.app.exit()
                return pyglet.event.EVENT_HANDLED
            return pyglet.event.EVENT_HANDLED 

        action_taken=False
        if button == self.keybindings.get('attack') and 'attack' not in self.conflicting_actions:
            targeted_info=self.get_target_block()
            if targeted_info:
                block_pos,_=targeted_info
                if block_pos in self.world:
                    block_type=self.world.get(block_pos)
                    if not (block_type=="stone" and block_pos[1]==0):
                        if self.mode=="creative": 
                            self.world.pop(block_pos); self.chunk_dirty=True; self.trigger_arm_swing_animation(); action_taken=True
                        else: 
                            if self.breaking_block_pos!=block_pos: 
                                self.breaking_block_pos=block_pos
                                self.breaking_block_start_time=time.time()
                                self.breaking_block_stage=0
                                self.rebuild_breaking_effect()
                            action_taken=True 
            else: 
                if self.breaking_block_pos: 
                    self.breaking_block_pos=None; self.breaking_block_stage=0; self.rebuild_breaking_effect()
            
            if not action_taken or not targeted_info : 
                self.trigger_arm_swing_animation()
        
        elif button == self.keybindings.get('place') and 'place' not in self.conflicting_actions: 
            hotbar_slot = self.hotbar[self.current_hotbar_index]
            selected_type_id = hotbar_slot['id'] if hotbar_slot else None
            
            target_info=self.get_target_block()

            if target_info:
                block_pos_hit,face_hit_normal=target_info
                block_hit_type = self.world.get(block_pos_hit)
                if block_hit_type == "crafting_table":
                    self.show_crafting_table_ui = True
                    self._update_mouse_exclusivity()
                    logging.info("Opened crafting table UI.")
                    return pyglet.event.EVENT_HANDLED
                
                if selected_type_id:
                    place_pos=(block_pos_hit[0]+face_hit_normal[0],
                               block_pos_hit[1]+face_hit_normal[1],
                               block_pos_hit[2]+face_hit_normal[2])
                    
                    player_min_x,player_max_x = self.position[0]-0.3, self.position[0]+0.3
                    player_min_y,player_max_y = self.position[1], self.position[1]+self.player_height
                    player_min_z,player_max_z = self.position[2]-0.3, self.position[2]+0.3
                    
                    block_min_x_place,block_max_x_place=place_pos[0],place_pos[0]+1
                    block_min_y_place,block_max_y_place=place_pos[1],place_pos[1]+1
                    block_min_z_place,block_max_z_place=place_pos[2],place_pos[2]+1

                    intersects_player=(player_min_x<block_max_x_place and player_max_x>block_min_x_place and \
                                       player_min_y<block_max_y_place and player_max_y>block_min_y_place and \
                                       player_min_z<block_max_z_place and player_max_z>block_min_z_place)

                    if place_pos not in self.world and not intersects_player:
                        self.world[place_pos]=selected_type_id
                        action_taken=True
                        self.trigger_arm_swing_animation()
                        if self.mode=="survival": 
                            hotbar_slot['count'] -= 1
                            if hotbar_slot['count'] <= 0:
                                self.hotbar[self.current_hotbar_index] = None
                            self.update_selected_block_from_hotbar()
        
        if action_taken: self.chunk_dirty=True

    def draw_crosshair(self):
        w,h=self.window.get_size(); center_x,center_y=w//2,h//2; size=10
        gl.glDisable(gl.GL_BLEND) 
        gl.glLineWidth(2)
        pyglet.graphics.draw(4,gl.GL_LINES,('v2f',(center_x-size,center_y,center_x+size,center_y, 
                                                  center_x,center_y-size,center_x,center_y+size)), 
                                          ('c3B',(200,200,200)*4)) 
    
    def load_recipes(self):
        self.recipes = {
            tuple(sorted(('oak_log',))): ('oak_planks', 4),
            tuple(sorted(('birch_log',))): ('birch_planks', 4),
            tuple(sorted(('oak_planks', 'oak_planks', 'oak_planks', 'oak_planks'))): ('crafting_table', 1),
            tuple(sorted(('birch_planks', 'birch_planks', 'birch_planks', 'birch_planks'))): ('crafting_table', 1),
        }
        logging.info(f"Loaded {len(self.recipes)} recipes.")

    def check_crafting_recipe(self, grid_type):
        if grid_type == 'inventory':
            grid = self.inventory_crafting_grid
        elif grid_type == 'crafting_table':
            grid = self.crafting_table_grid
        else:
            return

        items_in_grid = tuple(sorted([item['id'] for item in grid if item is not None and item['count'] > 0]))
        
        if not items_in_grid:
            result = None
        else:
            result = self.recipes.get(items_in_grid)

        if grid_type == 'inventory':
            self.inventory_crafting_result = result
        else:
            self.crafting_table_result = result
    
    def _draw_slot(self, batch, x, y, size):
        border_color = (80, 80, 80, 255)
        bg_color = (139, 139, 139, 255)
        
        batch.add(4, gl.GL_QUADS, None, ('v2f', (x, y, x + size, y, x + size, y + size, x, y + size)), ('c4B', border_color * 4))
        inset = 2
        batch.add(4, gl.GL_QUADS, None, ('v2f', (x + inset, y + inset, x + size - inset, y + inset, x + size - inset, y + size - inset, x + inset, y + size - inset)), ('c4B', bg_color * 4))

    def _get_inventory_slot_regions(self):
        if not self.show_inventory and not self.show_crafting_table_ui:
            return []
            
        scale = 2.0
        base_w, base_h = 176, 166
        total_width, total_height = base_w * scale, base_h * scale
        x_start = (self.window.width - total_width) / 2
        y_start = (self.window.height - total_height) / 2
        slot_size = 18 * scale
        
        slot_regions = []
        
        if self.show_crafting_table_ui:
            inv_base_x = x_start + 8 * scale
            inv_base_y_main = y_start + 8 * scale + 1 * slot_size
            for i in range(len(self.main_inventory)):
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = inv_base_y_main + (2 - row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'main', 'index': i, 'item': self.main_inventory[i]})

            inv_base_y_hotbar = y_start + 8 * scale
            for i in range(len(self.hotbar)):
                x = inv_base_x + i * slot_size
                y = inv_base_y_hotbar
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'hotbar', 'index': i, 'item': self.hotbar[i]})
            
            craft_base_x = x_start + 30 * scale
            craft_base_y = y_start + total_height - 70 * scale
            for i in range(9):
                row, col = divmod(i, 3)
                x = craft_base_x + col * slot_size
                y = craft_base_y + (2-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'craft_table', 'index': i, 'item': self.crafting_table_grid[i]})
        
        else: # Personal Inventory
            inv_base_x = x_start + (8 * scale)
            hotbar_y = y_start + (8 * scale)
            main_inv_y_start = hotbar_y + slot_size + (4 * scale)
            craft_base_x = x_start + 88 * scale
            craft_base_y = y_start + total_height - (70 * scale)

            for i in range(len(self.hotbar)):
                x = inv_base_x + i * slot_size
                slot_regions.append({'rect': (x, hotbar_y, slot_size, slot_size), 'type': 'hotbar', 'index': i, 'item': self.hotbar[i]})
            
            for i in range(len(self.main_inventory)):
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = main_inv_y_start + (2-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'main', 'index': i, 'item': self.main_inventory[i]})

            for i in range(4):
                row, col = divmod(i, 2)
                x = craft_base_x + col * slot_size
                y = craft_base_y + (1-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'craft_inv', 'index': i, 'item': self.inventory_crafting_grid[i]})

        return slot_regions

    def _update_tooltip(self):
        if not self.show_inventory and not self.show_crafting_table_ui:
            self.tooltip_label = None
            return
            
        if self.inventory_selected_item_info: 
            self.tooltip_label = None
            return

        slot_regions = self._get_inventory_slot_regions()
        
        self.tooltip_label = None
        self.tooltip_bg_batch = None
        for region in slot_regions:
            rx, ry, rw, rh = region['rect']
            item = region.get('item')
            if item and (rx <= self.mouse_x < rx + rw and ry <= self.mouse_y < ry + rh):
                item_id_text = f"minecraft:{item['id']}"
                self.tooltip_label = pyglet.text.Label(
                    item_id_text,
                    x=self.mouse_x + 15, y=self.mouse_y,
                    font_name='Consolas', font_size=12,
                    color=(220, 220, 220, 255),
                    anchor_x='left', anchor_y='top'
                )
                
                content_width = self.tooltip_label.content_width
                content_height = self.tooltip_label.content_height
                padding = 4
                
                self.tooltip_bg_batch = pyglet.graphics.Batch()
                self.tooltip_bg_batch.add(4, gl.GL_QUADS, None, ('v2f', (
                    self.mouse_x + 10, self.mouse_y + padding,
                    self.mouse_x + 10 + content_width + padding*2, self.mouse_y + padding,
                    self.mouse_x + 10 + content_width + padding*2, self.mouse_y - content_height,
                    self.mouse_x + 10, self.mouse_y - content_height
                )), ('c4B', (18, 18, 58, 200) * 4))
                break

    def _handle_inventory_click(self, click_x, click_y, ui_type, button):
        scale = 2.0
        base_w, base_h = 176, 166
        total_width, total_height = base_w * scale, base_h * scale
        x_start = (self.window.width - total_width) // 2
        y_start = (self.window.height - total_height) // 2
        slot_size = 18 * scale
        
        slot_regions = []
        
        if ui_type == 'crafting_table':
            inv_base_x = x_start + 8 * scale
            inv_base_y_main = y_start + 8 * scale + 1 * (slot_size + 0)
            for i in range(len(self.main_inventory)):
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = inv_base_y_main + (2 - row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'main', 'index': i})

            inv_base_y_hotbar = y_start + 8 * scale
            for i in range(len(self.hotbar)):
                x = inv_base_x + i * slot_size
                y = inv_base_y_hotbar
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'hotbar', 'index': i})

            craft_base_x = x_start + 30 * scale
            craft_base_y = y_start + total_height - 70 * scale
            for i in range(9):
                row, col = divmod(i, 3)
                x = craft_base_x + col * slot_size
                y = craft_base_y + (2-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'craft_table', 'index': i})

            result_x = x_start + 124 * scale
            result_y = y_start + total_height - 58 * scale
            slot_regions.append({'rect': (result_x, result_y, slot_size, slot_size), 'type': 'craft_table_res', 'index': 0})
        else: # Personal inventory
            inv_base_x = x_start + (8 * scale)
            hotbar_y = y_start + (8 * scale)
            main_inv_y_start = hotbar_y + slot_size + (4 * scale)
            craft_base_x = x_start + 88 * scale
            craft_base_y = y_start + total_height - (70 * scale)

            for i in range(len(self.hotbar)):
                x = inv_base_x + i * slot_size
                slot_regions.append({'rect': (x, hotbar_y, slot_size, slot_size), 'type': 'hotbar', 'index': i})
            
            for i in range(len(self.main_inventory)):
                row, col = divmod(i, self.inventory_cols)
                x = inv_base_x + col * slot_size
                y = main_inv_y_start + (2-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'main', 'index': i})

            for i in range(4):
                row, col = divmod(i, 2)
                x = craft_base_x + col * slot_size
                y = craft_base_y + (1-row) * slot_size
                slot_regions.append({'rect': (x, y, slot_size, slot_size), 'type': 'craft_inv', 'index': i})

            arrow_y_center = craft_base_y + slot_size / 2
            arrow_x = craft_base_x + (2 * slot_size) + (6 * scale)
            arrow_w = 22 * scale
            result_x = arrow_x + arrow_w + (6 * scale)
            result_y = arrow_y_center - (slot_size / 2)
            slot_regions.append({'rect': (result_x, result_y, slot_size, slot_size), 'type': 'craft_inv_res', 'index': 0})
        
        self.process_slot_click(click_x, click_y, slot_regions, button)
    
    def process_slot_click(self, x, y, regions, button):
        held_item = self.inventory_selected_item_info
        
        clicked_region = None
        for region in regions:
            rx, ry, rw, rh = region['rect']
            if rx <= x < rx + rw and ry <= y < ry + rh:
                clicked_region = region
                break
        
        if not clicked_region:
            if held_item:
                self.add_item_to_inventory(held_item['id'], held_item['count'])
                self.inventory_selected_item_info = None
            return

        slot_type = clicked_region['type']
        index = clicked_region['index']
        current_time = time.time()

        target_list = None
        if slot_type == 'hotbar': target_list = self.hotbar
        elif slot_type == 'main': target_list = self.main_inventory
        elif slot_type == 'craft_inv': target_list = self.inventory_crafting_grid
        elif slot_type == 'craft_table': target_list = self.crafting_table_grid
        
        is_double_click = (current_time - self.last_click_time < self.double_click_threshold and 
                           self.last_click_info == clicked_region)

        if button == mouse.LEFT and is_double_click and not held_item and target_list and target_list[index]:
            item_id_to_collect = target_list[index]['id']
            held_item = target_list[index]
            target_list[index] = None
            self.inventory_selected_item_info = held_item
            
            for inv_list in [self.main_inventory, self.hotbar, self.inventory_crafting_grid, self.crafting_table_grid]:
                for i in range(len(inv_list)):
                    slot = inv_list[i]
                    if held_item['count'] >= self.max_stack_size: break
                    if slot and slot['id'] == item_id_to_collect:
                        can_add = self.max_stack_size - held_item['count']
                        to_take = min(slot['count'], can_add)
                        held_item['count'] += to_take
                        slot['count'] -= to_take
                        if slot['count'] == 0:
                            inv_list[i] = None
                if held_item['count'] >= self.max_stack_size: break
            
            self.last_click_time = 0 
            self._refresh_inventory_display_layout()
            if 'craft' in slot_type: self.check_crafting_recipe('crafting_table' if 'table' in slot_type else 'inventory')
            return

        if 'res' in slot_type:
            is_table_craft = 'table' in slot_type
            result = self.crafting_table_result if is_table_craft else self.inventory_crafting_result
            grid = self.crafting_table_grid if is_table_craft else self.inventory_crafting_grid

            if result:
                res_id, res_count = result
                can_pickup = not held_item or (held_item['id'] == res_id and held_item['count'] + res_count <= self.max_stack_size)
                
                if can_pickup:
                    for i in range(len(grid)):
                        if grid[i]:
                            grid[i]['count'] -= 1
                            if grid[i]['count'] == 0:
                                grid[i] = None
                    
                    if not held_item:
                        self.inventory_selected_item_info = {'id': res_id, 'count': res_count}
                    else:
                        held_item['count'] += res_count
                    
                    self.check_crafting_recipe('crafting_table' if is_table_craft else 'inventory')
            
            self.last_click_time = current_time
            self.last_click_info = clicked_region
            return

        if target_list is None: return

        slot_item = target_list[index]

        if button == mouse.LEFT:
            if not held_item:
                if slot_item:
                    self.inventory_selected_item_info = slot_item
                    target_list[index] = None
            else:
                if not slot_item:
                    target_list[index] = held_item
                    self.inventory_selected_item_info = None
                elif slot_item['id'] == held_item['id']:
                    can_add = self.max_stack_size - slot_item['count']
                    to_add = min(held_item['count'], can_add)
                    slot_item['count'] += to_add
                    held_item['count'] -= to_add
                    if held_item['count'] == 0:
                        self.inventory_selected_item_info = None
                else:
                    target_list[index] = held_item
                    self.inventory_selected_item_info = slot_item
        elif button == mouse.RIGHT:
            if not held_item:
                if slot_item:
                    to_take = math.ceil(slot_item['count'] / 2)
                    to_leave = slot_item['count'] - to_take
                    
                    self.inventory_selected_item_info = {'id': slot_item['id'], 'count': to_take}
                    
                    if to_leave > 0:
                        slot_item['count'] = to_leave
                    else:
                        target_list[index] = None
            else:
                if not slot_item:
                    target_list[index] = {'id': held_item['id'], 'count': 1}
                    held_item['count'] -= 1
                    if held_item['count'] == 0:
                        self.inventory_selected_item_info = None
                elif slot_item['id'] == held_item['id'] and slot_item['count'] < self.max_stack_size:
                    slot_item['count'] += 1
                    held_item['count'] -= 1
                    if held_item['count'] == 0:
                        self.inventory_selected_item_info = None

        self.last_click_time = current_time
        self.last_click_info = clicked_region

        if 'craft' in slot_type:
            self.check_crafting_recipe('crafting_table' if 'table' in slot_type else 'inventory')
        self._refresh_inventory_display_layout()


def run_game():
    window = None
    game_instance = None
    try:
        cfg = gl.Config(double_buffer=True, depth_size=24, sample_buffers=1, samples=4)
        window = pyglet.window.Window(width=1024, height=768, caption="Minecraft Py", resizable=True, config=cfg)
        logging.info("Window created with Anti-Aliasing (MSAA x4).")
        window.set_fullscreen(True)
    except pyglet.window.NoSuchConfigException:
        window = pyglet.window.Window(width=1024, height=768, caption="Minecraft Py", resizable=True)
        logging.warning("Window created without Anti-Aliasing (default config).")
        window.set_fullscreen(True)
    except Exception as e:
        logging.critical(f"創建Pyglet視窗失敗:{e}", exc_info=True)
        return

    try:
        game_instance = Game(window)
        if game_instance:
            window.push_handlers(
                game_instance.on_key_press, game_instance.on_key_release,
                game_instance.on_mouse_motion, game_instance.on_mouse_press,
                game_instance.on_mouse_scroll, game_instance.on_mouse_release,
                game_instance.on_text
            )
    except Exception as e:
        logging.critical(f"創建Game物件或設定事件處理器失敗:{e}", exc_info=True)
        if window: window.close()
        return

    if game_instance is None or game_instance.keys is None: 
        logging.critical("Game instance or KeyStateHandler is None. Cannot proceed. Exiting.")
        if window and not window.has_exit: window.close()
        return

    pyglet.clock.schedule_interval(game_instance.update, 1 / 60.0) 

    @window.event
    def on_draw():
        window.clear()
        game_instance.setup_3d()
        if game_instance.chunk_dirty: game_instance.rebuild_world_geometry()
            
        game_instance.world_batch.draw()
        
        if not game_instance.show_inventory and not game_instance.pause_menu and not game_instance.show_crafting_table_ui and not game_instance.show_keybinding_menu:
            game_instance.draw_breaking_effect()
        if game_instance.selected_block: game_instance.draw_held_block()
        else: game_instance.draw_first_person_arm()
        
        game_instance.setup_2d() 
        
        if game_instance.show_crafting_table_ui:
            game_instance.draw_crafting_table_ui()
        elif game_instance.show_inventory:
            game_instance.draw_inventory()
        elif game_instance.show_keybinding_menu:
            game_instance.draw_keybinding_menu()
        elif game_instance.pause_menu: 
            game_instance.draw_pause_menu()
        else: 
            if game_instance.mode=="survival": 
                game_instance.hp_label.draw()
                game_instance.hunger_label.draw()
            game_instance.draw_hotbar()
            game_instance.draw_crosshair()

        if (game_instance.show_inventory or game_instance.show_crafting_table_ui) and game_instance.inventory_selected_item_info:
            held_item = game_instance.inventory_selected_item_info
            item_id = held_item['id']
            count_on_cursor = held_item['count']
            
            item_draw_size = 18 * 2.0
            draw_x = game_instance.mouse_x - item_draw_size / 2
            draw_y = game_instance.mouse_y - item_draw_size / 2
            
            gl.glPushMatrix()
            gl.glTranslatef(0, 0, 1) # Draw on top
            
            game_instance._draw_item_texture_in_slot(item_id, draw_x, draw_y, item_draw_size)
            
            if count_on_cursor > 1:
                game_instance._draw_text_with_shadow(str(count_on_cursor), font_size=10*2.0, x=draw_x + item_draw_size - 2, y=draw_y + 2)
            gl.glPopMatrix()
            
        if game_instance.tooltip_label:
            gl.glPushMatrix()
            gl.glTranslatef(0, 0, 2)
            if game_instance.tooltip_bg_batch:
                game_instance.tooltip_bg_batch.draw()
            game_instance.tooltip_label.draw()
            gl.glPopMatrix()

        game_instance.draw_chat_feedback()

        if game_instance.chat_active:
            game_instance.draw_chat_input()

        game_instance.pos_label.draw() 

    @window.event
    def on_close():
        if game_instance: game_instance.save_game()
        logging.info("遊戲視窗關閉事件觸發 (on_close)。Pyglet app將立即退出。")

    logging.info("開始 Pyglet 應用程式主循環...")
    pyglet.app.run()
    logging.info("Pyglet 應用程式主循環已結束。")

    if window and not window.has_exit: 
        window.close()

if __name__ == "__main__":
    run_game()