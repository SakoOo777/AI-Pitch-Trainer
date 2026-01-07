# ----------------------------------------------------------------------------------
# ** AI-Powered Pitch Trainer (Adaptive Learning) - Fixed Version 7 **
# ** FIX: Pygame 'rect argument is invalid' CRASH FIX **
# ** Fixed float-to-int conversion in draw_interface (Target Zone & Meter) **
# ----------------------------------------------------------------------------------

import pyaudio
import numpy as np
import pygame
import time
import math
import random
from aubio import pitch
from music21 import pitch as m21pitch
from music21 import scale as m21scale
from typing import Tuple, Any, List, Dict, Set
from collections import deque 

# --- Global Settings and Constants ---

# Audio Settings
BUFFER_SIZE: int = 1024         
FORMAT: int = pyaudio.paFloat32 
CHANNELS: int = 1               
RATE: int = 44100               

# Noise Gate
VOLUME_THRESHOLD_RMS: float = 0.015 

# Pitch Detection
TOLERANCE: float = 0.8          
WIN_S: int = 4096              
HOP_S: int = BUFFER_SIZE        
BASE_PITCH_TOLERANCE_CENTS: float = 35.0 # Starting tolerance (Easy)
MIN_PITCH_TOLERANCE_CENTS: float = 10.0  # Master tolerance (Hard)
SUCCESS_HOLD_TIME: float = 0.2       

# Timing
FAILURE_GRACE_TIME: float = 0.3 

# Learning
CENTS_HISTORY_LENGTH: int = 10  
INITIAL_MASTERY_SCORE: float = 0.0 
MASTERY_THRESHOLD: float = 0.85 

# Scales
TONIC_NOTES: List[str] = ["C", "G", "D", "A", "E", "B", "F#", "Db", "Ab", "Eb", "Bb", "F"]
SCALE_TYPES: List[str] = ["Major", "Minor"]

# --- Colors ---
BG_DARK: Tuple[int, int, int] = (25, 25, 35)          
BG_PANEL: Tuple[int, int, int] = (40, 40, 55)
TEXT_LIGHT: Tuple[int, int, int] = (240, 240, 250)    
TARGET_ZONE: Tuple[int, int, int] = (0, 190, 160)     
NEEDLE_ACTIVE: Tuple[int, int, int] = (255, 210, 0)   
ERROR_RED: Tuple[int, int, int] = (255, 80, 80)       
SUCCESS_GREEN: Tuple[int, int, int] = (80, 255, 100)   
KEY_BLACK: Tuple[int, int, int] = (40, 40, 40)        
KEY_WHITE: Tuple[int, int, int] = (245, 245, 245)     
MIC_OFF_COLOR: Tuple[int, int, int] = (180, 60, 60)
GLOW_COLOR: Tuple[int, int, int] = (100, 200, 255)
STATS_BG_COLOR: Tuple[int, int, int] = (30, 30, 45)

# --- Global State ---
p: pyaudio.PyAudio = pyaudio.PyAudio()
pitch_o: pitch = pitch("default", WIN_S, HOP_S, RATE)
pitch_o.set_unit("Hz")
pitch_o.set_tolerance(TOLERANCE)

screen: pygame.Surface | None = None
# Fonts
font_target: pygame.font.Font | None = None
font_large: pygame.font.Font | None = None
font_medium: pygame.font.Font | None = None
font_small: pygame.font.Font | None = None
error_buzzer_sound: pygame.mixer.Sound | None = None

# Visual Timers
error_visual_time: float = 0.0 
success_visual_time: float = 0.0 

# Detection State
last_detected_note_name: str = "N/A"
last_cents_error: float = 0.0
smooth_cents_error: float = 0.0 
is_in_tune: bool = False
octave_offset_str: str = "" 
correct_hold_start_time: float = 0.0
incorrect_hold_start_time: float = 0.0 
is_mic_active: bool = True 
current_target_tolerance: float = BASE_PITCH_TOLERANCE_CENTS
current_target_note: str = "C4" 
success_lock: bool = False 

# Progression Queue for Thread Safety
progression_queue: List[Tuple[str, bool, float]] = []

# UI State
show_stats_overlay: bool = False

# Scale State
current_tonic: str = "C"
current_scale_type: str = "Major"

# Data Structures
NOTES_POOL: List[str] = []       
NOTES_POOL_MIDIS: Dict[int, str] = {} 
ACTIVE_SEQUENCE: List[str] = []  
MASTERED_NOTES: List[str] = []   
NOTE_STATS: Dict[str, Dict[str, Any]] = {}

# User Interaction
user_selected_note: str | None = None 
user_selection_duration: float = 5.0 
user_selection_end_time: float = 0.0 
UI_ELEMENTS: Dict[str, pygame.Rect] = {}

# --- Particles ---
class Particle:
    def __init__(self, x, y, color):
        self.x = x
        self.y = y
        self.color = color
        self.vx = random.uniform(-4, 4)
        self.vy = random.uniform(-4, -1)
        self.gravity = 0.2
        self.life = 255 
        self.size = random.randint(3, 6)

    def update(self):
        self.x += self.vx
        self.y += self.vy
        self.vy += self.gravity
        self.life -= 5
        
    def draw(self, surface):
        if self.life > 0:
            s = pygame.Surface((self.size, self.size), pygame.SRCALPHA)
            r, g, b = self.color
            s.fill((r, g, b, int(self.life)))
            surface.blit(s, (int(self.x), int(self.y)))

particles: List[Particle] = []

def spawn_particles(center_x, center_y, count=20):
    colors = [SUCCESS_GREEN, TARGET_ZONE, (255, 255, 255), NEEDLE_ACTIVE]
    for _ in range(count):
        particles.append(Particle(center_x, center_y, random.choice(colors)))

# --- Helper: Pre-calculate Keyboard Mapping ---
KEY_MIDI_MAP: Dict[str, int] = {}
WHITE_KEY_NOTES_ORDER = ["C", "D", "E", "F", "G", "A", "B"]

def init_midi_map():
    for octave in range(3, 6):
        base_midi = 12 * (octave + 1)
        offsets = {
            "C": 0, "D": 2, "E": 4, "F": 5, "G": 7, "A": 9, "B": 11
        }
        for note in WHITE_KEY_NOTES_ORDER:
            KEY_MIDI_MAP[f"{note}{octave}"] = base_midi + offsets[note]
            if note in ["C", "D", "F", "G", "A"]:
                KEY_MIDI_MAP[f"{note}#{octave}"] = base_midi + offsets[note] + 1
    KEY_MIDI_MAP["C6"] = 84

init_midi_map()

# --- Scale Management ---

def generate_scale_notes(tonic_name: str, scale_type: str, start_octave: int = 4, end_octave: int = 5) -> List[str]:
    scale_type_map = {"Major": m21scale.MajorScale, "Minor": m21scale.MinorScale}
    if scale_type not in scale_type_map: return []
    try:
        start_pitch = m21pitch.Pitch(f"{tonic_name}{start_octave}")
        end_pitch = m21pitch.Pitch(f"{tonic_name}{end_octave + 1}")
    except Exception as e:
        print(f"ERROR: {e}")
        return []
    scale_obj = scale_type_map[scale_type](start_pitch)
    pitches = scale_obj.getPitches(start_pitch, end_pitch)
    scale_notes = []
    for p_note in pitches:
        if p_note.midi < end_pitch.midi:
            scale_notes.append(p_note.nameWithOctave)
    return scale_notes

def initialize_or_update_note_pool(tonic: str, scale_type: str) -> None:
    global NOTES_POOL, NOTES_POOL_MIDIS, NOTE_STATS, current_tonic, current_scale_type, current_target_note
    
    NOTES_POOL = generate_scale_notes(tonic, scale_type, start_octave=4, end_octave=5)
    current_tonic = tonic
    current_scale_type = scale_type
    
    NOTES_POOL_MIDIS = {}
    for note_name in NOTES_POOL:
        try:
            m = m21pitch.Pitch(note_name).midi
            NOTES_POOL_MIDIS[m] = note_name
        except: pass

    new_stats = {}
    for note in NOTES_POOL:
        if note in NOTE_STATS:
            new_stats[note] = NOTE_STATS[note]
        else:
            new_stats[note] = {
                'successes': 0, 'failures': 0,
                'cents_history': deque(maxlen=CENTS_HISTORY_LENGTH), 
                'mastery_score': INITIAL_MASTERY_SCORE 
            }
    NOTE_STATS = new_stats
    
    if NOTES_POOL:
        current_target_note = determine_next_note_ai(NOTES_POOL[0])
    else:
        current_target_note = "N/A"

    print(f"INFO: Scale {tonic} {scale_type} loaded. ({len(NOTES_POOL)} notes). Initial target: {current_target_note}")

# --- AI Logic ---

def calculate_mastery_score(note_stats: Dict[str, Any]) -> float:
    s = note_stats['successes']
    f = note_stats['failures']
    history = note_stats['cents_history']
    total_attempts = s + f
    if total_attempts == 0: return INITIAL_MASTERY_SCORE 
    success_rate = s / total_attempts
    avg_abs_cents_error = np.mean(np.abs(history)) if history else 0.0
    consistency = np.std(history) if len(history) >= 2 else 50.0 
    
    error_metric = max(0, 1 - (avg_abs_cents_error / 40.0))
    cons_metric = max(0, 1 - (consistency / 30.0)) 
    
    mastery = (0.40 * success_rate + 0.30 * error_metric + 0.30 * cons_metric)
    note_stats['mastery_score'] = mastery
    return mastery

def get_dynamic_tolerance(note_name: str) -> float:
    if note_name not in NOTE_STATS: return BASE_PITCH_TOLERANCE_CENTS
    score = NOTE_STATS[note_name]['mastery_score']
    tol = BASE_PITCH_TOLERANCE_CENTS - (score * (BASE_PITCH_TOLERANCE_CENTS - MIN_PITCH_TOLERANCE_CENTS))
    return max(MIN_PITCH_TOLERANCE_CENTS, tol)

def determine_next_note_ai(current_note: str) -> str:
    global ACTIVE_SEQUENCE, MASTERED_NOTES, NOTES_POOL
    
    candidates = []
    for note in NOTES_POOL:
        score = NOTE_STATS.get(note, {}).get('mastery_score', INITIAL_MASTERY_SCORE)
        if score < MASTERY_THRESHOLD:
            s = calculate_mastery_score(NOTE_STATS[note])
            candidates.append((note, s))
            
    if candidates:
        candidates.sort(key=lambda item: item[1])
        selected = candidates[0][0]
        
        ACTIVE_SEQUENCE = [c[0] for c in candidates]
        MASTERED_NOTES = [n for n in NOTES_POOL if n not in ACTIVE_SEQUENCE]
        
        return selected
        
    if NOTES_POOL:
        all_notes_scores = []
        for note in NOTES_POOL:
             s = calculate_mastery_score(NOTE_STATS.get(note, {}))
             all_notes_scores.append((note, s))
        
        all_notes_scores.sort(key=lambda item: item[1]) 
        
        ACTIVE_SEQUENCE = list(NOTES_POOL)
        MASTERED_NOTES = list(NOTES_POOL)
        
        print("INFO: All notes highly mastered (>85%). Switching to continuous review.")
        return all_notes_scores[0][0]
             
    return "N/A"

def update_stats_only(current_note: str, success: bool, cents_error: float) -> None:
    global NOTE_STATS, user_selected_note, user_selection_end_time
    if current_note not in NOTE_STATS: return
    stats = NOTE_STATS[current_note]
    stats['cents_history'].append(cents_error)
    
    if success:
        stats['successes'] += 1
        stats['failures'] = 0 
        if current_note == user_selected_note:
            user_selected_note = None
            user_selection_end_time = time.time() - 1 
    else:
        stats['failures'] += 1
        stats['successes'] = 0 
        
    calculate_mastery_score(stats) 

def process_progression_queue() -> None:
    global progression_queue, current_target_note, success_lock
    if not progression_queue: return
    if success_lock: return

    note, success, cents = progression_queue.pop(0)
    update_stats_only(note, success, cents)
    
    if success and note == current_target_note:
        if user_selected_note is None and NOTES_POOL:
            current_target_note = determine_next_note_ai(note) 
            print(f"PROGRESS: Target changed from {note} to {current_target_note}")

# --- UI Drawing ---

def generate_beep(freq=440, dur=0.1):
    sample_rate = 44100
    n_samples = int(dur * sample_rate)
    buf = np.zeros((n_samples, 2), dtype=np.int16)
    max_sample = 2**(16 - 1) - 1
    for s in range(n_samples):
        t = float(s) / sample_rate
        val = math.sin(2 * math.pi * freq * t)
        fade = 1.0 - (s / n_samples)
        sample = int(max_sample * val * fade * 0.5)
        buf[s][0] = sample 
        buf[s][1] = sample 
    sound = pygame.mixer.Sound(buf)
    sound.set_volume(0.5)
    return sound

WHITE_KEY_NOTES: List[str] = []
for octave in range(3, 6): 
    WHITE_KEY_NOTES.extend([f"{n}{octave}" for n in ["C", "D", "E", "F", "G", "A", "B"]])
WHITE_KEY_NOTES.append("C6") 
NUM_WHITE_KEYS: int = len(WHITE_KEY_NOTES) 

def draw_interactive_button(screen, rect, text, is_active, font, custom_color=None, mouse_pos=(0,0)):
    is_hovered = rect.collidepoint(mouse_pos)
    base_color = custom_color if custom_color else (TARGET_ZONE if is_active else BG_PANEL)
    
    if is_hovered:
        display_color = (min(255, base_color[0]+40), min(255, base_color[1]+40), min(255, base_color[2]+40))
        border_color = GLOW_COLOR
    else:
        display_color = base_color
        border_color = TARGET_ZONE if not custom_color else base_color

    if rect.width > 0 and rect.height > 0:
        shadow_rect = rect.copy()
        shadow_rect.x += 2
        shadow_rect.y += 2
        pygame.draw.rect(screen, (10, 10, 10), shadow_rect, border_radius=8)
        pygame.draw.rect(screen, display_color, rect, border_radius=8)
        pygame.draw.rect(screen, border_color, rect, 2 if is_active else 1, border_radius=8)
        
        text_color = BG_DARK if (is_active or is_hovered) and not custom_color else TEXT_LIGHT
        if custom_color and is_active: text_color = BG_DARK
        
        text_surf = font.render(text, True, text_color)
        text_rect = text_surf.get_rect(center=rect.center)
        screen.blit(text_surf, text_rect)

def draw_stats_overlay(width, height, mouse_pos):
    if width < 500 or height < 500: return
    
    cw = max(50, min(600, width - 40))
    ch = max(50, min(500, height - 40))
    cx, cy = width//2, height//2
    rect = pygame.Rect(cx - cw//2, cy - ch//2, cw, ch)
    
    overlay = pygame.Surface((width, height))
    overlay.set_alpha(230)
    overlay.fill(BG_DARK)
    screen.blit(overlay, (0,0))
    
    pygame.draw.rect(screen, BG_PANEL, rect, border_radius=15)
    pygame.draw.rect(screen, GLOW_COLOR, rect, 2, border_radius=15)
    
    t_surf = font_large.render("Performance Stats", True, TEXT_LIGHT)
    t_rect = t_surf.get_rect(center=(cx, rect.top + 40))
    screen.blit(t_surf, t_rect)
    
    start_x = rect.left + 50
    start_y = rect.top + 90
    pygame.draw.line(screen, (100,100,100), (start_x, start_y), (rect.right - 50, start_y), 2)
    
    headers = ["Note", "Mastery", "Success Rate", "Status"]
    col_widths = [80, 150, 120, 100]
    
    cur_x = start_x
    for i, h in enumerate(headers):
        s = font_small.render(h, True, NEEDLE_ACTIVE)
        screen.blit(s, (cur_x, start_y - 25))
        cur_x += col_widths[i]
        
    y_off = start_y + 15
    sorted_notes = sorted(NOTES_POOL, key=lambda n: (NOTE_STATS.get(n,{}).get('mastery_score',0) >= MASTERY_THRESHOLD, NOTE_STATS.get(n,{}).get('mastery_score',0)))
    
    for note in sorted_notes:
        if note not in NOTE_STATS: continue
        stats = NOTE_STATS[note]
        score = stats.get('mastery_score', 0.0)
        total = stats['successes'] + stats['failures']
        rate = (stats['successes'] / total * 100) if total > 0 else 0
        
        is_mastered = score >= MASTERY_THRESHOLD
        row_color = SUCCESS_GREEN if is_mastered else TEXT_LIGHT
        if score < 0.4 and not is_mastered: row_color = (255, 150, 150)
        
        cur_x = start_x
        screen.blit(font_small.render(note, True, row_color), (cur_x, y_off))
        cur_x += col_widths[0]
        
        bar_w = 100
        bar_h = 10
        pygame.draw.rect(screen, (50,50,50), (cur_x, y_off+5, bar_w, bar_h))
        fill_w = int(bar_w * score)
        col_bar = SUCCESS_GREEN if score >= MASTERY_THRESHOLD else (NEEDLE_ACTIVE if score > 0.4 else ERROR_RED)
        pygame.draw.rect(screen, col_bar, (cur_x, y_off+5, fill_w, bar_h))
        screen.blit(font_small.render(f"{score:.2f}", True, TEXT_LIGHT), (cur_x + bar_w + 10, y_off))
        cur_x += col_widths[1]
        
        screen.blit(font_small.render(f"{rate:.0f}%", True, TEXT_LIGHT), (cur_x, y_off))
        cur_x += col_widths[2]
        
        st_txt = "Mastered" if is_mastered else "Learning"
        screen.blit(font_small.render(st_txt, True, row_color), (cur_x, y_off))
        
        y_off += 30
        if y_off > rect.bottom - 60: break 
        
    close_rect = pygame.Rect(cx - 50, rect.bottom - 50, 100, 35)
    draw_interactive_button(screen, close_rect, "CLOSE", True, font_medium, ERROR_RED, mouse_pos)
    UI_ELEMENTS['stats_close'] = close_rect

def get_clicked_note(x: int, y: int, width: int, height: int) -> str | None:
    key_w = max(1, width // NUM_WHITE_KEYS) 
    kb_y_ratio = 0.75
    key_h = max(1, height - int(height * kb_y_ratio))
    kb_y = height - key_h
    bk_w = max(1, int(key_w * 0.6))
    bk_h = max(1, int(key_h * 0.6))

    detected_midi = -1

    if y >= kb_y and y < kb_y + bk_h:
        for i, white_name in enumerate(WHITE_KEY_NOTES):
            if white_name[0] in ["C", "D", "F", "G", "A"]:
                x_white = i * key_w
                x_black = int(x_white + key_w - (bk_w // 2))
                rect = pygame.Rect(x_black, kb_y, bk_w, bk_h)
                if rect.collidepoint(x, y):
                    sharp_name = white_name[0] + '#' + white_name[-1]
                    detected_midi = KEY_MIDI_MAP.get(sharp_name, -1)
                    break

    if detected_midi == -1 and y >= kb_y:
        idx = x // key_w
        if 0 <= idx < NUM_WHITE_KEYS:
            white_name = WHITE_KEY_NOTES[idx]
            is_near_bk = False
            if white_name[0] in ["C", "D", "F", "G", "A"] and idx < NUM_WHITE_KEYS - 1:
                 x_start = idx * key_w
                 bk_start = int(x_start + key_w - (bk_w // 2))
                 if y < kb_y + bk_h and (bk_start < x < bk_start + bk_w): is_near_bk = True
            if white_name[0] in ["D", "E", "G", "A", "B"] and idx > 0:
                 x_prev = (idx - 1) * key_w
                 bk_prev = int(x_prev + key_w - (bk_w // 2))
                 if y < kb_y + bk_h and (bk_prev < x < bk_prev + bk_w): is_near_bk = True
            
            if not is_near_bk:
                detected_midi = KEY_MIDI_MAP.get(white_name, -1)

    if detected_midi != -1:
        if detected_midi in NOTES_POOL_MIDIS:
            return NOTES_POOL_MIDIS[detected_midi] 
        for n, m in KEY_MIDI_MAP.items():
            if m == detected_midi: return n
    return None

def draw_piano_keyboard(detected_note_str: str, target_note_str: str, width: int, height: int, mouse_pos):
    if screen is None: return
    
    target_midi = -1
    detected_midi = -1
    
    if target_note_str != "N/A" and target_note_str != "DONE":
        try: target_midi = m21pitch.Pitch(target_note_str).midi
        except: pass
        
    if detected_note_str and detected_note_str not in ["N/A", "No Sound", "Too Quiet", "Mic OFF", "Error", "No Pitch"]:
        try: detected_midi = m21pitch.Pitch(detected_note_str).midi
        except: pass

    hovered_note_name = get_clicked_note(mouse_pos[0], mouse_pos[1], width, height)
    hovered_midi = -1
    if hovered_note_name:
        try: hovered_midi = m21pitch.Pitch(hovered_note_name).midi
        except: pass
    
    key_w = max(1, width // NUM_WHITE_KEYS)
    kb_y_ratio = 0.75 
    key_h = max(1, height - int(height * kb_y_ratio)) 
    kb_y = height - key_h
    bk_w = max(1, int(key_w * 0.6)) 
    bk_h = max(1, int(key_h * 0.6))
    white_key_draw_w = max(1, key_w - 2)

    pygame.draw.rect(screen, (30, 30, 30), (0, kb_y - 5, width, key_h + 5))

    for i, name in enumerate(WHITE_KEY_NOTES):
        x = i * key_w
        rect = pygame.Rect(x + 1, kb_y, white_key_draw_w, key_h)
        midi = KEY_MIDI_MAP.get(name, -1)
        
        color = KEY_WHITE
        is_in_pool = midi in NOTES_POOL_MIDIS
        
        if is_in_pool: color = (200, 200, 200)
        if midi == target_midi: color = TARGET_ZONE
        if midi == detected_midi:
            color = NEEDLE_ACTIVE
            if midi == target_midi: color = SUCCESS_GREEN
        if midi == hovered_midi and is_in_pool:
             color = (min(255, color[0]+40), min(255, color[1]+40), min(255, color[2]+40))

        pygame.draw.rect(screen, color, rect, border_bottom_left_radius=5, border_bottom_right_radius=5)
        if font_small and name.startswith('C'):
            ts = font_small.render(name, True, KEY_BLACK)
            tr = ts.get_rect(center=(x + key_w // 2, height - 15))
            screen.blit(ts, tr)

    for i, name in enumerate(WHITE_KEY_NOTES):
        if name[0] in ["C", "D", "F", "G", "A"]:
            sharp_name = name[0] + '#' + name[-1]
            midi = KEY_MIDI_MAP.get(sharp_name, -1)
            x_white = i * key_w
            x_black = int(x_white + key_w - (bk_w // 2))
            rect = pygame.Rect(x_black, kb_y, bk_w, bk_h)
            
            color = KEY_BLACK
            is_in_pool = midi in NOTES_POOL_MIDIS
            if is_in_pool: color = (60, 60, 70)
            if midi == target_midi: color = TARGET_ZONE
            if midi == detected_midi:
                color = NEEDLE_ACTIVE
                if midi == target_midi: color = SUCCESS_GREEN
            if midi == hovered_midi and is_in_pool:
                color = (min(120, color[0]+30), min(120, color[1]+30), min(120, color[2]+30))
                
            pygame.draw.rect(screen, color, rect, border_bottom_left_radius=4, border_bottom_right_radius=4)
            pygame.draw.rect(screen, (100,100,100), rect, 1, border_bottom_left_radius=4, border_bottom_right_radius=4)

def draw_interface():
    global screen, particles, show_stats_overlay, font_target, font_large, font_medium, font_small
    if screen is None: return
    
    w, h = screen.get_size()
    
    # CRITICAL: Prevent drawing on crushed window
    if w < 50 or h < 50: 
        screen.fill(BG_DARK)
        pygame.display.flip()
        return
    
    curr_time = time.time()
    mouse = pygame.mouse.get_pos()
    
    font_target = pygame.font.SysFont('Arial', max(10, int(h * 0.15)), bold=True)
    font_large = pygame.font.SysFont('Arial', max(10, int(h * 0.05)), bold=True)
    font_medium = pygame.font.SysFont('Arial', max(10, int(h * 0.035)))
    font_small = pygame.font.SysFont('Arial', max(10, int(h * 0.02)))
    
    process_progression_queue() 

    screen.fill(BG_DARK)
    
    if curr_time < error_visual_time:
        s = pygame.Surface((w, h)); s.set_alpha(60); s.fill(ERROR_RED)
        screen.blit(s, (0,0))
    elif curr_time < success_visual_time:
        s = pygame.Surface((w, h)); s.set_alpha(60); s.fill(SUCCESS_GREEN)
        screen.blit(s, (0,0))
        for p in particles[:]:
            p.update(); p.draw(screen)
            if p.life <= 0: particles.remove(p)
    else: particles = []

    if user_selected_note:
        tgt = user_selected_note
        mode = f"Manual ({max(0, user_selection_end_time - curr_time):.1f}s)"
    elif current_target_note != "N/A":
        tgt = current_target_note
        mode = "Continuous Review Mode" if len(ACTIVE_SEQUENCE) == len(NOTES_POOL) and len(NOTES_POOL) > 0 else "Adaptive AI Mode"
    else:
        tgt = "DONE"
        mode = "Loading or No Scale Selected"

    PANEL_H = min(140, h - 200) 
    pygame.draw.rect(screen, BG_PANEL, (0, 0, w, PANEL_H))
    pygame.draw.line(screen, (60,60,80), (0, PANEL_H), (w, PANEL_H), 2)
    
    if font_medium:
        screen.blit(font_medium.render(mode, True, NEEDLE_ACTIVE), (20, 15))
        tr = font_medium.render(f"{current_tonic} {current_scale_type}", True, TEXT_LIGHT).get_rect(topright=(w-20, 15))
        screen.blit(font_medium.render(f"{current_tonic} {current_scale_type}", True, TEXT_LIGHT), tr)

    btn_w, btn_h, start_y = 45, 35, 55
    if w > 600:
        for i, tonic in enumerate(TONIC_NOTES):
            r = pygame.Rect(20 + i*(btn_w+5), start_y, btn_w, btn_h)
            draw_interactive_button(screen, r, tonic, tonic==current_tonic, font_small, mouse_pos=mouse)
            UI_ELEMENTS[f'tonic_{tonic}'] = r
        type_x = w - 160
        for i, st in enumerate(SCALE_TYPES):
            r = pygame.Rect(type_x + i*80, start_y, 75, btn_h)
            draw_interactive_button(screen, r, st, st==current_scale_type, font_small, mouse_pos=mouse)
            UI_ELEMENTS[f'scale_{st}'] = r
        
    mic_r = pygame.Rect(20, start_y + btn_h + 10, 100, 30)
    mtxt = "MIC ON" if is_mic_active else "MIC OFF"
    mcol = SUCCESS_GREEN if is_mic_active else MIC_OFF_COLOR
    draw_interactive_button(screen, mic_r, mtxt, True, font_small, mcol, mouse)
    UI_ELEMENTS['mic'] = mic_r

    stats_r = pygame.Rect(130, start_y + btn_h + 10, 80, 30)
    draw_interactive_button(screen, stats_r, "STATS", show_stats_overlay, font_small, GLOW_COLOR if show_stats_overlay else None, mouse)
    UI_ELEMENTS['stats_btn'] = stats_r

    if NOTES_POOL:
        perc = len(MASTERED_NOTES) / len(NOTES_POOL) if len(NOTES_POOL) > 0 else 1.0
        py = PANEL_H - 15
        pygame.draw.rect(screen, (30,30,30), (0, py, w, 10))
        pygame.draw.rect(screen, SUCCESS_GREEN, (0, py, int(w*perc), 10))
    
    cy = PANEL_H + 20 + int(h * 0.08)
    pulse = math.sin(curr_time * 5) * 5
    fp = pygame.font.SysFont('Arial', max(1, int(h*0.15)+int(pulse)), bold=True)
    
    tt = fp.render(tgt, True, TARGET_ZONE)
    ttr = tt.get_rect(center=(w//2, cy))
    screen.blit(fp.render(tgt, True, (10,10,20)), (ttr.x+4, ttr.y+4))
    screen.blit(tt, ttr)
    
    if tgt in NOTE_STATS and font_medium:
        sc = NOTE_STATS[tgt]['mastery_score']
        tol = get_dynamic_tolerance(tgt)
        info_str = f"Mastery: {sc:.2f} | Required Accuracy: +/-{int(tol)} cents"
        st = font_small.render(info_str, True, (200, 200, 220))
        screen.blit(st, st.get_rect(center=(w//2, cy+70)))

    if font_large:
        dn = last_detected_note_name
        dc = NEEDLE_ACTIVE
        if dn == "Too Quiet": dn, dc = "Sing Louder...", (100,100,120)
        elif dn == "Mic OFF": dn, dc = "Paused", MIC_OFF_COLOR
        
        dt = font_large.render(dn, True, dc)
        dy = cy + 130
        screen.blit(dt, dt.get_rect(center=(w//2, dy)))
        
        if octave_offset_str and font_small:
             oct_col = (150, 200, 255) if "Higher" in octave_offset_str else (255, 150, 150)
             ot = font_small.render(octave_offset_str, True, oct_col)
             screen.blit(ot, ot.get_rect(center=(w//2, dy + 35)))
        
        # --- FIXED METER DRAWING LOGIC (Using ints) ---
        my = dy + 60
        mw = max(100, w - int(w * 0.3))
        mx = int((w - mw) / 2)
        cx = mx + mw // 2
        
        # Background
        pygame.draw.rect(screen, (30,30,40), (mx, my, mw, 20), border_radius=10)
        pygame.draw.circle(screen, TEXT_LIGHT, (cx, my+10), 5)
        
        global smooth_cents_error
        smooth_cents_error += (last_cents_error - smooth_cents_error) * 0.15
        vis_val = max(-50, min(50, smooth_cents_error))
        
        nx = int(cx + (vis_val/50.0)*(mw/2))
        nc = SUCCESS_GREEN if abs(last_cents_error) < current_target_tolerance else ERROR_RED
        
        # Needle
        pygame.draw.line(screen, nc, (nx, my-10), (nx, my+30), 4)
        pygame.draw.circle(screen, nc, (nx, my+30), 6)
        
        # Target Zone (CRASH FIX: Forced to int)
        tol_w_float = (current_target_tolerance / 50.0) * (mw / 2)
        tol_w_int = max(1, int(tol_w_float)) 
        
        zone_rect = pygame.Rect(int(cx - tol_w_int), int(my), int(tol_w_int * 2), 20)
        pygame.draw.rect(screen, (0, 100, 0), zone_rect, 1)
        
        if font_small:
            screen.blit(font_small.render(f"{smooth_cents_error:+.1f}", True, nc), (nx-15, my+40))

    draw_piano_keyboard(last_detected_note_name, tgt, w, h, mouse)
    if show_stats_overlay: draw_stats_overlay(w, h, mouse)
        
    pygame.display.flip()

# --- Audio & Event Loop ---

def audio_callback(in_data, frame_count, time_info, status):
    global last_detected_note_name, last_cents_error, is_in_tune, correct_hold_start_time
    global incorrect_hold_start_time, error_visual_time, user_selected_note
    global user_selection_end_time, octave_offset_str, current_target_tolerance, current_target_note
    global success_lock, progression_queue, success_visual_time

    now = time.time()
    
    if user_selected_note and now > user_selection_end_time: user_selected_note = None
    
    tgt = user_selected_note if user_selected_note else current_target_note
    if tgt == "N/A" or tgt == "DONE" or not is_mic_active: 
        success_lock = False
        correct_hold_start_time = 0.0
        incorrect_hold_start_time = 0.0
        if not is_mic_active: last_detected_note_name = "Mic OFF"
        return (in_data, pyaudio.paContinue)

    data = np.frombuffer(in_data, dtype=np.float32)
    rms = np.sqrt(np.mean(data**2))
    current_target_tolerance = get_dynamic_tolerance(tgt)
    
    if rms < VOLUME_THRESHOLD_RMS:
        last_detected_note_name = "Too Quiet"
        last_cents_error = 0
        correct_hold_start_time = 0.0
        octave_offset_str = ""
        success_lock = False 
        return (in_data, pyaudio.paContinue)

    pit = pitch_o(data)[0]
    if pit > 0:
        try:
            det_obj = m21pitch.Pitch(); det_obj.frequency = float(pit) 
            last_detected_note_name = det_obj.nameWithOctave
            
            tgt_pitch = m21pitch.Pitch(tgt)
            tgt_freq = tgt_pitch.frequency
            
            cents = 1200 * np.log2(pit / tgt_freq)
            
            raw_octave_diff = round(cents / 1200.0)
            if raw_octave_diff > 0: octave_offset_str = f"Higher (+{int(raw_octave_diff)} Oct)"
            elif raw_octave_diff < 0: octave_offset_str = f"Lower ({int(raw_octave_diff)} Oct)"
            else: octave_offset_str = "Correct Octave"

            last_cents_error = cents - (raw_octave_diff * 1200)
            distance_to_tune = abs(last_cents_error)

            if abs(last_cents_error) < current_target_tolerance:
                is_in_tune = True
                incorrect_hold_start_time = 0.0
                
                if not success_lock:
                    if correct_hold_start_time == 0.0: correct_hold_start_time = now
                    
                    if now - correct_hold_start_time >= SUCCESS_HOLD_TIME:
                        progression_queue.append((tgt, True, distance_to_tune))
                        success_visual_time = now + 0.5
                        if screen: spawn_particles(screen.get_width()//2, screen.get_height()//2)
                        
                        correct_hold_start_time = 0.0
                        success_lock = True 
                
            else:
                is_in_tune = False
                correct_hold_start_time = 0.0
                success_lock = False 
                
                if incorrect_hold_start_time == 0.0: incorrect_hold_start_time = now
                if now - incorrect_hold_start_time >= FAILURE_GRACE_TIME:
                    if now > error_visual_time:
                        error_visual_time = now + 0.3
                        if error_buzzer_sound: error_buzzer_sound.play()
                        if not progression_queue:
                             progression_queue.append((tgt, False, distance_to_tune))
                        incorrect_hold_start_time = 0.0
        except Exception as e:
            last_detected_note_name = "Error"
            last_cents_error = 0
            correct_hold_start_time = 0.0
            success_lock = False
    else:
        last_detected_note_name = "No Pitch"
        last_cents_error = 0
        correct_hold_start_time = 0.0
        octave_offset_str = ""
        success_lock = False 
        
    return (in_data, pyaudio.paContinue)

def handle_click(pos):
    global current_tonic, current_scale_type, is_mic_active, user_selected_note, user_selection_end_time
    global show_stats_overlay
    x, y = pos
    
    if show_stats_overlay:
        if UI_ELEMENTS.get('stats_close', pygame.Rect(0,0,0,0)).collidepoint(x,y):
            show_stats_overlay = False
        return

    if UI_ELEMENTS.get('mic', pygame.Rect(0,0,0,0)).collidepoint(x,y):
        is_mic_active = not is_mic_active
        return

    if UI_ELEMENTS.get('stats_btn', pygame.Rect(0,0,0,0)).collidepoint(x,y):
        show_stats_overlay = True
        return

    for t in TONIC_NOTES:
        if UI_ELEMENTS.get(f'tonic_{t}', pygame.Rect(0,0,0,0)).collidepoint(x,y):
            if t != current_tonic: initialize_or_update_note_pool(t, current_scale_type)
            return
            
    for s in SCALE_TYPES:
        if UI_ELEMENTS.get(f'scale_{s}', pygame.Rect(0,0,0,0)).collidepoint(x,y):
            if s != current_scale_type: initialize_or_update_note_pool(current_tonic, s)
            return
            
    w, h = pygame.display.get_surface().get_size()
    clicked = get_clicked_note(x, y, w, h)
    if clicked:
        user_selected_note = clicked
        user_selection_end_time = time.time() + user_selection_duration
        print(f"Manual Select: {clicked}")

def main():
    global font_target, screen, error_buzzer_sound
    pygame.init()
    pygame.mixer.init()
    
    screen = pygame.display.set_mode((1000, 700), pygame.RESIZABLE)
    pygame.display.set_caption("Pitch Trainer Fixed v7 (Float to Int Fix)")
    pygame.font.init()
    
    try: error_buzzer_sound = generate_beep(500, 0.15)
    except: pass
    
    initialize_or_update_note_pool("C", "Major") 
    
    try:
        stream = p.open(format=FORMAT, channels=CHANNELS, rate=RATE, input=True, 
                       frames_per_buffer=BUFFER_SIZE, stream_callback=audio_callback)
        stream.start_stream()
        
        running = True
        while running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT: running = False
                if event.type == pygame.VIDEORESIZE:
                    screen = pygame.display.set_mode((event.w, event.h), pygame.RESIZABLE)
                if event.type == pygame.MOUSEBUTTONDOWN:
                    handle_click(event.pos)
            
            draw_interface()
            pygame.time.Clock().tick(60)
            
    except Exception as e:
        print(f"FATAL ERROR: {e}")
        time.sleep(5)
    finally:
        if 'stream' in locals() and stream is not None and stream.is_active(): stream.stop_stream(); stream.close()
        p.terminate()
        pygame.quit()

if __name__ == "__main__":
    main()