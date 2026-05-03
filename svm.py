import os
import sys
import subprocess
import requests
import flask
from flask import Flask, render_template, request, jsonify, redirect, url_for, send_file, session, flash
from flask_socketio import SocketIO, emit, join_room, leave_room
from flask_login import LoginManager, UserMixin, login_user, login_required, logout_user, current_user
import random
import string
import json
import datetime
from datetime import timedelta
import time
import logging
import socket
import paramiko
import traceback
import shutil
import sqlite3
import threading
from dotenv import load_dotenv
from functools import wraps
from werkzeug.security import generate_password_hash, check_password_hash
import psutil
import pty
import select
import termios
import tty
import fcntl
import struct
import signal
import uuid
import csv
import io
from werkzeug.utils import secure_filename
import tarfile
from io import BytesIO
import smtplib
from email.mime.text import MIMEText
from collections import deque
import shlex
import re

# Base directories
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "svm_data")
LOG_DIR = os.path.join(BASE_DIR, "logs")
UPLOAD_FOLDER = os.path.join(BASE_DIR, 'uploads')

for directory in [DATA_DIR, LOG_DIR, UPLOAD_FOLDER]:
    try:
        os.makedirs(directory, exist_ok=True)
        print(f"✅ Created directory: {directory}")
    except Exception as e:
        print(f"❌ Failed to create directory {directory}: {e}")
        sys.exit(1)

log_file = os.path.join(LOG_DIR, 'svm_panel.log')
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(log_file),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger('SVMPanel')

load_dotenv()

SECRET_KEY = os.getenv('SECRET_KEY', ''.join(random.choices(string.ascii_letters + string.digits, k=32)))
ADMIN_USERNAME = os.getenv('ADMIN_USERNAME', 'admin')
ADMIN_PASSWORD = os.getenv('ADMIN_PASSWORD', 'admin')
PANEL_NAME = os.getenv('PANEL_NAME', 'SVM PANEL')
WATERMARK = os.getenv('WATERMARK', 'SVM VPS Service')
WELCOME_MESSAGE = os.getenv('WELCOME_MESSAGE', 'Welcome to SVM PANEL! Power Your Future!')
MAX_VPS_PER_USER = int(os.getenv('MAX_VPS_PER_USER', '999'))
DEFAULT_OS_IMAGE = os.getenv('DEFAULT_OS_IMAGE', 'ubuntu:22.04')
MAX_CONTAINERS = int(os.getenv('MAX_CONTAINERS', '1000'))
DB_FILE = os.path.join(BASE_DIR, 'svm_panel.db')
BACKUP_FILE = os.path.join(BASE_DIR, 'svm_panel_backup.json')
SERVER_IP = os.getenv('SERVER_IP', socket.gethostbyname(socket.gethostname()))
SERVER_PORT = int(os.getenv('SERVER_PORT', '3000'))
DEBUG = os.getenv('DEBUG', 'False').lower() == 'true'
ALLOWED_EXTENSIONS = {'tar', 'gz', 'iso'}
VPS_HOSTNAME_PREFIX = os.getenv('VPS_HOSTNAME_PREFIX', 'svm-')
OVERCOMMIT_RATIO = float(os.getenv('OVERCOMMIT_RATIO', '10.0'))
BACKUP_SCHEDULE = os.getenv('BACKUP_SCHEDULE', 'daily')

# LXC specific settings
DEFAULT_STORAGE_POOL = os.getenv('DEFAULT_STORAGE_POOL', 'default')
CPU_THRESHOLD = int(os.getenv('CPU_THRESHOLD', '90'))
RAM_THRESHOLD = int(os.getenv('RAM_THRESHOLD', '90'))
CHECK_INTERVAL = int(os.getenv('CHECK_INTERVAL', '600'))

MINER_PATTERNS = [
    'xmrig', 'ethminer', 'cgminer', 'sgminer', 'bfgminer',
    'minerd', 'cpuminer', 'cryptonight', 'stratum', 'nicehash', 'miner',
    'xmr-stak', 'ccminer', 'ewbf', 'lolminer', 'trex', 'nanominer'
]

app = Flask(__name__)
app.config['SECRET_KEY'] = SECRET_KEY
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['SESSION_TYPE'] = 'filesystem'
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=7)
app.config['MAX_CONTENT_LENGTH'] = 100 * 1024 * 1024

socketio = SocketIO(app, async_mode='threading', cors_allowed_origins="*", ping_timeout=60, ping_interval=25)

login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = 'login'
login_manager.login_message = "Please log in to access this page."

class User(UserMixin):
    def __init__(self, id, username, role='user', email=None, theme='light'):
        self.id = str(id)
        self.username = username
        self.role = role
        self.email = email
        self.theme = theme
    
    def get_id(self):
        return str(self.id)

class Database:
    def __init__(self, db_file):
        self.db_file = db_file
        self.lock = threading.Lock()
        self.conn = None
        self.cursor = None
        self._connect()
        self._create_tables()
        self._initialize_settings()
        self._migrate_database()

    def _connect(self):
        self.conn = sqlite3.connect(self.db_file, check_same_thread=False, timeout=30)
        self.conn.row_factory = sqlite3.Row
        self.cursor = self.conn.cursor()

    def _execute(self, query, params=()):
        with self.lock:
            for attempt in range(3):
                try:
                    self.cursor.execute(query, params)
                    self.conn.commit()
                    return
                except sqlite3.OperationalError as e:
                    if "database is locked" in str(e) and attempt < 2:
                        time.sleep(0.2)
                    else:
                        raise
                except Exception as e:
                    logger.error(f"Database error: {e}")
                    raise

    def _fetchone(self, query, params=()):
        with self.lock:
            self.cursor.execute(query, params)
            row = self.cursor.fetchone()
            return dict(row) if row else None

    def _fetchall(self, query, params=()):
        with self.lock:
            self.cursor.execute(query, params)
            rows = self.cursor.fetchall()
            return [dict(row) for row in rows]

    def _create_tables(self):
        self._execute('''
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE,
                password TEXT,
                role TEXT DEFAULT 'user',
                email TEXT,
                created_at TEXT,
                theme TEXT DEFAULT 'light'
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS vps_instances (
                token TEXT PRIMARY KEY,
                vps_id TEXT UNIQUE,
                container_name TEXT,
                hostname TEXT,
                memory INTEGER,
                cpu INTEGER,
                disk INTEGER,
                bandwidth_limit INTEGER DEFAULT 0,
                username TEXT,
                password TEXT,
                root_password TEXT,
                created_by INTEGER,
                created_at TEXT,
                tmate_session TEXT,
                tmate_web TEXT,
                tmate_ssh TEXT,
                watermark TEXT,
                os_image TEXT,
                restart_count INTEGER DEFAULT 0,
                last_restart TEXT,
                status TEXT DEFAULT 'running',
                port INTEGER DEFAULT 22,
                expires_at TEXT,
                expires_days INTEGER DEFAULT 30,
                expires_hours INTEGER DEFAULT 0,
                expires_minutes INTEGER DEFAULT 0,
                additional_ports TEXT DEFAULT '',
                uptime_start TEXT,
                tags TEXT DEFAULT '',
                data_path TEXT,
                last_verified TEXT,
                suspended BOOLEAN DEFAULT 0,
                suspension_history TEXT DEFAULT '[]',
                shared_with TEXT DEFAULT '[]',
                config TEXT,
                FOREIGN KEY (created_by) REFERENCES users (id)
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS usage_stats (
                key TEXT PRIMARY KEY,
                value INTEGER DEFAULT 0
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS system_settings (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS banned_users (
                user_id INTEGER PRIMARY KEY,
                FOREIGN KEY (user_id) REFERENCES users (id)
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS notifications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                message TEXT,
                created_at TEXT,
                read BOOLEAN DEFAULT FALSE
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS audit_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                action TEXT,
                details TEXT,
                timestamp TEXT
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS resource_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                vps_id TEXT,
                cpu_percent REAL,
                memory_percent REAL,
                disk_usage REAL,
                bandwidth_in REAL,
                bandwidth_out REAL,
                timestamp TEXT
            )
        ''')

        self._execute('''
            CREATE TABLE IF NOT EXISTS referrals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                referral_code TEXT UNIQUE,
                referred_users INTEGER DEFAULT 0,
                FOREIGN KEY (user_id) REFERENCES users (id)
            )
        ''')

    def _migrate_database(self):
        try:
            columns = [col['name'] for col in self._fetchall("PRAGMA table_info(vps_instances)")]
           
            if 'uptime_start' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN uptime_start TEXT')
           
            if 'additional_ports' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN additional_ports TEXT DEFAULT ""')
           
            if 'expires_days' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN expires_days INTEGER DEFAULT 30')
           
            if 'expires_hours' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN expires_hours INTEGER DEFAULT 0')
           
            if 'expires_minutes' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN expires_minutes INTEGER DEFAULT 0')
           
            if 'bandwidth_limit' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN bandwidth_limit INTEGER DEFAULT 0')
           
            if 'tags' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN tags TEXT DEFAULT ""')
            
            if 'data_path' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN data_path TEXT')
            
            if 'last_verified' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN last_verified TEXT')
            
            if 'tmate_web' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN tmate_web TEXT')
            
            if 'tmate_ssh' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN tmate_ssh TEXT')
            
            if 'suspended' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN suspended BOOLEAN DEFAULT 0')
            
            if 'suspension_history' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN suspension_history TEXT DEFAULT "[]"')
            
            if 'shared_with' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN shared_with TEXT DEFAULT "[]"')
            
            if 'config' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN config TEXT')
            
            if 'hostname' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN hostname TEXT')
            
            if 'port' not in columns:
                self._execute('ALTER TABLE vps_instances ADD COLUMN port INTEGER DEFAULT 22')
           
            user_columns = [col['name'] for col in self._fetchall("PRAGMA table_info(users)")]
            if 'email' not in user_columns:
                self._execute('ALTER TABLE users ADD COLUMN email TEXT')
            if 'theme' not in user_columns:
                self._execute('ALTER TABLE users ADD COLUMN theme TEXT DEFAULT "light"')
        except Exception as e:
            logger.error(f"Migration error: {e}")

    def _initialize_settings(self):
        defaults = {
            'max_containers': str(MAX_CONTAINERS),
            'max_vps_per_user': str(MAX_VPS_PER_USER),
            'panel_name': PANEL_NAME,
            'watermark': WATERMARK,
            'welcome_message': WELCOME_MESSAGE,
            'server_ip': SERVER_IP,
            'vps_hostname_prefix': VPS_HOSTNAME_PREFIX,
            'overcommit_ratio': str(OVERCOMMIT_RATIO),
            'cpu_threshold': str(CPU_THRESHOLD),
            'ram_threshold': str(RAM_THRESHOLD),
            'check_interval': str(CHECK_INTERVAL),
            'default_storage_pool': DEFAULT_STORAGE_POOL,
            'backup_schedule': BACKUP_SCHEDULE
        }
        for key, value in defaults.items():
            self._execute('INSERT OR IGNORE INTO system_settings (key, value) VALUES (?, ?)', (key, value))
       
        admin = self._fetchone('SELECT id FROM users WHERE username = ?', (ADMIN_USERNAME,))
        if not admin:
            hashed = generate_password_hash(ADMIN_PASSWORD)
            self._execute('INSERT INTO users (username, password, role, created_at) VALUES (?, ?, ?, ?)',
                          (ADMIN_USERNAME, hashed, 'admin', str(datetime.datetime.now())))

    def get_setting(self, key, default=None):
        result = self._fetchone('SELECT value FROM system_settings WHERE key = ?', (key,))
        return result['value'] if result else default

    def set_setting(self, key, value):
        self._execute('INSERT OR REPLACE INTO system_settings (key, value) VALUES (?, ?)', (key, str(value)))

    def get_stat(self, key, default=0):
        result = self._fetchone('SELECT value FROM usage_stats WHERE key = ?', (key,))
        return result['value'] if result else default

    def increment_stat(self, key, amount=1):
        current = self.get_stat(key)
        self._execute('INSERT OR REPLACE INTO usage_stats (key, value) VALUES (?, ?)', (key, current + amount))

    def get_user(self, username):
        return self._fetchone('SELECT * FROM users WHERE username = ?', (username,))

    def get_user_by_id(self, user_id):
        return self._fetchone('SELECT * FROM users WHERE id = ?', (user_id,))

    def create_user(self, username, password, role='user', email=None, theme='light'):
        try:
            hashed = generate_password_hash(password)
            self._execute('INSERT INTO users (username, password, role, email, created_at, theme) VALUES (?, ?, ?, ?, ?, ?)',
                          (username, hashed, role, email, str(datetime.datetime.now()), theme))
            return True
        except sqlite3.IntegrityError:
            return False

    def update_user(self, user_id, username=None, password=None, role=None, email=None, theme=None):
        updates = {}
        if username: updates['username'] = username
        if password: updates['password'] = generate_password_hash(password)
        if role: updates['role'] = role
        if email: updates['email'] = email
        if theme: updates['theme'] = theme
        if not updates: return False
        set_clause = ', '.join(f'{k} = ?' for k in updates)
        values = list(updates.values()) + [user_id]
        self._execute(f'UPDATE users SET {set_clause} WHERE id = ?', values)
        return True

    def delete_user(self, user_id):
        self._execute('DELETE FROM users WHERE id = ?', (user_id,))
        return True

    def get_vps_by_id(self, vps_id):
        vps = self._fetchone('SELECT * FROM vps_instances WHERE vps_id = ?', (vps_id,))
        if vps:
            return vps['token'], vps
        return None, None

    def get_vps_by_token(self, token):
        return self._fetchone('SELECT * FROM vps_instances WHERE token = ?', (token,))

    def get_user_vps_count(self, user_id):
        result = self._fetchone('SELECT COUNT(*) as count FROM vps_instances WHERE created_by = ?', (user_id,))
        return result['count'] if result else 0

    def get_user_vps(self, user_id):
        return self._fetchall('SELECT * FROM vps_instances WHERE created_by = ?', (user_id,))

    def get_all_vps(self):
        rows = self._fetchall('SELECT * FROM vps_instances')
        return {row['vps_id']: row for row in rows}

    def add_vps(self, vps_data):
        try:
            columns = list(vps_data.keys())
            placeholders = ', '.join('?' for _ in vps_data)
            sql = f'INSERT INTO vps_instances ({", ".join(columns)}) VALUES ({placeholders})'
            self._execute(sql, tuple(vps_data.values()))
            self.increment_stat('total_vps_created')
            return True
        except Exception as e:
            logger.error(f"Error adding VPS: {e}")
            return False

    def remove_vps(self, token):
        self._execute('DELETE FROM vps_instances WHERE token = ?', (token,))
        return True

    def update_vps(self, token, updates):
        try:
            set_clause = ', '.join(f'{k} = ?' for k in updates)
            values = list(updates.values()) + [token]
            self._execute(f'UPDATE vps_instances SET {set_clause} WHERE token = ?', values)
            return True
        except Exception as e:
            logger.error(f"Error updating VPS: {e}")
            return False

    def is_user_banned(self, user_id):
        return self._fetchone('SELECT 1 FROM banned_users WHERE user_id = ?', (user_id,)) is not None

    def ban_user(self, user_id):
        self._execute('INSERT OR IGNORE INTO banned_users (user_id) VALUES (?)', (user_id,))

    def unban_user(self, user_id):
        self._execute('DELETE FROM banned_users WHERE user_id = ?', (user_id,))

    def get_banned_users(self):
        return [row['user_id'] for row in self._fetchall('SELECT user_id FROM banned_users')]

    def get_all_users(self):
        return self._fetchall('SELECT id, username, role, created_at, email, theme FROM users')

    def update_user_role(self, user_id, role):
        self._execute('UPDATE users SET role = ? WHERE id = ?', (role, user_id))
        return True

    def add_notification(self, user_id, message):
        self._execute('INSERT INTO notifications (user_id, message, created_at) VALUES (?, ?, ?)',
                      (user_id, message, str(datetime.datetime.now())))

    def get_notifications(self, user_id):
        return self._fetchall('SELECT * FROM notifications WHERE user_id = ? ORDER BY created_at DESC', (user_id,))

    def mark_notification_read(self, notif_id):
        self._execute('UPDATE notifications SET read = TRUE WHERE id = ?', (notif_id,))

    def log_action(self, user_id, action, details):
        self._execute('INSERT INTO audit_logs (user_id, action, details, timestamp) VALUES (?, ?, ?, ?)',
                      (user_id, action, details, str(datetime.datetime.now())))

    def get_audit_logs(self, limit=100):
        return self._fetchall('SELECT * FROM audit_logs ORDER BY timestamp DESC LIMIT ?', (limit,))

    def add_resource_history(self, vps_id, cpu, mem, disk, band_in, band_out):
        self._execute('INSERT INTO resource_history (vps_id, cpu_percent, memory_percent, disk_usage, bandwidth_in, bandwidth_out, timestamp) VALUES (?, ?, ?, ?, ?, ?, ?)',
                      (vps_id, cpu, mem, disk, band_in, band_out, str(datetime.datetime.now())))

    def get_resource_history(self, vps_id, limit=100):
        return self._fetchall('SELECT * FROM resource_history WHERE vps_id = ? ORDER BY timestamp DESC LIMIT ?', (vps_id, limit))

    def generate_referral_code(self, user_id):
        code = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))
        self._execute('INSERT INTO referrals (user_id, referral_code) VALUES (?, ?)', (user_id, code))
        return code

    def get_referral_code(self, user_id):
        result = self._fetchone('SELECT referral_code FROM referrals WHERE user_id = ?', (user_id,))
        return result['referral_code'] if result else None

    def increment_referred(self, user_id):
        self._execute('UPDATE referrals SET referred_users = referred_users + 1 WHERE user_id = ?', (user_id,))

    def backup_data(self):
        data = {
            'users': self.get_all_users(),
            'vps_instances': list(self.get_all_vps().values()),
            'usage_stats': {row['key']: row['value'] for row in self._fetchall('SELECT * FROM usage_stats')},
            'system_settings': {row['key']: row['value'] for row in self._fetchall('SELECT * FROM system_settings')},
            'banned_users': self.get_banned_users(),
            'notifications': self._fetchall('SELECT * FROM notifications'),
            'audit_logs': self._fetchall('SELECT * FROM audit_logs'),
            'resource_history': self._fetchall('SELECT * FROM resource_history'),
            'referrals': self._fetchall('SELECT * FROM referrals')
        }
        with open(BACKUP_FILE, 'w') as f:
            json.dump(data, f, indent=4, default=str)
        return True

    def restore_data(self):
        if not os.path.exists(BACKUP_FILE):
            return False
       
        with open(BACKUP_FILE, 'r') as f:
            data = json.load(f)
       
        try:
            self._execute('DELETE FROM users')
            for user in data.get('users', []):
                self._execute('INSERT INTO users (id, username, password, role, email, created_at, theme) VALUES (?, ?, ?, ?, ?, ?, ?)',
                              (user['id'], user['username'], user['password'], user['role'], user.get('email'), user['created_at'], user.get('theme', 'light')))
           
            self._execute('DELETE FROM vps_instances')
            for vps in data.get('vps_instances', []):
                columns = ', '.join(vps.keys())
                placeholders = ', '.join('?' for _ in vps)
                self._execute(f'INSERT INTO vps_instances ({columns}) VALUES ({placeholders})', tuple(vps.values()))
           
            self._execute('DELETE FROM usage_stats')
            for k, v in data.get('usage_stats', {}).items():
                self._execute('INSERT INTO usage_stats (key, value) VALUES (?, ?)', (k, v))
           
            self._execute('DELETE FROM system_settings')
            for k, v in data.get('system_settings', {}).items():
                self._execute('INSERT INTO system_settings (key, value) VALUES (?, ?)', (k, v))
           
            self._execute('DELETE FROM banned_users')
            for uid in data.get('banned_users', []):
                self._execute('INSERT INTO banned_users (user_id) VALUES (?)', (uid,))
           
            self._execute('DELETE FROM notifications')
            for notif in data.get('notifications', []):
                columns = ', '.join(notif.keys())
                placeholders = ', '.join('?' for _ in notif)
                self._execute(f'INSERT INTO notifications ({columns}) VALUES ({placeholders})', tuple(notif.values()))
           
            self._execute('DELETE FROM audit_logs')
            for log in data.get('audit_logs', []):
                columns = ', '.join(log.keys())
                placeholders = ', '.join('?' for _ in log)
                self._execute(f'INSERT INTO audit_logs ({columns}) VALUES ({placeholders})', tuple(log.values()))
           
            self._execute('DELETE FROM resource_history')
            for hist in data.get('resource_history', []):
                columns = ', '.join(hist.keys())
                placeholders = ', '.join('?' for _ in hist)
                self._execute(f'INSERT INTO resource_history ({columns}) VALUES ({placeholders})', tuple(hist.values()))

            self._execute('DELETE FROM referrals')
            for ref in data.get('referrals', []):
                columns = ', '.join(ref.keys())
                placeholders = ', '.join('?' for _ in ref)
                self._execute(f'INSERT INTO referrals ({columns}) VALUES ({placeholders})', tuple(ref.values()))
           
            return True
        except Exception as e:
            logger.error(f"Restore error: {e}")
            return False

    def close(self):
        if self.conn:
            self.conn.close()

db = Database(DB_FILE)

@login_manager.user_loader
def load_user(user_id):
    try:
        user_data = db.get_user_by_id(int(user_id))
        if user_data:
            return User(
                id=user_data['id'],
                username=user_data['username'],
                role=user_data['role'],
                email=user_data.get('email'),
                theme=user_data.get('theme', 'light')
            )
    except Exception as e:
        logger.error(f"Error loading user {user_id}: {e}")
    return None

# LXC helper functions
def check_lxc_installed():
    try:
        subprocess.run(["lxc", "--version"], check=True, capture_output=True)
        return True
    except:
        return False

if not check_lxc_installed():
    logger.error("LXC not installed. Please install LXC first.")
    print("\n❌ LXC not found! Please install LXC with:")
    print("   sudo apt update && sudo apt install lxc lxc-utils -y")
    print("   sudo snap install lxd")
    print("   sudo lxd init")
    sys.exit(1)

def execute_lxc(command, timeout=120):
    """Execute LXC command with timeout and error handling"""
    try:
        cmd = shlex.split(command)
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        
        if result.returncode != 0:
            error = result.stderr.strip() if result.stderr else "Command failed with no error output"
            raise Exception(error)
        
        return result.stdout.strip() if result.stdout else True
    except subprocess.TimeoutExpired:
        logger.error(f"LXC command timed out: {command}")
        raise Exception(f"Command timed out after {timeout} seconds")
    except Exception as e:
        logger.error(f"LXC Error: {command} - {str(e)}")
        raise

def get_container_status(container_name):
    """Get the status of the LXC container"""
    try:
        result = subprocess.run(["lxc", "info", container_name], capture_output=True, text=True)
        output = result.stdout
        for line in output.splitlines():
            if line.startswith("Status: "):
                return line.split(": ", 1)[1].strip()
        return "Unknown"
    except Exception:
        return "Unknown"

def get_container_cpu(container_name):
    """Get CPU usage inside the container"""
    try:
        result = subprocess.run(["lxc", "exec", container_name, "--", "top", "-bn1"], capture_output=True, text=True)
        output = result.stdout
        for line in output.splitlines():
            if '%Cpu(s):' in line:
                words = line.split()
                for i, word in enumerate(words):
                    if word == 'id,':
                        idle_str = words[i-1].rstrip(',')
                        try:
                            idle = float(idle_str)
                            usage = 100.0 - idle
                            return f"{usage:.1f}%"
                        except ValueError:
                            pass
                break
        return "0%"
    except Exception:
        return "0%"

def get_container_memory(container_name):
    """Get memory usage inside the container"""
    try:
        result = subprocess.run(["lxc", "exec", container_name, "--", "free", "-m"], capture_output=True, text=True)
        lines = result.stdout.splitlines()
        if len(lines) > 1:
            parts = lines[1].split()
            total = int(parts[1])
            used = int(parts[2])
            return f"{used}/{total} MB"
        return "Unknown"
    except Exception:
        return "Unknown"

def get_container_disk(container_name):
    """Get disk usage inside the container"""
    try:
        result = subprocess.run(["lxc", "exec", container_name, "--", "df", "-h", "/"], capture_output=True, text=True)
        lines = result.stdout.splitlines()
        for line in lines:
            if '/dev/' in line and ' /' in line:
                parts = line.split()
                if len(parts) >= 5:
                    used = parts[2]
                    size = parts[1]
                    perc = parts[4]
                    return f"{used}/{size} ({perc})"
        return "Unknown"
    except Exception:
        return "Unknown"

def get_container_ip(container_name):
    """Get container IP address"""
    try:
        result = subprocess.run(["lxc", "list", container_name, "--format", "csv", "-c", "4"], capture_output=True, text=True)
        if result.returncode == 0 and result.stdout:
            return result.stdout.strip()
        return None
    except:
        return None

def get_cpu_usage():
    """Get current CPU usage percentage"""
    try:
        result = subprocess.run(['top', '-bn1'], capture_output=True, text=True)
        output = result.stdout
        for line in output.split('\n'):
            if '%Cpu(s):' in line:
                words = line.split()
                for i, word in enumerate(words):
                    if word == 'id,':
                        idle_str = words[i-1].rstrip(',')
                        try:
                            idle = float(idle_str)
                            usage = 100.0 - idle
                            return usage
                        except ValueError:
                            pass
                break
        return 0.0
    except Exception as e:
        logger.error(f"Error getting CPU usage: {e}")
        return 0.0

system_stats = {}
vps_stats_cache = {}
console_sessions = {}
resource_history = {}
ssh_clients = {}

def generate_token():
    return str(uuid.uuid4())

def generate_vps_id():
    return ''.join(random.choices(string.ascii_uppercase + string.digits, k=12))

def generate_ssh_password():
    chars = string.ascii_letters + string.digits + "!@#$%^&*"
    return ''.join(random.choices(chars, k=16))

def generate_hostname(custom_hostname=None, vps_id=None):
    """Generate a hostname for the VPS"""
    if custom_hostname and custom_hostname.strip():
        # Sanitize hostname (only allow alphanumeric and hyphens)
        sanitized = re.sub(r'[^a-zA-Z0-9-]', '', custom_hostname.strip())
        if sanitized:
            return sanitized.lower()
    # Default fallback
    prefix = db.get_setting('vps_hostname_prefix', VPS_HOSTNAME_PREFIX)
    return f"{prefix}{vps_id.lower()}"

def is_admin(user):
    if not user or not user.is_authenticated:
        return False
    user_data = db.get_user_by_id(user.id)
    return user_data and user_data['role'] == 'admin'

def admin_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not current_user.is_authenticated:
            return redirect(url_for('login'))
        if not is_admin(current_user):
            return render_template('error.html', error='Admin access required'), 403
        return f(*args, **kwargs)
    return decorated_function

def run_command(command, timeout=30):
    if isinstance(command, str):
        command = shlex.split(command)
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout, check=True)
        return True, result.stdout, result.stderr
    except subprocess.CalledProcessError as e:
        return False, e.stdout, e.stderr
    except subprocess.TimeoutExpired:
        return False, "", "Timeout"
    except Exception as e:
        return False, "", str(e)

def run_lxc_command(container_name, command, timeout=1200):
    if isinstance(command, str):
        command = shlex.split(command)
    try:
        result = subprocess.run(["lxc", "exec", container_name, "--"] + command, capture_output=True, text=True, timeout=timeout, check=True)
        return True, result.stdout, result.stderr
    except subprocess.CalledProcessError as e:
        return False, e.stdout, e.stderr
    except subprocess.TimeoutExpired:
        return False, "", "Timeout"
    except Exception as e:
        return False, "", str(e)

def check_host_resources(memory_gb, cpu_cores, disk_gb):
    try:
        host_memory = psutil.virtual_memory().total / (1024**3)
        host_cpu = psutil.cpu_count()
        host_disk = psutil.disk_usage('/').total / (1024**3)
        
        allocated_memory = 0
        allocated_cpu = 0
        allocated_disk = 0
        
        for vps in db.get_all_vps().values():
            allocated_disk += vps['disk']
            if vps['status'] == 'running':
                allocated_memory += vps['memory']
                allocated_cpu += vps['cpu']
        
        memory_overcommit = float(db.get_setting('overcommit_ratio', '10.0'))
        cpu_overcommit = 20.0
        disk_overcommit = 5.0
        
        available_memory = (host_memory * memory_overcommit) - allocated_memory
        available_cpu = (host_cpu * cpu_overcommit) - allocated_cpu
        available_disk = (host_disk * disk_overcommit) - allocated_disk
        
        logger.info(f"Host Resources - RAM: {host_memory:.1f}GB, CPU: {host_cpu}, Disk: {host_disk:.1f}GB")
        logger.info(f"Allocated - RAM: {allocated_memory:.1f}GB, CPU: {allocated_cpu}, Disk: {allocated_disk:.1f}GB")
        logger.info(f"Available - RAM: {available_memory:.1f}GB, CPU: {available_cpu:.1f}, Disk: {available_disk:.1f}GB")
        
        warnings = []
        
        if memory_gb > available_memory:
            warnings.append(f"RAM overcommit: {memory_gb}GB > {available_memory:.1f}GB")
        
        if cpu_cores > available_cpu:
            warnings.append(f"CPU overcommit: {cpu_cores} cores > {available_cpu:.1f}")
        
        if disk_gb > available_disk:
            warnings.append(f"Disk overcommit: {disk_gb}GB > {available_disk:.1f}GB")
            if disk_gb > host_disk * 10:
                return False, f"Disk overcommit too high: {disk_gb}GB requested, host has {host_disk:.1f}GB"
        
        if warnings:
            logger.warning(f"Resource warnings: {', '.join(warnings)}")
            return True, f"VPS created with warnings: {', '.join(warnings)}"
        
        return True, "Resources available"
        
    except Exception as e:
        logger.error(f"Resource check error: {e}")
        return True, "Resource check failed, proceeding anyway"

def create_vps_data_directory(vps_id, disk_size_gb):
    try:
        data_path = os.path.join(DATA_DIR, vps_id)
        os.makedirs(data_path, exist_ok=True)
        
        with open(os.path.join(data_path, 'README.txt'), 'w') as f:
            f.write(f"VPS {vps_id} Data Directory\n")
            f.write(f"Allocated Disk Size: {disk_size_gb} GB\n")
            f.write(f"Created: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        
        logger.info(f"Created data directory for {vps_id}: {data_path} (size limit: {disk_size_gb}GB)")
        return data_path
    except Exception as e:
        logger.error(f"Failed to create data directory for {vps_id}: {e}")
        return None

def cleanup_vps_data(vps_id):
    try:
        data_path = os.path.join(DATA_DIR, vps_id)
        if os.path.exists(data_path):
            shutil.rmtree(data_path, ignore_errors=True)
            logger.info(f"Cleaned up data directory for {vps_id}")
        return True
    except Exception as e:
        logger.error(f"Cleanup error for {vps_id}: {e}")
        return False

def update_system_stats():
    global system_stats
    try:
        cpu = psutil.cpu_percent(interval=0.1)
        mem = psutil.virtual_memory()
        disk = psutil.disk_usage('/')
        net = psutil.net_io_counters()
        
        allocated_memory = 0
        allocated_cpu = 0
        allocated_disk = 0
        
        for vps in db.get_all_vps().values():
            allocated_disk += vps['disk']
            if vps['status'] == 'running':
                allocated_memory += vps['memory']
                allocated_cpu += vps['cpu']
        
        host_memory = mem.total / (1024**3)
        host_cpu = psutil.cpu_count()
        host_disk = disk.total / (1024**3)
        
        system_stats = {
            'cpu_usage': cpu,
            'memory_usage': mem.percent,
            'memory_used': mem.used / (1024 ** 3),
            'memory_total': host_memory,
            'disk_usage': disk.percent,
            'disk_used': disk.used / (1024 ** 3),
            'disk_total': host_disk,
            'network_sent': net.bytes_sent / (1024 ** 2),
            'network_recv': net.bytes_recv / (1024 ** 2),
            'active_connections': len(psutil.net_connections()),
            'allocated_memory': allocated_memory,
            'allocated_cpu': allocated_cpu,
            'allocated_disk': allocated_disk,
            'remaining_memory': host_memory - allocated_memory,
            'remaining_cpu': host_cpu - allocated_cpu,
            'remaining_disk': host_disk - allocated_disk,
            'last_updated': time.time()
        }
    except Exception as e:
        logger.error(f"System stats error: {e}")

def update_vps_stats():
    global vps_stats_cache
    try:
        for vps_id, vps in db.get_all_vps().items():
            if vps['status'] != 'running':
                vps_stats_cache[vps_id] = {'status': vps['status']}
                continue
            try:
                # Get real-time stats
                status = get_container_status(vps['container_name'])
                ip = get_container_ip(vps['container_name'])
                
                vps_stats_cache[vps_id] = {
                    'status': status,
                    'ip': ip
                }
            except Exception as e:
                logger.error(f"VPS {vps_id} stats error: {e}")
                vps_stats_cache[vps_id] = {'status': 'error'}
    except Exception as e:
        logger.error(f"VPS stats update error: {e}")

def system_stats_updater():
    """Background thread to update system stats"""
    while True:
        update_system_stats()
        socketio.emit('system_stats', system_stats, namespace='/admin')
        time.sleep(10)

def vps_stats_updater():
    """Background thread to update VPS stats"""
    while True:
        update_vps_stats()
        socketio.emit('vps_stats', vps_stats_cache, namespace='/admin')
        time.sleep(5)

def setup_container(container_name, vps_id, hostname, memory, cpu, disk, root_password, watermark, welcome):
    try:
        # Configure container limits
        ram_mb = memory * 1024
        subprocess.run(["lxc", "config", "set", container_name, "limits.memory", f"{ram_mb}MB"], check=True)
        subprocess.run(["lxc", "config", "set", container_name, "limits.cpu", str(cpu)], check=True)
        
        # Set disk size
        subprocess.run(["lxc", "config", "device", "set", container_name, "root", "size", f"{disk}GB"], check=True)
        
        # Start the container
        subprocess.run(["lxc", "start", container_name], check=True)
        time.sleep(5)
        
        # Set root password
        subprocess.run(["lxc", "exec", container_name, "--", "bash", "-c", f"echo 'root:{shlex.quote(root_password)}' | chpasswd"], check=True)
        
        # Set welcome message
        subprocess.run(["lxc", "exec", container_name, "--", "bash", "-c", f"echo '{shlex.quote(welcome)}' > /etc/motd"], check=True)
        
        # Set custom hostname
        subprocess.run(["lxc", "exec", container_name, "--", "bash", "-c", f"echo '{hostname}' > /etc/hostname && hostname {hostname}"], check=True)
        
        # Install basic packages
        setup_cmds = [
            "apt-get update",
            "apt-get install -y openssh-server neofetch htop tmate curl wget",
            "systemctl enable ssh",
            "systemctl start ssh",
            "echo 'PermitRootLogin yes' >> /etc/ssh/sshd_config",
            "echo 'PasswordAuthentication yes' >> /etc/ssh/sshd_config",
            "systemctl restart ssh"
        ]
        for cmd in setup_cmds:
            subprocess.run(["lxc", "exec", container_name, "--", "bash", "-c", cmd], check=True)
        
        # Generate tmate session
        tmate_ssh, tmate_web = get_tmate_session(container_name)
        
        logger.info(f"✅ Container {vps_id} setup completed with hostname: {hostname}")
        return True, tmate_ssh, tmate_web
    except subprocess.CalledProcessError as e:
        logger.error(f"Setup failed for {container_name}: {e.stderr if e.stderr else str(e)}")
        return False, None, None
    except Exception as e:
        logger.error(f"Setup failed for {container_name}: {e}")
        return False, None, None

def get_tmate_session(container_name):
    """Generate tmate session for container"""
    try:
        # Kill any existing tmate sessions
        subprocess.run(["lxc", "exec", container_name, "--", "pkill", "-f", "tmate"], capture_output=True)
        time.sleep(2)
        
        # Start tmate in a new session
        subprocess.run(["lxc", "exec", container_name, "--", "tmate", "-S", "/tmp/tmate.sock", "new-session", "-d"], capture_output=True)
        time.sleep(3)
        
        # Wait for tmate to generate keys
        ssh_url = None
        for i in range(5):
            time.sleep(1)
            # Get SSH connection string
            result = subprocess.run(["lxc", "exec", container_name, "--", "tmate", "-S", "/tmp/tmate.sock", "display", "-p", "#{tmate_ssh}"], capture_output=True, text=True)
            if result.returncode == 0 and result.stdout.strip():
                ssh_url = result.stdout.strip()
                break
        
        # Get web connection string
        web_result = subprocess.run(["lxc", "exec", container_name, "--", "tmate", "-S", "/tmp/tmate.sock", "display", "-p", "#{tmate_web}"], capture_output=True, text=True)
        web_url = web_result.stdout.strip() if web_result.returncode == 0 and web_result.stdout.strip() else None
        
        if ssh_url:
            logger.info(f"✅ tmate session generated: {ssh_url}")
            return ssh_url, web_url
        else:
            logger.warning("Failed to get tmate session URL")
            return None, None
    except Exception as e:
        logger.error(f"tmate error: {e}")
        return None, None

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def send_email(to_email, subject, body):
    logger.info(f"📧 Email would be sent to {to_email}: {subject}")
    return True

# Routes
@app.route('/')
def index():
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
    return redirect(url_for('login'))

@app.route('/login', methods=['GET', 'POST'])
def login():
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
   
    if request.method == 'POST':
        username = request.form.get('username')
        password = request.form.get('password')
        user_data = db.get_user(username)
        if user_data and check_password_hash(user_data['password'], password):
            if db.is_user_banned(user_data['id']):
                flash('Account banned', 'danger')
                return render_template('login.html', panel_name=db.get_setting('panel_name', PANEL_NAME))
            user = User(
                user_data['id'], 
                user_data['username'], 
                user_data['role'], 
                user_data.get('email'), 
                user_data.get('theme', 'light')
            )
            login_user(user, remember=True)
            db.log_action(user.id, 'login', f'Logged in from {request.remote_addr}')
            return redirect(url_for('dashboard'))
        flash('Invalid credentials', 'danger')
        return render_template('login.html', panel_name=db.get_setting('panel_name', PANEL_NAME))
   
    return render_template('login.html', panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/register', methods=['GET', 'POST'])
def register():
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))
   
    if request.method == 'POST':
        username = request.form.get('username')
        password = request.form.get('password')
        confirm = request.form.get('confirm_password')
        email = request.form.get('email')
        referral_code = request.form.get('referral_code')
        
        if password != confirm:
            flash('Passwords do not match', 'danger')
            return render_template('register.html', panel_name=db.get_setting('panel_name', PANEL_NAME))
        if len(password) < 8:
            flash('Password must be at least 8 characters', 'danger')
            return render_template('register.html', panel_name=db.get_setting('panel_name', PANEL_NAME))
        
        if db.create_user(username, password, email=email):
            user_id = db.get_user(username)['id']
            db.log_action(user_id, 'register', 'New user registered')
            if referral_code:
                referrer = db._fetchone('SELECT user_id FROM referrals WHERE referral_code = ?', (referral_code,))
                if referrer:
                    db.increment_referred(referrer['user_id'])
                    db.add_notification(referrer['user_id'], f'New referral from {username}')
            flash('Registration successful! Please login.', 'success')
            return redirect(url_for('login'))
        flash('Username already exists', 'danger')
        return render_template('register.html', panel_name=db.get_setting('panel_name', PANEL_NAME))
   
    return render_template('register.html', panel_name=db.get_setting('panel_name', PANEL_NAME))

@app.route('/logout')
@login_required
def logout():
    db.log_action(current_user.id, 'logout', 'Logged out')
    logout_user()
    return redirect(url_for('login'))

@app.route('/dashboard')
@login_required
def dashboard():
    if db.is_user_banned(current_user.id):
        logout_user()
        return redirect(url_for('login'))
   
    vps_list = db.get_user_vps(current_user.id)
    notifications = db.get_notifications(current_user.id)
    theme = current_user.theme
    now = datetime.datetime.now().isoformat()
    return render_template(
        'dashboard.html', 
        vps_list=vps_list, 
        notifications=notifications, 
        panel_name=db.get_setting('panel_name', PANEL_NAME), 
        server_ip=db.get_setting('server_ip', SERVER_IP), 
        is_admin=is_admin(current_user), 
        theme=theme,
        vps_stats=vps_stats_cache,
        now=now
    )

@app.route('/profile', methods=['GET', 'POST'])
@login_required
def profile():
    if request.method == 'POST':
        current = request.form.get('current_password')
        new = request.form.get('new_password')
        confirm = request.form.get('confirm_password')
        email = request.form.get('email')
        theme = request.form.get('theme')
        
        user_data = db.get_user_by_id(current_user.id)
        if not check_password_hash(user_data['password'], current):
            flash('Current password is incorrect', 'danger')
            return render_template('profile.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
        
        if new:
            if new != confirm:
                flash('New passwords do not match', 'danger')
                return render_template('profile.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
            if len(new) < 8:
                flash('Password must be at least 8 characters', 'danger')
                return render_template('profile.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
            db.update_user(current_user.id, password=new, email=email, theme=theme)
        else:
            db.update_user(current_user.id, email=email, theme=theme)
        
        db.log_action(current_user.id, 'update_profile', 'Updated profile')
        current_user.theme = theme
        flash('Profile updated successfully', 'success')
        return render_template('profile.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=theme)
   
    return render_template('profile.html', panel_name=db.get_setting('panel_name', PANEL_NAME), email=current_user.email, theme=current_user.theme)

@app.route('/create_vps', methods=['GET', 'POST'])
@login_required
def create_vps():
    os_images = [
        'ubuntu:22.04', 'ubuntu:24.04', 'ubuntu:20.04',
        'debian:12', 'debian:11', 'debian:10',
        'alpine:latest', 'centos:7', 'fedora:40',
        'archlinux:latest'
    ]
    users = db.get_all_users() if is_admin(current_user) else None

    if request.method == 'POST':
        try:
            memory = int(request.form['memory'])
            cpu = int(request.form['cpu'])
            disk = int(request.form['disk'])
            os_image = request.form.get('os_image', DEFAULT_OS_IMAGE)
            custom_hostname = request.form.get('hostname', '')
            expires_days = int(request.form.get('expires_days', 30))
            expires_hours = int(request.form.get('expires_hours', 0))
            expires_minutes = int(request.form.get('expires_minutes', 0))
            bandwidth_limit = int(request.form.get('bandwidth_limit', 0))
            tags = request.form.get('tags', '')
            user_id = current_user.id if not is_admin(current_user) else int(request.form.get('user_id', current_user.id))

            if memory < 1 or memory > 512:
                raise ValueError('RAM must be between 1-512GB')
            if cpu < 1 or cpu > 32:
                raise ValueError('CPU cores must be between 1-32')
            if disk < 10 or disk > 1000:
                raise ValueError('Disk size must be between 10-1000GB')

            resources_available, resource_message = check_host_resources(memory, cpu, disk)
            if not resources_available:
                raise ValueError(f"Host resources insufficient: {resource_message}")

            total_min = expires_days * 1440 + expires_hours * 60 + expires_minutes
            if total_min <= 0 or expires_days > 3650:
                raise ValueError('Invalid expiration')

            if not db.get_user_by_id(user_id):
                raise ValueError('Invalid user')

            if db.get_user_vps_count(user_id) >= int(db.get_setting('max_vps_per_user', MAX_VPS_PER_USER)):
                raise ValueError('Max VPS reached')

            vps_id = generate_vps_id()
            token = generate_token()
            root_password = generate_ssh_password()
            
            # Generate hostname
            hostname = generate_hostname(custom_hostname, vps_id)
            container_name = f"fvm-{vps_id.lower()}"
            
            # Create LXC container
            os_image_formatted = os_image.replace(':', '/')
            subprocess.run(["lxc", "init", os_image_formatted, container_name, "--storage", db.get_setting('default_storage_pool', DEFAULT_STORAGE_POOL)], check=True)
            
            config_str = f"{memory}GB RAM / {cpu} CPU / {disk}GB Disk"

            # Setup container with resources and custom hostname
            watermark = db.get_setting('watermark', WATERMARK)
            welcome = db.get_setting('welcome_message', WELCOME_MESSAGE)
            setup_success, tmate_ssh, tmate_web = setup_container(
                container_name, vps_id, hostname, memory, cpu, disk,
                root_password, watermark, welcome
            )
            if not setup_success:
                subprocess.run(["lxc", "delete", container_name, "--force"], capture_output=True)
                raise Exception('Setup failed')

            # Get container IP
            container_ip = get_container_ip(container_name)

            now = datetime.datetime.now()
            expires_at = now + datetime.timedelta(
                days=expires_days, hours=expires_hours, minutes=expires_minutes
            )

            vps_data = {
                'token': token,
                'vps_id': vps_id,
                'container_name': container_name,
                'hostname': hostname,
                'memory': memory,
                'cpu': cpu,
                'disk': disk,
                'bandwidth_limit': bandwidth_limit,
                'username': 'root',
                'password': root_password,
                'root_password': root_password,
                'created_by': user_id,
                'created_at': str(now),
                'tmate_session': tmate_ssh,
                'tmate_ssh': tmate_ssh,
                'tmate_web': tmate_web,
                'watermark': watermark,
                'os_image': os_image,
                'restart_count': 0,
                'last_restart': None,
                'status': 'running',
                'port': 22,
                'expires_at': str(expires_at),
                'expires_days': expires_days,
                'expires_hours': expires_hours,
                'expires_minutes': expires_minutes,
                'additional_ports': '',
                'uptime_start': str(now),
                'tags': tags,
                'data_path': None,
                'last_verified': str(now),
                'suspended': False,
                'suspension_history': '[]',
                'shared_with': '[]',
                'config': config_str
            }

            if db.add_vps(vps_data):
                db.log_action(current_user.id, 'create_vps', f'Created VPS {vps_id}')
                db.add_notification(user_id, f'New VPS {vps_id} created')
                
                resource_history[vps_id] = deque(maxlen=3600)
                
                flash('VPS created successfully!', 'success')
                return render_template(
                    'vps_created.html',
                    vps=vps_data,
                    server_ip=db.get_setting('server_ip', SERVER_IP),
                    container_ip=container_ip,
                    panel_name=db.get_setting('panel_name', PANEL_NAME),
                    theme=current_user.theme
                )
            else:
                subprocess.run(["lxc", "delete", container_name, "--force"], capture_output=True)
                raise Exception('Database add failed')

        except subprocess.CalledProcessError as e:
            error_msg = f"LXC command failed: {e.stderr if e.stderr else str(e)}"
            logger.error(f"Create VPS error: {error_msg}")
            return render_template(
                'create_vps.html',
                error=error_msg,
                panel_name=db.get_setting('panel_name', PANEL_NAME),
                os_images=os_images,
                users=users,
                theme=current_user.theme
            )
        except Exception as e:
            logger.error(f"Create VPS error: {e}")
            return render_template(
                'create_vps.html',
                error=str(e),
                panel_name=db.get_setting('panel_name', PANEL_NAME),
                os_images=os_images,
                users=users,
                theme=current_user.theme
            )

    return render_template(
        'create_vps.html',
        os_images=os_images,
        users=users,
        panel_name=db.get_setting('panel_name', PANEL_NAME),
        theme=current_user.theme
    )

@app.route('/vps/<vps_id>')
@login_required
def vps_details(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if VPS is suspended and user is not admin
    if vps.get('suspended', False) and vps['created_by'] != current_user.id and not is_admin(current_user):
        flash('This VPS has been suspended by an administrator.', 'warning')
        return redirect(url_for('dashboard'))
   
    try:
        status = get_container_status(vps['container_name'])
        container_ip = get_container_ip(vps['container_name'])
    except:
        status = 'not_found'
        container_ip = None
   
    history = db.get_resource_history(vps_id, 360)
    now = datetime.datetime.now().isoformat()
    
    return render_template(
        'vps_details.html', 
        vps=vps, 
        container_status=status, 
        container_ip=container_ip,
        server_ip=db.get_setting('server_ip', SERVER_IP), 
        panel_name=db.get_setting('panel_name', PANEL_NAME), 
        history=history,
        now=now,
        is_admin=is_admin(current_user),
        theme=current_user.theme
    )

@app.route('/vps/<vps_id>/start')
@login_required
def start_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        flash('This VPS is suspended and cannot be started.', 'warning')
        return redirect(url_for('vps_details', vps_id=vps_id))
   
    try:
        result = subprocess.run(["lxc", "start", vps['container_name']], capture_output=True, text=True)
        if result.returncode != 0:
            raise Exception(result.stderr)
        db.update_vps(token, {'status': 'running', 'uptime_start': str(datetime.datetime.now())})
        db.log_action(current_user.id, 'start_vps', f'Started VPS {vps_id}')
        flash('VPS started successfully', 'success')
    except Exception as e:
        logger.error(f"Start VPS error: {e}")
        flash(f'Error starting VPS: {str(e)}', 'danger')
    
    return redirect(url_for('vps_details', vps_id=vps_id))

@app.route('/vps/<vps_id>/stop')
@login_required
def stop_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        flash('This VPS is suspended and cannot be stopped.', 'warning')
        return redirect(url_for('vps_details', vps_id=vps_id))
   
    try:
        result = subprocess.run(["lxc", "stop", vps['container_name']], capture_output=True, text=True)
        if result.returncode != 0:
            raise Exception(result.stderr)
        db.update_vps(token, {'status': 'stopped'})
        db.log_action(current_user.id, 'stop_vps', f'Stopped VPS {vps_id}')
        flash('VPS stopped successfully', 'success')
    except Exception as e:
        logger.error(f"Stop VPS error: {e}")
        flash(f'Error stopping VPS: {str(e)}', 'danger')
    
    return redirect(url_for('vps_details', vps_id=vps_id))

@app.route('/vps/<vps_id>/restart')
@login_required
def restart_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        flash('This VPS is suspended and cannot be restarted.', 'warning')
        return redirect(url_for('vps_details', vps_id=vps_id))
   
    try:
        result = subprocess.run(["lxc", "restart", vps['container_name']], capture_output=True, text=True)
        if result.returncode != 0:
            raise Exception(result.stderr)
        
        # Generate new tmate session on restart
        tmate_ssh, tmate_web = get_tmate_session(vps['container_name'])
        
        updates = {
            'restart_count': vps.get('restart_count', 0) + 1,
            'last_restart': str(datetime.datetime.now()),
            'status': 'running',
            'uptime_start': str(datetime.datetime.now())
        }
        
        if tmate_ssh:
            updates['tmate_session'] = tmate_ssh
            updates['tmate_ssh'] = tmate_ssh
            updates['tmate_web'] = tmate_web
        
        db.update_vps(token, updates)
        db.log_action(current_user.id, 'restart_vps', f'Restarted VPS {vps_id}')
        flash('VPS restarted successfully', 'success')
    except Exception as e:
        logger.error(f"Restart VPS error: {e}")
        flash(f'Error restarting VPS: {str(e)}', 'danger')
    
    return redirect(url_for('vps_details', vps_id=vps_id))

@app.route('/vps/<vps_id>/suspend')
@login_required
@admin_required
def suspend_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps:
        flash('VPS not found', 'danger')
        return redirect(url_for('admin_panel'))
    
    try:
        result = subprocess.run(["lxc", "stop", vps['container_name'], "--force"], capture_output=True, text=True)
        if result.returncode != 0:
            logger.error(f"LXC stop error: {result.stderr}")
        
        suspension_history = json.loads(vps.get('suspension_history', '[]'))
        suspension_history.append({
            'time': datetime.datetime.now().isoformat(),
            'reason': 'Suspended by admin',
            'by': current_user.username
        })
        
        db.update_vps(token, {
            'status': 'suspended',
            'suspended': True,
            'suspension_history': json.dumps(suspension_history)
        })
        
        db.log_action(current_user.id, 'suspend_vps', f'Suspended VPS {vps_id}')
        flash('VPS suspended successfully', 'success')
    except Exception as e:
        logger.error(f"Suspend VPS error: {e}")
        flash(f'Error suspending VPS: {str(e)}', 'danger')
    
    return redirect(url_for('admin_panel'))

@app.route('/vps/<vps_id>/unsuspend')
@login_required
@admin_required
def unsuspend_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps:
        flash('VPS not found', 'danger')
        return redirect(url_for('admin_panel'))
    
    try:
        result = subprocess.run(["lxc", "start", vps['container_name']], capture_output=True, text=True)
        if result.returncode != 0:
            logger.error(f"LXC start error: {result.stderr}")
        
        db.update_vps(token, {
            'status': 'running',
            'suspended': False,
            'uptime_start': str(datetime.datetime.now())
        })
        
        db.log_action(current_user.id, 'unsuspend_vps', f'Unsuspended VPS {vps_id}')
        flash('VPS unsuspended successfully', 'success')
    except Exception as e:
        logger.error(f"Unsuspend VPS error: {e}")
        flash(f'Error unsuspending VPS: {str(e)}', 'danger')
    
    return redirect(url_for('admin_panel'))

@app.route('/vps/<vps_id>/delete', methods=['POST'])
@login_required
def delete_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    
    try:
        # Stop container
        subprocess.run(["lxc", "stop", vps['container_name'], "--force"], capture_output=True, text=True)
        time.sleep(1)
        
        # Delete container
        subprocess.run(["lxc", "delete", vps['container_name']], capture_output=True, text=True)
        
        # Clean up data directory
        cleanup_vps_data(vps_id)
        
        # Remove from database
        db.remove_vps(token)
        
        db.log_action(current_user.id, 'delete_vps', f'Deleted VPS {vps_id}')
        
        return jsonify({'message': 'VPS deleted successfully'})
        
    except Exception as e:
        logger.error(f"Delete VPS error: {e}")
        return jsonify({'error': str(e)}), 500

@app.route('/vps/<vps_id>/console')
@login_required
def vps_console(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        flash('This VPS is suspended and console access is disabled.', 'warning')
        return redirect(url_for('vps_details', vps_id=vps_id))
    
    container_ip = get_container_ip(vps['container_name'])
    return render_template("console.html", vps=vps, container_ip=container_ip, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)

@app.route('/vps/<vps_id>/logs')
@login_required
def vps_logs(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        flash('Access denied', 'danger')
        return redirect(url_for('dashboard'))
    
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        flash('This VPS is suspended and logs are disabled.', 'warning')
        return redirect(url_for('vps_details', vps_id=vps_id))
    
    try:
        result = subprocess.run(["lxc", "info", vps['container_name']], capture_output=True, text=True)
        logs = result.stdout + "\n\n" + result.stderr
        
        # Also get recent container logs
        logs_result = subprocess.run(["lxc", "exec", vps['container_name'], "--", "journalctl", "-n", "100"], capture_output=True, text=True)
        if logs_result.returncode == 0:
            logs += "\n\n--- Recent System Logs ---\n" + logs_result.stdout
        
        return render_template('logs.html', vps=vps, logs=logs, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
    except Exception as e:
        return render_template('logs.html', vps=vps, logs=f"Error getting logs: {e}", panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)

@app.route('/vps/<vps_id>/stats')
@login_required
def vps_stats(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        return jsonify({'error': 'Access denied'}), 403
    
    try:
        cpu = get_container_cpu(vps['container_name'])
        memory = get_container_memory(vps['container_name'])
        disk = get_container_disk(vps['container_name'])
        
        return jsonify({
            'cpu': cpu,
            'memory': memory,
            'disk': disk,
            'status': vps['status']
        })
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/vps/<vps_id>/edit', methods=['GET', 'POST'])
@login_required
@admin_required
def edit_vps(vps_id):
    token, vps = db.get_vps_by_id(vps_id)
    if not vps:
        flash('VPS not found', 'danger')
        return redirect(url_for('admin_panel'))
    
    os_images = [
        'ubuntu:22.04', 'ubuntu:24.04', 'ubuntu:20.04',
        'debian:12', 'debian:11', 'debian:10',
        'alpine:latest', 'centos:7', 'fedora:40',
        'archlinux:latest'
    ]
    
    if request.method == 'POST':
        try:
            memory = int(request.form['memory'])
            cpu = int(request.form['cpu'])
            disk = int(request.form['disk'])
            hostname = request.form.get('hostname', vps.get('hostname', ''))
            
            if memory < 1 or memory > 512:
                raise ValueError('RAM must be between 1-512GB')
            if cpu < 1 or cpu > 32:
                raise ValueError('CPU cores must be between 1-32')
            if disk < 10 or disk > 1000:
                raise ValueError('Disk size must be between 10-1000GB')
            
            # Check if container exists
            check_result = subprocess.run(["lxc", "info", vps['container_name']], capture_output=True, text=True)
            if check_result.returncode != 0:
                raise Exception(f"Container {vps['container_name']} not found")
            
            # Stop container if running
            was_running = False
            status_result = subprocess.run(["lxc", "info", vps['container_name']], capture_output=True, text=True)
            if 'Status: Running' in status_result.stdout:
                was_running = True
                subprocess.run(["lxc", "stop", vps['container_name'], "--force"], check=True)
                time.sleep(2)
            
            # Update container config
            ram_mb = memory * 1024
            subprocess.run(["lxc", "config", "set", vps['container_name'], "limits.memory", f"{ram_mb}MB"], check=True)
            subprocess.run(["lxc", "config", "set", vps['container_name'], "limits.cpu", str(cpu)], check=True)
            subprocess.run(["lxc", "config", "device", "set", vps['container_name'], "root", "size", f"{disk}GB"], check=True)
            
            # Update hostname if changed
            if hostname and hostname != vps.get('hostname'):
                subprocess.run(["lxc", "start", vps['container_name']], check=True)
                time.sleep(3)
                subprocess.run(["lxc", "exec", vps['container_name'], "--", "bash", "-c", f"echo '{hostname}' > /etc/hostname && hostname {hostname}"], check=True)
                subprocess.run(["lxc", "stop", vps['container_name']], check=True)
            
            # Start container if it was running
            if was_running:
                subprocess.run(["lxc", "start", vps['container_name']], check=True)
            
            # Update database
            db.update_vps(token, {
                'memory': memory,
                'cpu': cpu,
                'disk': disk,
                'hostname': hostname,
                'config': f"{memory}GB RAM / {cpu} CPU / {disk}GB Disk"
            })
            
            db.log_action(current_user.id, 'edit_vps', f'Edited VPS {vps_id}')
            flash('VPS updated successfully', 'success')
            return redirect(url_for('admin_panel'))
            
        except subprocess.CalledProcessError as e:
            error_msg = f"LXC command failed: {e.stderr if e.stderr else str(e)}"
            logger.error(f"Edit VPS error: {error_msg}")
            return render_template('edit_vps.html', vps=vps, error=error_msg, os_images=os_images, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
        except Exception as e:
            logger.error(f"Edit VPS error: {e}")
            return render_template('edit_vps.html', vps=vps, error=str(e), os_images=os_images, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
    
    return render_template('edit_vps.html', vps=vps, os_images=os_images, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)

@app.route('/admin')
@login_required
@admin_required
def admin_panel():
    update_system_stats()
    all_vps = list(db.get_all_vps().values())
    all_users = db.get_all_users()
    banned = db.get_banned_users()
   
    settings = {
        'panel_name': db.get_setting('panel_name', PANEL_NAME),
        'watermark': db.get_setting('watermark', WATERMARK),
        'welcome_message': db.get_setting('welcome_message', WELCOME_MESSAGE),
        'server_ip': db.get_setting('server_ip', SERVER_IP),
        'max_containers': db.get_setting('max_containers', MAX_CONTAINERS),
        'max_vps_per_user': db.get_setting('max_vps_per_user', MAX_VPS_PER_USER),
        'vps_hostname_prefix': db.get_setting('vps_hostname_prefix', VPS_HOSTNAME_PREFIX),
        'cpu_threshold': db.get_setting('cpu_threshold', CPU_THRESHOLD),
        'ram_threshold': db.get_setting('ram_threshold', RAM_THRESHOLD),
        'default_storage_pool': db.get_setting('default_storage_pool', DEFAULT_STORAGE_POOL)
    }
   
    stats = {
        'total_vps': len(all_vps),
        'total_users': len(all_users),
        'total_banned': len(banned),
        'total_restarts': db.get_stat('total_restarts'),
        'total_vps_created': db.get_stat('total_vps_created')
    }
   
    audit_logs = db.get_audit_logs(50)
    log_file_path = os.path.join(LOG_DIR, 'fvm_panel.log')
    try:
        with open(log_file_path, 'r') as f:
            logs = ''.join(f.readlines()[-200:])
    except:
        logs = "No logs available"
   
    now = datetime.datetime.now().isoformat()
    return render_template(
        'admin.html', 
        system_stats=system_stats, 
        vps_list=all_vps, 
        vps_stats=vps_stats_cache, 
        users=all_users, 
        banned_users=banned, 
        audit_logs=audit_logs, 
        now=now,
        **settings, 
        **stats, 
        recent_logs=logs, 
        theme=current_user.theme
    )

@app.route('/admin/settings', methods=['POST'])
@login_required
@admin_required
def admin_settings():
    for key in ['panel_name', 'watermark', 'welcome_message', 'server_ip', 'vps_hostname_prefix', 'default_storage_pool']:
        value = request.form.get(key)
        if value:
            db.set_setting(key, value)
   
    for key in ['max_containers', 'max_vps_per_user', 'overcommit_ratio', 'cpu_threshold', 'ram_threshold', 'check_interval']:
        value = request.form.get(key)
        if value and value.replace('.', '').isdigit():
            db.set_setting(key, float(value) if '.' in value else int(value))
   
    db.log_action(current_user.id, 'update_settings', 'Updated system settings')
    flash('Settings updated successfully', 'success')
    return redirect(url_for('admin_panel'))

@app.route('/admin/add_user', methods=['GET', 'POST'])
@login_required
@admin_required
def add_user():
    if request.method == 'POST':
        username = request.form['username']
        password = request.form['password']
        email = request.form['email']
        role = request.form.get('role', 'user')
        if len(password) < 8:
            flash('Password too short', 'danger')
            return render_template('add_user.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
        if db.create_user(username, password, role, email):
            db.log_action(current_user.id, 'add_user', f'Added user {username}')
            flash(f'User {username} added successfully', 'success')
            return redirect(url_for('admin_panel'))
        flash('Username already exists', 'danger')
        return render_template('add_user.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
   
    return render_template('add_user.html', panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)

@app.route('/admin/edit_user/<int:user_id>', methods=['GET', 'POST'])
@login_required
@admin_required
def edit_user(user_id):
    user = db.get_user_by_id(user_id)
    if not user:
        flash('User not found', 'danger')
        return redirect(url_for('admin_panel'))
   
    if request.method == 'POST':
        username = request.form.get('username', user['username'])
        password = request.form.get('password')
        role = request.form.get('role', user['role'])
        email = request.form.get('email', user.get('email'))
        if password and len(password) < 8:
            flash('Password too short', 'danger')
            return render_template('edit_user.html', user=user, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
        if db.update_user(user_id, username=username, password=password, role=role, email=email):
            db.log_action(current_user.id, 'edit_user', f'Edited user {user_id}')
            flash('User updated successfully', 'success')
            return redirect(url_for('admin_panel'))
        flash('Update failed', 'danger')
        return render_template('edit_user.html', user=user, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)
   
    return render_template('edit_user.html', user=user, panel_name=db.get_setting('panel_name', PANEL_NAME), theme=current_user.theme)

@app.route('/admin/delete_user/<int:user_id>', methods=['POST'])
@login_required
@admin_required
def delete_user(user_id):
    if db.delete_user(user_id):
        db.log_action(current_user.id, 'delete_user', f'Deleted user {user_id}')
        return jsonify({'message': 'User deleted successfully'})
    return jsonify({'error': 'Failed to delete user'}), 500

@app.route('/admin/user/<user_id>/ban')
@login_required
@admin_required
def ban_user(user_id):
    db.ban_user(int(user_id))
    db.log_action(current_user.id, 'ban_user', f'Banned user {user_id}')
    flash('User banned successfully', 'success')
    return redirect(url_for('admin_panel'))

@app.route('/admin/user/<user_id>/unban')
@login_required
@admin_required
def unban_user(user_id):
    db.unban_user(int(user_id))
    db.log_action(current_user.id, 'unban_user', f'Unbanned user {user_id}')
    flash('User unbanned successfully', 'success')
    return redirect(url_for('admin_panel'))

@app.route('/admin/user/<user_id>/make_admin')
@login_required
@admin_required
def make_admin(user_id):
    db.update_user_role(int(user_id), 'admin')
    db.log_action(current_user.id, 'make_admin', f'Made user {user_id} admin')
    flash('User promoted to admin', 'success')
    return redirect(url_for('admin_panel'))

@app.route('/admin/user/<user_id>/remove_admin')
@login_required
@admin_required
def remove_admin(user_id):
    db.update_user_role(int(user_id), 'user')
    db.log_action(current_user.id, 'remove_admin', f'Removed admin from user {user_id}')
    flash('Admin privileges removed', 'success')
    return redirect(url_for('admin_panel'))

@app.route('/admin/backup')
@login_required
@admin_required
def admin_backup():
    if db.backup_data():
        db.log_action(current_user.id, 'backup_system', 'Performed system backup')
        return send_file(BACKUP_FILE, as_attachment=True, download_name=f'fvm_backup_{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}.json')
    flash('Backup failed', 'danger')
    return redirect(url_for('admin_panel'))

@app.route('/admin/restore', methods=['POST'])
@login_required
@admin_required
def admin_restore():
    if 'backup_file' not in request.files:
        flash('No file uploaded', 'danger')
        return redirect(url_for('admin_panel'))
   
    file = request.files['backup_file']
    if file.filename == '':
        flash('No file selected', 'danger')
        return redirect(url_for('admin_panel'))
   
    if file and file.filename.endswith('.json'):
        file.save(BACKUP_FILE)
        if db.restore_data():
            db.log_action(current_user.id, 'restore_system', 'Restored system from backup')
            flash('System restored successfully', 'success')
        else:
            flash('Restore failed', 'danger')
    else:
        flash('Invalid file format', 'danger')
    
    return redirect(url_for('admin_panel'))

@app.route('/admin/docker_prune')
@login_required
@admin_required
def admin_docker_prune():
    try:
        subprocess.run(["docker", "system", "prune", "-f"], check=True)
        db.log_action(current_user.id, 'docker_prune', 'Pruned Docker system')
        flash('Docker pruned successfully', 'success')
    except Exception as e:
        logger.error(f"Docker prune error: {e}")
        flash(f'Error pruning Docker: {str(e)}', 'danger')
    
    return redirect(url_for('admin_panel'))

@app.route('/admin/export_vps')
@login_required
@admin_required
def export_vps():
    vps_list = list(db.get_all_vps().values())
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(['VPS ID', 'Hostname', 'Container Name', 'Memory', 'CPU', 'Disk', 'Status', 'Created By', 'Created At', 'Expires At', 'Tags'])
    for vps in vps_list:
        writer.writerow([
            vps['vps_id'], vps.get('hostname', ''), vps['container_name'], vps['memory'], vps['cpu'], 
            vps['disk'], vps['status'], vps['created_by'], vps['created_at'], 
            vps['expires_at'], vps['tags']
        ])
    output.seek(0)
    db.log_action(current_user.id, 'export_vps', 'Exported VPS list')
    return send_file(
        io.BytesIO(output.getvalue().encode()), 
        download_name=f'vps_export_{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}.csv', 
        as_attachment=True
    )

@app.route('/admin/export_users')
@login_required
@admin_required
def export_users():
    users = db.get_all_users()
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(['ID', 'Username', 'Role', 'Email', 'Created At', 'Theme'])
    for user in users:
        writer.writerow([user['id'], user['username'], user['role'], user.get('email'), user['created_at'], user.get('theme')])
    output.seek(0)
    db.log_action(current_user.id, 'export_users', 'Exported users list')
    return send_file(
        io.BytesIO(output.getvalue().encode()), 
        download_name=f'users_export_{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}.csv', 
        as_attachment=True
    )

@socketio.on('connect', namespace='/console')
def handle_console_connect():
    logger.info(f"Console client connected: {request.sid}")

@socketio.on('disconnect', namespace='/console')
def handle_console_disconnect():
    sid = request.sid
    if sid in console_sessions:
        try:
            os.killpg(os.getpgid(console_sessions[sid]['pid']), signal.SIGTERM)
        except:
            pass
        del console_sessions[sid]
    logger.info(f"Console client disconnected: {sid}")

@socketio.on('start_shell', namespace='/console')
def start_shell(data):
    vps_id = data.get('vps_id')
    token, vps = db.get_vps_by_id(vps_id)
    
    if not vps or (vps['created_by'] != current_user.id and not is_admin(current_user)):
        emit('error', 'Access denied')
        return
   
    # Check if suspended
    if vps.get('suspended', False) and not is_admin(current_user):
        emit('error', 'VPS is suspended')
        return
   
    try:
        # Check if container is running
        status = get_container_status(vps['container_name'])
        if 'running' not in status.lower():
            emit('error', 'VPS is not running')
            return
    except Exception as e:
        logger.error(f"Container not found: {e}")
        emit('error', 'Container not found')
        return
   
    try:
        master, slave = pty.openpty()
        
        flags = fcntl.fcntl(master, fcntl.F_GETFL)
        fcntl.fcntl(master, fcntl.F_SETFL, flags | os.O_NONBLOCK)
        
        if 'rows' in data and 'cols' in data:
            winsize = struct.pack("HHHH", data['rows'], data['cols'], 0, 0)
            fcntl.ioctl(slave, termios.TIOCSWINSZ, winsize)
   
        pid = os.fork()
        if pid == 0:
            os.setsid()
            fcntl.ioctl(slave, termios.TIOCSCTTY, 0)
            os.dup2(slave, 0)
            os.dup2(slave, 1)
            os.dup2(slave, 2)
            os.close(master)
            os.close(slave)
            os.environ['TERM'] = 'xterm-256color'
            os.environ['SHELL'] = '/bin/bash'
            cmd = ['lxc', 'exec', vps['container_name'], '/bin/bash']
            os.execvp(cmd[0], cmd)
            sys.exit(1)
        else:
            os.close(slave)
            sid = request.sid
            console_sessions[sid] = {'fd': master, 'pid': pid}
            
            def reader():
                buffer = b''
                while True:
                    try:
                        r, _, _ = select.select([master], [], [], 0.1)
                        if master in r:
                            data = os.read(master, 1024)
                            if not data:
                                break
                            buffer += data
                            try:
                                text = buffer.decode('utf-8')
                                emit('output', text)
                                buffer = b''
                            except UnicodeDecodeError:
                                continue
                    except (OSError, IOError) as e:
                        if e.errno != 11:
                            break
                    except Exception:
                        break
                
                if buffer:
                    try:
                        emit('output', buffer.decode('utf-8', errors='ignore'))
                    except:
                        pass
                
                if sid in console_sessions:
                    del console_sessions[sid]
                emit('shell_exit')
            
            threading.Thread(target=reader, daemon=True).start()
            emit('ready', {'message': 'Shell started'})
            
    except Exception as e:
        logger.error(f"Error starting shell: {e}")
        emit('error', f'Failed to start shell: {str(e)}')

@socketio.on('input', namespace='/console')
def handle_input(data):
    sid = request.sid
    if sid in console_sessions:
        try:
            os.write(console_sessions[sid]['fd'], data.encode('utf-8'))
        except Exception as e:
            logger.error(f"Error writing input: {e}")
            emit('error', 'Failed to send input')

@socketio.on('resize', namespace='/console')
def resize_handler(data):
    sid = request.sid
    if sid in console_sessions:
        try:
            fd = console_sessions[sid]['fd']
            winsize = struct.pack("HHHH", data['rows'], data['cols'], 0, 0)
            fcntl.ioctl(fd, termios.TIOCSWINSZ, winsize)
        except Exception as e:
            logger.error(f"Error resizing: {e}")

@socketio.on('connect', namespace='/admin')
def handle_admin_connect():
    emit('system_stats', system_stats)
    emit('vps_stats', vps_stats_cache)

@socketio.on('connect', namespace='/vps')
def handle_vps_connect():
    pass

@socketio.on('join_vps', namespace='/vps')
def join_vps(data):
    vps_id = data['vps_id']
    join_room(vps_id)
    if vps_id in resource_history:
        emit('history', list(resource_history[vps_id]))

@socketio.on('leave_vps', namespace='/vps')
def leave_vps(data):
    vps_id = data['vps_id']
    leave_room(vps_id)

# Background threads
cpu_monitor_active = True

def cpu_monitor():
    """Monitor CPU usage and stop all VPS if threshold is exceeded"""
    global cpu_monitor_active
    
    while cpu_monitor_active:
        try:
            cpu_usage = get_cpu_usage()
            cpu_threshold = float(db.get_setting('cpu_threshold', CPU_THRESHOLD))
            
            if cpu_usage > cpu_threshold:
                logger.warning(f"CPU usage ({cpu_usage}%) exceeded threshold ({cpu_threshold}%). Stopping all VPS.")
                
                for token, vps in db.get_all_vps().items():
                    try:
                        subprocess.run(["lxc", "stop", vps['container_name'], "--force"], capture_output=True)
                        db.update_vps(token, {'status': 'stopped'})
                    except:
                        pass
            
            time.sleep(60)
        except Exception as e:
            logger.error(f"Error in CPU monitor: {e}")
            time.sleep(60)

def vps_monitor():
    """Monitor each VPS for high CPU/RAM usage"""
    while True:
        try:
            cpu_threshold = float(db.get_setting('cpu_threshold', CPU_THRESHOLD))
            ram_threshold = float(db.get_setting('ram_threshold', RAM_THRESHOLD))
            
            for token, vps in db.get_all_vps().items():
                if vps['status'] == 'running' and not vps.get('suspended', False):
                    container = vps['container_name']
                    cpu = get_container_cpu(container)
                    memory = get_container_memory(container)
                    
                    # Parse percentages
                    cpu_val = float(cpu.replace('%', '')) if '%' in cpu else 0
                    
                    # Parse memory (format: "used/total MB")
                    mem_parts = memory.split('/')
                    if len(mem_parts) == 2:
                        used = float(mem_parts[0].strip())
                        total = float(mem_parts[1].strip().split()[0])
                        ram_val = (used / total) * 100 if total > 0 else 0
                    else:
                        ram_val = 0
                    
                    if cpu_val > cpu_threshold or ram_val > ram_threshold:
                        reason = f"High resource usage: CPU {cpu}, RAM {memory}"
                        logger.warning(f"Suspending {container}: {reason}")
                        try:
                            subprocess.run(["lxc", "stop", container], capture_output=True)
                            suspension_history = json.loads(vps.get('suspension_history', '[]'))
                            suspension_history.append({
                                'time': datetime.datetime.now().isoformat(),
                                'reason': reason,
                                'by': 'Auto-System'
                            })
                            db.update_vps(token, {
                                'status': 'suspended',
                                'suspended': True,
                                'suspension_history': json.dumps(suspension_history)
                            })
                            # Notify owner
                            db.add_notification(vps['created_by'], f'VPS {vps["vps_id"]} suspended due to high resource usage')
                        except Exception as e:
                            logger.error(f"Failed to suspend {container}: {e}")
            time.sleep(int(db.get_setting('check_interval', CHECK_INTERVAL)))
        except Exception as e:
            logger.error(f"VPS monitor error: {e}")
            time.sleep(60)

def clean_stopped_containers():
    """Clean up stopped containers not in database"""
    while True:
        try:
            result = subprocess.run(["lxc", "list", "--format", "csv", "-c", "n"], capture_output=True, text=True)
            if result.returncode == 0:
                containers = result.stdout.strip().split('\n') if result.stdout else []
                db_containers = [v['container_name'] for v in db.get_all_vps().values()]
                
                for cont in containers:
                    if cont and cont not in db_containers:
                        try:
                            subprocess.run(["lxc", "delete", cont, "--force"], capture_output=True)
                        except:
                            pass
        except Exception as e:
            logger.error(f"Clean stopped containers error: {e}")
        time.sleep(600)

def check_expired_vps():
    """Check for expired VPS"""
    while True:
        now = datetime.datetime.now()
        for token, vps in db.get_all_vps().items():
            if vps.get('expires_at'):
                try:
                    expires = datetime.datetime.fromisoformat(vps['expires_at'])
                    if now > expires and vps['status'] != 'expired':
                        subprocess.run(["lxc", "stop", vps['container_name'], "--force"], capture_output=True)
                        subprocess.run(["lxc", "delete", vps['container_name'], "--force"], capture_output=True)
                        db.update_vps(token, {'status': 'expired'})
                        db.add_notification(vps['created_by'], f'VPS {vps["vps_id"]} has expired')
                except Exception as e:
                    logger.error(f"Error expiring VPS {vps['vps_id']}: {e}")
        time.sleep(60)

def scheduled_backups():
    """Scheduled backup function"""
    while True:
        backup_schedule = db.get_setting('backup_schedule', BACKUP_SCHEDULE)
        if backup_schedule == 'daily':
            time.sleep(86400)
        elif backup_schedule == 'hourly':
            time.sleep(3600)
        else:
            time.sleep(86400)
        db.backup_data()
        logger.info("Scheduled backup performed")

# Start all background threads
threading.Thread(target=system_stats_updater, daemon=True).start()
threading.Thread(target=vps_stats_updater, daemon=True).start()
threading.Thread(target=cpu_monitor, daemon=True).start()
threading.Thread(target=vps_monitor, daemon=True).start()
threading.Thread(target=clean_stopped_containers, daemon=True).start()
threading.Thread(target=check_expired_vps, daemon=True).start()
threading.Thread(target=scheduled_backups, daemon=True).start()

__version__ = "6.0"

DEFAULT_ART = r"""
  ______     __   __     __    __        _____     ______     __   __     ______     __        
 /\  ___\   /\ \ / /    /\ "-./  \      /\  __-.  /\  __ \   /\ "-.\ \   /\  ___\   /\ \       
 \ \___  \  \ \ \'/     \ \ \-./\ \     \ \ \/\ \ \ \  __ \  \ \ \-.  \  \ \  __\   \ \ \____  
  \/\_____\  \ \__|      \ \_\ \ \_\     \ \____-  \ \_\ \_\  \ \_\\"\_\  \ \_____\  \ \_____\ 
   \/_____/   \/_/        \/_/  \/_/      \/____/   \/_/\/_/   \/_/ \/_/   \/_____/   \/_____/
                   
"""

def show_banner():
    print(DEFAULT_ART)
    print(f"Version: {__version__}\n")
    print(f"✅ FVM Mode Enabled - Resources show correctly!")
    print(f"✅ Data Directory: {DATA_DIR}")
    print(f"✅ Log Directory: {LOG_DIR}")
    print(f"✅ Server running on port {SERVER_PORT}")
    print(f"\n🔗 Access the panel at: http://{SERVER_IP}:{SERVER_PORT}")
    print(f"   Default login: admin / admin")
    print(f"\n✅ Custom hostnames supported!")
    print(f"✅ VPS deletion with cleanup!")
    print(f"✅ Suspend/Unsuspend working!")
    print(f"✅ tMate regenerates on restart!")
    print(f"✅ Status shows Running/Stopped/Suspended correctly!")
    print(f"✅ Suspended VPS redirect users to dashboard with message!")

if __name__ == '__main__':
    show_banner()
    socketio.run(app, host='0.0.0.0', port=SERVER_PORT, debug=DEBUG, allow_unsafe_werkzeug=True)