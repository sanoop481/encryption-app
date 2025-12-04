"""
File Encryption System with AES-256-GCM

THREAT MODEL:
============
This system protects files against:
- Unauthorized access: Files are encrypted with AES-256-GCM. Without the exact 
  entropy source (image/video) and optional passphrase, files cannot be decrypted.
- Tampering: AES-GCM authentication tags detect any modification to encrypted files.
- Brute-force attacks: Key derivation uses HKDF-SHA256 with unique salts per file,
  making attacks computationally infeasible.

Protection limitations:
- Does NOT protect against: keyloggers, malware on client/server, physical access
  to entropy sources, server-side data leaks if server is compromised.
- Assumes: entropy source files are kept secure and not shared publicly.

Security properties:
- Encryption: AES-256-GCM (authenticated encryption)
- Key derivation: HKDF-SHA256 with unique salt per file
- Entropy source: SHA256 hash of image/video pixels/frames
- Nonce: 12-byte random nonce per file (GCM requirement)
- Integrity: 16-byte authentication tag verified on decryption

RECOMMENDATIONS:
- Use strong, unique passphrases for sensitive files
- Store entropy sources securely (they are required for decryption)
- Keep encrypted files and entropy sources separate
- Change default admin credentials in production
- Use HTTPS in production (set FLASK_SECURE_COOKIES=1)
- Rotate SECRET_KEY periodically
"""

import os
import uuid
import struct
import shutil
import hashlib
import json
import time
import re
import logging
import random
from typing import Tuple, Optional
from threading import RLock
from functools import wraps

from flask import Flask, request, send_file, abort, after_this_request, session, redirect, url_for, jsonify, render_template
from werkzeug.utils import secure_filename
from werkzeug.security import generate_password_hash, check_password_hash

import cv2
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
import tempfile

# Storage and limits
BASE_UPLOAD_FOLDER = "uploads"
os.makedirs(BASE_UPLOAD_FOLDER, exist_ok=True)
MAX_CONTENT_LENGTH_BYTES = 4 * 1024 * 1024 * 1024  # 4 GiB
CHUNK_SIZE = 1024 * 1024  # 1 MiB for better throughput

# File format constants (GCM-based)
# Format version 1: MAGIC | VERSION | SALT | NONCE | FILENAME_LEN | FILENAME | CIPHERTEXT | TAG
MAGIC = b"VKEYGCM1"
FORMAT_VERSION = 1
VERSION_LEN = 1  # 1 byte version field
SALT_LEN = 16
NONCE_LEN = 12  # recommended size for GCM
TAG_LEN = 16    # GCM tag length (128-bit)
FILENAME_LEN_FMT = "!H"  # 2-byte unsigned big-endian
MIN_ENTROPY_BYTES = 1024  # Minimum file size for entropy source validation

# Allowed entropy types by extension (common image & video formats only)
ALLOWED_ENTROPY_EXTS = {
    # Images
    ".jpg", ".jpeg", ".png", ".bmp", ".gif", ".tif", ".tiff", ".jfif",
    # Videos
    ".mp4", ".avi", ".mov", ".mkv", ".webm", ".flv", ".wmv", ".mpeg", ".mpg",
}

USERNAME_RE = re.compile(r"^[A-Za-z0-9_]{3,32}$")

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = MAX_CONTENT_LENGTH_BYTES
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-change-me")

# Session cookie hardening
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SECURE=os.environ.get("FLASK_SECURE_COOKIES", "1") not in {"0", "false", "False"},
    SESSION_COOKIE_SAMESITE="Lax",
)
app.permanent_session_lifetime = 60 * 60 * 24  # 1 day

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
logger = logging.getLogger("encryption_app")


@app.after_request
def add_security_headers(response):
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "DENY")
    # Basic CSP that disallows inline script except the existing theme script in base_css
    response.headers.setdefault(
        "Content-Security-Policy",
        "default-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self' 'unsafe-inline'; img-src 'self' data:; media-src 'self' data:",
    )
    return response

# (No database configuration; JSON files are used for persistence)

# Simple user storage (JSON file with hashed passwords)
USERS_DB_PATH = os.environ.get("USERS_DB_PATH", os.path.join(os.path.dirname(__file__), "users.json"))
USERS_LOCK = RLock()
ALLOW_SELF_SIGNUP = os.environ.get("ALLOW_SELF_SIGNUP", "1") not in {"0", "false", "False"}

# Inbox storage for user-to-user delivery
INBOX_FOLDER = os.path.join(BASE_UPLOAD_FOLDER, "inbox")
os.makedirs(INBOX_FOLDER, exist_ok=True)

# In-memory login rate limiting state
login_attempts: dict = {}


def _cleanup_request_dirs() -> None:
    """
    Best-effort cleanup of old/empty per-request directories under BASE_UPLOAD_FOLDER.
    Removes empty dirs and dirs older than 24 hours.
    """
    cutoff = time.time() - 24 * 60 * 60
    try:
        for name in os.listdir(BASE_UPLOAD_FOLDER):
            if name == "inbox":
                continue
            path = os.path.join(BASE_UPLOAD_FOLDER, name)
            if not os.path.isdir(path):
                continue
            try:
                if not os.listdir(path) or os.path.getmtime(path) < cutoff:
                    shutil.rmtree(path, ignore_errors=True)
            except Exception:
                continue
    except Exception:
        pass

# One-time download token store (persisted). Maps token -> (file_path, download_name, owner_username, created, ttl)
_TOKENS_LOCK = RLock()
TOKENS_DB_PATH = os.path.join(BASE_UPLOAD_FOLDER, "tokens.json")
TOKENS_SEND_DB_PATH = os.path.join(BASE_UPLOAD_FOLDER, "tokens_send.json")

DEFAULT_TOKEN_TTL = 60 * 60 * 24  # 24 hours

# Admin credentials (fully hard-coded, no environment variables involved).
# Change these here in the code if you want different admin credentials.
ADMIN_USERNAME = "admin"
ADMIN_PASSWORD = "sanoop46"

def _purge_expired(tokens: dict) -> dict:
    now = int(time.time())
    out = {}
    for k, v in tokens.items():
        if isinstance(v, (list, tuple)) and len(v) >= 3:
            if len(v) >= 5:
                created = int(v[3])
                ttl = int(v[4])
            else:
                created = 0
                ttl = 0
            if ttl == 0 or (created + ttl) > now:
                out[k] = v
        else:
            out[k] = v
    return out

def _load_tokens() -> dict:
    with _TOKENS_LOCK:
        if not os.path.exists(TOKENS_DB_PATH):
            return {}
        try:
            with open(TOKENS_DB_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                if not isinstance(data, dict):
                    return {}
                data = _purge_expired(data)
                return data
        except Exception:
            return {}

def _save_tokens(tokens: dict) -> None:
    with _TOKENS_LOCK:
        tokens = _purge_expired(tokens)
        os.makedirs(os.path.dirname(TOKENS_DB_PATH), exist_ok=True)
        tmp_path = TOKENS_DB_PATH + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(tokens, f)
        os.replace(tmp_path, TOKENS_DB_PATH)

def _load_transfer_tokens() -> dict:
    with _TOKENS_LOCK:
        if not os.path.exists(TOKENS_SEND_DB_PATH):
            return {}
        try:
            with open(TOKENS_SEND_DB_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                if not isinstance(data, dict):
                    return {}
                data = _purge_expired(data)
                return data
        except Exception:
            return {}

def _save_transfer_tokens(tokens: dict) -> None:
    with _TOKENS_LOCK:
        tokens = _purge_expired(tokens)
        os.makedirs(os.path.dirname(TOKENS_SEND_DB_PATH), exist_ok=True)
        tmp_path = TOKENS_SEND_DB_PATH + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(tokens, f)
        os.replace(tmp_path, TOKENS_SEND_DB_PATH)

# (Removed DB import; JSON files remain the single source of truth)

def _load_users() -> dict:
    """
    Load users from JSON without modifying the file on disk.
    - Usernames are normalized to lowercase keys.
    - Stored password values are left exactly as-is (no auto-hashing/migration).
    This keeps existing plaintext or hashed entries untouched.
    """
    with USERS_LOCK:
        if not os.path.exists(USERS_DB_PATH):
            return {}
        try:
            with open(USERS_DB_PATH, "r", encoding="utf-8") as f:
                raw = json.load(f)
        except Exception:
            return {}

        if not isinstance(raw, dict):
            return {}

        users: dict = {}
        for raw_username, value in raw.items():
            if not isinstance(raw_username, str):
                continue
            username = raw_username.strip()
            if not username:
                continue
            key = username.lower()
            if key in users:
                # Drop duplicates ignoring case
                continue
            # Keep stored password value unchanged (plaintext or hash)
            if not isinstance(value, str):
                continue
            users[key] = value

        return users

def _save_users(users: dict) -> None:
    with USERS_LOCK:
        tmp_path = USERS_DB_PATH + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(users, f)
        os.replace(tmp_path, USERS_DB_PATH)

def _add_user(username: str, password: str) -> None:
    username = (username or "").strip()
    if not USERNAME_RE.match(username or ""):
        raise ValueError(
            "Username must be 3-32 characters, letters A-Z/a-z, digits 0-9 or underscore (_). Usernames are not case-sensitive."
        )
    if username.lower() == ADMIN_USERNAME.lower():
        raise ValueError("Cannot register reserved username.")
    if not password or len(password) < 8:
        raise ValueError("Password must be at least 8 characters.")
    users = _load_users()
    key = username.lower()
    if key in users:
        raise ValueError("Username already exists (case-insensitive).")
    users[key] = generate_password_hash(password)
    _save_users(users)

def _verify_user(username: str, password: str) -> bool:
    username = (username or "").strip()
    if not username or not password:
        return False

    # Admin is authenticated via environment credentials only
    if username.lower() == ADMIN_USERNAME.lower():
        return password == ADMIN_PASSWORD

    users = _load_users()
    ph = users.get(username.lower())
    if not isinstance(ph, str):
        return False

    # Try secure hash verification first (supports any Werkzeug scheme).
    try:
        if check_password_hash(ph, password):
            return True
    except Exception:
        # If the stored value isn't a valid hash, fall back below.
        pass

    # Backward compatibility: if a plaintext password ever slipped through,
    # allow direct comparison so existing users are not locked out.
    return ph == password

def _user_exists(username: str) -> bool:
    uname = (username or "").strip()
    if not uname:
        return False
    if uname.lower() == ADMIN_USERNAME.lower():
        # admin is considered an existing account for auth purposes
        return True
    users = _load_users()
    return uname.lower() in users

def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "username" not in session:
            next_url = request.path
            return redirect(url_for("login", next=next_url))
        return fn(*args, **kwargs)
    return wrapper

def admin_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
            return redirect(url_for("login", next=url_for("admin")))
        return fn(*args, **kwargs)
    return wrapper

def is_allowed_entropy_file(filename: str) -> bool:
    """
    Only allow certain image and video extensions to be used as entropy sources.
    """
    ext = os.path.splitext(filename or "")[1].lower()
    return ext in ALLOWED_ENTROPY_EXTS

def validate_entropy_source(media_path: str) -> dict:
    """
    Collect basic stats about the entropy source without enforcing strict validation.
    This no longer blocks encryption based on file size or entropy estimates.
    Returns dict with: size_bytes, entropy_estimate, frame_count (if video), validation_passed
    """
    file_size = os.path.getsize(media_path)

    ext = os.path.splitext(media_path.lower())[1]
    vid_exts = {".mp4", ".avi", ".mov", ".mkv", ".webm"}

    result = {
        "size_bytes": file_size,
        "entropy_estimate": None,
        "frame_count": None,
        "validation_passed": True,
    }

    # For videos, try to get frame count (best-effort)
    if ext in vid_exts:
        try:
            cap = cv2.VideoCapture(media_path)
            if cap.isOpened():
                frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
                result["frame_count"] = frame_count
            cap.release()
        except Exception:
            pass

    # Simple entropy estimate (for info only, no rejection)
    try:
        with open(media_path, "rb") as f:
            sample = f.read(min(8192, file_size))
            if len(sample) > 0:
                unique_bytes = len(set(sample))
                entropy_estimate = unique_bytes / 256.0  # Normalized 0-1
                result["entropy_estimate"] = entropy_estimate
    except Exception:
        # If anything goes wrong, just return what we have
        pass

    return result

def _hash_file_bytes(media_path: str) -> bytes:
    """Fallback: hash full file bytes if media decoding fails."""
    hasher = hashlib.sha256()
    with open(media_path, "rb") as f:
        while True:
            chunk = f.read(8192)
            if not chunk:
                break
            hasher.update(chunk)
    return hasher.digest()


def generate_raw_key_from_media(media_path: str, frames_to_sample: int = 10) -> bytes:
    """
    Support both images and videos.
    - If image: hash pixel bytes.
    - If video: sample up to frames_to_sample frames (evenly spaced if frame count known),
                update hash incrementally to avoid large memory use.
    Returns 32-byte SHA256 digest.
    """
    ext = os.path.splitext(media_path.lower())[1]
    img_exts = {".jpg", ".jpeg", ".png", ".bmp", ".gif"}
    vid_exts = {".mp4", ".avi", ".mov", ".mkv", ".webm"}

    if ext in img_exts:
        try:
            img = cv2.imread(media_path, cv2.IMREAD_UNCHANGED)
            if img is None:
                return _hash_file_bytes(media_path)
            return hashlib.sha256(img.tobytes()).digest()
        except Exception:
            return _hash_file_bytes(media_path)

    if ext in vid_exts:
        try:
            cap = cv2.VideoCapture(media_path)
            if not cap.isOpened():
                # small wait loop to avoid transient open issues
                start = time.time()
                while not cap.isOpened() and (time.time() - start) < 5.0:
                    time.sleep(0.05)
                if not cap.isOpened():
                    cap.release()
                    return _hash_file_bytes(media_path)

            try:
                total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
            except Exception:
                total_frames = 0

            hasher = hashlib.sha256()
            sampled = 0
            frames_to_sample = min(max(1, frames_to_sample), 12)

            if total_frames and total_frames > 0:
                # Randomly sample unique indices across the full range
                indices = list(range(total_frames))
                random.shuffle(indices)
                for frame_index in indices[:frames_to_sample]:
                    cap.set(cv2.CAP_PROP_POS_FRAMES, int(frame_index))
                    ret, frame = cap.read()
                    if not ret:
                        continue
                    hasher.update(frame.tobytes())
                    sampled += 1
            else:
                # Unknown frame count: read sequentially but only up to frames_to_sample frames
                while sampled < frames_to_sample:
                    ret, frame = cap.read()
                    if not ret:
                        break
                    hasher.update(frame.tobytes())
                    sampled += 1

            cap.release()

            if sampled == 0:
                return _hash_file_bytes(media_path)
            return hasher.digest()
        except Exception:
            return _hash_file_bytes(media_path)

    # For any other extension, treat as unsupported for entropy/key derivation.
    raise ValueError("Unsupported media type for key derivation.")

def derive_enc_key(raw_key: bytes, salt: bytes, passphrase: Optional[str]) -> bytes:
    """
    Derive a 32-byte AES key using HKDF-SHA256.
    The passphrase (if provided) is mixed into the HKDF 'info' to strengthen the key.
    """
    if not isinstance(raw_key, (bytes, bytearray)) or len(raw_key) == 0:
        raise ValueError("Invalid raw key material.")
    if not isinstance(salt, (bytes, bytearray)) or len(salt) != SALT_LEN:
        raise ValueError("Invalid salt length.")

    info_parts = [b"video-file-encryption-aes-gcm"]
    if passphrase:
        info_parts.append(b"|passphrase:")
        info_parts.append(passphrase.encode("utf-8", errors="ignore"))
    info = b"".join(info_parts)

    hkdf = HKDF(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        info=info,
    )
    return hkdf.derive(raw_key)  # 32 bytes

def _ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)

def _make_request_dir() -> str:
    req_id = uuid.uuid4().hex
    req_dir = os.path.join(BASE_UPLOAD_FOLDER, req_id)
    _ensure_dir(req_dir)
    return req_dir


def _safe_join(base: str, *paths: str) -> str:
    """
    Safely join one or more path components to a base directory, preventing
    directory traversal. Raises ValueError if the result escapes the base.
    """
    final_path = os.path.abspath(os.path.join(base, *paths))
    base_path = os.path.abspath(base)
    if os.path.commonpath([final_path, base_path]) != base_path:
        raise ValueError("Unsafe path")
    return final_path

def _create_download_token(file_path: str, download_name: str, owner_username: str, ttl: int = DEFAULT_TOKEN_TTL) -> str:
    token = uuid.uuid4().hex
    tokens = _load_tokens()
    tokens[token] = (file_path, download_name, owner_username, int(time.time()), int(ttl))
    _save_tokens(tokens)
    return token

def _pop_download_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_tokens()
    entry = tokens.pop(token, None)
    _save_tokens(tokens)
    return tuple(entry[:3]) if entry else None

def _get_download_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_tokens()
    entry = tokens.get(token)
    return tuple(entry[:3]) if entry else None

def _create_transfer_token(file_path: str, download_name: str, owner_username: str, ttl: int = DEFAULT_TOKEN_TTL) -> str:
    token = uuid.uuid4().hex
    tokens = _load_transfer_tokens()
    tokens[token] = (file_path, download_name, owner_username, int(time.time()), int(ttl))
    _save_transfer_tokens(tokens)
    return token

def _get_transfer_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_transfer_tokens()
    entry = tokens.get(token)
    return tuple(entry[:3]) if entry else None

def _pop_transfer_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_transfer_tokens()
    entry = tokens.pop(token, None)
    _save_transfer_tokens(tokens)
    return tuple(entry[:3]) if entry else None

def _ensure_inbox_dir(username: str) -> str:
    user_dir = os.path.join(INBOX_FOLDER, secure_filename(username or ""))
    os.makedirs(user_dir, exist_ok=True)
    return user_dir

def encrypt_file_streaming(
    media_path: str,
    plaintext_path: str,
    out_path: str,
    original_filename: str,
    passphrase: Optional[str] = None,
) -> dict:
    """
    Encrypt file using AES-256-GCM with streaming support.
    
    File format (version 1):
    - MAGIC (8 bytes)
    - VERSION (1 byte)
    - SALT (16 bytes)
    - NONCE (12 bytes)
    - FILENAME_LEN (2 bytes, !H)
    - FILENAME (utf-8, variable)
    - CIPHERTEXT (AES-256-GCM, variable)
    - TAG (16 bytes)
    
    AAD = MAGIC || VERSION || SALT || NONCE || FILENAME_LEN || FILENAME
    
    Returns dict with encryption metadata including entropy_info.
    """
    try:
        # Validate and get entropy source info
        entropy_info = validate_entropy_source(media_path)
        
        # Generate random salt and nonce for this encryption
        raw_key = generate_raw_key_from_media(media_path)
        salt = os.urandom(SALT_LEN)  # Unique salt per file
        nonce = os.urandom(NONCE_LEN)  # Unique nonce per file (GCM requirement)
        enc_key = derive_enc_key(raw_key, salt, passphrase)

        filename_bytes = original_filename.encode("utf-8")
        if len(filename_bytes) > 65535:
            raise ValueError("Original filename too long (max 65535 bytes).")

        # Authenticated Additional Data (AAD) - protects header integrity
        aad = b"".join([
            MAGIC,
            bytes([FORMAT_VERSION]),
            salt,
            nonce,
            struct.pack(FILENAME_LEN_FMT, len(filename_bytes)),
            filename_bytes,
        ])

        cipher = Cipher(algorithms.AES(enc_key), modes.GCM(nonce))
        encryptor = cipher.encryptor()
        encryptor.authenticate_additional_data(aad)

        with open(plaintext_path, "rb") as fin, open(out_path, "wb") as fout:
            # Write header: MAGIC | VERSION | SALT | NONCE | FILENAME_LEN | FILENAME
            fout.write(MAGIC)
            fout.write(bytes([FORMAT_VERSION]))
            fout.write(salt)
            fout.write(nonce)
            fout.write(struct.pack(FILENAME_LEN_FMT, len(filename_bytes)))
            fout.write(filename_bytes)

            # Stream encrypt in chunks (supports large files up to 4 GiB)
            bytes_encrypted = 0
            while True:
                chunk = fin.read(CHUNK_SIZE)
                if not chunk:
                    break
                ct = encryptor.update(chunk)
                if ct:
                    fout.write(ct)
                    bytes_encrypted += len(chunk)

            final_ct = encryptor.finalize()
            if final_ct:
                fout.write(final_ct)

            # Write authentication tag (must be last)
            tag = encryptor.tag
            if not tag or len(tag) != TAG_LEN:
                raise ValueError("Encryption failed: invalid authentication tag produced.")
            fout.write(tag)

        return {
            "entropy_info": entropy_info,
            "bytes_encrypted": bytes_encrypted,
            "salt_length": SALT_LEN,
            "nonce_length": NONCE_LEN,
            "format_version": FORMAT_VERSION
        }
    except Exception as e:
        # Clean up any partial files on error
        for path in [out_path]:
            try:
                if os.path.exists(path):
                    os.remove(path)
            except Exception:
                pass
        raise e

def decrypt_file_streaming(
    media_path: str,
    encrypted_path: str,
    out_folder: str,
    passphrase: Optional[str] = None,
) -> str:
    """
    Decrypt file using AES-256-GCM with integrity verification.
    
    Raises ValueError with explicit tampering message if authentication fails.
    Supports streaming for large files.
    """
    file_size = os.path.getsize(encrypted_path)
    # Minimum size for old format (without version) - for backward compatibility
    min_old_format = len(MAGIC) + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + TAG_LEN
    min_new_format = len(MAGIC) + VERSION_LEN + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + TAG_LEN
    if file_size < min_old_format:
        raise ValueError("Encrypted file too small or corrupted (invalid header).")

    with open(encrypted_path, "rb") as fin:
        # Read and verify magic bytes
        magic_read = fin.read(len(MAGIC))
        if magic_read != MAGIC:
            raise ValueError("Invalid file format: magic bytes mismatch. File may be corrupted or not encrypted with this system.")

        # Detect format version (backward compatibility: old files don't have version byte)
        current_pos = fin.tell()
        has_version_field = file_size >= min_new_format
        
        file_version = FORMAT_VERSION
        if has_version_field:
            version_byte = fin.read(VERSION_LEN)
            if len(version_byte) == VERSION_LEN:
                file_version = version_byte[0]
                # Version 0 is invalid, treat as old format
                if file_version == 0:
                    # Rewind and treat as old format
                    fin.seek(current_pos, os.SEEK_SET)
                    has_version_field = False
                    file_version = FORMAT_VERSION
                elif file_version > FORMAT_VERSION:
                    raise ValueError(f"Unsupported file format version {file_version}. This system supports up to version {FORMAT_VERSION}.")
            else:
                # Couldn't read version, treat as old format
                fin.seek(current_pos, os.SEEK_SET)
                has_version_field = False
        else:
            # File too small for new format, must be old format
            has_version_field = False

        # Read salt and nonce
        salt = fin.read(SALT_LEN)
        if len(salt) != SALT_LEN:
            raise ValueError("Corrupted header: invalid salt length.")
        
        nonce = fin.read(NONCE_LEN)
        if len(nonce) != NONCE_LEN:
            raise ValueError("Corrupted header: invalid nonce length.")

        # Read filename
        fname_len_bytes = fin.read(struct.calcsize(FILENAME_LEN_FMT))
        if len(fname_len_bytes) != struct.calcsize(FILENAME_LEN_FMT):
            raise ValueError("Corrupted header: missing filename length.")
        (fname_len,) = struct.unpack(FILENAME_LEN_FMT, fname_len_bytes)
        if fname_len > 65535:
            raise ValueError("Corrupted header: filename length exceeds maximum (65535 bytes).")
        
        filename_bytes = fin.read(fname_len)
        if len(filename_bytes) != fname_len:
            raise ValueError("Corrupted header: filename data incomplete.")
        try:
            original_filename = filename_bytes.decode("utf-8")
        except UnicodeDecodeError:
            raise ValueError("Corrupted header: filename is not valid UTF-8.")

        # Derive decryption key
        raw_key = generate_raw_key_from_media(media_path)
        enc_key = derive_enc_key(raw_key, salt, passphrase)

        # Reconstruct AAD (must match encryption exactly)
        # Old format files don't have version byte in AAD
        if has_version_field:
            aad = b"".join([
                MAGIC,
                bytes([file_version]),
                salt,
                nonce,
                fname_len_bytes,
                filename_bytes,
            ])
        else:
            # Old format: AAD without version byte (for backward compatibility)
            aad = b"".join([
                MAGIC,
                salt,
                nonce,
                fname_len_bytes,
                filename_bytes,
            ])

        # Calculate header length and ciphertext length
        if has_version_field:
            header_len = len(MAGIC) + VERSION_LEN + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + fname_len
        else:
            # Old format: no version byte
            header_len = len(MAGIC) + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + fname_len
        ciphertext_len = file_size - header_len - TAG_LEN
        if ciphertext_len < 0:
            raise ValueError("Corrupted file: calculated ciphertext length is negative (file truncated or malformed).")

        # Read authentication tag from end of file
        fin.seek(file_size - TAG_LEN, os.SEEK_SET)
        tag = fin.read(TAG_LEN)
        if len(tag) != TAG_LEN:
            raise ValueError("Corrupted file: authentication tag missing or incomplete.")
        fin.seek(header_len, os.SEEK_SET)

        # Initialize cipher with tag for verification
        cipher = Cipher(algorithms.AES(enc_key), modes.GCM(nonce, tag))
        decryptor = cipher.decryptor()
        decryptor.authenticate_additional_data(aad)

        # Create temporary output file
        safe_name = secure_filename(original_filename) or "decrypted_output"
        final_out_path = os.path.join(out_folder, safe_name)
        with tempfile.NamedTemporaryFile(prefix=".tmp_", dir=out_folder, delete=False) as tmpf:
            tmp_out_path = tmpf.name

        # Stream decrypt in chunks
        bytes_remaining = ciphertext_len
        try:
            with open(tmp_out_path, "wb") as fout:
                while bytes_remaining > 0:
                    to_read = min(CHUNK_SIZE, bytes_remaining)
                    chunk = fin.read(to_read)
                    if not chunk or len(chunk) < to_read:
                        raise ValueError("Unexpected EOF while reading ciphertext (file truncated).")
                    bytes_remaining -= len(chunk)
                    pt = decryptor.update(chunk)
                    if pt:
                        fout.write(pt)

                # Finalize decryption - this verifies the authentication tag
                final = decryptor.finalize()
                if final:
                    fout.write(final)

            # Atomic replace only after successful verification
            os.replace(tmp_out_path, final_out_path)
            return final_out_path

        except Exception as e:
            # Clean up temp file on error
            try:
                if os.path.exists(tmp_out_path):
                    os.remove(tmp_out_path)
            except Exception:
                pass
            
            # Check if it's an authentication failure
            if "Authentication tag" in str(e) or "authentication" in str(e).lower():
                raise ValueError("INTEGRITY CHECK FAILED: File has been tampered with or corrupted. Authentication tag verification failed. Do not trust the decrypted content.") from e
            raise

# Base CSS without dynamic admin link (to avoid context issues)
base_css = """
<style>
  :root {
    --bg: radial-gradient(circle at top left, #0f172a 0, #020617 55%, #000 100%);
    --surface: rgba(15,23,42,0.9);
    --surface-soft: rgba(15,23,42,0.7);
    --fg: #e5e7eb;
    --muted: #9ca3af;
    --border: rgba(148,163,184,0.35);
    --accent: #6366f1;
    --accent-soft: rgba(99,102,241,0.15);
    --accent-strong: #a855f7;
    --input-bg: rgba(15,23,42,0.85);
    --shadow-soft: 0 18px 45px rgba(15,23,42,0.75);
    --shadow-chip: 0 0 0 1px rgba(148,163,184,0.5);
    --radius-lg: 18px;
    --radius-md: 12px;
    --radius-full: 999px;
    --font-body: system-ui, -apple-system, BlinkMacSystemFont, "SF Pro Text", "Inter", "Segoe UI", sans-serif;
    --font-mono: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "JetBrains Mono", monospace;
  }
  [data-theme="modern"] {
    --bg: radial-gradient(circle at top left, #020617 0, #0b1120 40%, #020617 100%);
  }
  [data-theme="light"] {
    --bg: radial-gradient(circle at top left, #f9fafb 0, #e5e7eb 60%, #d1d5db 100%);
    --surface: rgba(255,255,255,0.92);
    --surface-soft: rgba(255,255,255,0.85);
    --fg: #020617;
    --muted: #6b7280;
    --border: rgba(203,213,225,0.9);
    --input-bg: rgba(248,250,252,0.95);
  }
  [data-theme="retro"] {
    --bg: radial-gradient(circle at top left, #052e16 0, #022c22 55%, #020617 100%);
    --accent: #22c55e;
    --accent-soft: rgba(34,197,94,0.14);
    --accent-strong: #4ade80;
  }
  [data-theme="futuristic"] {
    --bg: radial-gradient(circle at top left, #020617 0, #0b1120 45%, #030712 100%);
    --accent: #38bdf8;
    --accent-soft: rgba(56,189,248,0.14);
    --accent-strong: #a855f7;
  }
  *,
  *::before,
  *::after {
    box-sizing: border-box;
  }
  html, body {
    margin: 0;
    padding: 0;
    min-height: 100vh;
    color: var(--fg);
    font-family: var(--font-body);
    background: var(--bg);
    background-attachment: fixed;
  }
  body {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: flex-start;
  }
  .container {
    width: 100%;
    max-width: 960px;
    padding: 72px 20px 40px;
  }
  .stack {
    display: flex;
    flex-direction: column;
    gap: 20px;
  }
  h1, h2, h3 {
    color: var(--fg);
    font-family: var(--font-mono);
    letter-spacing: 0.06em;
    text-transform: uppercase;
  }
  h2 {
    font-size: 1.4rem;
  }
  h3 {
    font-size: 1.1rem;
  }
  .card {
    background: radial-gradient(circle at top left, rgba(148,163,184,0.18), transparent 45%), var(--surface);
    border-radius: var(--radius-lg);
    padding: 24px 22px;
    border: 1px solid var(--border);
    box-shadow: var(--shadow-soft);
    backdrop-filter: blur(18px) saturate(130%);
    position: relative;
    overflow: hidden;
  }
  .card::before {
    content: "";
    position: absolute;
    inset: 0;
    background: radial-gradient(circle at top right, rgba(96,165,250,0.12), transparent 55%);
    mix-blend-mode: screen;
    opacity: 0.7;
    pointer-events: none;
  }
  .card > * {
    position: relative;
    z-index: 1;
  }
  form {
    display: flex;
    flex-direction: column;
    gap: 12px;
    background: linear-gradient(135deg, rgba(15,23,42,0.95), rgba(15,23,42,0.85));
    border-radius: var(--radius-md);
    padding: 18px 16px 16px;
    border: 1px solid rgba(148,163,184,0.55);
  }
  label {
    font-size: 0.78rem;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    color: var(--muted);
  }
  input[type="file"],
  input[type="submit"],
  input[type="password"],
  input[type="text"] {
    background: var(--input-bg);
    border-radius: var(--radius-md);
    border: 1px solid rgba(148,163,184,0.6);
    color: var(--fg);
    padding: 11px 13px;
    font-family: var(--font-body);
    font-size: 0.95rem;
    outline: none;
    transition: border-color 0.16s ease, box-shadow 0.16s ease, background 0.16s ease, transform 0.06s ease;
    width: 100%;
  }
  input[type="text"]:focus,
  input[type="password"]:focus,
  input[type="file"]:focus-visible {
    border-color: var(--accent);
    box-shadow: 0 0 0 1px rgba(99,102,241,0.7);
  }
  input[type="submit"] {
    margin-top: 6px;
    cursor: pointer;
    background: radial-gradient(circle at top left, var(--accent-strong), var(--accent));
    border: none;
    font-weight: 600;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    box-shadow: 0 16px 35px rgba(15,23,42,0.8);
  }
  input[type="submit"]:hover {
    transform: translateY(-1px);
    box-shadow: 0 22px 45px rgba(15,23,42,0.9);
  }
  input[type="submit"]:active {
    transform: translateY(0);
    box-shadow: 0 10px 28px rgba(15,23,42,0.9);
  }
  a {
    color: var(--accent-strong);
    font-weight: 500;
    text-decoration: none;
  }
  a:hover {
    text-decoration: underline;
  }
  .muted {
    color: var(--muted);
    font-size: 0.9rem;
  }
  .alert-success,
  .alert-error {
    border-radius: var(--radius-md);
    padding: 10px 12px;
    font-size: 0.9rem;
    display: flex;
    align-items: center;
    gap: 8px;
  }
  .alert-success {
    background: var(--accent-soft);
    border: 1px solid rgba(52,211,153,0.35);
    color: #bbf7d0;
  }
  .alert-error {
    background: rgba(248,113,113,0.13);
    border: 1px solid rgba(248,113,113,0.45);
    color: #fecaca;
  }
  .topbar {
    position: fixed;
    top: 0;
    left: 0;
    right: 0;
    z-index: 40;
    padding: 14px 26px;
    display: flex;
    justify-content: center;
    backdrop-filter: blur(20px) saturate(130%);
  }
  .topbar-inner {
    width: 100%;
    max-width: 960px;
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 14px;
    border-radius: var(--radius-full);
    padding: 8px 14px;
    background: linear-gradient(120deg, rgba(15,23,42,0.96), rgba(15,23,42,0.9));
    border: 1px solid rgba(148,163,184,0.5);
    box-shadow: 0 18px 40px rgba(15,23,42,0.85);
  }
  .topbar .links {
    display: flex;
    align-items: center;
    gap: 10px;
  }
  .topbar .links a {
    position: relative;
    padding: 6px 10px;
    border-radius: var(--radius-full);
    font-size: 0.85rem;
    color: var(--muted);
    text-decoration: none;
    transition: background 0.15s ease, color 0.15s ease;
  }
  .topbar .links a::after {
    content: "";
    position: absolute;
    inset: 0;
    border-radius: inherit;
    background: radial-gradient(circle at top, rgba(148,163,184,0.4), transparent 60%);
    opacity: 0;
    transition: opacity 0.18s ease;
    pointer-events: none;
  }
  .topbar .links a:hover {
    color: var(--fg);
    background: rgba(15,23,42,0.9);
  }
  .topbar .links a:hover::after {
    opacity: 1;
  }
  .theme-picker {
    position: relative;
    display: inline-block;
  }
  .theme-button {
    border-radius: var(--radius-full);
    border: 1px solid rgba(148,163,184,0.6);
    background: radial-gradient(circle at top left, rgba(148,163,184,0.35), rgba(15,23,42,0.95));
    color: var(--fg);
    padding: 6px 14px;
    cursor: pointer;
    font-family: var(--font-mono);
    font-size: 0.8rem;
    letter-spacing: 0.06em;
    text-transform: uppercase;
    display: inline-flex;
    align-items: center;
    gap: 6px;
  }
  .theme-menu {
    position: absolute;
    right: 0;
    top: 120%;
    background: var(--surface-soft);
    border: 1px solid rgba(148,163,184,0.6);
    padding: 6px;
    border-radius: var(--radius-md);
    display: none;
    min-width: 160px;
    z-index: 9999;
    box-shadow: 0 16px 40px rgba(15,23,42,0.95);
    backdrop-filter: blur(20px) saturate(140%);
  }
  .theme-menu button {
    display: flex;
    align-items: center;
    width: 100%;
    text-align: left;
    background: transparent;
    border: none;
    color: var(--fg);
    padding: 7px 8px;
    cursor: pointer;
    font-family: var(--font-mono);
    font-size: 0.78rem;
    border-radius: var(--radius-md);
  }
  .theme-menu button:hover {
    background: rgba(15,23,42,0.9);
  }
  @media (max-width: 640px) {
    .topbar-inner {
      padding-inline: 10px;
    }
    .topbar .links {
      gap: 6px;
    }
    .topbar .links a {
      padding-inline: 8px;
      font-size: 0.78rem;
    }
    .card {
      padding-inline: 18px;
    }
  }
</style>
"""

@app.route("/get_theme")
def get_theme():
    # Return current session theme (default 'hacker')
    return jsonify({"theme": session.get("theme", "hacker")})

@app.route("/set_theme", methods=["POST"])
def set_theme():
    try:
        data = request.get_json(force=True)
        theme = (data.get("theme") or "hacker")
        # Only allow known themes
        if theme not in {"hacker", "modern", "light", "retro", "futuristic"}:
            theme = "hacker"
        session["theme"] = theme
        return ("OK", 200)
    except Exception:
        return ("Bad Request", 400)

@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        ip = request.remote_addr or "unknown"

        # Simple in-memory rate limiting: 5 attempts per minute per IP
        now = time.time()
        window = 60.0
        max_attempts = 5
        attempts = login_attempts.setdefault(ip, [])
        attempts[:] = [t for t in attempts if now - t < window]
        if len(attempts) >= max_attempts:
            logger.warning("Rate limit triggered for IP %s", ip)
            return render_template(
                "login.html",
                base_css=base_css,
                allow_signup=ALLOW_SELF_SIGNUP,
                error="Too many login attempts. Please try again later.",
            ), 429

        attempts.append(now)

        # Check if user exists and password is correct
        if _verify_user(username, password):
            # Reset session to avoid fixation and ensure fresh data
            session.clear()
            session["username"] = username.lower()
            session.permanent = True
            logger.info("User '%s' logged in successfully", username.lower())

            # If admin, always redirect to admin dashboard
            if username.lower() == ADMIN_USERNAME.lower():
                return redirect("/admin")
            else:
                # Regular users go to next URL or home
                next_url = request.args.get("next", "/")
                return redirect(next_url)

        logger.warning("Failed login attempt for user '%s' from %s", username, ip)
        return render_template(
            "login.html",
            base_css=base_css,
            allow_signup=ALLOW_SELF_SIGNUP,
            error="Invalid username or password.",
        ), 401

    return render_template("login.html", base_css=base_css, allow_signup=ALLOW_SELF_SIGNUP, error=None)

@app.route("/register", methods=["GET", "POST"])
def register():
    if not ALLOW_SELF_SIGNUP:
        abort(404)
    err = ""
    ok = ""
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        confirm = request.form.get("confirm") or ""
        if password != confirm:
            err = "Passwords do not match."
        else:
            try:
                _add_user(username, password)
                ok = "Account created. You can now log in."
            except Exception as e:
                err = str(e)
    return render_template("register.html", base_css=base_css, ok=ok, err=err)

@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))

@app.route("/", methods=["GET", "POST"])
@login_required
def index():
    if request.method == "POST":
        entropy_file = request.files.get("entropy")
        data_file = request.files.get("data_file")
        passphrase = request.form.get("passphrase") or None

        if not entropy_file or not data_file:
            return render_template(
                "index.html",
                base_css=base_css,
                error="Please upload both an image/video (entropy) and a file to encrypt.",
            )

        if not is_allowed_entropy_file(entropy_file.filename):
            return render_template(
                "index.html",
                base_css=base_css,
                error="Entropy source must be a photo or video (allowed: jpg,jpeg,png,bmp,gif,mp4,avi,mov,mkv,webm).",
            )

        # Check file sizes
        entropy_file.seek(0, 2)  # Seek to end
        entropy_size = entropy_file.tell()
        entropy_file.seek(0)  # Reset position
        
        data_file.seek(0, 2)
        data_size = data_file.tell() 
        data_file.seek(0)
        
        if entropy_size > 100 * 1024 * 1024:  # 100MB limit for entropy
            return render_template(
                "index.html",
                base_css=base_css,
                error="Entropy file too large (max 100MB).",
            )
        
        if data_size > 500 * 1024 * 1024:  # 500MB limit for data
            return render_template(
                "index.html",
                base_css=base_css,
                error="Data file too large (max 500MB).",
            )

        req_dir = _make_request_dir()
        try:
            entropy_filename = secure_filename(entropy_file.filename) or "entropy"
            plaintext_filename = secure_filename(data_file.filename) or "data"

            entropy_path = os.path.join(req_dir, uuid.uuid4().hex)
            plaintext_path = os.path.join(req_dir, uuid.uuid4().hex)
            encrypted_filename = f"{uuid.uuid4().hex}_secret.enc"
            encrypted_path = os.path.join(req_dir, encrypted_filename)

            entropy_file.save(entropy_path)
            data_file.save(plaintext_path)

            # Encrypt and get metadata including entropy info
            encrypt_metadata = encrypt_file_streaming(entropy_path, plaintext_path, encrypted_path, plaintext_filename, passphrase)

            # Cleanup temp inputs
            for p in (entropy_path, plaintext_path):
                try:
                    if os.path.exists(p):
                        os.remove(p)
                except Exception:
                    pass

            token = _create_download_token(encrypted_path, encrypted_filename, session.get("username", ""))
            send_token = _create_transfer_token(encrypted_path, encrypted_filename, session.get("username", ""))
            
            entropy_info = encrypt_metadata.get("entropy_info", {}) or {}

            return render_template(
                "index_result.html",
                base_css=base_css,
                entropy_info=entropy_info,
                bytes_encrypted=encrypt_metadata.get("bytes_encrypted"),
                format_version=encrypt_metadata.get("format_version", 1),
                download_token=token,
                send_token=send_token,
            )
        except Exception as e:
            # Attempt to clean request directory (best-effort)
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return render_template(
                "index.html",
                base_css=base_css,
                error=f"Encryption failed: {e}",
            )

    return render_template("index.html", base_css=base_css)

@app.route("/decrypt", methods=["GET", "POST"])
@login_required
def decrypt():
    if request.method == "POST":
        enc_file = request.files.get("enc_file")
        entropy_file = request.files.get("entropy")
        passphrase = request.form.get("passphrase") or None

        if not enc_file or not entropy_file:
            return render_template(
                "decrypt.html",
                base_css=base_css,
                error="Please upload the encrypted file and the original photo/video used to encrypt it.",
            )

        if not is_allowed_entropy_file(entropy_file.filename):
            return render_template(
                "decrypt.html",
                base_css=base_css,
                error="Entropy source must be a photo or video file.",
            )

        req_dir = _make_request_dir()
        try:
            enc_filename = secure_filename(enc_file.filename) or "encrypted_input.enc"
            entropy_filename = secure_filename(entropy_file.filename) or "entropy"
            enc_path = os.path.join(req_dir, uuid.uuid4().hex)
            entropy_path = os.path.join(req_dir, uuid.uuid4().hex)

            enc_file.save(enc_path)
            entropy_file.save(entropy_path)

            decrypted_path = decrypt_file_streaming(entropy_path, enc_path, req_dir, passphrase)

            # Cleanup temp inputs
            for p in (enc_path, entropy_path):
                try:
                    if os.path.exists(p):
                        os.remove(p)
                except Exception:
                    pass

            download_name = os.path.basename(decrypted_path)
            token = _create_download_token(decrypted_path, download_name, session.get("username", ""))
            return render_template(
                "decrypt_result.html",
                base_css=base_css,
                download_token=token,
            )
        except ValueError as e:
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return render_template(
                "decrypt.html",
                base_css=base_css,
                error=f"Decryption failed: {e}",
            )
        except Exception as e:
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return render_template(
                "decrypt.html",
                base_css=base_css,
                error=f"Unexpected error: {e}",
            )

    return render_template("decrypt.html", base_css=base_css)

@app.route("/send", methods=["POST"])
@login_required
def send_to_user():
    sender = session.get("username", "")
    recipient = (request.form.get("recipient") or "").strip()
    token = (request.form.get("token") or "").strip()

    if not recipient or not token:
        return render_template(
            "index.html",
            base_css=base_css,
            error="Missing recipient or file token.",
        )

    if recipient.lower() == (sender or "").lower():
        return render_template(
            "index.html",
            base_css=base_css,
            error="You cannot send files to yourself.",
        )

    if not _user_exists(recipient):
        return render_template(
            "index.html",
            base_css=base_css,
            error=f"Recipient '{recipient}' does not exist.",
        )

    # Use transfer token store so downloading doesn't invalidate sending
    entry = _get_transfer_token(token)
    if not entry:
        return render_template(
            "index.html",
            base_css=base_css,
            error="File token is invalid or already used.",
        )

    file_path, download_name, owner_username = entry
    if owner_username != sender:
        return render_template(
            "index.html",
            base_css=base_css,
            error="Not authorized to send this file.",
        )

    if not os.path.exists(file_path):
        return render_template(
            "index.html",
            base_css=base_css,
            error="The encrypted file is no longer available.",
        )

    inbox_dir = _ensure_inbox_dir(recipient)
    safe_sender = secure_filename(sender)
    created_ts = int(time.time())
    # Preserve original encrypted name, include sender for context, and prefix created timestamp
    inbox_name = f"{created_ts}_{uuid.uuid4().hex}_from_{safe_sender}_{download_name}"
    dest_path = os.path.join(inbox_dir, inbox_name)

    try:
        os.replace(file_path, dest_path)
    except Exception:
        # Fallback to copy+remove
        try:
            shutil.copy2(file_path, dest_path)
            os.remove(file_path)
        except Exception as e:
            return render_template(
                "index.html",
                base_css=base_css,
                error=f"Failed to deliver: {e}",
            )

    # Invalidate the transfer token after successful delivery
    _pop_transfer_token(token)

    # Best-effort cleanup of the old per-request directory
    try:
        parent_dir = os.path.dirname(file_path)
        if os.path.exists(parent_dir):
            shutil.rmtree(parent_dir, ignore_errors=True)
    except Exception:
        pass

    return render_template(
        "index.html",
        base_css=base_css,
        message=f"File sent to {recipient}!",
    )

@app.route("/inbox", methods=["GET"])
@login_required
def inbox():
    username = session.get("username", "")
    user_dir = _ensure_inbox_dir(username)

    # TTL cleanup: auto-delete inbox files older than 7 days
    cutoff = time.time() - 7 * 24 * 60 * 60
    files = []
    try:
        for f in os.listdir(user_dir):
            path = os.path.join(user_dir, f)
            if not os.path.isfile(path):
                continue
            # Prefer created timestamp embedded in filename if present
            parts = f.split("_", 1)
            ts_ok = False
            if parts and parts[0].isdigit():
                try:
                    created_ts = int(parts[0])
                    if created_ts < cutoff:
                        os.remove(path)
                        continue
                    ts_ok = True
                except Exception:
                    pass
            if not ts_ok:
                try:
                    if os.path.getmtime(path) < cutoff:
                        os.remove(path)
                        continue
                except Exception:
                    pass
            files.append(f)
    except Exception:
        files = []

    return render_template("inbox.html", base_css=base_css, files=sorted(files))

@app.route("/inbox/download/<name>")
@login_required
def inbox_download(name: str):
    username = session.get("username", "")
    user_dir = _ensure_inbox_dir(username)
    safe_name = secure_filename(name)
    try:
        file_path = _safe_join(user_dir, safe_name)
    except ValueError:
        abort(400)

    if not os.path.exists(file_path):
        abort(404)

    @after_this_request
    def cleanup(response):
        try:
            if os.path.exists(file_path):
                os.remove(file_path)
        except Exception:
            pass
        return response

    return send_file(file_path, as_attachment=True, download_name=safe_name)

@app.route("/download/<token>")
@login_required
def download_once(token: str):
    entry = _pop_download_token(token)
    if not entry:
        abort(404)
    file_path, download_name, owner_username = entry
    if session.get("username") != owner_username:
        abort(403)

    if not os.path.exists(file_path):
        abort(404)

    parent_dir = os.path.dirname(file_path)

    @after_this_request
    def cleanup(response):
        try:
            if os.path.exists(file_path):
                os.remove(file_path)
        except Exception:
            pass
        try:
            # Remove the per-request directory if empty or regardless (best-effort)
            if os.path.exists(parent_dir):
                shutil.rmtree(parent_dir, ignore_errors=True)
        except Exception:
            pass
        return response

    try:
        safe_path = _safe_join(BASE_UPLOAD_FOLDER, os.path.relpath(file_path, BASE_UPLOAD_FOLDER))
    except ValueError:
        abort(400)

    return send_file(safe_path, as_attachment=True, download_name=download_name)

# Admin routes
@app.route("/admin")
def admin():
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
    
    users = _load_users()

    user_rows = []
    for u in sorted(users.keys()):
        is_admin = u.lower() == ADMIN_USERNAME.lower()
        user_rows.append(
            {
                "username": u,
                "username_safe": secure_filename(u),
                "role": "Admin" if is_admin else "User",
                "can_view_files": not is_admin,
                "can_delete": not is_admin,
            }
        )

    # Include admin row if not in users DB
    if ADMIN_USERNAME.lower() not in {u.lower() for u in users.keys()}:
        user_rows.insert(
            0,
            {
                "username": ADMIN_USERNAME,
                "username_safe": secure_filename(ADMIN_USERNAME),
                "role": "Admin",
                "can_view_files": False,
                "can_delete": False,
            },
        )

    tokens = _load_tokens()
    transfer_tokens = _load_transfer_tokens()

    token_rows = []
    for t, v in tokens.items():
        try:
            if len(v) >= 3:
                fp, dn, owner = v[0], v[1], v[2]
                token_rows.append(
                    {
                        "token": t,
                        "prefix": t[:16],
                        "owner": owner,
                        "filename": dn,
                        "type": "Download",
                    }
                )
        except Exception:
            continue

    for t, v in transfer_tokens.items():
        try:
            if len(v) >= 3:
                fp, dn, owner = v[0], v[1], v[2]
                token_rows.append(
                    {
                        "token": t,
                        "prefix": t[:16],
                        "owner": owner,
                        "filename": dn,
                        "type": "Transfer",
                    }
                )
        except Exception:
            continue

    return render_template(
        "admin.html",
        base_css=base_css,
        current_user=session.get("username"),
        users=user_rows,
        tokens=token_rows,
        error=None,
    )

@app.route("/admin/user/<username>")
def admin_user_files(username: str):
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
        
    username = secure_filename(username or "")
    try:
        user_dir = _safe_join(INBOX_FOLDER, username)
    except ValueError:
        abort(400)
    files = []
    if os.path.exists(user_dir):
        files = [f for f in os.listdir(user_dir) if os.path.isfile(os.path.join(user_dir, f))]

    return render_template(
        "admin_user_files.html",
        base_css=base_css,
        username=username,
        files=sorted(files),
    )

@app.route("/admin/inbox_download/<username>/<name>")
def admin_inbox_download(username: str, name: str):
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
        
    username = secure_filename(username or "")
    safe_name = secure_filename(name or "")
    try:
        base = _safe_join(INBOX_FOLDER, username)
        file_path = _safe_join(base, safe_name)
    except ValueError:
        abort(400)
    if not os.path.exists(file_path):
        abort(404)
    logger.info("Admin downloaded inbox file '%s' for user '%s'", safe_name, username)
    return send_file(file_path, as_attachment=True, download_name=safe_name)

@app.route("/admin/delete_inbox_file/<username>/<name>")
def admin_delete_inbox_file(username: str, name: str):
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
        
    username = secure_filename(username or "")
    safe_name = secure_filename(name or "")
    try:
        base = _safe_join(INBOX_FOLDER, username)
        file_path = _safe_join(base, safe_name)
    except ValueError:
        abort(400)
    try:
        if os.path.exists(file_path):
            os.remove(file_path)
            logger.info("Admin deleted inbox file '%s' for user '%s'", safe_name, username)
    except Exception:
        pass
    return redirect(url_for("admin_user_files", username=username))

@app.route("/admin/delete_user/<username>")
def admin_delete_user(username: str):
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
        
    username = (username or "").strip()
    if username == ADMIN_USERNAME:
        return render_template(
            "admin.html",
            base_css=base_css,
            current_user=session.get("username"),
            users=[],
            tokens=[],
            error="Cannot delete admin account.",
        )
    users = _load_users()
    if username in users:
        users.pop(username, None)
        _save_users(users)
        logger.info("Admin deleted user '%s'", username)
    # remove inbox dir
    user_dir = os.path.join(INBOX_FOLDER, secure_filename(username))
    try:
        if os.path.exists(user_dir):
            shutil.rmtree(user_dir, ignore_errors=True)
    except Exception:
        pass
    # remove tokens owned by this user
    tokens = _load_tokens()
    tokens = {k:v for k,v in tokens.items() if not (isinstance(v,(list,tuple)) and len(v)>=3 and v[2]==username)}
    _save_tokens(tokens)
    ttokens = _load_transfer_tokens()
    ttokens = {k:v for k,v in ttokens.items() if not (isinstance(v,(list,tuple)) and len(v)>=3 and v[2]==username)}
    _save_transfer_tokens(ttokens)
    return redirect(url_for("admin"))

@app.route("/admin/download_token/<token>")
def admin_download_token(token: str):
    # Check if user is admin
    if (session.get("username") or "").lower() != ADMIN_USERNAME.lower():
        return redirect(url_for("login", next=url_for("admin")))
        
    # Admin may download any file referenced by token (non-destructive)
    entry = _get_download_token(token)
    if not entry:
        abort(404)
    file_path, download_name, owner_username = entry
    if not os.path.exists(file_path):
        abort(404)
    try:
        safe_path = _safe_join(BASE_UPLOAD_FOLDER, os.path.relpath(file_path, BASE_UPLOAD_FOLDER))
    except ValueError:
        abort(400)
    logger.info("Admin downloaded token-based file for owner '%s'", owner_username)
    return send_file(safe_path, as_attachment=True, download_name=download_name)

# Simple health/uptime endpoint for monitoring
@app.route("/health")
def health():
    # Periodic background-style cleanups on health checks
    _cleanup_request_dirs()
    return "OK", 200

if __name__ == "__main__":
    import os
    port = int(os.environ.get("PORT", 5000))
    app.run(debug=False, host="0.0.0.0", port=port)