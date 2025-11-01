import os
import uuid
import struct
import shutil
import hashlib
import json
from typing import Tuple, Optional
from threading import Lock
from functools import wraps

from flask import Flask, request, send_file, abort, after_this_request, session, redirect, url_for
from werkzeug.utils import secure_filename
from werkzeug.security import generate_password_hash, check_password_hash

import cv2
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

# Storage and limits
BASE_UPLOAD_FOLDER = "uploads"
os.makedirs(BASE_UPLOAD_FOLDER, exist_ok=True)
MAX_CONTENT_LENGTH_BYTES = 4 * 1024 * 1024 * 1024  # 4 GiB
CHUNK_SIZE = 1024 * 1024  # 1 MiB for better throughput

# File format constants (GCM-based)
MAGIC = b"VKEYGCM1"
SALT_LEN = 16
NONCE_LEN = 12  # recommended size for GCM
TAG_LEN = 16    # GCM tag length (128-bit)
FILENAME_LEN_FMT = "!H"  # 2-byte unsigned big-endian

# Allowed entropy types by extension
ALLOWED_ENTROPY_EXTS = {
    ".mp4", ".avi", ".mov", ".mkv", ".jpg", ".jpeg", ".png", ".bmp", ".webm", ".gif"
}

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = MAX_CONTENT_LENGTH_BYTES
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-change-me")

# Simple user storage (JSON file with hashed passwords)
USERS_DB_PATH = os.environ.get("USERS_DB_PATH", os.path.join(os.path.dirname(__file__), "users.json"))
USERS_LOCK = Lock()
ALLOW_SELF_SIGNUP = os.environ.get("ALLOW_SELF_SIGNUP", "1") not in {"0", "false", "False"}

# Inbox storage for user-to-user delivery
INBOX_FOLDER = os.path.join(BASE_UPLOAD_FOLDER, "inbox")
os.makedirs(INBOX_FOLDER, exist_ok=True)

# One-time download token store (persisted). Maps token -> (file_path, download_name, owner_username)
_TOKENS_LOCK = Lock()
TOKENS_DB_PATH = os.path.join(BASE_UPLOAD_FOLDER, "tokens.json")
TOKENS_SEND_DB_PATH = os.path.join(BASE_UPLOAD_FOLDER, "tokens_send.json")


def _load_tokens() -> dict:
    with _TOKENS_LOCK:
        if not os.path.exists(TOKENS_DB_PATH):
            return {}
        try:
            with open(TOKENS_DB_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}


def _save_tokens(tokens: dict) -> None:
    with _TOKENS_LOCK:
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
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}


def _save_transfer_tokens(tokens: dict) -> None:
    with _TOKENS_LOCK:
        os.makedirs(os.path.dirname(TOKENS_SEND_DB_PATH), exist_ok=True)
        tmp_path = TOKENS_SEND_DB_PATH + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(tokens, f)
        os.replace(tmp_path, TOKENS_SEND_DB_PATH)


def _load_users() -> dict:
    with USERS_LOCK:
        if not os.path.exists(USERS_DB_PATH):
            return {}
        try:
            with open(USERS_DB_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}


def _save_users(users: dict) -> None:
    with USERS_LOCK:
        tmp_path = USERS_DB_PATH + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(users, f)
        os.replace(tmp_path, USERS_DB_PATH)


def _add_user(username: str, password: str) -> None:
    username = (username or "").strip()
    if not username or len(username) < 3:
        raise ValueError("Username must be at least 3 characters.")
    if not password or len(password) < 8:
        raise ValueError("Password must be at least 8 characters.")
    users = _load_users()
    if username in users:
        raise ValueError("Username already exists.")
    users[username] = generate_password_hash(password)
    _save_users(users)


def _verify_user(username: str, password: str) -> bool:
    users = _load_users()
    ph = users.get(username or "")
    return bool(ph and check_password_hash(ph, password or ""))


def _user_exists(username: str) -> bool:
    users = _load_users()
    return (username or "") in users


def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if "username" not in session:
            next_url = request.path
            return redirect(url_for("login", next=next_url))
        return fn(*args, **kwargs)
    return wrapper


def is_allowed_entropy_file(filename: str) -> bool:
    ext = os.path.splitext(filename or "")[1].lower()
    return ext in ALLOWED_ENTROPY_EXTS


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
        img = cv2.imread(media_path, cv2.IMREAD_UNCHANGED)
        if img is None:
            raise RuntimeError("Could not read image for key derivation.")
        return hashlib.sha256(img.tobytes()).digest()

    if ext in vid_exts:
        cap = cv2.VideoCapture(media_path)
        if not cap.isOpened():
            cap.release()
            raise RuntimeError("Could not open video for key derivation.")

        try:
            total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
        except Exception:
            total_frames = 0

        hasher = hashlib.sha256()
        sampled = 0

        if total_frames and total_frames > 0:
            # Evenly sample indices across the full range
            for i in range(frames_to_sample):
                frame_index = int(i * max(total_frames - 1, 0) / max(frames_to_sample - 1, 1))
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_index)
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
            raise RuntimeError("No frame data could be read from the video for key derivation.")
        return hasher.digest()

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


def _create_download_token(file_path: str, download_name: str, owner_username: str) -> str:
    token = uuid.uuid4().hex
    tokens = _load_tokens()
    tokens[token] = (file_path, download_name, owner_username)
    _save_tokens(tokens)
    return token


def _pop_download_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_tokens()
    entry = tokens.pop(token, None)
    _save_tokens(tokens)
    return tuple(entry) if entry else None


def _get_download_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_tokens()
    entry = tokens.get(token)
    return tuple(entry) if entry else None


def _create_transfer_token(file_path: str, download_name: str, owner_username: str) -> str:
    token = uuid.uuid4().hex
    tokens = _load_transfer_tokens()
    tokens[token] = (file_path, download_name, owner_username)
    _save_transfer_tokens(tokens)
    return token


def _get_transfer_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_transfer_tokens()
    entry = tokens.get(token)
    return tuple(entry) if entry else None


def _pop_transfer_token(token: str) -> Optional[Tuple[str, str, str]]:
    tokens = _load_transfer_tokens()
    entry = tokens.pop(token, None)
    _save_transfer_tokens(tokens)
    return tuple(entry) if entry else None


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
) -> None:
    """
    File format:
    - MAGIC
    - salt (16)
    - nonce (12)
    - filename_len (2, !H)
    - filename (utf-8)
    - ciphertext (AES-256-GCM)
    - tag (16)
    AAD = MAGIC || salt || nonce || filename_len || filename
    """
    raw_key = generate_raw_key_from_media(media_path)
    salt = os.urandom(SALT_LEN)
    enc_key = derive_enc_key(raw_key, salt, passphrase)
    nonce = os.urandom(NONCE_LEN)

    filename_bytes = original_filename.encode("utf-8")
    if len(filename_bytes) > 65535:
        raise ValueError("Original filename too long.")

    aad = b"".join([
        MAGIC,
        salt,
        nonce,
        struct.pack(FILENAME_LEN_FMT, len(filename_bytes)),
        filename_bytes,
    ])

    cipher = Cipher(algorithms.AES(enc_key), modes.GCM(nonce))
    encryptor = cipher.encryptor()
    encryptor.authenticate_additional_data(aad)

    with open(plaintext_path, "rb") as fin, open(out_path, "wb") as fout:
        # header
        fout.write(MAGIC)
        fout.write(salt)
        fout.write(nonce)
        fout.write(struct.pack(FILENAME_LEN_FMT, len(filename_bytes)))
        fout.write(filename_bytes)

        # stream encrypt
        while True:
            chunk = fin.read(CHUNK_SIZE)
            if not chunk:
                break
            ct = encryptor.update(chunk)
            if ct:
                fout.write(ct)

        final_ct = encryptor.finalize()
        if final_ct:
            fout.write(final_ct)

        tag = encryptor.tag
        if not tag or len(tag) != TAG_LEN:
            raise ValueError("Encryption failed to produce valid authentication tag.")
        fout.write(tag)


def decrypt_file_streaming(
    media_path: str,
    encrypted_path: str,
    out_folder: str,
    passphrase: Optional[str] = None,
) -> str:
    file_size = os.path.getsize(encrypted_path)
    min_size = len(MAGIC) + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + TAG_LEN
    if file_size < min_size:
        raise ValueError("Encrypted file too small or corrupted.")

    with open(encrypted_path, "rb") as fin:
        magic_read = fin.read(len(MAGIC))
        if magic_read != MAGIC:
            raise ValueError("Unsupported or corrupted encrypted file (magic mismatch).")

        salt = fin.read(SALT_LEN)
        nonce = fin.read(NONCE_LEN)
        fname_len_bytes = fin.read(struct.calcsize(FILENAME_LEN_FMT))
        (fname_len,) = struct.unpack(FILENAME_LEN_FMT, fname_len_bytes)
        if fname_len > 65535:
            raise ValueError("Corrupted header (filename length invalid).")
        filename_bytes = fin.read(fname_len)
        try:
            original_filename = filename_bytes.decode("utf-8")
        except Exception:
            raise ValueError("Corrupted header (filename decode failed).")

        raw_key = generate_raw_key_from_media(media_path)
        enc_key = derive_enc_key(raw_key, salt, passphrase)

        aad = b"".join([MAGIC, salt, nonce, fname_len_bytes, filename_bytes])

        # Determine ciphertext length and read tag from the end
        header_len = len(MAGIC) + SALT_LEN + NONCE_LEN + struct.calcsize(FILENAME_LEN_FMT) + fname_len
        ciphertext_len = file_size - header_len - TAG_LEN
        if ciphertext_len < 0:
            raise ValueError("Encrypted file corrupted (inconsistent lengths).")

        # Read tag from end, then seek back to ciphertext start
        fin.seek(file_size - TAG_LEN, os.SEEK_SET)
        tag = fin.read(TAG_LEN)
        if len(tag) != TAG_LEN:
            raise ValueError("Missing or short authentication tag.")
        fin.seek(header_len, os.SEEK_SET)

        cipher = Cipher(algorithms.AES(enc_key), modes.GCM(nonce, tag))
        decryptor = cipher.decryptor()
        decryptor.authenticate_additional_data(aad)

        safe_name = secure_filename(original_filename) or "decrypted_output"
        final_out_path = os.path.join(out_folder, safe_name)
        tmp_out_path = os.path.join(out_folder, f".tmp_{uuid.uuid4().hex}")

        bytes_remaining = ciphertext_len
        with open(tmp_out_path, "wb") as fout:
            while bytes_remaining > 0:
                to_read = min(CHUNK_SIZE, bytes_remaining)
                chunk = fin.read(to_read)
                if not chunk:
                    raise ValueError("Unexpected EOF while reading ciphertext.")
                bytes_remaining -= len(chunk)
                pt = decryptor.update(chunk)
                if pt:
                    fout.write(pt)

            final = decryptor.finalize()
            if final:
                fout.write(final)

        # Atomic replace after successful verification
        os.replace(tmp_out_path, final_out_path)
        return final_out_path


base_css = """
<style>
  body { background-color: #000; color: #00FF00; font-family: 'Courier New', monospace; margin: 40px auto; max-width: 900px; line-height: 1.5; text-shadow: 0 0 5px #00FF00; }
  h2,h3 { color:#00FF00; text-shadow:0 0 10px #00FF00; }
  input[type="file"], input[type="submit"], input[type="password"], input[type="text"] { background:#111; border:1px solid #00FF00; color:#00FF00; padding:10px; font-family:monospace; font-size:16px; margin:5px 0 15px 0; display:block; width:100%; box-sizing:border-box; }
  input[type="submit"] { cursor:pointer; transition:background-color .3s; }
  input[type="submit"]:hover { background:#00FF00; color:#000; font-weight:bold; }
  form { border:2px solid #00FF00; padding:20px; border-radius:10px; box-shadow:0 0 20px #00FF00; }
  a { color:#00FF00; font-weight:bold; text-decoration:none; }
  small { color: #7CFC00; }
</style>
"""


@app.route("/login", methods=["GET", "POST"])
def login():
    err = ""
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        next_url = request.args.get("next") or url_for("index")
        if _verify_user(username, password):
            session["username"] = username
            return redirect(next_url)
        else:
            err = "Invalid username or password."

    signup_link = ("<p><a href=\"/register\">Create an account</a></p>" if ALLOW_SELF_SIGNUP else "<small>Signup disabled</small>")
    return base_css + f"""
    <h2>Login</h2>
    <form method="POST">
        Username: <input type="text" name="username" required><br>
        Password: <input type="password" name="password" required><br>
        <input type="submit" value="Login">
    </form>
    <p style='color:red;'>{err}</p>
    {signup_link}
    """


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
    return base_css + f"""
    <h2>Register</h2>
    <form method="POST">
        Username: <input type="text" name="username" required><br>
        Password: <input type="password" name="password" required><br>
        Confirm: <input type="password" name="confirm" required><br>
        <input type="submit" value="Create account">
    </form>
    <p style='color:lime;'>{ok}</p>
    <p style='color:red;'>{err}</p>
    <p><a href="/login">Back to Login</a></p>
    """


@app.route("/logout")
def logout():
    session.pop("username", None)
    return redirect(url_for("login"))


@app.route("/", methods=["GET", "POST"])
@login_required
def index():
    if request.method == "POST":
        entropy_file = request.files.get("entropy")
        data_file = request.files.get("data_file")
        passphrase = request.form.get("passphrase") or None

        if not entropy_file or not data_file:
            return base_css + "<p style='color:red;'>Please upload both an image/video (entropy) and a file to encrypt.</p>"

        if not is_allowed_entropy_file(entropy_file.filename):
            return base_css + "<p style='color:red;'>Entropy source must be a photo or video (allowed: jpg,jpeg,png,bmp,gif,mp4,avi,mov,mkv,webm).</p>"

        req_dir = _make_request_dir()
        try:
            entropy_filename = secure_filename(entropy_file.filename) or f"{uuid.uuid4().hex}_entropy"
            plaintext_filename = secure_filename(data_file.filename) or f"{uuid.uuid4().hex}_data"

            entropy_path = os.path.join(req_dir, f"entropy_{entropy_filename}")
            plaintext_path = os.path.join(req_dir, f"plain_{plaintext_filename}")
            encrypted_filename = f"{uuid.uuid4().hex}_secret.enc"
            encrypted_path = os.path.join(req_dir, encrypted_filename)

            entropy_file.save(entropy_path)
            data_file.save(plaintext_path)

            encrypt_file_streaming(entropy_path, plaintext_path, encrypted_path, plaintext_filename, passphrase)

            # Cleanup temp inputs
            for p in (entropy_path, plaintext_path):
                try:
                    if os.path.exists(p):
                        os.remove(p)
                except Exception:
                    pass

            token = _create_download_token(encrypted_path, encrypted_filename, session.get("username", ""))
            send_token = _create_transfer_token(encrypted_path, encrypted_filename, session.get("username", ""))
            return base_css + f"""
                <h3>Encryption completed!</h3>
                <p><a href="/download/{token}">Download Encrypted File</a></p>
                <p><strong>Keep the original photo/video and passphrase (if used) safe.</strong> You will need the same to decrypt.</p>
                <p><a href="/decrypt">Go to Decryption Page</a></p>
                <small>Note: download link is one-time. The file is deleted after download.</small>
                <hr>
                <h3>Send Encrypted File to a User</h3>
                <form method="POST" action="/send">
                    <input type="hidden" name="token" value="{send_token}">
                    Recipient Username: <input type="text" name="recipient" required><br>
                    <input type="submit" value="Send to User">
                </form>
                <p><a href="/inbox">Go to Inbox</a></p>
            """
        except Exception as e:
            # Attempt to clean request directory (best-effort)
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return base_css + f"<h3 style='color:red;'>Encryption failed:</h3><pre>{str(e)}</pre>"

    return base_css + """
    <h2>Encrypt Any File — Entropy must be Image or Video</h2>
    <form method="POST" enctype="multipart/form-data">
        Photo or Video (used as entropy source): <input type="file" name="entropy" accept="image/*,video/*" required><br>
        Optional passphrase (recommended): <input type="password" name="passphrase" placeholder="Leave empty to skip"><br>
        File to encrypt: <input type="file" name="data_file" required><br>
        <input type="submit" value="Encrypt">
    </form>
    <p><a href="/decrypt">Go to Decryption Page</a></p>
    <p><a href="/inbox">Inbox</a></p>
    """


@app.route("/decrypt", methods=["GET", "POST"])
@login_required
def decrypt():
    if request.method == "POST":
        enc_file = request.files.get("enc_file")
        entropy_file = request.files.get("entropy")
        passphrase = request.form.get("passphrase") or None

        if not enc_file or not entropy_file:
            return base_css + "<p style='color:red;'>Please upload the encrypted file and the original photo/video used to encrypt it.</p>"

        if not is_allowed_entropy_file(entropy_file.filename):
            return base_css + "<p style='color:red;'>Entropy source must be a photo or video file.</p>"

        req_dir = _make_request_dir()
        try:
            enc_filename = secure_filename(enc_file.filename) or f"{uuid.uuid4().hex}_in.enc"
            entropy_filename = secure_filename(entropy_file.filename) or f"{uuid.uuid4().hex}_entropy"
            enc_path = os.path.join(req_dir, f"in_{enc_filename}")
            entropy_path = os.path.join(req_dir, f"entropy_{entropy_filename}")

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
            return base_css + f"""
                <h3>Decryption successful!</h3>
                <p><a href="/download/{token}">Download Decrypted File</a></p>
                <p><a href="/">Back to Encryption</a></p>
                <small>Note: download link is one-time. The file is deleted after download.</small>
            """
        except ValueError as e:
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return base_css + f"<h3 style='color:red;'>Decryption failed:</h3><pre>{str(e)}</pre>"
        except Exception as e:
            try:
                if os.path.exists(req_dir):
                    shutil.rmtree(req_dir, ignore_errors=True)
            except Exception:
                pass
            return base_css + f"<h3 style='color:red;'>Unexpected error:</h3><pre>{str(e)}</pre>"

    return base_css + """
    <h2>Decrypt File (requires original photo/video and passphrase if used)</h2>
    <form method="POST" enctype="multipart/form-data">
        Encrypted file: <input type="file" name="enc_file" required><br>
        Original photo or video (used at encryption time): <input type="file" name="entropy" accept="image/*,video/*" required><br>
        Passphrase (if you set one during encryption): <input type="password" name="passphrase" placeholder="Leave empty if none"><br>
        <input type="submit" value="Decrypt">
    </form>
    <p><a href="/">Go back to Encryption Page</a></p>
    <p><a href="/inbox">Inbox</a></p>
    """


@app.route("/send", methods=["POST"])
@login_required
def send_to_user():
    sender = session.get("username", "")
    recipient = (request.form.get("recipient") or "").strip()
    token = (request.form.get("token") or "").strip()

    if not recipient or not token:
        return base_css + "<p style='color:red;'>Missing recipient or file token.</p><p><a href='/'>Back</a></p>"

    if not _user_exists(recipient):
        return base_css + f"<p style='color:red;'>Recipient '{recipient}' does not exist.</p><p><a href='/'>Back</a></p>"

    # Use transfer token store so downloading doesn't invalidate sending
    entry = _get_transfer_token(token)
    if not entry:
        return base_css + "<p style='color:red;'>File token is invalid or already used.</p><p><a href='/'>Back</a></p>"

    file_path, download_name, owner_username = entry
    if owner_username != sender:
        return base_css + "<p style='color:red;'>Not authorized to send this file.</p><p><a href='/'>Back</a></p>"

    if not os.path.exists(file_path):
        return base_css + "<p style='color:red;'>The encrypted file is no longer available.</p><p><a href='/'>Back</a></p>"

    inbox_dir = _ensure_inbox_dir(recipient)
    safe_sender = secure_filename(sender)
    # Preserve original encrypted name, include sender for context
    inbox_name = f"{uuid.uuid4().hex}_from_{safe_sender}_{download_name}"
    dest_path = os.path.join(inbox_dir, inbox_name)

    try:
        os.replace(file_path, dest_path)
    except Exception:
        # Fallback to copy+remove
        try:
            shutil.copy2(file_path, dest_path)
            os.remove(file_path)
        except Exception as e:
            return base_css + f"<h3 style='color:red;'>Failed to deliver:</h3><pre>{str(e)}</pre><p><a href='/'>Back</a></p>"

    # Invalidate the transfer token after successful delivery
    _pop_transfer_token(token)

    # Best-effort cleanup of the old per-request directory
    try:
        parent_dir = os.path.dirname(file_path)
        if os.path.exists(parent_dir):
            shutil.rmtree(parent_dir, ignore_errors=True)
    except Exception:
        pass

    return base_css + f"""
        <h3>File sent to {recipient}!</h3>
        <p><a href="/inbox">Go to your Inbox</a></p>
        <p><a href="/">Back to Encryption</a></p>
    """


@app.route("/inbox", methods=["GET"])
@login_required
def inbox():
    username = session.get("username", "")
    user_dir = _ensure_inbox_dir(username)

    try:
        files = [f for f in os.listdir(user_dir) if os.path.isfile(os.path.join(user_dir, f))]
    except Exception:
        files = []

    items_html = "".join(
        f"<li>{f} — <a href=\"/inbox/download/{secure_filename(f)}\">Download</a></li>"
        for f in sorted(files)
    ) or "<li>No messages.</li>"

    return base_css + f"""
        <h2>Inbox</h2>
        <ul>
            {items_html}
        </ul>
        <p><a href="/">Back to Encryption</a></p>
    """


@app.route("/inbox/download/<name>")
@login_required
def inbox_download(name: str):
    username = session.get("username", "")
    user_dir = _ensure_inbox_dir(username)
    safe_name = secure_filename(name)
    file_path = os.path.join(user_dir, safe_name)

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

    return send_file(file_path, as_attachment=True, download_name=download_name)


# Simple health/uptime endpoint for monitoring
@app.route("/health")
def health():
    return "OK", 200


if __name__ == "__main__":
    # When testing locally, this will still run.
    # When deployed with gunicorn or a platform, they will ignore app.run.
    import os
    port = int(os.environ.get("PORT", 5000))
    app.run(debug=False, host="0.0.0.0", port=port)
