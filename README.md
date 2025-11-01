# Encryption App (Flask)

Securely encrypt any file (up to 4 GiB) using entropy from a photo/video, with optional passphrase. Includes direct user-to-user sending via inbox and one-time download links.

## Run locally (Windows/PowerShell)

```powershell
cd "E:\\encryption app"
py -3.12 -m venv .venv
& ".\\.venv\\Scripts\\python.exe" -m pip install --upgrade pip
& ".\\.venv\\Scripts\\python.exe" -m pip install -r requirements.txt
$env:SECRET_KEY = "change-me-to-a-long-random-string"
& ".\\.venv\\Scripts\\python.exe" app.py
```

Open http://localhost:5000/login (self-signup enabled by default).

## Features
- AES-256-GCM streaming encryption
- Key derived from image/video frames + optional passphrase via HKDF-SHA256
- One-time download tokens
- Direct send to another user’s inbox
- Persistent token/user store when `uploads/` is mounted

## Deploy on Render
- Web Service → connect GitHub repo
- Build: `pip install --upgrade pip && pip install -r requirements.txt`
- Start: `gunicorn app:app`
- Environment variables:
  - `SECRET_KEY` (required)
  - `ALLOW_SELF_SIGNUP=1` (optional)
  - `USERS_DB_PATH=/opt/render/project/src/uploads/users.json`
- Add a Disk and mount at `/opt/render/project/src/uploads` to persist users/tokens/inbox.

## Health check
- `GET /health` returns `200 OK` with `OK` body.

## Notes
- Accepts common image/video types for entropy: jpg, jpeg, png, bmp, gif, mp4, avi, mov, mkv, webm.
- Keep your original photo/video and passphrase—both are required for decryption.

