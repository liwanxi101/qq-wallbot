"""回归测试：公开副本不能携带私有素材或写死运营者身份。"""

import io
import json
from dataclasses import replace
from pathlib import Path

from PIL import Image

import main


ROOT = Path(__file__).resolve().parents[1]


def test_shipped_source_has_no_personal_media_or_qid():
    source = (ROOT / "main.py").read_text(encoding="utf-8")
    assert "_ADMIN_BADGE_PNG_BASE64" not in source
    assert "_CHAT_BACKGROUND_JPG_BASE64" not in source
    assert main.Settings().owner_whitelist == ()
    assert "_FACE_EMCODE_TEXT" not in source
    assert "_FACE_NAME_TEXT" not in source


def test_defaults_are_brand_free(monkeypatch):
    settings = main.Settings()
    assert settings.owner_whitelist == ()
    assert settings.support_contact_qq == ()
    assert settings.admin_badge_enabled is False
    assert settings.admin_badge_path == ""
    assert settings.chat_background_path == ""
    assert main.admin_badge_bytes(settings) is None
    assert main.chat_background_bytes(settings) is None
    assert main.load_chat_background(settings, 720, 300) is None
    monkeypatch.setattr(main, "_FACE_MAP", {})
    assert main.face_cdn_id("14") is None


def test_custom_media_only_when_explicitly_set(tmp_path):
    image = Image.new("RGB", (16, 16), "white")
    raw = io.BytesIO()
    image.save(raw, format="PNG")
    bg = tmp_path / "own-background.png"
    badge = tmp_path / "own-badge.png"
    bg.write_bytes(raw.getvalue())
    badge.write_bytes(raw.getvalue())
    settings = main.Settings(chat_background_path=str(bg), admin_badge_path=str(badge))
    assert main.chat_background_bytes(settings) == raw.getvalue()
    assert main.admin_badge_bytes(settings) is None
    settings = replace(settings, admin_badge_enabled=True)
    assert main.admin_badge_bytes(settings) == raw.getvalue()
    assert main.load_chat_background(settings, 720, 200) is not None


def test_missing_custom_media_gracefully_falls_back(tmp_path):
    settings = main.Settings(
        chat_background_path=str(tmp_path / "missing.png"),
        admin_badge_path=str(tmp_path / "missing.png"),
        admin_badge_enabled=True,
    )
    assert main.chat_background_bytes(settings) is None
    assert main.admin_badge_bytes(settings) is None
    assert main.load_chat_background(settings, 720, 100) is None


def test_only_user_provided_face_map_is_accepted(tmp_path, monkeypatch):
    path = tmp_path / "my-mapping.json"
    path.write_text(json.dumps({"14": {"cdn_id": "100", "name": "smile"}, "bad": "not an entry"}), encoding="utf-8")
    monkeypatch.setenv("FACE_MAP_PATH", str(path))
    mapping = main._load_face_map()
    assert mapping == {"14": {"cdn_id": "100", "name": "smile"}}
    monkeypatch.setattr(main, "_FACE_MAP", mapping)
    assert main.face_name_of("14") == "smile"
    assert main.face_cdn_id("14") == "100"
    assert main.face_cdn_id("bad") is None

def test_env_search_does_not_inherit_parent_project(tmp_path):
    parent_env = tmp_path / ".env"
    parent_env.write_text("OWNER_QQ=123456789", encoding="utf-8")
    project_dir = tmp_path / "public-project"
    project_dir.mkdir()
    assert main._find_env_file(start=project_dir, limit=1) is None
    own_env = project_dir / ".env"
    own_env.write_text("OWNER_QQ=", encoding="utf-8")
    assert main._find_env_file(start=project_dir, limit=1) == own_env


def test_documented_health_route_exists():
    assert any(getattr(route, "path", None) == "/healthz" for route in main.app.routes)
