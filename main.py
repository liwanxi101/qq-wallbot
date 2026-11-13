"""QQ 校园墙投稿服务：NapCat / OneBot v11、FastAPI 与 QQ 空间。

主要模块：Settings 统一读取环境变量，SubmissionManager 收集私聊投稿并执行
限额、审核与发布，Database 持久化审核结果和空间 tid，QZonePublisher
完成图片上传和说说发布，ConnectionManager 路由 OneBot 事件与回执。

安全约束：审核失败不发布；公开图片须纳入审核；管理员命令按角色
再次鉴权；仅在部署者显式配置时读取背景与徽标图片，默认纯色渲染。
匿名仅影响公开截图，不删除数据库内的投稿身份。

独立开源副本不包含原部署者身份、用户数据、校园素材或第三方表情表。
运行前应配置 .env 并阅读 docs/TECHNICAL_MANUAL.md。
"""

from __future__ import annotations

import asyncio
import base64
import contextlib
import glob
import hashlib
import io
import ipaddress
import json
import logging
import math
import os
import re
import shutil
import time
import uuid
from collections.abc import Mapping
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone, tzinfo
from pathlib import Path
from typing import Any, Iterable, Sequence
from zoneinfo import ZoneInfo

import aiosqlite
import httpx
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from openai import AsyncOpenAI
from PIL import Image, ImageChops, ImageDraw, ImageFont

try:  # qzone-sdk 是发布环节的可选重依赖：缺失时给出明确报错，而不是导入期崩溃。
    from qzone_sdk import ManualCookieProvider, NapCatAuthProvider, QZoneClient, QZoneConfig

    try:  # 接口地址优先跟随 SDK 的定义；SDK 内部结构变动时退回下面的内置地址常量
        from qzone_sdk.constants import URLS as _QZONE_URLS  # type: ignore[import-not-found]
    except Exception:  # pragma: no cover - 只在 SDK 换了模块布局时走到
        _QZONE_URLS = {}
except ImportError:  # pragma: no cover - 依赖缺失路径由 QZonePublisher 显式报错覆盖
    ManualCookieProvider = NapCatAuthProvider = QZoneClient = QZoneConfig = None  # type: ignore[assignment]
    _QZONE_URLS = {}

from dotenv import load_dotenv

logger = logging.getLogger("campus-wall")

# --------------------------------------------------------------------------------------
# 零、.env 加载（必须早于任何 Settings 读取）
# --------------------------------------------------------------------------------------
#
# 「配置改了没生效」在本项目出现过四次（DEEPSEEK_MODEL / IDLE_TIMEOUT_SECONDS /
# RATE_LIMIT_WINDOW_SECONDS / DEEPSEEK_API_KEY），所以这里把两件事显式化：
#   1) 找到的到底是哪个 .env 文件（从 cwd 逐级向上找，与 python-dotenv 同语义）；
#   2) 值的**优先级**：文件里的非空值 > 进程环境变量 > 代码默认值。
#
# 为什么不直接用 load_dotenv()：它默认 override=False，只要旧值被 export 在
# shell / systemd 里，改 .env 就永远不生效 —— 而且没有任何提示（ERR-013）。
# 为什么空值不覆盖：示例文件里保留着 `DEEPSEEK_API_KEY=` 这类空行，
# 若让空值生效，反而会把真正可用的环境变量清掉，变成「明明配了 key 却提示未配置」。

_ENV_FILE_PATH: Path | None = None
_ENV_FILE_VALUES: dict[str, str] = {}
_ENV_AT_START: dict[str, str] = {}
_ENV_FILE_OVERRIDES: list[str] = []


def _find_env_file(start: Path | None = None, limit: int = 5) -> Path | None:
    """从 `start`（默认 cwd）逐级向上找 `.env`，最多上溯 limit 层。

    与 python-dotenv 的查找语义一致：cwd 是决定读哪个 .env 的关键 ——
    「改了文件没生效」有一部分就是**从别的目录启动**，读到的是另一份 .env。
    """
    directory = (start or Path.cwd()).resolve()
    for _ in range(max(1, limit)):
        candidate = directory / ".env"
        if candidate.is_file():
            return candidate
        if directory.parent == directory:
            break
        directory = directory.parent
    return None


def _read_env_file(path: Path) -> dict[str, str] | None:
    """解析 .env 文件；python-dotenv 不可用时返回 None（由调用方退回官方 load_dotenv）。"""
    try:
        from dotenv import dotenv_values  # python-dotenv >= 0.16
    except Exception:  # pragma: no cover - 依赖缺失时走回退分支
        return None
    try:
        values = dotenv_values(path)
    except Exception:
        logger.warning(".env 解析失败，按「未配置」处理：%s", path, exc_info=True)
        return None
    return {str(key): value for key, value in values.items() if value is not None}


def _apply_env_values(values: dict[str, str], environ: dict[str, str]) -> list[str]:
    """把 .env 里的**非空**值写进环境；返回「被覆盖掉的原值不相同」的键名。

    空值一律跳过（见本节开头的说明）。返回值只用于日志：让「.env 压过了外部环境变量」
    这件事在启动日志里留痕，下次就不用再靠猜。
    """
    overridden: list[str] = []
    for name, value in values.items():
        if value is None or value.strip() == "":
            continue
        previous = environ.get(name)
        if previous is not None and previous != value:
            overridden.append(name)
        environ[name] = value
    return overridden


def _load_env() -> bool:
    """加载 .env，返回「是否找到了文件」。结果同时记进本节的几个模块级变量。"""
    global _ENV_FILE_PATH
    global _ENV_FILE_VALUES
    global _ENV_AT_START
    global _ENV_FILE_OVERRIDES

    # 只读取当前项目目录的 .env，不继承父目录旧项目的账号或密钥。
    _ENV_FILE_PATH = _find_env_file(start=Path(__file__).resolve().parent, limit=1)
    _ENV_AT_START = dict(os.environ)
    if _ENV_FILE_PATH is None:
        return False

    values = _read_env_file(_ENV_FILE_PATH)
    if values is None:
        # 没有 python-dotenv（或解析失败）：退回官方实现，保持可用（但不覆盖进程环境变量）
        return bool(load_dotenv(_ENV_FILE_PATH))

    _ENV_FILE_VALUES = values
    _ENV_FILE_OVERRIDES = _apply_env_values(values, os.environ)
    return True


_DOTENV_LOADED = _load_env()
if _ENV_FILE_OVERRIDES:
    logger.info(
        "配置来源：.env 覆盖了同名的进程环境变量 %s（文件优先）",
        ", ".join(sorted(_ENV_FILE_OVERRIDES)),
    )


def mask_secret(value: str) -> str:
    """把密钥打码成「前 6 位…后 4 位（共 N 字符）」。

    用途是日志：确认「新 key 到底换上没有」时需要一个可比对的指纹，
    但完整密钥绝不能进日志（日志会被发给别人排查）。
    """
    text = (value or "").strip()
    if not text:
        return "未配置"
    if len(text) <= 12:
        return f"***（{len(text)} 字符）"
    return f"{text[:6]}…{text[-4:]}（{len(text)} 字符）"


def describe_config_source(name: str, value: str) -> str:
    """说明某个配置项的取值来自哪一层（.env / 进程环境变量 / 代码默认值）。"""
    if not value:
        return "未配置（代码默认值也为空）"
    if _ENV_FILE_VALUES.get(name) == value:
        return f".env（{_ENV_FILE_PATH}）"
    if name in _ENV_AT_START:
        return "进程环境变量（systemd / shell export）"
    return "代码内默认值"

# --------------------------------------------------------------------------------------
# 一、配置
# --------------------------------------------------------------------------------------


def _env_str(name: str, default: str) -> str:
    """解析字符串环境变量；未设置或为空串一律回退默认值。

    与 config.example.env 的约定一致（"值为空的项表示使用代码内默认值"）：
    容器/编排里常见的 `KEY=` 空值写法不应把默认值清空。
    """
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    return raw


def _env_bool(name: str, default: bool) -> bool:
    """解析布尔环境变量，接受 1/true/yes/on（大小写不敏感）。"""
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    return raw.strip().lower() in {"1", "true", "yes", "on", "y"}


def _env_float(name: str, default: float) -> float:
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    try:
        return float(raw)
    except ValueError:
        logger.warning("环境变量 %s=%r 不是合法数字，回退默认值 %s", name, raw, default)
        return default


def _env_int(name: str, default: int) -> int:
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    try:
        return int(raw)
    except ValueError:
        logger.warning("环境变量 %s=%r 不是合法整数，回退默认值 %s", name, raw, default)
        return default


def _env_list(name: str, default: Sequence[str]) -> tuple[str, ...]:
    """逗号分隔的列表环境变量，例如 PROMO_KEYWORDS=腾讯游戏,腾讯新闻。"""
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return tuple(default)
    return tuple(item.strip() for item in raw.split(",") if item.strip())


class RuntimeRoles:
    """运行期角色名单：`/设置管理员`、`/设置审核员` 等命令的结果。

    为什么需要它：`ADMIN_WHITELIST` / `REVIEWER_WHITELIST` 是启动配置，改一次要重启；
    而「加个审核员」「撤掉某个管理员」是日常操作，必须能在线做、并且重启后还在。

    因此这里存的是**增量**，最终生效名单 = 配置里的名单 ∪ granted − revoked。
    落盘位置 `<DATA_DIR>/roles.json`，格式：
        {"admins": [...], "reviewers": [...],
         "revoked_admins": [...], "revoked_reviewers": [...]}
    文件读不进来 / 内容坏了都按「没有任何增量」处理：配置里的名单照样生效，
    不会因为一个坏 JSON 把所有者锁在门外。
    """

    def __init__(self, path: str | Path | None = None) -> None:
        self.path: Path | None = Path(path) if path else None
        self.admins: set[str] = set()
        self.reviewers: set[str] = set()
        self.revoked_admins: set[str] = set()
        self.revoked_reviewers: set[str] = set()
        self.load()

    @staticmethod
    def _as_set(value: Any) -> set[str]:
        if not isinstance(value, list):
            return set()
        return {str(item).strip() for item in value if str(item).strip()}

    def load(self) -> None:
        """从磁盘读增量（不存在 / 坏文件都按空处理，只记一条警告）。"""
        if self.path is None:
            return
        try:
            raw = self.path.read_text(encoding="utf-8")
        except FileNotFoundError:
            return
        except OSError:
            logger.warning("角色文件读取失败，本次按「只有配置名单」处理：%s", self.path)
            return
        try:
            data = json.loads(raw)
        except ValueError:
            logger.warning("角色文件不是合法 JSON，本次按「只有配置名单」处理：%s", self.path)
            return
        if not isinstance(data, dict):
            return
        self.admins = self._as_set(data.get("admins"))
        self.reviewers = self._as_set(data.get("reviewers"))
        self.revoked_admins = self._as_set(data.get("revoked_admins"))
        self.revoked_reviewers = self._as_set(data.get("revoked_reviewers"))

    def save(self) -> bool:
        """把增量写回磁盘；失败只记日志，内存状态仍然生效（下次启动会丢，用户能看到）。"""
        if self.path is None:
            return False
        payload = {
            "admins": sorted(self.admins),
            "reviewers": sorted(self.reviewers),
            "revoked_admins": sorted(self.revoked_admins),
            "revoked_reviewers": sorted(self.revoked_reviewers),
        }
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text(
                json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
            )
            return True
        except OSError:
            logger.exception("角色文件写入失败：本次改动在重启后会丢失")
            return False


# 是否按旧版名单布局加载（`SUPER_ADMIN_WHITELIST` + `ADMIN_WHITELIST`）。
# 只在 _resolve_whitelists() 里置位，启动日志会把这件事明确打出来。
_LEGACY_WHITELIST_LAYOUT = False


def _env_key_present(name: str) -> bool:
    """这个键在「.env 文件」或「进程环境变量」里出现过（值可以为空）。"""
    return name in os.environ or name in _ENV_FILE_VALUES


def _resolve_whitelists(
    default_admins: Sequence[str], default_reviewers: Sequence[str]
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """解析「管理员 / 审核员」两份白名单，并兼容旧版 .env。

    为什么不能简单地把 `ADMIN_WHITELIST` 直接当成新的「管理员」名单：
    2026-10 的角色改名是「超级管理员 → 管理员」「管理员 → 审核员」，
    也就是说旧 `.env` 里的 `ADMIN_WHITELIST` 装的是**审核员**。按新名字直接读，
    那批只会删帖的人会立刻拿到急停 / 拉黑 / 重置额度等全部权限 —— 这是权限放大，
    不能靠「用户自己记得改名」来兜底。

    判定规则（只看「键有没有出现过」，不看值是否为空）：
      * 出现了 `SUPER_ADMIN_WHITELIST`、且没有出现 `REVIEWER_WHITELIST`
        → 判定为旧版布局：`SUPER_ADMIN_WHITELIST` = 管理员，`ADMIN_WHITELIST` = 审核员；
      * 其余情况按新版布局：`ADMIN_WHITELIST` = 管理员，`REVIEWER_WHITELIST` = 审核员
        （同时仍接受 `SUPER_ADMIN_WHITELIST` 作为管理员的别名，避免半迁移的配置把人锁在外面）。
    """
    global _LEGACY_WHITELIST_LAYOUT

    legacy_admins = _env_list("SUPER_ADMIN_WHITELIST", ())
    legacy_reviewers = _env_list("ADMIN_WHITELIST", ())
    new_reviewers = _env_list("REVIEWER_WHITELIST", ())

    if _env_key_present("SUPER_ADMIN_WHITELIST") and not _env_key_present("REVIEWER_WHITELIST"):
        _LEGACY_WHITELIST_LAYOUT = True
        admins = legacy_admins
        reviewers = legacy_reviewers
    else:
        admins = _env_list("ADMIN_WHITELIST", tuple(default_admins)) or legacy_admins
        reviewers = new_reviewers or tuple(default_reviewers)
    return tuple(admins), tuple(reviewers)


@dataclass(frozen=True)
class Settings:
    """运行期配置。全部可通过环境变量覆盖，便于容器化部署。"""

    # --- 服务 ---
    host: str = "127.0.0.1"
    port: int = 8080
    ws_path: str = "/onebot/v11/ws"

    # --- 防刷屏（每日额度，0 点重置）---
    # 每个用户**每个自然日**最多被「收录」多少条消息；0 = 不限制。
    # 默认 9 条（需求）。单位是「条消息」不是「次投稿」。
    # 「一天」按 DISPLAY_TIMEZONE（默认 Asia/Shanghai）算，零点自动重置 ——
    # 不再有滑动窗口，也不再需要「等 X 分钟」的提示。
    daily_message_limit: int = 9
    # 超限提示的冷却：用户连发时只提示一次，避免提示本身变成刷屏
    rate_limit_notice_cooldown_seconds: float = 300.0

    # --- 投稿会话 ---
    # 最后一条消息之后 idle_timeout_seconds 秒没有新消息 → 立刻开始渲染并结束本次投稿
    idle_timeout_seconds: float = 60.0  # 默认 1 分钟（需求：最后一条消息发送一分钟后开始渲染）
    data_dir: str = "data"               # 截图 / 原图 / 存档落盘目录
    db_path: str = "data/campus_wall.db"
    screenshot_width: int = 720
    max_publish_images: int = 9          # qzone-sdk 单条说说最多 9 张图
    # 投稿存档根目录：每份渲染出来的投稿一个子目录（`<编号>_<投稿人QQ>`），
    # 里面放截图、原图与「审核操作日志.txt」。留空 = `<data_dir>/archive`。
    archive_dir: str = ""

    # --- 定时放送（已删除）---
    # 2026-10 起**整体删除**：「把投稿攒到一起、到固定时间统一放送」这个功能不要了。
    # 因此 PUBLISH_SCHEDULE_ENABLED / PUBLISH_QUIET_* / PUBLISH_SLOT_MINUTES /
    # PUBLISH_EXPRESS_DELAY_SECONDS / PUBLISH_DISPATCH_TICK_SECONDS / MAX_QUEUE_IMAGE_BYTES /
    # BATCH_MODERATION_ENABLED 这些配置项一并移除（.env 里留着也不会报错，只是不再生效）。
    # 现在最后一条消息发出 1 分钟后（idle_timeout_seconds）立刻渲染并发布。

    # --- 审核 ---
    deepseek_api_key: str = ""
    deepseek_base_url: str = "https://api.deepseek.com"
    deepseek_model: str = "deepseek-flash"         # 纯文本审核使用的模型
    # 含图片时改用视觉模型：同为 deepseek-flash（DeepSeek-V4.1-Flash 支持 Vision）。
    # 两个键位保留独立，便于将来按需把文本与图片分流到不同模型。
    deepseek_vision_model: str = "deepseek-flash"
    moderation_timeout: float = 30.0
    # 审核的思考强度（成本关键项）：
    #   disabled（默认）= 完全关闭思考，最省最快（此时 temperature 才真正生效）
    #   low    = 最低强度思考：请求 reasoning_effort=minimal，文档口径实际映射为 low
    #   high / max = 需要更强判断时用；default = 不下发任何参数
    # 注意：不传任何参数时模型默认「开启思考且强度为 high」，也就是最贵的一档。
    moderation_thinking: str = "disabled"
    # 单次投稿的**照片**张数上限（默认 4）：
    #   ① 收稿时最多收录几张照片（超出的当条不收录，并立刻告诉用户分次发送）；
    #   ② 送审时最多把几张照片发给模型；
    #   ③ 因此也是一次投稿最多几张照片能被公开的上限。
    # **表情包 / 动图表情不占这个额度**（它们走 max_stickers_per_submission），
    # 但同样会被送审 —— 只要出现在公开截图里就必须被模型看过（DEC-9）。
    # 接口上限是 600 张，这里按成本/延迟取小值。
    moderation_max_images: int = 4
    # 单次投稿的**表情包 / 动图表情**个数上限（默认 8）。表情不单独发布，只画在截图里，
    # 所以单列一条额度：用户发 4 张照片 + 几个表情，不该被"图片太多"挡住。
    # 0 或负数 = 不限制（此时只受请求体积与单条投稿字节预算约束）。
    max_stickers_per_submission: int = 8
    moderation_image_detail: str = "low"           # low=缩放到 512x512 更省 token；需要更精细时改 original
    # 单次投稿的图片**总字节**预算（默认 64 MiB）。截图下载与发布原图共用这个预算：
    # 超过就不再下载剩余图片，并终止本次发布 —— 宁可少发一条，也不让内存被吃光。
    max_submission_image_bytes: int = 64 * 1024 * 1024
    # 单张图片**解码前**的像素上限（默认 3000 万像素 ≈ 120 MB RGBA）。
    # 压缩文件很小、像素极大的图（解压炸弹）同样能在解码时吃光内存，所以按像素拦。
    max_image_pixels: int = 30_000_000

    # --- 空间发布 ---
    qzone_auth_mode: str = "napcat"      # napcat | cookie
    qzone_ws_url: str = "ws://localhost:3001"
    qzone_cookie: str = ""
    qzone_uin: str = ""
    qzone_visible: int = 1               # 1=公开 3=好友 4=仅自己
    qzone_timeout: float = 30.0          # 传入 QZoneConfig 的请求超时（SDK 语义待实测）
    publish_caption: str = "#校园墙投稿#"

    # --- 截图时间戳 ---
    # 截图底部「投稿时间」使用的时区。写 IANA 名称（如 Asia/Shanghai）即可，
    # 这样无论服务器时区是 UTC 还是别的，截图都固定按北京时间显示；
    # 填 local 表示沿用服务器本地时区（旧行为）。
    display_timezone: str = "Asia/Shanghai"
    # 仅当上面的时区名无法解析（例如系统缺 tzdata）时使用的固定偏移兜底，默认 +8。
    display_utc_offset: float = 8.0

    # --- 网络 ---
    http_timeout: float = 20.0
    # 单次下载字节上限（0 = 不限制）。防止超大响应被整个读进内存。
    max_download_bytes: int = 16 * 1024 * 1024
    # 是否允许图片地址指向内网/回环地址。NapCat 常把图片挂在 127.0.0.1 上，
    # 因此默认放开；若你的 NapCat 用公网地址供图，可设为 false 收紧。
    allow_private_image_hosts: bool = True

    # --- 头像 ---
    # 已核实的 QQ 头像直链格式（会暴露 QQ 号，隐私要求高时改成
    # https://s.p.qq.com/pub/get_face?img_type=3&uin={user_id} 这类不透明地址）。
    avatar_url_template: str = "https://q1.qlogo.cn/g?b=qq&nk={user_id}&s=640"
    draw_avatar: bool = True

    # --- 表情 ---
    # 腾讯表情 CDN 的编号与消息内 QSid 不同；仅使用 FACE_MAP_PATH 显式映射。
    # 未配置有效映射时回退为文字占位，避免猜测后显示成错误表情。
    face_cdn_url_template: str = "https://qzonestyle.gtimg.cn/qzone/em/e{id}.gif"
    # 可选备用表情图源；仅在缺少映射时使用，必须由部署者核对编号规则。
    # 留空则不请求未经映射的表情图片。
    face_image_url_template: str = ""
    # 「动画表情 / 表情包」的识别关键词：图片段的 summary（或文件名）命中即视为表情 ——
    # 只出现在合并截图里，**不单独发布为说说原图**。
    #   - 商城表情（mface）由 NapCat 转成 image 段并带 emoji_id，必定命中（无需关键词）；
    #   - 用户收藏的动图表情则以普通 image 段到达，只能靠 summary / sub_type 认。
    sticker_keywords: tuple[str, ...] = ("动画表情", "表情包", "贴纸")
    # 图片段的 sub_type 命中这些值也视为表情（默认空 = 不启用）。
    # sub_type 的取值含义官方未给出明确枚举，请先按日志里「图片段：… sub_type=…」的
    # 实际取值确认，再填进来 —— 填错会让正常照片不再单独发布（仍会出现在截图里）。
    sticker_sub_types: tuple[str, ...] = ()

    # --- 消息过滤规则 ---
    # 系统消息关键词：命中即整条丢弃，绝不作为投稿发布。
    # 典型来源：添加好友时 QQ 自动发出的验证语（“请求添加你为好友”）。
    # 若你的环境还会推送其它系统文案，把原文追加上去即可（一条一个，逗号分隔）。
    blocked_keywords: tuple[str, ...] = (
        "请求添加你为好友",
    )
    promo_keywords: tuple[str, ...] = (
        "腾讯游戏", "腾讯新闻", "腾讯视频", "游戏福利", "点击领取",
        "扫码进群", "加群领", "推广", "广告合作",
    )
    anonymous_keywords: tuple[str, ...] = (
        "匿名", "不要暴露我", "别暴露我", "打码", "打个码", "隐藏我", "不显示昵称", "匿了","匿"
    )

    # --- 好友请求 ---
    friend_auto_approve: bool = True
    friend_require_keyword: bool = True
    friend_keywords: tuple[str, ...] = ("投稿", "校园墙")
    friend_min_qq_level: int = 0         # 0 = 不启用等级门槛
    friend_action_timeout: float = 10.0
    # 同意好友请求后，自动回一条使用说明（告知「发完消息约 1 分钟后才会投稿」与联系方式）。
    # 说明发不出去只记日志，不影响「已同意好友」这个结果。
    friend_welcome_enabled: bool = True
    # 自定义说明文案；留空使用内置文案（会按实际配置渲染等待时长、频率上限、联系方式）。
    # 可用占位符：{idle_minutes} {support_qq} {rate_limit_max_messages} {rate_limit_window_minutes}
    friend_welcome_message: str = ""
    # 内置文案里「有疑问请联系」的 QQ 号，可填多个（逗号分隔），会渲染成
    # 「QQ 111 或 222」；留空则整行不出现。
    support_contact_qq: tuple[str, ...] = ()

    # --- 管理员 / 审核员（白名单）---
    # 白名单里的 QQ 发「/命令」时：这条消息**不当作投稿**，而是对本服务执行命令。
    # 用途：不想把账号密码交给别人，又希望有人能替你「急停」。
    # 多个 QQ 用逗号分隔；留空 = 命令功能完全不启用。
    #
    # 两级权限（2026-10 改名：超级管理员 → 管理员，管理员 → 审核员）：
    #   * 管理员（admin_whitelist，旧名 super_admin_whitelist）：全部管理命令
    #     （急停 / 恢复 / 状态 / 删帖 / 封禁 / 解封 / 查作者 / 拉黑用户 /
    #      重置每日额度 / 调取审核操作日志），且**不受每日条数限制**；
    #     他们的投稿会带上「管理员」标记图。
    #   * 审核员（reviewer_whitelist，旧名 admin_whitelist）：只有
    #     「删帖」「封禁」「解封」「帮助」四条命令；删帖与封禁**必须写理由**。
    # 同时出现在两个名单里按管理员处理（取权限高的那一个）。
    # 名单可以在运行时用`/设置管理员`、`/设置审核员`等命令增删（落盘在 <DATA_DIR>/roles.json）。
    admin_whitelist: tuple[str, ...] = ()
    reviewer_whitelist: tuple[str, ...] = ()
    # 所有者 QQ：只有他们能设置/撤职管理员与审核员（由部署者在 .env 指定）。
    # 所有者本身永远是管理员（不能被撤职），避免出现「把所有人撤光，再也改不回来」。
    owner_whitelist: tuple[str, ...] = ()
    # 命令前缀：消息必须以此开头才算命令 —— 白名单的人发普通投稿（不带前缀）仍正常收稿。
    command_prefix: str = "/"

    # --- 管理员投稿标记 ---
    # 需求：管理员的投稿要在截图里带上标记，让一般读者一眼看出这是管理员发布的内容。
    # 不附带默认徽标文件，避免发布时泄露组织标识。
    # 如需自定义徽标，设置本地路径；留空即不绘制。
    admin_badge_path: str = ""
    # 关掉就完全不画标记（例如：不希望匿名投稿暴露「这是管理员发的」时）。
    admin_badge_enabled: bool = False

    # --- 投稿截图背景 ---
    # 截图默认纯色背景；仅显式配置本地素材时才使用背景图片。
    # 留空表示纯色背景；不附带任何校园照片。
    # 读不到 / 解码失败会退回纯白底，绝不会因为换背景让投稿发不出去。
    # 启用自定义背景时，截图保持背景图自己的宽高比；
    # 正文放不下这个比例就改用纯白底，高度随内容增长（见 load_chat_background）。
    chat_background_path: str = ""

    # --- 截图字体 ---
    # 中文字体文件路径；留空 = 按 _FONT_CANDIDATES 的顺序自动找（Linux 首选
    # /usr/share/fonts/truetype/harmonyos/HarmonyOS_Sans_SC_Bold.ttf，即鸿蒙 HarmonyOS Sans SC）。
    # 想换字重（Regular / Medium）或字体放在别处时，把绝对路径填到这里即可。
    font_path: str = ""

    # --- 换服务器时清理旧说说 ---
    # 填 `YYYY-MM-DD`（按 DISPLAY_TIMEZONE 的 00:00 计算）：服务启动后会把**数据库里
    # 记过 tid、且发布时刻早于这个时间点**的说说全部删掉，并把记录标成 deleted。
    # 留空 = 不清理。注意：只能删到本机器人自己发过、留下 tid 的说说 ——
    # QZone 没有「列出我所有说说」的公开接口，手工发的旧说说删不到。
    purge_before: str = ""

    # --- 自动封禁 ---
    # 自动封禁：最近 auto_ban_window_hours 小时内被审核拒绝 auto_ban_strikes 次 → 封禁
    # auto_ban_hours 小时（0 = 永久封禁）。auto_ban_strikes=0 表示关闭自动封禁。
    auto_ban_strikes: int = 3
    auto_ban_window_hours: float = 72.0
    auto_ban_hours: float = 72.0
    # 管理员 /封禁 不给天数时用这个默认值
    default_ban_days: float = 3.0

    # --- 运行期角色（`/设置管理员` 等命令的增量，落盘 <DATA_DIR>/roles.json）---
    # 不在环境变量里：它由命令维护。字段放在最后，避免影响上面按位置传参的老代码。
    runtime_roles: RuntimeRoles = field(default_factory=RuntimeRoles, repr=False, compare=False)

    def __post_init__(self) -> None:
        """给 runtime_roles 定位到 `<DATA_DIR>/roles.json` 并载入。

        放在这里而不是 from_env()：测试与脚本常常直接 `Settings(data_dir=...)` 构造配置，
        这样也能拿到同一份角色文件；显式传入带 path 的 RuntimeRoles 时保持原样。
        """
        roles = self.runtime_roles
        if not isinstance(roles, RuntimeRoles) or roles.path is None:
            object.__setattr__(
                self, "runtime_roles", RuntimeRoles(Path(self.data_dir) / "roles.json")
            )
        else:
            roles.load()

    @classmethod
    def from_env(cls) -> "Settings":
        """从环境变量构造配置；未设置项使用默认值。"""
        admins, reviewers = _resolve_whitelists(cls.admin_whitelist, cls.reviewer_whitelist)
        return cls(
            host=_env_str("HOST", cls.host),
            port=_env_int("PORT", cls.port),
            ws_path=_env_str("WS_PATH", cls.ws_path),
            idle_timeout_seconds=_env_float("IDLE_TIMEOUT_SECONDS", cls.idle_timeout_seconds),
            daily_message_limit=_env_int("DAILY_MESSAGE_LIMIT", cls.daily_message_limit),
            rate_limit_notice_cooldown_seconds=_env_float(
                "RATE_LIMIT_NOTICE_COOLDOWN_SECONDS", cls.rate_limit_notice_cooldown_seconds
            ),
            data_dir=_env_str("DATA_DIR", cls.data_dir),
            db_path=_env_str("DB_PATH", cls.db_path),
            archive_dir=_env_str("ARCHIVE_DIR", cls.archive_dir),
            screenshot_width=_env_int("SCREENSHOT_WIDTH", cls.screenshot_width),
            max_publish_images=_env_int("MAX_PUBLISH_IMAGES", cls.max_publish_images),
            deepseek_api_key=_env_str("DEEPSEEK_API_KEY", cls.deepseek_api_key),
            deepseek_base_url=_env_str("DEEPSEEK_BASE_URL", cls.deepseek_base_url),
            deepseek_model=_env_str("DEEPSEEK_MODEL", cls.deepseek_model),
            deepseek_vision_model=_env_str("DEEPSEEK_VISION_MODEL", cls.deepseek_vision_model),
            moderation_timeout=_env_float("MODERATION_TIMEOUT", cls.moderation_timeout),
            moderation_thinking=_env_str("MODERATION_THINKING", cls.moderation_thinking),
            moderation_max_images=_env_int("MODERATION_MAX_IMAGES", cls.moderation_max_images),
            max_stickers_per_submission=_env_int(
                "MAX_STICKERS_PER_SUBMISSION", cls.max_stickers_per_submission
            ),
            moderation_image_detail=_env_str("MODERATION_IMAGE_DETAIL", cls.moderation_image_detail),
            max_submission_image_bytes=_env_int(
                "MAX_SUBMISSION_IMAGE_BYTES", cls.max_submission_image_bytes
            ),
            max_image_pixels=_env_int("MAX_IMAGE_PIXELS", cls.max_image_pixels),
            qzone_auth_mode=_env_str("QZONE_AUTH_MODE", cls.qzone_auth_mode).strip().lower(),
            qzone_ws_url=_env_str("QZONE_WS_URL", cls.qzone_ws_url),
            qzone_cookie=_env_str("QZONE_COOKIE", cls.qzone_cookie),
            qzone_uin=_env_str("QZONE_UIN", cls.qzone_uin),
            qzone_visible=_env_int("QZONE_VISIBLE", cls.qzone_visible),
            qzone_timeout=_env_float("QZONE_TIMEOUT", cls.qzone_timeout),
            publish_caption=_env_str("PUBLISH_CAPTION", cls.publish_caption),
            http_timeout=_env_float("HTTP_TIMEOUT", cls.http_timeout),
            display_timezone=_env_str("DISPLAY_TIMEZONE", cls.display_timezone),
            display_utc_offset=_env_float("DISPLAY_UTC_OFFSET", cls.display_utc_offset),
            max_download_bytes=_env_int("MAX_DOWNLOAD_BYTES", cls.max_download_bytes),
            allow_private_image_hosts=_env_bool(
                "ALLOW_PRIVATE_IMAGE_HOSTS", cls.allow_private_image_hosts
            ),
            avatar_url_template=_env_str("AVATAR_URL_TEMPLATE", cls.avatar_url_template),
            face_image_url_template=_env_str("FACE_IMAGE_URL_TEMPLATE", cls.face_image_url_template),
            face_cdn_url_template=_env_str("FACE_CDN_URL_TEMPLATE", cls.face_cdn_url_template),
            sticker_keywords=_env_list("STICKER_KEYWORDS", cls.sticker_keywords),
            sticker_sub_types=_env_list("STICKER_SUB_TYPES", cls.sticker_sub_types),
            draw_avatar=_env_bool("DRAW_AVATAR", cls.draw_avatar),
            promo_keywords=_env_list("PROMO_KEYWORDS", cls.promo_keywords),
            blocked_keywords=_env_list("BLOCKED_KEYWORDS", cls.blocked_keywords),
            anonymous_keywords=_env_list("ANONYMOUS_KEYWORDS", cls.anonymous_keywords),
            friend_auto_approve=_env_bool("FRIEND_AUTO_APPROVE", cls.friend_auto_approve),
            friend_require_keyword=_env_bool("FRIEND_REQUIRE_KEYWORD", cls.friend_require_keyword),
            friend_keywords=_env_list("FRIEND_KEYWORDS", cls.friend_keywords),
            friend_min_qq_level=_env_int("FRIEND_MIN_QQ_LEVEL", cls.friend_min_qq_level),
            friend_action_timeout=_env_float("FRIEND_ACTION_TIMEOUT", cls.friend_action_timeout),
            friend_welcome_enabled=_env_bool("FRIEND_WELCOME_ENABLED", cls.friend_welcome_enabled),
            friend_welcome_message=_env_str("FRIEND_WELCOME_MESSAGE", cls.friend_welcome_message),
            support_contact_qq=_env_list("SUPPORT_CONTACT_QQ", cls.support_contact_qq),
            admin_whitelist=admins,
            reviewer_whitelist=reviewers,
            owner_whitelist=_env_list("OWNER_QQ", cls.owner_whitelist),
            chat_background_path=_env_str(
                "CHAT_BACKGROUND_PATH", cls.chat_background_path
            ),
            font_path=_env_str("FONT_PATH", cls.font_path),
            purge_before=_env_str("PURGE_BEFORE", cls.purge_before),
            admin_badge_path=_env_str(
                "ADMIN_BADGE_PATH", _env_str("SUPER_ADMIN_BADGE_PATH", cls.admin_badge_path)
            ),
            admin_badge_enabled=_env_bool(
                "ADMIN_BADGE_ENABLED",
                _env_bool("SUPER_ADMIN_BADGE_ENABLED", cls.admin_badge_enabled),
            ),
            command_prefix=_env_str("COMMAND_PREFIX", cls.command_prefix),
            auto_ban_strikes=_env_int("AUTO_BAN_STRIKES", cls.auto_ban_strikes),
            auto_ban_window_hours=_env_float("AUTO_BAN_WINDOW_HOURS", cls.auto_ban_window_hours),
            auto_ban_hours=_env_float("AUTO_BAN_HOURS", cls.auto_ban_hours),
            default_ban_days=_env_float("DEFAULT_BAN_DAYS", cls.default_ban_days),
        )


SETTINGS = Settings.from_env()

# --------------------------------------------------------------------------------------
# 二、OneBot v11 消息段解析与规则判定（纯函数，便于单测）
# --------------------------------------------------------------------------------------

# 只把这些段类型视为「可单独发布的原图」；其余（face / mface / bface / rps / dice …）
# 属于表情包，按需求只出现在合并截图里。
PUBLISHABLE_IMAGE_TYPES = frozenset({"image"})


@dataclass
class CollectedMessage:
    """一条被纳入投稿的消息段。"""

    kind: str                     # text | image | face
    text: str = ""                # kind == text 时的文本
    image_url: str = ""           # kind == image/face 时的远程地址（表情也可能有图）
    image_path: str = ""          # kind == image 且下载成功后的本地路径
    image_bytes: bytes | None = None  # 截图阶段下载到的原始字节，供原图保存复用（避免二次下载）
    face_id: str = ""             # kind == face 时的表情 ID（可套用表情图源模板）
    face_label: str = ""          # kind == face 时的可读标签，如「表情 14」「表情包 收到」
    is_sticker: bool = False      # kind == image 且其实是「动画表情/表情包」：只进截图，不单独发布
    # 备用图源：主图源下载失败时依次尝试（表情尤其需要 —— 第三方表情源经常不可达，
    # 主源取不到就一路退到文字占位，用户看到的就是「[表情 28]」，见 errors/ERR-014.md）。
    image_fallbacks: list[str] = field(default_factory=list)

    def image_candidates(self) -> list[str]:
        """按优先级返回这次的候选图源（主源在前，去重且忽略空串）。"""
        seen: set[str] = set()
        ordered: list[str] = []
        for url in [self.image_url, *self.image_fallbacks]:
            text = str(url or "").strip()
            if text and text not in seen:
                seen.add(text)
                ordered.append(text)
        return ordered


@dataclass
class SubmissionSession:
    """单个用户的一次投稿会话（内存态，随进程生命周期存在）。"""

    user_id: int
    nickname: str = ""
    messages: list[CollectedMessage] = field(default_factory=list)
    started_at: float = field(default_factory=time.time)
    updated_at: float = field(default_factory=time.time)
    timer: asyncio.Task | None = None

    def text_content(self) -> str:
        """本次投稿的全部文本（按发生顺序用换行拼接）。"""
        return "\n".join(msg.text for msg in self.messages if msg.kind == "text" and msg.text)

    def image_segments(self) -> list[CollectedMessage]:
        """全部「原图」段（kind == "image"，**含**贴纸）。

        贴纸也要留在列表里：它虽然不单独发布，但会出现在合并截图里，
        而截图同样要发到空间 —— 内容必须一起送审。
        注意：以 `face` 段到达的表情（商城表情 / 带 url 的 mface）不在这里，
        它们由 `image_messages()` 覆盖 —— 只按 kind == "image" 过滤会漏审（ERR-016）。
        """
        return [msg for msg in self.messages if msg.kind == "image" and msg.image_url]

    def image_messages(self) -> list[CollectedMessage]:
        """**所有可能公开的图片**：原图 + 表情/贴纸。

        判据是「有没有图源或字节」而不是 kind：表情段（kind == "face"）同样会被
        画进公开截图。凡是进得了截图的，都必须一起送审，否则就是审核空洞。
        """
        return [msg for msg in self.messages if msg.image_url or msg.image_bytes]

    def rendered_image_messages(self) -> list[CollectedMessage]:
        """真正拿到了字节、一定会被画进截图的图片段。

        发布前的审核覆盖检查以它为准：没有字节的图只会渲染成「[图片加载失败]」
        占位文本，不含图片内容，因此不需要（也无法）送审。
        """
        return [msg for msg in self.image_messages() if msg.image_bytes]

    def photo_messages(self) -> list[CollectedMessage]:
        """照片（会作为原图单独发布）：排除表情/贴纸。"""
        return [msg for msg in self.messages if msg.kind == "image" and not msg.is_sticker]

    def sticker_messages(self) -> list[CollectedMessage]:
        """表情包 / 贴纸 / 动图表情（只画在截图里，不单独发布）。"""
        return [msg for msg in self.messages if is_sticker_message(msg)]

    def publish_image_segments(self) -> list[CollectedMessage]:
        """要单独发布为说说原图的图片段（表情/贴纸不算，它们只出现在截图里）。"""
        return [msg for msg in self.image_segments() if not msg.is_sticker]

    def face_segments(self) -> list[CollectedMessage]:
        """仅返回被识别为表情的图片段，不计入照片发布列表。"""
        return [msg for msg in self.messages if msg.kind == "face"]


def contains_any(text: str, keywords: Iterable[str]) -> bool:
    """文本是否命中任一关键词（空文本或空关键词集合视为未命中）。"""
    if not text:
        return False
    return any(keyword and keyword in text for keyword in keywords)


def contains_promo(text: str, keywords: Iterable[str]) -> bool:
    """判断文本是否命中推广关键词（需求：命中即忽略该条消息）。"""
    return contains_any(text, keywords)


def is_sticker_message(message: "CollectedMessage") -> bool:
    """这段是不是「表情包 / 贴纸 / 动图表情」—— 只进截图，不单独发布。

    两种到达方式都算：`kind == "face"`（经典表情、mface、被转成表情的商城表情），
    以及 `kind == "image"` 但带贴纸标记（`is_sticker`）的图片段。
    它们**不占照片额度**，但仍要送审（会画进公开截图）。
    """
    return message.kind == "face" or (message.kind == "image" and message.is_sticker)


def wants_anonymous(text: str, keywords: Iterable[str]) -> bool:
    """判断本次投稿是否包含匿名要求（需求：命中任一关键词即视为要求匿名）。"""
    return contains_any(text, keywords)


# --------------------------------------------------------------------------------------
# 管理员 / 审核员命令（白名单）
#
# 场景：账号主人没法随时盯着这个号，但又不想把账号密码交给帮忙看号的人。
# 因此白名单里的 QQ 发「/命令」时，这条消息**不进投稿流水线**，而是变成对服务的操作。
# 权限判定：① 是所有者 / 管理员 / 审核员；② 消息以 COMMAND_PREFIX 开头；
#          ③ 该动作在这个角色的权限集合里（见 admin_actions）。
#
# 角色（2026-10 改名：超级管理员 → 管理员，管理员 → 审核员）：
#   * 所有者（OWNER_QQ，必须配置实际 QQ 号）：管理员全部权限 + 设置/撤职管理员与审核员；
#   * 管理员：停/恢复/状态/删帖/封禁/解封/查作者/拉黑用户/重置每日额度/调取审核日志，
#     且**不受每日条数限制**；投稿带「管理员」标记；
#   * 审核员：删帖 / 封禁 / 解封 / 帮助，删帖与封禁**必须写理由**。
# --------------------------------------------------------------------------------------

_ADMIN_COMMAND_ALIASES: dict[str, str] = {
    # 暂停：不再收投稿、不再发布，等待中的投稿一并取消
    "停止账号活动": "pause", "暂停": "pause", "停止": "pause", "stop": "pause", "pause": "pause",
    # 恢复
    "恢复账号活动": "resume", "恢复": "resume", "继续": "resume", "start": "resume", "resume": "resume",
    "状态": "status", "运行状态": "status", "status": "status",
    "帮助": "help", "命令": "help", "help": "help",
    # 删帖：只删这一条已发布的投稿，**不拉黑作者**（管理员与审核员都可用，但必须写理由）
    "删帖": "delete", "删除帖子": "delete", "删除投稿": "delete", "delete": "delete",
    # 查作者：看某条投稿是谁发的（匿名投稿同样能查到）—— 仅管理员
    "查作者": "who", "查看作者": "who", "查投稿人": "who",
    "查QQ": "who", "查qq": "who", "who": "who",
    # 永久拉黑某个 QQ（不删除他已发布的投稿）—— 仅管理员
    "拉黑用户": "blacklist_user", "永久拉黑": "blacklist_user", "blacklist": "blacklist_user",
    # 按截图上的「编号」或「投稿时间」定位投稿 → 拉黑作者 → 删掉他所有已发布的投稿（需理由）
    "拉黑并删除": "ban", "拉黑": "ban", "ban": "ban",
    # 解除拉黑 / 解除封禁（后面跟 QQ 号）
    "解除拉黑": "unban", "取消拉黑": "unban", "unban": "unban", "黑名单": "unban_list",
    # 限期封禁（不给天数就用 DEFAULT_BAN_DAYS；必须写理由）
    "封禁": "tempban", "暂时封禁": "tempban", "tempban": "tempban",
    "解封": "unban", "解除封禁": "unban",
    # 列表命令与「黑名单」是同一个动作（都走 _cmd_blacklist）
    "封禁列表": "unban_list", "黑名单列表": "unban_list",
    # 重置每日发言条数：给一个人（会给他发提示）/ 给全体
    "重置限额": "reset_quota", "重置额度": "reset_quota", "重置发言上限": "reset_quota",
    "重置条数": "reset_quota", "reset_quota": "reset_quota",
    "重置全体限额": "reset_quota_all", "重置全员限额": "reset_quota_all",
    "重置全部限额": "reset_quota_all", "重置所有人限额": "reset_quota_all",
    "重置全体发言上限": "reset_quota_all", "reset_quota_all": "reset_quota_all",
    # 调取「审核操作日志」：把日志文件直接发给管理员（可按编号只看某一条投稿）
    "审核日志": "audit_log", "审核操作日志": "audit_log", "操作日志": "audit_log",
    "调取审核日志": "audit_log", "audit_log": "audit_log", "auditlog": "audit_log",
    # 清空「某个日期以前」的全部已发布投稿（换新服务器时一次性清理历史用）—— 仅所有者
    "清理旧说说": "purge_old", "清理旧投稿": "purge_old", "删除旧说说": "purge_old",
    "清理旧动态": "purge_old", "清理历史投稿": "purge_old", "清空旧说说": "purge_old",
    "清理空间": "purge_old", "purge_old": "purge_old",
    # 清理前的自查：库里有几条、早于截止日的有几条、PURGE_BEFORE 配没配（只读，不删）
    "清理诊断": "purge_report", "清理检查": "purge_report", "迁移检查": "purge_report",
    "旧投稿诊断": "purge_report", "purge_report": "purge_report",
    # 人事任免：仅所有者可用
    "设置管理员": "grant_admin", "添加管理员": "grant_admin", "任命管理员": "grant_admin",
    "加管理员": "grant_admin", "grant_admin": "grant_admin",
    "取消管理员": "revoke_admin", "撤职管理员": "revoke_admin", "移除管理员": "revoke_admin",
    "撤销管理员": "revoke_admin", "revoke_admin": "revoke_admin",
    "设置审核员": "grant_reviewer", "添加审核员": "grant_reviewer", "任命审核员": "grant_reviewer",
    "加审核员": "grant_reviewer", "grant_reviewer": "grant_reviewer",
    "取消审核员": "revoke_reviewer", "撤职审核员": "revoke_reviewer", "移除审核员": "revoke_reviewer",
    "撤销审核员": "revoke_reviewer", "revoke_reviewer": "revoke_reviewer",
}

# 角色 → 允许的动作。
# 审核员（原「普通管理员」）只有删帖 / 封禁 / 解封 / 帮助；
# 管理员（原「超级管理员」）拥有全部管理动作；
# 所有者再额外拥有四条人事任免命令（需求：只有 OWNER_QQ 指定的用户能加/撤管理员与审核员）。
_REVIEWER_ACTIONS = frozenset({"delete", "tempban", "unban", "help"})
_ADMIN_ACTIONS = frozenset(
    {
        "pause", "resume", "status", "help",
        "delete", "tempban",
        "blacklist_user", "ban", "who", "unban", "unban_list",
        "reset_quota", "reset_quota_all", "audit_log", "purge_report",
    }
)
_OWNER_ACTIONS = _ADMIN_ACTIONS | frozenset(
    {"grant_admin", "revoke_admin", "grant_reviewer", "revoke_reviewer", "purge_old"}
)


# RuntimeRoles 的定义在 Settings 之前（角色文件路径依赖 data_dir），这里不再重复定义。


def command_prefix_of(settings: Settings) -> str:
    """取命令前缀；配置成空串时退回默认的 `/`（否则命令永远匹配不上）。"""
    return (settings.command_prefix or "").strip() or "/"


def _normalize_qq_list(items: Iterable[str]) -> set[str]:
    """把配置里的 QQ 名单规整成集合（去空白、去空项）。"""
    return {str(item).strip() for item in items if str(item).strip()}


def _qq(user_id: int | str) -> str:
    """把 QQ 号规整成字符串（比较名单时统一用它，避免 int/str 混用对不上）。"""
    return str(user_id).strip()


def owner_ids(settings: Settings) -> set[str]:
    """所有者名单（能任免管理员与审核员的人）。"""
    return _normalize_qq_list(settings.owner_whitelist)


def admin_ids(settings: Settings) -> set[str]:
    """最终生效的管理员名单 = （配置 ∪ 在线授予 − 在线撤销）∪ 所有者。

    注意「在线撤销」必须能减掉**配置里**的人：否则 `取消管理员` 对一个写在 .env 里的
    管理员完全无效，回复却说「已撤销」—— 那是最容易让人误解的一类假成功。
    所有者永远在名单里（不能被撤销），因此最后再做一次并集。
    """
    roles = settings.runtime_roles
    configured = _normalize_qq_list(settings.admin_whitelist)
    return ((configured | roles.admins) - roles.revoked_admins) | owner_ids(settings)


def reviewer_ids(settings: Settings) -> set[str]:
    """最终生效的审核员名单 = 配置 ∪ 在线授予 − 在线撤销（撤销同样能减掉配置里的人）。"""
    roles = settings.runtime_roles
    configured = _normalize_qq_list(settings.reviewer_whitelist)
    return (configured | roles.reviewers) - roles.revoked_reviewers


def is_owner(settings: Settings, user_id: int) -> bool:
    """是否所有者（只有他们能加/撤管理员与审核员）。"""
    return _qq(user_id) in owner_ids(settings)


def is_admin(settings: Settings, user_id: int) -> bool:
    """是否管理员（拥有全部管理命令、不受每日条数限制、投稿带标记图）。"""
    return _qq(user_id) in admin_ids(settings)


def is_reviewer(settings: Settings, user_id: int) -> bool:
    """是否审核员（只有删帖 / 封禁 / 解封 / 帮助）。"""
    return _qq(user_id) in reviewer_ids(settings)


def is_staff(settings: Settings, user_id: int) -> bool:
    """是否具备任意管理权限（所有者、管理员或审核员）。

    注意这只回答「能不能发命令」，**不回答「能发哪条命令」** ——
    具体动作必须再过一遍 admin_actions()，否则审核员会连带拿到急停等权限。
    """
    return is_admin(settings, user_id) or is_reviewer(settings, user_id)


def admin_actions(settings: Settings, user_id: int) -> frozenset[str]:
    """该 QQ 号允许执行的动作集合；不在任何名单里返回空集。"""
    if is_owner(settings, user_id):
        return _OWNER_ACTIONS
    if is_admin(settings, user_id):
        return _ADMIN_ACTIONS
    if is_reviewer(settings, user_id):
        return _REVIEWER_ACTIONS
    return frozenset()


def role_label(settings: Settings, user_id: int) -> str:
    """角色的中文名（用于日志与回复；不在名单里返回「非白名单用户」）。"""
    if is_owner(settings, user_id):
        return "所有者"
    if is_admin(settings, user_id):
        return "管理员"
    if is_reviewer(settings, user_id):
        return "审核员"
    return "非白名单用户"


def looks_like_command(text: str, settings: Settings) -> bool:
    """消息是否以命令前缀开头。

    只判断「像命令」，不判断权限 —— 调用方据此决定：白名单用户执行命令、
    白名单外的人忽略（而不是把 `/xxx` 当成投稿发到空间上去）。
    """
    return text.strip().startswith(command_prefix_of(settings))


def parse_admin_command(text: str, settings: Settings) -> tuple[str, str] | None:
    """把「/命令 [参数]」解析成 (动作, 参数)；不是已知命令返回 None。

    动作取值见 _OWNER_ACTIONS / _ADMIN_ACTIONS / _REVIEWER_ACTIONS。
    """
    body = text.strip()
    prefix = command_prefix_of(settings)
    if not body.startswith(prefix):
        return None
    body = body[len(prefix):].strip()
    if not body:
        return "help", ""
    parts = body.split(maxsplit=1)
    action = _ADMIN_COMMAND_ALIASES.get(parts[0].strip().lower())
    if action is None:
        return None
    return action, (parts[1].strip() if len(parts) > 1 else "")


def _build_admin_help(settings: Settings, role: str) -> str:
    """按角色拼命令说明；role 取 owner / admin / reviewer。"""
    prefix = command_prefix_of(settings)
    is_admin_role = role in {"owner", "admin"}
    if role == "owner":
        lines = ["可用命令（你是所有者：管理员全部权限 + 任免管理员/审核员）："]
    elif role == "admin":
        lines = ["可用命令（你的账号是管理员）："]
    else:
        lines = ["可用命令（你的账号是审核员）："]
    if is_admin_role:
        lines += [
            f"{prefix}停止账号活动 —— 暂停：不再收投稿、不再发布，等待中的投稿一并取消",
            f"{prefix}恢复账号活动 —— 恢复收稿与发布",
            f"{prefix}状态 —— 查看运行状态",
        ]
    lines += [
        f"{prefix}删帖 <编号 或 投稿时间> <理由> —— 删除这一条已发布的投稿"
        "（不拉黑作者，**理由必填**）",
        f"{prefix}封禁 <QQ号> [天数] <理由> —— 限期封禁（不给天数默认 "
        f"{settings.default_ban_days:g} 天），到点自动恢复，**理由必填**",
        f"{prefix}解封 <QQ号>（别名「解除拉黑」）—— "
        + (
            "解除任意拉黑 / 封禁"
            if is_admin_role
            else "只能解封「AI 自动封禁」或你自己封禁的用户（其他人封禁的需管理员）"
        ),
    ]
    if is_admin_role:
        lines += [
            f"{prefix}拉黑用户 <QQ号> [原因] —— 永久拉黑该 QQ（保留他已发布的投稿）",
            f"{prefix}拉黑并删除 <编号 或 投稿时间> <理由> —— "
            "定位投稿 → 拉黑作者 → 删除他所有已发布的投稿",
            f"{prefix}查作者 <编号 或 投稿时间> —— 查看投稿人 QQ（匿名投稿同样能查到）",
            f"{prefix}封禁列表（别名「黑名单」）—— 列出被封禁的人（含到期时间）",
            f"{prefix}重置限额 <QQ号> [提示语] —— 把这个人今天的条数清零，"
            "并用本号给他发一条提示",
            f"{prefix}重置全体限额 —— 把所有人今天的条数清零",
            f"{prefix}审核日志 [编号] —— 把「审核操作日志」文件通过本号发给你"
            "（带编号只看那一条投稿的）",
            f"{prefix}清理诊断 [YYYY-MM-DD] —— 只看不删：库里有多少条投稿、"
            "其中多少条在空间上删得掉、早于某天的有几条",
        ]
    if role == "owner":
        lines += [
            f"{prefix}设置管理员 <QQ号> / {prefix}取消管理员 <QQ号> —— 任免管理员",
            f"{prefix}设置审核员 <QQ号> / {prefix}取消审核员 <QQ号> —— 任免审核员",
            f"{prefix}清理旧说说 <YYYY-MM-DD> —— 把这一天之前（不含当天）发布到空间的投稿"
            "全部删除（换服务器前清历史用；会先回你一条「确认执行」的提示；"
            f"拿不准就先发 {prefix}清理诊断 <YYYY-MM-DD> 看有多少条）",
        ]
    lines += [
        f"{prefix}帮助 —— 显示这条说明",
        f"每人每天最多 {settings.daily_message_limit} 条投稿消息，每日 0 点重置"
        "（管理员不受此限制）。",
        "命令本身不会被投稿，请放心发。",
        "「编号」就是截图底部那串 5 位字符（如 K7F2M）；也可以用截图上的投稿时间。",
    ]
    if role == "reviewer":
        lines.append("你的账号是审核员：只有上面删帖 / 封禁 / 解封 / 帮助四条命令可用。其它操作请联系管理员。")
    return "\n".join(lines)


def format_admin_help(settings: Settings, *, role: str = "admin") -> str:
    """给白名单用户的命令说明。

    按角色裁剪：审核员只看得到自己能用的命令 —— 列出用不了的命令，
    只会让人发了没反应还以为是坏的。
    """
    return _build_admin_help(settings, role)


# 可选自定义素材：默认不附带管理员徽标或校园背景。
# 部署者可单独配置本地图片路径；图片失效时继续用纯色渲染。
ADMIN_BADGE_HEIGHT = 26
ADMIN_BADGE_HEIGHT = 26


def admin_badge_bytes(settings: Settings) -> bytes | None:
    """仅在显式启用时读取自定义徽标；不附带任何默认学校素材。"""
    if not settings.admin_badge_enabled:
        return None
    path = str(settings.admin_badge_path or "").strip()
    if not path:
        return None
    try:
        return Path(path).read_bytes() or None
    except OSError:
        logger.warning("管理员徽标读取失败：%s", path, exc_info=True)
        return None


def _drop_flat_background(image: Image.Image, *, tolerance: int = 24) -> Image.Image:
    """把「与四角连通的纯色底」变透明（素材常带不透明白底）。

    为什么用泛洪填充而不是按颜色全体替换：徽标里是白色文字（「管理员」三个字）与
    白色花瓣，和纯白底只差十几个色阶 —— 按颜色抠会把字和花瓣一起抠没。
    泛洪只吃从四角连通的外圈底色，被深蓝底包住的白字不受影响。
    本来就带透明通道的图原样返回。
    """
    if image.getchannel("A").getextrema()[0] < 255:
        return image
    width, height = image.size
    sentinel = (255, 0, 255, 255)
    for corner in ((0, 0), (width - 1, 0), (0, height - 1), (width - 1, height - 1)):
        ImageDraw.floodfill(image, corner, sentinel, thresh=tolerance)
    diff = ImageChops.difference(
        image.convert("RGB"), Image.new("RGB", (width, height), sentinel[:3])
    )
    image.putalpha(diff.convert("L").point(lambda value: 0 if value == 0 else 255))
    return image


def load_admin_badge(
    data: bytes | None, *, height: int = ADMIN_BADGE_HEIGHT
) -> Image.Image | None:
    """把标记图抠底 + 裁边 + 缩放成头像旁边那枚徽标。

    裁边是必须的：素材四周常留白，不裁的话「按高度缩放」会把徽标缩得很小、
    四周还顶着一圈空透明 —— 画在昵称旁边就会忽大忽小。

    任何异常都只记日志并返回 None：标记只是装饰，绝不能因为它坏了就发不出投稿。
    """
    if not data:
        return None
    try:
        with Image.open(io.BytesIO(data)) as raw:
            badge = raw.convert("RGBA")
    except Exception:
        logger.warning("管理员标记图解码失败，本次不绘制标记", exc_info=True)
        return None
    try:
        badge = _drop_flat_background(badge)
        bbox = badge.getbbox()
        if bbox is not None:
            badge = badge.crop(bbox)
    except Exception:
        logger.warning("管理员标记图抠底/裁边失败，本次不绘制标记", exc_info=True)
        return None
    if badge.width <= 0 or badge.height <= 0:
        return None
    target_height = max(1, int(height))
    ratio = target_height / badge.height
    return badge.resize((max(1, round(badge.width * ratio)), target_height), Image.LANCZOS)


def chat_background_bytes(settings: Settings) -> bytes | None:
    """仅读取部署者自行配置的背景；未配置时渲染器使用纯色。"""
    path = str(settings.chat_background_path or "").strip()
    if not path:
        return None
    try:
        return Path(path).read_bytes() or None
    except OSError:
        logger.warning("背景图片读取失败：%s", path, exc_info=True)
        return None


def load_chat_background(
    settings: Settings, width: int, content_height: int
) -> Image.Image | None:
    """按**背景图自己的宽高比**铺满宽度，返回一张 (width, 该比例的高度) 的图。

    规则（仅在配置自定义背景时适用）：
      * 背景图按宽度等比缩放，得到 ``bg_h = width × 图高 / 图宽``（以自定义图片比例为准）；
      * 只有当**正文内容需要的高度** ≤ ``bg_h`` 时才能用背景 —— 这时画布高度就取
        ``bg_h``，多出来的部分留给照片（图看起来是一张完整的背景卡片）；
      * 内容更高（长文/多图）→ 返回 None，调用方整页改用纯白底、高度随内容走。

    为什么不再「放大 + 裁剪」去凑内容：那会改变照片的取景比例，正是需求要避免的。
    取不到图 / 解码失败同样返回 None —— 背景绝不能阻断投稿。
    """
    if width <= 0 or content_height <= 0:
        return None
    data = chat_background_bytes(settings)
    if not data:
        return None
    try:
        with Image.open(io.BytesIO(data)) as raw:
            _reject_oversized_image(raw, settings.max_image_pixels, source="背景图")
            with contextlib.suppress(Exception):
                raw.draft("RGB", (width, content_height))
            image = raw.convert("RGB")
    except Exception:
        logger.warning("背景图解码失败，本次使用纯白背景", exc_info=True)
        return None
    if image.width <= 0 or image.height <= 0:
        return None

    bg_height = int(round(width * image.height / image.width))
    if content_height > bg_height:
        logger.info(
            "正文需要 %dpx，超过背景图比例能容纳的 %dpx（%dx%d 按宽缩放），本次改用纯白背景",
            content_height,
            bg_height,
            width,
            bg_height,
        )
        return None
    return image.resize((width, bg_height), Image.LANCZOS)


def parse_message_segments(
    segments: Any, settings: Settings | None = None
) -> list[CollectedMessage]:
    """把 OneBot v11 的 message 数组解析成 CollectedMessage 列表。

    仅处理本次需求涉及的段类型；未知段类型（json / xml / at 等）忽略，
    避免把无法渲染的内容写入投稿。

    settings 只用于「表情/贴纸识别」（关键词与 sub_type 白名单）；不传则只做结构性
    判定（emoji 字段、表情 CDN 域名），便于纯规则单测。
    """
    if not isinstance(segments, list):
        # 兼容 CQ 码字符串形式：整段按文本处理，保证不丢内容。
        if isinstance(segments, str):
            return [CollectedMessage(kind="text", text=segments)] if segments else []
        return []

    collected: list[CollectedMessage] = []
    for segment in segments:
        if not isinstance(segment, dict):
            continue
        seg_type = str(segment.get("type", ""))
        data = segment.get("data") or {}
        if not isinstance(data, dict):
            data = {}

        if seg_type == "text":
            text = str(data.get("text", ""))
            if text:
                collected.append(CollectedMessage(kind="text", text=text))
        elif seg_type in PUBLISHABLE_IMAGE_TYPES:
            url = str(data.get("url") or data.get("file") or "")
            if not url:
                continue
            if _is_emoji_image(data):
                # 商城表情（mface）在 NapCat 里通常被转换成 image 段，并带上
                # emoji_id / emoji_package_id / key 等字段。它仍然是「表情」：
                # 只出现在合并截图里，绝不能当原图单独发布到说说。
                collected.append(
                    CollectedMessage(
                        kind="face",
                        image_url=url,
                        face_id=segment_face_id(data),
                        face_label=_face_label("mface", data),
                    )
                )
            else:
                is_sticker, sticker_reason = _is_sticker_image(data, settings)
                logger.info(
                    "图片段：%s → %s",
                    _describe_image_segment(data),
                    f"表情（{sticker_reason}），只进截图" if is_sticker else "原图，会单独发布",
                )
                collected.append(
                    CollectedMessage(kind="image", image_url=url, is_sticker=is_sticker)
                )
        elif seg_type in {"face", "mface", "bface", "sface"}:
            # 表情包：只进截图，不单独发布。
            collected.append(
                CollectedMessage(
                    kind="face",
                    image_url=str(data.get("url") or ""),
                    face_id=segment_face_id(data),
                    face_label=_face_label(seg_type, data),
                )
            )
        # 其余段类型（reply / at / json / xml / video / record …）本次不处理。
    return collected


def _is_emoji_image(data: dict[str, Any]) -> bool:
    """判断一个 image 段其实是不是商城表情（NapCat 会把 mface 转成 image 段）。

    只认 `emoji_id` / `emoji_package_id` 这两个明确的表情字段；官方文档说明
    商城表情转换成的 image 段一定带 `emoji_id`，所以这样判定是充分的。

    刻意**不**拿 `key` 当判据：`key` 是通用字段名，普通图片也可能带。
    一旦把普通图片误判成表情，它既不会被单独发布、也不会被送进审核
    （模型看不到图 → 只能回「仅包含图片，无法审核」），代价远大于误判的收益。
    """
    return bool(data.get("emoji_id") or data.get("emoji_package_id"))


def _url_host(url: str) -> str:
    """从 URL 里取出主机名（小写、去掉端口与 userinfo）；取不到返回空串。"""
    match = re.match(r"^[a-zA-Z][a-zA-Z0-9+.\-]*://([^/?#]+)", url.strip())
    if not match:
        return ""
    authority = match.group(1).split("@")[-1]
    return authority.split(":")[0].strip().lower()


# NapCat 把商城表情（mface）转成 image 段时，图片固定挂在表情 CDN 上
# （见 NapCatQQ packages/napcat-onebot/api/msg.ts 的 marketFaceElement 转换）。
_STICKER_URL_HOSTS = frozenset({"gxh.vip.qq.com"})


def _describe_image_segment(data: dict[str, Any]) -> str:
    """给图片段打一行可判读的摘要，用来确认 NapCat 到底给了哪些标记。

    刻意**不打印完整 URL**：NapCat 的图片地址带 rkey 这类一次性凭据，
    写进日志等于把凭据留在磁盘上，只留主机名足够判断。
    """
    return (
        f"summary={str(data.get('summary') or '')[:40]!r} "
        f"sub_type={data.get('sub_type')!r} "
        f"file={str(data.get('file') or '')[:60]!r} "
        f"host={_url_host(str(data.get('url') or '')) or '(无)'} "
        f"emoji={data.get('emoji_id') or data.get('emoji_package_id') or '无'}"
    )


def _is_sticker_image(data: dict[str, Any], settings: Settings | None) -> tuple[bool, str]:
    """判断一个 image 段是不是「动画表情 / 表情包」。返回 (是否表情, 判据说明)。

    判据（任一命中即可），都来自 NapCat 源码与实测日志，不靠猜：

      1. 图片挂在表情 CDN（gxh.vip.qq.com）—— 商城表情的固定图源；
      2. `summary`（或文件名）命中 `STICKER_KEYWORDS`（默认 动画表情 / 表情包 / 贴纸）——
         用户收藏的动图表情以普通 image 段到达，summary 形如「[动画表情]」；
      3. `sub_type` 命中 `STICKER_SUB_TYPES`（默认不启用：该字段的取值含义官方没有
         明确枚举，先按日志确认实际取值再配置，避免误伤正常照片）。

    命中后该图片**仍然进合并截图、也仍然送审**，只是不再作为原图单独发布到说说。
    """
    host = _url_host(str(data.get("url") or ""))
    if host in _STICKER_URL_HOSTS:
        return True, f"表情 CDN（{host}）"

    keywords = settings.sticker_keywords if settings else ()
    summary = str(data.get("summary") or "").lower()
    filename = str(data.get("file") or "").lower()
    for keyword in keywords:
        lowered = str(keyword).strip().lower()
        if lowered and (lowered in summary or lowered in filename):
            return True, f"命中关键词「{keyword}」"

    sub_types = {
        str(item).strip()
        for item in (settings.sticker_sub_types if settings else ())
        if str(item).strip()
    }
    sub_type = data.get("sub_type")
    if sub_type is not None and str(sub_type).strip() in sub_types:
        return True, f"sub_type={sub_type} 命中配置"
    return False, ""


# QQ 表情的 QSid 与 CDN 编号并不一一对应，不能自行猜测。
# 开源包不附带第三方实现的数据表；部署者可提供自己有权使用的 JSON 映射。
# JSON 格式：{"14": {"cdn_id": "100", "name": "微笑"}}；文件仅在运行机器读取。
def _load_face_map() -> dict[str, dict[str, str]]:
    path = os.getenv("FACE_MAP_PATH", "").strip()
    if not path:
        return {}
    try:
        raw = json.loads(Path(path).read_text(encoding="utf-8"))
        if not isinstance(raw, dict):
            raise ValueError("映射根节点必须是对象")
        return {
            str(qsid): {"cdn_id": str(item.get("cdn_id", "")), "name": str(item.get("name", ""))}
            for qsid, item in raw.items()
            if str(qsid).isdigit() and isinstance(item, dict)
        }
    except (OSError, UnicodeError, ValueError, TypeError):
        logger.warning("FACE_MAP_PATH 无法读取或格式错误，将以文字展示 QQ 表情：%s", path, exc_info=True)
        return {}


_FACE_MAP = _load_face_map()


def face_name_of(face_id: str) -> str:
    """查询部署者提供的表情名；没有授权映射时返回空串。"""
    return _FACE_MAP.get(str(face_id).strip(), {}).get("name", "")


def segment_face_id(data: dict[str, Any]) -> str:
    """取出表情段里的表情 ID（QSid / 商城表情的 emoji_id）。

    ⚠️ 不能用 `data.get("id") or data.get("emoji_id")` 这种写法：
    **QSid 0 是合法表情（惊讶）**，而 `0 or x` 会把它当成「没有」丢掉 ——
    表现就是发「惊讶」既不显示图、也不显示名字。
    """
    for key in ("id", "emoji_id"):
        value = data.get(key)
        if value is None or value == "":
            continue
        return str(value).strip()
    return ""


# 不从 QSid 猜 CDN 编号；仅信任部署者提供的显式映射。


def face_cdn_id(face_id: str) -> str | None:
    """只使用显式映射的 CDN ID；无法确认对应关系时不猜测、不画错表情。"""
    cdn_id = _FACE_MAP.get(str(face_id).strip(), {}).get("cdn_id", "")
    return cdn_id if cdn_id.isdigit() else None


def face_image_id(face_id: str) -> str:
    """[旧接口，保留兼容] 把 face 段的 id 换算成图源编号；查不到时原样返回。

    ⚠️ 新代码请用 `face_cdn_id()`：它用 None 明确表达「没有可用图源」。
    本函数的「原样返回」是 1.5 版留下的语义（那时第三方源直接用 QSid 编号），
    保留它只是为了不破坏既有调用方与测试。
    """
    return face_cdn_id(face_id) or str(face_id).strip()


def apply_face_image_template(messages: Iterable[CollectedMessage], settings: Settings) -> None:
    """仅对已确认的 QSid 映射或部署者显式配置的备用源设置图片地址。

    QQ 表情编号体系不等同 CDN 编号。无可用映射时宁可留下文字占位，
    也不能把一个表情错误地绘制成另一个。
    """
    cdn_template = (settings.face_cdn_url_template or "").strip()
    third_party = (settings.face_image_url_template or "").strip()
    for message in messages:
        if message.kind != "face" or message.image_url or not message.face_id:
            continue
        qsid = str(message.face_id).strip()
        cdn_id = face_cdn_id(message.face_id)
        if cdn_id and cdn_template:
            message.image_url = cdn_template.format(id=cdn_id, face_id=cdn_id, qsid=qsid)
            message.image_fallbacks = []
            continue
        if third_party:
            # 未提供映射时仅使用部署者明确配置的备用源；下载失败退回文字。
            message.image_url = third_party.format(id=qsid, face_id=qsid, qsid=qsid)
            message.image_fallbacks = []


def _face_name(data: dict[str, Any]) -> str:
    """尽力取出这个表情的可读名字（NapCat 会把 QQ 的名称放在 raw.faceText 里）。"""
    raw = data.get("raw")
    candidates: list[Any] = [data.get("text"), data.get("summary")]
    if isinstance(raw, dict):
        candidates.extend([raw.get("faceText"), raw.get("text"), raw.get("summary")])
    for item in candidates:
        name = str(item or "").strip().strip("[]【】").strip()
        if name:
            return name
    return ""


def _face_label(seg_type: str, data: dict[str, Any]) -> str:
    """把表情段转成可读标签，用于在截图中占位显示。

    优先使用消息中自带的表情名；可选映射可提供缺失的名称
    （28 → 憨笑、364 → 超级赞、317 → 菜汪），最后才退回 `[表情 264]` 这种形式 ——
    编号对用户毫无意义，名字至少看得懂。
    """
    if seg_type == "face":
        name = _face_name(data) or face_name_of(segment_face_id(data))
        return f"[{name}]" if name else f"[表情 {segment_face_id(data) or '?'}]"
    name = str(data.get("text") or data.get("summary") or "").strip()
    return f"[表情包 {name}]" if name else "[表情包]"


def should_approve_friend_request(
    comment: str,
    qq_level: int | None,
    settings: Settings,
) -> tuple[bool, str]:
    """好友请求过滤判定，返回 (是否通过, 原因)。

    过滤顺序：总开关 → QQ 等级门槛 → 关键词门槛。
    qq_level 为 None 表示未取到（例如接口不可用），此时不因等级拦截。
    """
    if not settings.friend_auto_approve:
        return False, "自动通过好友请求已关闭"

    if settings.friend_min_qq_level > 0 and qq_level is not None:
        if qq_level < settings.friend_min_qq_level:
            return False, f"QQ 等级 {qq_level} 低于门槛 {settings.friend_min_qq_level}"

    if settings.friend_require_keyword and settings.friend_keywords:
        if not contains_any(comment or "", settings.friend_keywords):
            return False, "验证消息未包含允许的关键词"

    return True, "通过"


# --------------------------------------------------------------------------------------
# 三、截图渲染
# --------------------------------------------------------------------------------------

_FONT_CANDIDATES = (
    "/usr/share/fonts/truetype/harmonyos/HarmonyOS_Sans_SC_Bold.ttf",
    "C:/Windows/Fonts/msyh.ttc",
    "C:/Windows/Fonts/msyhbd.ttc",
    "C:/Windows/Fonts/simhei.ttf",
    "C:/Windows/Fonts/simsun.ttc",
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "/usr/share/fonts/truetype/noto/NotoSansCJK-Regular.ttc",
    "/System/Library/Fonts/PingFang.ttc",
)

# 字体文件名不统一：同样是鸿蒙，有人放 Bold、有人放 Regular/Medium；系统包的目录也各有各的
# 摆法。所以除了上面的固定路径，再按文件名 glob 补搜一轮 —— 少一次「字体明明装了却没生效」。
_FONT_GLOBS = (
    "/usr/share/fonts/**/HarmonyOS_Sans*.ttf",
    "/usr/share/fonts/**/HarmonyOS_Sans*.otf",
    "/usr/local/share/fonts/**/HarmonyOS_Sans*",
    str(Path.home() / ".local/share/fonts/**/HarmonyOS_Sans*"),
)

# 运行时覆盖：FONT_PATH 指向哪个文件就优先用它（高于全部候选），只换字重/换字体时不用改代码。
_FONT_OVERRIDE: str = ""
_FONT_CACHE: dict[tuple[str, int], Any] = {}
_FONT_REPORTED: set[str] = set()


def set_font_path(path: str) -> None:
    """设置自定义中文字体（来自 FONT_PATH）；空字符串表示回到内置候选列表。"""
    global _FONT_OVERRIDE
    value = str(path or "").strip()
    if value == _FONT_OVERRIDE:
        return
    _FONT_OVERRIDE = value
    _FONT_CACHE.clear()


def _candidate_font_paths() -> list[str]:
    """按优先级给出候选字体：FONT_PATH > 固定候选 > glob 命中的鸿蒙字体。"""
    ordered: list[str] = []
    seen: set[str] = set()

    def push(path: str) -> None:
        text = str(path or "").strip()
        if text and text not in seen:
            seen.add(text)
            ordered.append(text)

    if _FONT_OVERRIDE:
        push(_FONT_OVERRIDE)
    for path in _FONT_CANDIDATES:
        push(path)
    for pattern in _FONT_GLOBS:
        try:
            for path in sorted(glob.glob(pattern, recursive=True)):
                push(path)
        except OSError:  # glob 撞上权限问题不该让整张图渲染失败
            continue
    return ordered


def _load_font(size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    """加载中文字体（带按字号缓存）；找不到候选字体时降级为 Pillow 内置位图字体。"""
    key = (_FONT_OVERRIDE, int(size))
    cached = _FONT_CACHE.get(key)
    if cached is not None:
        return cached
    for path in _candidate_font_paths():
        if not os.path.exists(path):
            continue
        try:
            font = ImageFont.truetype(path, size)
        except OSError:  # 字体文件损坏 / 权限问题 → 继续找下一个
            logger.warning("字体加载失败，尝试下一个候选：%s", path)
            continue
        # 每条投稿要按好几档字号取字体：缓存省掉重复 mmap；来源只在首次命中时记一条。
        _FONT_CACHE[key] = font
        if path not in _FONT_REPORTED:
            _FONT_REPORTED.add(path)
            logger.info("截图使用字体：%s", path)
        return font
    logger.warning("未找到任何中文字体候选，截图将使用 Pillow 内置字体（中文可能显示为方块）")
    fallback = ImageFont.load_default()
    _FONT_CACHE[key] = fallback
    return fallback


# --- emoji 渲染 ---------------------------------------------------------------------
#
# 为什么需要它：QQ 消息里的 emoji（🔴🌹😂❤…）是中文字体**没有字形**的码位。
# 直接交给 msyh / Noto Sans CJK 去画，FreeType 画出来的是**看不见的空隙** ——
# 用户看到的就是「文字中间莫名其妙多了个空格」（见 errors/ERR-015.md）。
# 处理办法：
#   * 有 emoji 字体 → emoji 交给它画（彩色字体用 embedded_color 画彩色）；
#   * 没有 emoji 字体，但中文字体自己能画（如 ♥ ★）→ 照常画；
#   * 都没有 → 画一个**方框**占位：宁可让人看到「这里有个表情我画不出来」，
#     也绝不留下看不见的空隙。
_EMOJI_FONT_CANDIDATES = (
    "C:/Windows/Fonts/seguiemj.ttf",  # Segoe UI Emoji（Windows）
    "C:/Windows/Fonts/seguisym.ttf",  # Segoe UI Symbol（Windows，单色兜底）
    "/usr/share/fonts/truetype/noto/NotoEmoji-Regular.ttf",  # 单色，任意字号可用（推荐）
    "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",  # 彩色位图：只带固定字号，需缩放
    "/usr/share/fonts/truetype/ancient-scripts/Symbola_hint.ttf",
    "/System/Library/Fonts/Apple Symbols.ttf",
)
# 名字里带 moji / ymbola 的字体也认（不同发行版路径与包名不一致）
_EMOJI_FONT_GLOBS = (
    "/usr/share/fonts/**/*moji*.ttf",
    "/usr/share/fonts/**/*ymbola*.ttf",
    "/usr/share/fonts/**/OpenMoji*.ttf",
)
# 彩色位图 emoji 字体（NotoColorEmoji）只内置了这些字号；加载别的字号会 OSError。
# 命中时按内置字号画、再缩放到目标字号（否则「装了彩色 emoji 字体却还是方框」）。
_EMOJI_BITMAP_SIZES = (109, 128, 136, 160, 96, 64)
# 用来确认「这个字体真的能画 emoji」的探针字形 —— 防止把普通文本字体当成 emoji 字体
_EMOJI_PROBE_CHARS = ("🔴", "😀", "❤")
# 按 emoji 处理的码位区间。注意这里**故意宽松**：多认几个没关系，
# 因为「没有 emoji 字体」时还会再用 _font_can_draw 判断中文字体能不能画，
# 能画就照常画（不会把 ♥ 变成方框）。
_EMOJI_RANGES = (
    (0x1F000, 0x1FAFF),  # 表情 / 交通 / 补充符号 / 扩展 A（🔴🌹😂🚗🦄…）
    (0x1F1E6, 0x1F1FF),  # 区域指示符（国旗）
    (0x2600, 0x27BF),  # 杂项符号 + 装饰符号（☀❤✅✌…）
    (0x2B00, 0x2BFF),  # 杂项符号与箭头（⭐⬛…）
    (0x2190, 0x21FF),  # 箭头（←→↔…）
    (0x2900, 0x297F),  # 补充箭头（⤴…）
    (0x2300, 0x23FF),  # 技术符号（⌚⏰⏳…）
    (0x25A0, 0x25FF),  # 几何图形（■□▲▶…）
    (0x203C, 0x203C),
    (0x2049, 0x2049),
    (0x2122, 0x2122),
    (0x2139, 0x2139),
    (0x2934, 0x2935),
    (0x3030, 0x3030),
    (0x303D, 0x303D),
    (0x3297, 0x3297),
    (0x3299, 0x3299),
)
# 这些码位本身不是 emoji，只是「挂在 emoji 上」的修饰符（变体选择符 / 零宽连接 / 键帽）
_EMOJI_SKIP_CHARS = frozenset("\ufe0e\ufe0f\u200d\u20e3")
_EMOJI_FALLBACK_COLOR = (176, 182, 192)
_emoji_font_cache: dict[int, Any] = {}
_emoji_font_warned = False


def _font_draws_emoji(font: Any, probe: str) -> bool:
    """这个字体真的能画出 emoji 吗（画到透明小图上，看有没有留下像素）。"""
    try:
        size = int(getattr(font, "size", 28) or 28)
        tile = Image.new("RGBA", (size * 2, size * 2), (0, 0, 0, 0))
        tile_draw = ImageDraw.Draw(tile)
        try:
            tile_draw.text((0, 0), probe, font=font, embedded_color=True)
        except Exception:
            tile_draw.text((0, 0), probe, font=font)
        return tile.getbbox() is not None
    except Exception:
        return False


class _EmojiRenderer:
    """emoji 字体适配器：屏蔽「可缩放字体」与「彩色位图字体」的差别。

    位图字体（NotoColorEmoji）只内置了固定字号，`ImageFont.truetype(path, 28)` 会直接
    OSError。这里按内置字号加载、绘制时缩放到目标字号 —— 否则用户按网上教程装了
    fonts-noto-color-emoji，截图里还是方框，等于没修。
    """

    def __init__(self, path: str, font: Any, native_size: int, target_size: int) -> None:
        self.path = path
        self.font = font
        self.native_size = native_size
        self.target_size = target_size

    @property
    def scaled(self) -> bool:
        return self.native_size != self.target_size

    def width(self, text: str) -> float:
        raw = _safe_getlength(self.font, text)
        if raw <= 0:
            raw = float(self.native_size) * max(1, len(text))
        return raw * self.target_size / self.native_size

    def draw(
        self,
        canvas: Any,
        draw: ImageDraw.ImageDraw,
        x: float,
        y: float,
        text: str,
        fill: tuple[int, int, int],
    ) -> None:
        if not self.scaled:
            try:
                draw.text((x, y), text, font=self.font, fill=fill, embedded_color=True)
                return
            except Exception:
                draw.text((x, y), text, font=self.font, fill=fill)
                return
        # 位图字体：先按内置字号画到透明图，再整体缩放贴回画布
        source_width = max(1, int(math.ceil(_safe_getlength(self.font, text) or self.native_size)))
        source_height = int(self.native_size * 1.35)
        tile = Image.new("RGBA", (source_width, source_height), (0, 0, 0, 0))
        tile_draw = ImageDraw.Draw(tile)
        try:
            tile_draw.text((0, 0), text, font=self.font, fill=fill, embedded_color=True)
        except Exception:
            tile_draw.text((0, 0), text, font=self.font, fill=fill)
        scale = self.target_size / self.native_size
        target = (
            max(1, int(source_width * scale)),
            max(1, int(source_height * scale)),
        )
        tile = tile.resize(target, Image.LANCZOS)
        if canvas is None:
            return
        canvas.paste(tile, (int(x), int(y)), tile)


def _try_load_emoji_renderer(path: str, size: int) -> _EmojiRenderer | None:
    """尝试把一个字体文件变成能用的 emoji 渲染器；不行就返回 None。"""
    candidates: list[tuple[Any, int]] = []
    try:
        candidates.append((ImageFont.truetype(path, size), size))
    except OSError:
        pass
    for native in _EMOJI_BITMAP_SIZES:
        if native == size:
            continue
        try:
            candidates.append((ImageFont.truetype(path, native), native))
        except OSError:
            continue
    for font, native in candidates:
        if any(_font_draws_emoji(font, probe) for probe in _EMOJI_PROBE_CHARS):
            return _EmojiRenderer(path, font, native, size)
    return None


def _candidate_emoji_font_paths() -> list[str]:
    """按顺序给出本机可能存在的 emoji 字体路径（显式候选 + 通配扫描，去重保序）。"""
    paths = [path for path in _EMOJI_FONT_CANDIDATES if os.path.exists(path)]
    for pattern in _EMOJI_FONT_GLOBS:
        paths.extend(sorted(glob.glob(pattern, recursive=True)))
    seen: set[str] = set()
    result: list[str] = []
    for path in paths:
        if path not in seen:
            seen.add(path)
            result.append(path)
    return result


def _load_emoji_font(size: int) -> _EmojiRenderer | None:
    """加载 emoji 渲染器（按字号缓存）；一个都用不了时返回 None（调用方画方框占位）。"""
    if size in _emoji_font_cache:
        return _emoji_font_cache[size]
    global _emoji_font_warned
    renderer: _EmojiRenderer | None = None
    for path in _candidate_emoji_font_paths():
        renderer = _try_load_emoji_renderer(path, size)
        if renderer is not None:
            logger.info(
                "emoji 字体：%s%s",
                path,
                f"（位图字体 {renderer.native_size}px → 缩放到 {size}px）" if renderer.scaled else "",
            )
            break
    if renderer is None and not _emoji_font_warned:
        _emoji_font_warned = True
        logger.warning(
            "未找到可用的 emoji 字体：截图里的 emoji 会画成方框占位（不会再是看不见的空隙）。"
            "Linux 推荐装 fonts-noto-core（含单色可缩放的 NotoEmoji）；"
            "fonts-noto-color-emoji 是位图字体，代码会按内置字号缩放使用。"
            "也可把任意 emoji 字体放到这些路径之一：%s",
            "、".join(_EMOJI_FONT_CANDIDATES[:4]),
        )
    _emoji_font_cache[size] = renderer
    return renderer


def _char_is_emoji(char: str, text: str, index: int) -> bool:
    """判断单个字符是否该按 emoji 画。

    键帽 emoji（1️⃣ = '1' + 变体选择符 + 组合键帽）**刻意不算 emoji**：
    交给 emoji 字体画会变成「1 + 方框」（Segoe UI Emoji 没有键帽字形），
    交给中文字体画则是干净的一个「1」（组合符不可见），后者更好看。
    """
    code = ord(char)
    for low, high in _EMOJI_RANGES:
        if low <= code <= high:
            return True
    return False


def _normalize_keycap_marks(text: str) -> str:
    """把键帽 emoji（1️⃣）降级成基础字符（1）。

    两个字体都画不好这个组合：中文字体没有「组合键帽」字形（画出来是「1 + 方框」），
    emoji 字体对键帽序列也常有缺字。降级成数字既干净又不影响阅读 ——
    总比让读者看到一串方框强。
    """
    result: list[str] = []
    for char in text:
        if char in "\ufe0f\u20e3" and result and result[-1] in "0123456789#*":
            continue
        result.append(char)
    return "".join(result)


def _iter_text_runs(text: str) -> list[tuple[bool, str]]:
    """把文本切成 (是否 emoji, 片段) 的序列；ZWJ 组合表情不会被拆开。

    量宽度与绘制都走这里，保证「量出来的宽度」与「画出来的样子」一致。
    """
    runs: list[tuple[bool, str]] = []
    buffer = ""
    buffer_is_emoji = False
    for index, char in enumerate(_normalize_keycap_marks(text)):
        is_emoji = _char_is_emoji(char, text, index) or (
            char in _EMOJI_SKIP_CHARS and buffer_is_emoji
        )
        if buffer and is_emoji != buffer_is_emoji:
            runs.append((buffer_is_emoji, buffer))
            buffer = ""
        buffer += char
        buffer_is_emoji = is_emoji
    if buffer:
        runs.append((buffer_is_emoji, buffer))
    return runs


def _emoji_base_count(run: str) -> int:
    """一段 emoji 里有几个「表情本体」（修饰符不算），用于没有字体时画几个方框。"""
    return max(1, sum(1 for char in run if char not in _EMOJI_SKIP_CHARS))


def _emoji_box_width(emoji_size: int) -> float:
    """方框占位的宽度（与字号等宽，画出来多宽就按多宽算）。"""
    return float(emoji_size)


def _safe_getlength(font: Any, text: str) -> float:
    try:
        return float(font.getlength(text))
    except Exception:  # 某些位图字体的度量接口会抛异常，不该影响出图
        logger.debug("字体度量失败：%r", text, exc_info=True)
        return 0.0


def _font_can_draw(font: Any, text: str) -> bool:
    """这个字体能不能画出这段文字：缺字时 FreeType 给的是空 mask。"""
    for char in text:
        if char in _EMOJI_SKIP_CHARS or char.isspace():
            continue
        try:
            if font.getmask(char).getbbox() is None:
                return False
        except Exception:
            return False
    return True


def _emoji_renderer_width(renderer: Any, run: str, emoji_size: int) -> float:
    """一段 emoji 的宽度：优先用渲染器自己的度量（位图字体会按缩放比例换算）。"""
    width_method = getattr(renderer, "width", None)
    if callable(width_method):
        try:
            width = float(width_method(run))
        except Exception:
            width = 0.0
        if width > 0:
            return width
    width = _safe_getlength(renderer, run)
    return width if width > 0 else emoji_size * _emoji_base_count(run)


def _emoji_run_width(run: str, font: Any, emoji_font: Any, emoji_size: int) -> float:
    """一段 emoji 画出来有多宽（供折行与居中复用，必须与 _draw_rich_text 一致）。"""
    if emoji_font is not None:
        return _emoji_renderer_width(emoji_font, run, emoji_size)
    if _font_can_draw(font, run):
        return _safe_getlength(font, run)
    return _emoji_box_width(emoji_size) * _emoji_base_count(run)


def _rich_text_length(
    text: str, font: Any, emoji_font: Any = None, emoji_size: int = 28
) -> float:
    """按「emoji 走 emoji 字体、其余走中文字体」的规则量宽度。"""
    total = 0.0
    for is_emoji, run in _iter_text_runs(text):
        if is_emoji:
            total += _emoji_run_width(run, font, emoji_font, emoji_size)
        else:
            total += _safe_getlength(font, run)
    return total


def _draw_emoji_boxes(
    draw: ImageDraw.ImageDraw, x: float, y: float, run: str, emoji_size: int
) -> float:
    """画方框占位（用矩形而不是字形 —— 任何字体下都保证看得见）。"""
    width = _emoji_box_width(emoji_size)
    for index in range(_emoji_base_count(run)):
        left = x + index * width
        draw.rounded_rectangle(
            (left + 1, y + 4, left + width - 6, y + emoji_size - 4),
            radius=3,
            outline=_EMOJI_FALLBACK_COLOR,
            width=2,
        )
    return width * _emoji_base_count(run)


def _draw_rich_text(
    draw: ImageDraw.ImageDraw,
    xy: tuple[float, float],
    text: str,
    font: Any,
    *,
    emoji_font: Any = None,
    fill: tuple[int, int, int] = (31, 31, 31),
    emoji_size: int = 28,
    canvas: Any = None,
    stroke_width: int = 0,
    stroke_fill: tuple[int, int, int] | None = None,
) -> float:
    """画一行（可能混着 emoji 的）文字，返回结束时的 x 坐标。

    canvas 只在「位图 emoji 字体需要缩放后贴回」时用到；不传也能画，只是位图字体
    不会缩放（单测里直接传 ImageDraw 更方便）。

    stroke_width / stroke_fill 是**描边**（不是底色）：直接写在照片上的昵称、QQ 号
    靠它保证在亮背景上也看得清；缺字体的位图字体不支持描边，会自动退回无描边重画。
    """
    x, y = xy
    for is_emoji, run in _iter_text_runs(text):
        if not run:
            continue
        if is_emoji and emoji_font is not None:
            painter = getattr(emoji_font, "draw", None)
            if callable(painter):
                try:
                    painter(canvas, draw, x, y, run, fill)
                except Exception:
                    logger.debug("emoji 渲染失败，改用方框占位", exc_info=True)
                    x += _draw_emoji_boxes(draw, x, y, run, emoji_size)
                    continue
            else:  # 兼容只提供 getlength 的测试替身
                try:
                    draw.text((x, y), run, font=emoji_font, fill=fill, embedded_color=True)
                except Exception:
                    draw.text((x, y), run, font=emoji_font, fill=fill)
            x += _emoji_renderer_width(emoji_font, run, emoji_size)
            continue
        if is_emoji and not _font_can_draw(font, run):
            x += _draw_emoji_boxes(draw, x, y, run, emoji_size)
            continue
        if stroke_width > 0:
            try:
                draw.text(
                    (x, y),
                    run,
                    font=font,
                    fill=fill,
                    stroke_width=stroke_width,
                    stroke_fill=stroke_fill or fill,
                )
                x += _safe_getlength(font, run)
                continue
            except (ValueError, TypeError):  # 位图字体不支持描边 → 退回无描边
                logger.debug("字体不支持描边，已退回普通文字", exc_info=True)
        draw.text((x, y), run, font=font, fill=fill)
        x += _safe_getlength(font, run)
    return x


def _draw_plain_text(
    draw: ImageDraw.ImageDraw,
    xy: tuple[float, float],
    text: str,
    font: Any,
    fill: tuple[int, int, int],
    *,
    stroke_width: int = 0,
    stroke_fill: tuple[int, int, int] | None = None,
) -> None:
    """draw.text 的描边兼容包装：字体不支持描边（如内置位图字体）时自动退回无描边。

    描边不是底色 —— 它只沿字形轮廓勾一圈细线，让「直接写在照片上」的文字在亮处
    也读得清，而不会在文字后面铺出一块白底。
    """
    if stroke_width > 0:
        try:
            draw.text(
                xy,
                text,
                font=font,
                fill=fill,
                stroke_width=stroke_width,
                stroke_fill=stroke_fill or fill,
            )
            return
        except (ValueError, TypeError):
            logger.debug("字体不支持描边，已退回普通文字", exc_info=True)
    draw.text(xy, text, font=font, fill=fill)


def _contrast_text_colors(
    canvas: Image.Image, box: tuple[float, float, float, float]
) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    """按 box 区域的平均亮度选前景色与描边色，返回 (字色, 描边色)。

    为什么需要它：昵称/QQ 现在是**直接写在背景照片上**的，照片哪一块亮哪一块暗
    事先并不知道。亮底用深字 + 白描边、暗底用白字 + 深描边，两种都不需要垫底色。
    取平均亮度用「缩到 1×1 的 BOX 滤波」，等价于对整个区域取均值，比逐像素统计便宜。
    """
    try:
        left = max(0, int(box[0]))
        top = max(0, int(box[1]))
        right = min(canvas.width, int(box[2]))
        bottom = min(canvas.height, int(box[3]))
        if right <= left or bottom <= top:
            return (34, 38, 48), (255, 255, 255)
        patch = canvas.crop((left, top, right, bottom)).convert("L").resize((1, 1), Image.BOX)
        level = patch.getpixel((0, 0))
    except Exception:  # 亮度取不到就按亮底处理（深字更常见）
        logger.debug("背景亮度取样失败，按亮底配色", exc_info=True)
        return (34, 38, 48), (255, 255, 255)
    if isinstance(level, tuple):  # 某些模式下会返回单元素元组
        level = level[0]
    if level >= 128:
        return (34, 38, 48), (255, 255, 255)
    return (248, 249, 252), (30, 34, 44)


@dataclass
class _BubbleLayout:
    """单条消息的排版结果（先量后画，避免二次裁剪）。"""

    message: CollectedMessage
    text_lines: list[str]
    images: list[Image.Image]
    image_heights: list[int]


def _wrap_text(
    text: str, font: ImageFont.ImageFont, max_width: int, emoji_font: Any = None
) -> list[str]:
    """按像素宽度折行；中文按字断行，英文数字尽量保持单词完整。

    量宽度用的是 `_rich_text_length`（emoji 走 emoji 字体/方框宽度），
    否则含 emoji 的行会量不准 —— emoji 在中文字体里宽度是 0，折行会算少。
    """
    if emoji_font is None:
        emoji_font = _load_emoji_font(28)

    def width_of(candidate: str) -> float:
        return _rich_text_length(candidate, font, emoji_font)

    lines: list[str] = []
    for raw_line in text.splitlines() or [""]:
        current = ""
        token = ""
        for char in raw_line:
            # ASCII 可见字符累积成 token，遇到分隔符再整体试放，减少单词被劈开。
            if char.isascii() and not char.isspace():
                token += char
                continue
            for piece in (token, char):
                if not piece:
                    continue
                candidate = current + piece
                if width_of(candidate) <= max_width or not current:
                    current = candidate
                else:
                    lines.append(current)
                    current = piece
            token = ""
        if token:
            candidate = current + token
            if width_of(candidate) <= max_width or not current:
                current = candidate
            else:
                lines.append(current)
                current = token
        lines.append(current)
    return lines


def _reject_oversized_image(raw: Image.Image, max_pixels: int, *, source: str) -> None:
    """解码前按**像素数**拦一道：压缩文件小、像素极大的图（解压炸弹）会吃光内存。

    为什么不能只看文件字节：一张 1 MB 的 PNG 可以是 30000×30000（9 亿像素），
    解码成 RGBA 要 3.6 GB。Pillow 自带的 MAX_IMAGE_PIXELS 阈值（约 8900 万）也高于
    我们需要的量级，所以这里用配置值再收紧一次。
    """
    if max_pixels <= 0:
        return
    width, height = raw.size
    if width * height > max_pixels:
        raise ValueError(
            f"图片像素数 {width}×{height}={width * height} 超过上限 {max_pixels}，已拒绝解码：{source[:64]}"
        )


def _load_image(
    data: bytes, *, max_width: int, max_height: int, max_pixels: int = 0
) -> Image.Image:
    """把下载到的字节解码并按比例缩放到截图内可放置的尺寸。

    max_pixels > 0 时先做像素上限检查；JPEG 还会先用 draft() 降采样再解码，
    避免为了画一张 360px 高的缩略图而把整张原始大图读进内存。
    """
    with Image.open(io.BytesIO(data)) as raw:
        _reject_oversized_image(raw, max_pixels, source="截图素材")
        # draft 只对 JPEG 生效（libjpeg 按 1/2、1/4、1/8 缩放解码），其它格式是空操作
        with contextlib.suppress(Exception):
            raw.draft("RGB", (max_width, max_height))
        image = raw.convert("RGBA")
    scale = min(max_width / image.width, max_height / image.height, 1.0)
    if scale < 1.0:
        image = image.resize(
            (max(1, int(image.width * scale)), max(1, int(image.height * scale))),
            Image.LANCZOS,
        )
    return image


def _circle_avatar(image: Image.Image, size: int) -> Image.Image:
    """把头像裁成圆形（带 4 倍超采样，边缘更平滑）。"""
    oversample = 4
    big = image.convert("RGBA").resize((size * oversample, size * oversample), Image.LANCZOS)
    mask = Image.new("L", (size * oversample, size * oversample), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size * oversample - 1, size * oversample - 1), fill=255)
    big.putalpha(mask)
    return big.resize((size, size), Image.LANCZOS)


def _placeholder_avatar(
    nickname: str, size: int, font: ImageFont.ImageFont, emoji_font: Any = None
) -> Image.Image:
    """昵称首字占位头像（头像接口不可用时的降级路径，不阻断投稿）。

    昵称全是 emoji 时（如「🌹」）：首字用 emoji 字体画，画不出来才退回 "?" ——
    否则会出现「一个没有任何字的蓝圆」。
    """
    image = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    draw.ellipse((0, 0, size - 1, size - 1), fill=(140, 160, 190, 255))
    initial = _first_drawable_char(nickname, font, emoji_font)
    try:
        width = _rich_text_length(initial, font, emoji_font)
        left, top, right, bottom = draw.textbbox((0, 0), initial, font=font)
        draw_x = (size - width) / 2
        draw_y = (size - (bottom - top)) / 2 - top
        _draw_rich_text(
            draw,
            (draw_x, draw_y),
            initial,
            font,
            emoji_font=emoji_font,
            fill=(255, 255, 255),
            canvas=image,
        )
    except Exception:  # 字体缺字等异常不应影响主流程
        logger.debug("占位头像绘制失败", exc_info=True)
    return image


def _first_drawable_char(nickname: str, font: Any, emoji_font: Any = None) -> str:
    """取昵称里第一个「画得出来」的字符：中文字体能画的优先，其次是 emoji，都没有则 "?"。"""
    text = (nickname or "").strip()
    for index, char in enumerate(text):
        if char.isspace():
            continue
        if emoji_font is not None and _char_is_emoji(char, text, index):
            return char
        if _font_can_draw(font, char):
            return char
    return "?"


# 时区解析结果缓存：(时区名, 固定偏移) → tzinfo；以及「已经警告过」的键（用于只警告一次）。
_ZONE_CACHE: dict[tuple[str, float], tzinfo] = {}
_ZONE_WARNED: set[tuple[str, float]] = set()


def resolve_display_timezone(settings: Settings) -> tzinfo:
    """解析截图时间戳使用的时区。

    默认按 `DISPLAY_TIMEZONE`（Asia/Shanghai）解析；填 `local` 则沿用服务器本地时区。
    时区名解析失败时（常见于缺 tzdata 的 Windows 或精简容器镜像）退回
    `DISPLAY_UTC_OFFSET` 固定偏移，避免因环境差异导致截图时间错乱。

    结果按 (时区名, 偏移) 缓存：这个函数每条消息要调好几次（时间戳、额度日、日志行），
    不缓存的话「缺 tzdata」的机器会**每调一次就打一条 warning**，日志几小时就几十兆。
    """
    name = (settings.display_timezone or "").strip()
    if not name or name.lower() == "local":
        return datetime.now().astimezone().tzinfo or timezone.utc
    key = (name, float(settings.display_utc_offset))
    cached = _ZONE_CACHE.get(key)
    if cached is not None:
        return cached
    try:
        zone: tzinfo = ZoneInfo(name)
    except Exception:
        if key not in _ZONE_WARNED:
            # 只警告一次：真正的风险是「静默用错时区」，而不是「反复提醒」。
            _ZONE_WARNED.add(key)
            logger.warning(
                "时区 %s 无法解析（可能缺少 tzdata），回退为固定偏移 UTC%+g",
                name,
                settings.display_utc_offset,
            )
        zone = timezone(timedelta(hours=settings.display_utc_offset))
    _ZONE_CACHE[key] = zone
    return zone


def format_submission_time(settings: Settings, timestamp: float | None = None) -> str:
    """生成截图底部的投稿时间文本。

    刻意走配置时区而不是 `datetime.now()`：服务器时区常常是 UTC，
    那样会在截图里显示成格林威治时间（比北京时间少 8 小时）。
    """
    zone = resolve_display_timezone(settings)
    moment = datetime.fromtimestamp(timestamp, zone) if timestamp is not None else datetime.now(zone)
    return moment.strftime("投稿时间 %Y-%m-%d %H:%M:%S")


_SUBMISSION_CODE_ALPHABET = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"  # 去掉 0/O、1/I/L 这些易混字符
_SUBMISSION_CODE_LENGTH = 5  # 31^5 ≈ 2860 万种，几百条投稿里撞号概率可忽略


def generate_submission_code() -> str:
    """生成投稿编号：5 位、去掉易混字符，方便管理员从截图里一眼读出来。

    编号会画在截图底部（`投稿时间 … · 编号 K7F2M`），管理员据此就能定位到具体是哪一份
    投稿 —— 匿名投稿时截图里没有昵称，编号是唯一可靠的定位手段。

    取字符用「除以字符集大小取余」逐位剥离（divmod），而不是位运算取模：
    字符集大小 31 不是 2 的幂，位运算取模会让某些字符出现得更频繁（有偏）。
    """
    value = uuid.uuid4().int
    size = len(_SUBMISSION_CODE_ALPHABET)
    chars: list[str] = []
    for _ in range(_SUBMISSION_CODE_LENGTH):
        value, index = divmod(value, size)
        chars.append(_SUBMISSION_CODE_ALPHABET[index])
    return "".join(chars)


def quota_date(settings: Settings, timestamp: float | None = None) -> str:
    """当前「额度日」= DISPLAY_TIMEZONE 下的日期（每日 0 点重置就靠它）。

    刻意不走服务器时区：服务器常常是 UTC，那样「今天」会比北京时间晚 8 小时切换，
    用户会看到「明明刚过零点却没重置」。
    """
    zone = resolve_display_timezone(settings)
    moment = datetime.fromtimestamp(timestamp, zone) if timestamp is not None else datetime.now(zone)
    return moment.strftime("%Y-%m-%d")


def format_archive_time(display_time: str) -> str:
    """取掉截图时间戳里的「投稿时间」前缀，用于存档头部（避免写成「投稿时间：投稿时间 …」）。"""
    text = str(display_time or "").strip()
    prefix = "投稿时间"
    if text.startswith(prefix):
        return text[len(prefix) :].strip() or text
    return text or "（未知）"


def format_log_time(settings: Settings, timestamp: float | None = None) -> str:
    """日志行首的时间戳（按 DISPLAY_TIMEZONE，与截图上的时间同一口径）。"""
    zone = resolve_display_timezone(settings)
    moment = datetime.fromtimestamp(timestamp, zone) if timestamp is not None else datetime.now(zone)
    return moment.strftime("%Y-%m-%d %H:%M:%S")


def parse_date_cutoff(text: str, settings: Settings) -> datetime | None:
    """把「2026-10-31」解析成 DISPLAY_TIMEZONE 当天 0 点，返回带时区的 UTC 时间。

    支持 `2026-10-31`、`2026/10/31`、`2026.10.31`、`2026年10月31日`，
    也接受后面跟 `HH:MM[:SS]`（Cutoff 就变成那个时刻，而不是当天 0 点）。
    返回 None 表示格式不对 —— 调用方据此回一句用法提示，绝不猜一个日期去删数据。
    """
    raw = str(text or "").strip()
    if not raw:
        return None
    normalized = raw.replace("年", "-").replace("月", "-").replace("日", "")
    normalized = normalized.replace("/", "-").replace(".", "-").replace(" ", "-")
    # 允许「2026-10-31-14:30」这种被空格换成横线的写法
    match = re.match(
        r"^(\d{4})-(\d{1,2})-(\d{1,2})(?:-(\d{1,2}):(\d{2})(?::(\d{2}))?)?$",
        normalized,
    )
    if not match:
        return None
    try:
        local = datetime(
            int(match.group(1)),
            int(match.group(2)),
            int(match.group(3)),
            int(match.group(4) or 0),
            int(match.group(5) or 0),
            int(match.group(6) or 0),
            tzinfo=resolve_display_timezone(settings),
        )
    except ValueError:
        return None
    return local.astimezone(timezone.utc)


def seconds_until_quota_reset(settings: Settings, timestamp: float | None = None) -> float:
    """距离下一个 0 点还有多少秒（超限提示里告诉用户什么时候能再发）。"""
    zone = resolve_display_timezone(settings)
    now = datetime.fromtimestamp(timestamp, zone) if timestamp is not None else datetime.now(zone)
    tomorrow = (now + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
    return max(0.0, (tomorrow - now).total_seconds())


def format_quota_reset_countdown(seconds: float) -> str:
    """把「还有多久到 0 点」渲染成「3 小时 12 分钟」这种人话（不足 1 分钟按 1 分钟）。"""
    total_minutes = max(1, int(math.ceil(max(0.0, float(seconds)) / 60.0)))
    hours, minutes = divmod(total_minutes, 60)
    if hours and minutes:
        return f"{hours} 小时 {minutes} 分钟"
    if hours:
        return f"{hours} 小时"
    return f"{minutes} 分钟"


def format_rate_limit_notice(settings: Settings, wait_seconds: float) -> str:
    """生成「今天的投稿条数已用完」的提示文案（每日 0 点重置）。"""
    limit = settings.daily_message_limit
    countdown = format_quota_reset_countdown(wait_seconds)
    return (
        f"今天已经发满 {limit} 条啦～每人每天最多 {limit} 条投稿消息。\n"
        f"这条没有被收录，{countdown}后（每日 0 点）自动重置。"
    )


def format_due_time(settings: Settings, timestamp: float) -> str:
    """把时间点渲染成「今天 18:00」「明天 08:00」这种可读文本。

    用途：封禁到期时间、额度重置时间等一切「告诉用户什么时候恢复」的地方。
    """
    zone = resolve_display_timezone(settings)
    moment = datetime.fromtimestamp(timestamp, zone)
    days = (moment.date() - datetime.now(zone).date()).days
    label = {0: "今天", 1: "明天"}.get(days, moment.strftime("%m-%d"))
    return f"{label} {moment.strftime('%H:%M')}"


class _ImageBudgetExceeded(RuntimeError):
    """本次投稿的图片总体积超过预算：终止发布，避免把内存吃光。"""


async def render_screenshot(
    session: SubmissionSession,
    *,
    anonymous: bool,
    settings: Settings,
    http_client: httpx.AsyncClient,
    output_dir: Path,
    submission_code: str = "",
    display_time: str = "",
    badge_bytes: bytes | None = None,
    failures: list[str] | None = None,
) -> Path:
    """下载必要素材后，把投稿渲染成长截图并返回落盘路径。

    anonymous=True 时不绘制昵称与头像（连头像都不下载，避免无谓暴露）。
    badge_bytes 是管理员标记图的字节（None = 不画）；它只影响叠加的小徽标，
    下载/解码失败都不会影响投稿本身。
    failures 若传入一个列表，会把「哪张图/为什么没读进来」追加进去（给用户看的诊断信息）。
    渲染（Pillow 解码 / 缩放 / 绘图 / 保存）是同步 CPU 工作，统一交给
    asyncio.to_thread 执行：既避免阻塞事件循环导致 WebSocket 接收停摆，
    也保证这里的每次 await 都是真正的网络挂起点。
    """
    # --- 异步阶段：只做网络下载 ---
    avatar_bytes: bytes | None = None
    if not anonymous and settings.draw_avatar and settings.avatar_url_template:
        avatar_url = settings.avatar_url_template.format(user_id=session.user_id)
        try:
            avatar_bytes = await download_asset(http_client, avatar_url, settings)
        except asyncio.CancelledError:
            raise  # 外部取消必须继续向上传播
        except Exception:
            logger.warning("头像下载失败，将使用占位头像：user_id=%s", session.user_id, exc_info=True)

    image_bytes: dict[int, bytes] = {}
    # 单次投稿的图片总字节预算：截图与发布原图共用同一个额度（见 MAX_SUBMISSION_IMAGE_BYTES）
    budget = max(0, settings.max_submission_image_bytes)
    used_bytes = 0
    for index, message in enumerate(session.messages):
        # 表情也可能带图（商城表情 / 配置了表情图源），同样要在截图里显示
        candidates = message.image_candidates()
        if not candidates and not message.image_bytes:
            continue
        raw: bytes | None = message.image_bytes  # 已下载过的字节优先复用
        used_url = candidates[0] if candidates else message.image_url
        last_error = ""
        if raw is None:
            for position, url in enumerate(candidates):
                # 先看是不是本机文件（file:// 或绝对路径）：NapCat 偶尔只给 file 不给 url
                local = await asyncio.to_thread(read_local_asset, url)
                if local is not None:
                    raw = local
                    used_url = url
                    logger.info("图片直接读自本机文件（未走 HTTP）：%s", Path(url).name)
                    break
                try:
                    raw = await download_asset_retry(http_client, url, settings)
                except asyncio.CancelledError:
                    raise  # 外部取消必须继续向上传播
                except Exception as exc:  # 单个图源失败只影响该源，继续试下一个（不阻断整次投稿）
                    last_error = str(exc) or exc.__class__.__name__
                    logger.warning(
                        "截图素材下载失败（图源 %d/%d）：%s → %s",
                        position + 1,
                        len(candidates),
                        _url_host(url) or "(非 http 地址)",
                        exc,
                    )
                    continue
                used_url = url
                if position:
                    # 「主图源在国内取不到 → 表情只剩文字」的正解就是这一条自动换源（ERR-014）
                    logger.info("主图源不可用，已改用备用图源取到素材：%s", url)
                break
        if raw is None:
            # 把所有图源都试过了：这正是「图片没能读取成功」最常见的那一类
            logger.warning("截图素材的所有图源都失败，改用占位文本：%s", candidates)
            if failures is not None:
                host = _url_host(candidates[0]) if candidates else ""
                detail = f"：{last_error}" if last_error else ""
                failures.append(
                    f"第 {index + 1} 条消息的图片下载失败"
                    + (f"（图源主机 {host}）" if host else "（消息里没有可用的图片地址）")
                    + detail
                )
            continue
        if budget and used_bytes + len(raw) > budget:
            # 超预算就整条不发：截图少一张图 = 用户以为发全了，比明说「没发」更糟
            raise _ImageBudgetExceeded(
                f"图片总体积超过 {budget / 1048576:.0f} MiB 预算"
                f"（已处理 {used_bytes / 1048576:.1f} MiB，本张 {len(raw) / 1048576:.1f} MiB）"
            )
        used_bytes += len(raw)
        # 下载后立刻统一成「空间能上传」的格式（JPEG/PNG/GIF）。这样一来送审与发布
        # 看的是同一份字节，不会出现「审核跳过不支持格式 → 审核通过 → 发布时上传失败」。
        prepared = await asyncio.to_thread(
            _prepare_image_for_publish, raw, used_url, max_pixels=settings.max_image_pixels
        )
        if prepared is None:
            logger.warning("图片无法识别，已放弃该图：%s", used_url)
            if failures is not None:
                failures.append(
                    f"第 {index + 1} 条消息的图片无法识别或超过像素上限"
                    f"（上限 {settings.max_image_pixels or 0} 像素；格式可能不受支持）"
                )
            continue
        data, _suffix = prepared
        image_bytes[index] = data
        message.image_bytes = data  # 供原图保存复用，避免同一张图下载两次

    output_dir.mkdir(parents=True, exist_ok=True)
    target = _safe_join(
        output_dir, f"screenshot_{session.user_id}_{int(time.time())}_{uuid.uuid4().hex[:8]}.png"
    )

    # --- 同步阶段：全部 Pillow 工作放到线程里，避免阻塞事件循环 ---
    await asyncio.to_thread(
        _compose_screenshot,
        session,
        anonymous=anonymous,
        settings=settings,
        avatar_bytes=avatar_bytes,
        image_bytes=image_bytes,
        target=target,
        submission_code=submission_code,
        display_time=display_time,
        badge_bytes=badge_bytes,
    )
    return target


# 发言气泡宽度占整张图的比例（需求：文字只占整图宽度的 3/5）。
BUBBLE_WIDTH_RATIO = 0.6
# 背景照片不可用时的页面底色（需求：铺不下这张照片时改用纯白，不要拉伸/放大它）。
CHAT_BACKGROUND_FALLBACK = (255, 255, 255)


def _ellipsize(text: str, font: Any, max_width: float, emoji_font: Any = None) -> str:
    """把过长的文字截成「……」，避免撑破头像旁边那块小牌。"""
    body = (text or "").strip()
    if not body or max_width <= 0:
        return ""
    if _rich_text_length(body, font, emoji_font) <= max_width:
        return body
    while body and _rich_text_length(body + "…", font, emoji_font) > max_width:
        body = body[:-1]
    return (body + "…") if body else "…"


def _compose_screenshot(
    session: SubmissionSession,
    *,
    anonymous: bool,
    settings: Settings,
    avatar_bytes: bytes | None,
    image_bytes: dict[int, bytes],
    target: Path,
    submission_code: str = "",
    display_time: str = "",
    badge_bytes: bytes | None = None,
) -> None:
    """同步渲染核心（在 asyncio.to_thread 中执行，故此处不得出现 await）。

    渲染版式：
      * **用背景时整张图保持背景图自己的横向比例**（按自定义图片比例）：画布高度 = 宽度 × 图高/图宽，
        正文放得下就留白给照片，看起来是一张完整的背景卡片；
      * 正文放不下（长文/多图）→ 整页改用纯白底，高度随内容增长（不再为塞内容去拉伸照片）；
      * 左上角头像，右边两行直接写在背景上（没有白底小牌）：
        上行昵称 + 管理员徽标，下行投稿人 QQ；
      * 发言气泡宽度固定为整图宽度的 3/5（BUBBLE_WIDTH_RATIO），高度随文字多少伸缩，
        圆角 10px；字号与内边距都比上一版更小；
      * 「投稿时间 · 编号」不带底条，直接压在画面下部。
    """
    width = max(320, settings.screenshot_width)
    pad = 24
    avatar_size = 54
    bubble_pad = 10
    line_height = 25
    bubble_radius = 10
    # 需求：发言文字宽度只占整张图宽度的五分之三
    bubble_width = int(round(width * BUBBLE_WIDTH_RATIO))
    bubble_width = max(180, min(bubble_width, width - pad * 2))
    inner_width = max(80, bubble_width - bubble_pad * 2)
    text_font = _load_font(18)
    name_font = _load_font(21)
    meta_font = _load_font(16)
    emoji_font = _load_emoji_font(18)
    name_emoji_font = _load_emoji_font(21)
    image_max_height = 320
    # 管理员徽标：画在昵称右边（加载失败为 None，只是不画，不影响投稿）
    badge = load_admin_badge(badge_bytes)
    badge_gap = 8
    name_row_height = 30
    qq_row_height = 22
    header_h = max(avatar_size, name_row_height + qq_row_height)
    footer_h = 24

    # --- 第一遍：量算（图片解码失败 → 退化为占位文本）---
    layouts: list[_BubbleLayout] = []
    for index, message in enumerate(session.messages):
        layout = _BubbleLayout(message=message, text_lines=[], images=[], image_heights=[])
        if message.kind == "text":
            layout.text_lines = (
                _wrap_text(message.text, text_font, inner_width, emoji_font) or [""]
            )
        elif message.kind in {"image", "face"}:
            image = None
            data = image_bytes.get(index)
            if data is not None:
                try:
                    image = _load_image(
                        data,
                        max_width=inner_width,
                        max_height=image_max_height,
                        max_pixels=settings.max_image_pixels,
                    )
                except Exception:
                    logger.warning(
                        "截图内图片解码失败，已用占位文本替代：%s",
                        message.image_url or message.face_label,
                        exc_info=True,
                    )
            if image is None:
                if message.kind == "face":
                    layout.text_lines = [message.face_label or "[表情]"]
                else:
                    layout.text_lines = ["[图片加载失败]"]
            else:
                layout.images = [image]
                layout.image_heights = [image.height]
        layouts.append(layout)

    # --- 第二遍：计算画布高度（文字越多，气泡越高）---
    body_height = 0
    for layout in layouts:
        inner = 0
        if layout.text_lines:
            inner += len(layout.text_lines) * line_height
        for image_height in layout.image_heights:
            inner += image_height + 8
        body_height += max(inner + bubble_pad * 2, 50) + 12
    content_height = max(220, pad + header_h + 10 + body_height + footer_h + pad)

    # 背景：正文放得下就用照片，并且**画布高度取背景图自己的比例**（默认 720×540 = 4:3）；
    # 放不下就整页纯白、高度随内容长（绝不为了塞内容去拉伸照片）。
    background = load_chat_background(settings, width, content_height)
    total_height = background.height if background is not None else content_height
    canvas = Image.new("RGB", (width, total_height), CHAT_BACKGROUND_FALLBACK)
    if background is not None:
        canvas.paste(background, (0, 0))
    draw = ImageDraw.Draw(canvas)

    # --- 头部：头像 + 两行文字（昵称+徽标 / QQ，均不垫白底）---
    if anonymous:
        display_name = "匿名投稿"
        sub_text = "投稿人已隐藏"
        text_x = pad
        avatar = None
    else:
        display_name = session.nickname or f"QQ {session.user_id}"
        sub_text = f"QQ {session.user_id}"
        text_x = pad + avatar_size + 12
        avatar = None
        if avatar_bytes is not None:
            try:
                with Image.open(io.BytesIO(avatar_bytes)) as raw:
                    # 头像同样先过像素上限再解码：这个地址也可能被换成一张超大图
                    _reject_oversized_image(raw, settings.max_image_pixels, source="头像")
                    with contextlib.suppress(Exception):
                        raw.draft("RGB", (avatar_size, avatar_size))
                    avatar = _circle_avatar(raw.convert("RGBA"), avatar_size)
            except Exception:
                logger.warning(
                    "头像解码失败，使用占位头像：user_id=%s", session.user_id, exc_info=True
                )
        if avatar is None:
            avatar = _placeholder_avatar(
                session.nickname, avatar_size, name_font, name_emoji_font
            )

    on_photo = background is not None

    badge_w = badge.width if badge is not None else 0
    # 昵称最多占到这个位置：整图右边界留给徽标，超长昵称用「…」截断
    max_name_w = max(
        40.0,
        float(width - pad - text_x - (badge_w + badge_gap if badge is not None else 0)),
    )
    display_name = _ellipsize(display_name, name_font, max_name_w, name_emoji_font)
    name_w = _rich_text_length(display_name, name_font, name_emoji_font)
    # 两行文字与头像一起垂直居中：没有底牌之后，只剩文字本身要贴着头像
    block_h = name_row_height + qq_row_height
    head_y = pad + max(0, (header_h - block_h) // 2)
    if avatar is not None:
        canvas.paste(avatar, (pad, pad + (header_h - avatar_size) // 2), avatar)
    # 文字颜色随**文字正下方这一小块底图**的亮度切换：亮底深字、暗底白字。
    # 取样框只覆盖文字实际占的宽度 —— 取整行会把右边的亮背景算进来，判断就会跑偏。
    text_block_w = max(
        name_w + (badge_w + badge_gap if badge is not None else 0.0),
        _safe_getlength(meta_font, sub_text),
    )
    if on_photo:
        head_fill, head_edge = _contrast_text_colors(
            canvas, (text_x, head_y, text_x + text_block_w + 6, head_y + block_h)
        )
        name_fill, name_stroke, name_stroke_fill = head_fill, 0, None
        sub_fill, sub_stroke, sub_stroke_fill = head_fill, 0, None
    else:
        name_fill, name_stroke, name_stroke_fill = (34, 38, 48), 0, None
        sub_fill, sub_stroke, sub_stroke_fill = (48, 54, 66), 0, None
    _draw_rich_text(
        draw,
        (text_x, head_y),
        display_name,
        name_font,
        emoji_font=name_emoji_font,
        fill=name_fill,
        canvas=canvas,
        stroke_width=name_stroke,
        stroke_fill=name_stroke_fill,
    )
    if badge is not None:
        canvas.paste(
            badge,
            (
                int(text_x + name_w + badge_gap),
                int(head_y + (name_row_height - badge.height) / 2),
            ),
            badge,
        )
    _draw_plain_text(
        draw,
        (text_x, head_y + name_row_height),
        sub_text,
        meta_font,
        sub_fill,
        stroke_width=sub_stroke,
        stroke_fill=sub_stroke_fill,
    )

    # --- 消息气泡：宽度固定 3/5，高度随内容 ---
    y = pad + header_h + 10
    for layout in layouts:
        inner = 0
        if layout.text_lines:
            inner += len(layout.text_lines) * line_height
        for image_height in layout.image_heights:
            inner += image_height + 8
        bubble_height = max(inner + bubble_pad * 2, 50)
        draw.rounded_rectangle(
            (pad, y, pad + bubble_width, y + bubble_height),
            radius=bubble_radius,
            fill=(255, 255, 255),
            outline=(228, 232, 239),
            width=1,
        )
        cursor_y = y + bubble_pad
        if layout.text_lines:
            for line in layout.text_lines:
                is_placeholder = line.startswith("[") and line.endswith("]")
                _draw_rich_text(
                    draw,
                    (pad + bubble_pad, cursor_y),
                    line,
                    text_font,
                    emoji_font=emoji_font,
                    fill=(150, 150, 150) if is_placeholder else (30, 30, 34),
                    canvas=canvas,
                )
                cursor_y += line_height
        for image in layout.images:
            canvas.paste(image, (pad + bubble_pad, cursor_y), image)
            cursor_y += image.height + 8
        y += bubble_height + 12

    # --- 底部：投稿时间 · 编号（不再加深色底条，直接写在画面下部）---
    footer_text = display_time or format_submission_time(settings)
    if submission_code:
        footer_text = f"{footer_text} · 编号 {submission_code}"
    footer_text = _ellipsize(footer_text, meta_font, width - pad * 2)
    footer_y = total_height - pad - 16
    if on_photo:
        footer_w = int(_safe_getlength(meta_font, footer_text))
        footer_fill, footer_edge = _contrast_text_colors(
            canvas, (pad, footer_y, pad + footer_w + 4, footer_y + 22)
        )
        footer_stroke, footer_stroke_fill = 0, None
    else:
        footer_fill, footer_stroke, footer_stroke_fill = (96, 102, 114), 0, None
    _draw_plain_text(
        draw,
        (pad, footer_y),
        footer_text,
        meta_font,
        footer_fill,
        stroke_width=footer_stroke,
        stroke_fill=footer_stroke_fill,
    )

    canvas.save(target, format="PNG")

def _safe_join(base: Path, name: str) -> Path:
    """把生成的文件名拼到白名单目录内，并拒绝任何越界路径（安全红线：路径穿越）。"""
    base_resolved = base.resolve()
    candidate = (base_resolved / name).resolve()
    if base_resolved != candidate.parent:
        raise ValueError(f"非法的输出路径：{name}")
    return candidate


# --------------------------------------------------------------------------------------
# 四、网络下载
# --------------------------------------------------------------------------------------

# 下载最多跟随几次重定向。每一跳都会重新做一次地址检查（见 fetch_bytes）——
# 只在入口检查一次的话，公网地址 302 到内网就绕过了 ALLOW_PRIVATE_IMAGE_HOSTS（ERR-017）。
_MAX_REDIRECT_HOPS = 5


def _is_private_host(hostname: str | None) -> bool:
    """主机名是否指向回环 / 私网 / 链路本地地址。

    只做字面量判定、不做 DNS 解析：DNS 解析既增加延迟又有 TOCTOU 问题，
    而这里的目标是拦住「投稿里塞一个内网地址」这类明显滥用，不是完整 SSRF 防护。
    """
    host = (hostname or "").strip().strip("[]").lower()
    if not host:
        return True
    if host in {"localhost", "localhost.localdomain"}:
        return True
    try:
        address = ipaddress.ip_address(host)
    except ValueError:
        return False  # 普通域名
    return (
        address.is_private
        or address.is_loopback
        or address.is_link_local
        or address.is_reserved
    )


async def fetch_bytes(
    client: httpx.AsyncClient,
    url: str,
    *,
    timeout: float,
    max_bytes: int = 0,
    allow_private_hosts: bool = True,
    max_redirects: int = _MAX_REDIRECT_HOPS,
) -> bytes:
    """流式下载二进制内容。

    - 仅允许 http/https；
    - `max_bytes > 0` 时超过上限立即中止，避免把超大响应整个读进内存；
    - `allow_private_hosts=False` 时拒绝回环 / 私网 / 链路本地目标，
      并且**逐跳**检查重定向目标 —— 只在入口检查一次的话，一个公网地址
      302 到 127.0.0.1 就绕过去了（ERR-017）。

    `allow_private_hosts` 默认 True 是有意的：NapCat 常把图片挂在 127.0.0.1 上，
    默认收紧会把图片功能直接打挂，因此改成显式开关交给部署方决定。
    """
    current = url
    hops = max(0, max_redirects)
    for hop in range(hops + 1):
        if not current.lower().startswith(("http://", "https://")):
            raise ValueError(f"仅支持 http/https 地址：{current[:32]}")

        parsed = httpx.URL(current)
        if not allow_private_hosts and _is_private_host(parsed.host):
            raise ValueError(f"目标地址属于内网/回环，已拒绝下载：{parsed.host}")

        chunks: list[bytes] = []
        total = 0
        # follow_redirects=False：重定向由本函数自己逐跳处理，保证每一跳都过一遍地址检查
        async with client.stream(
            "GET", current, timeout=timeout, follow_redirects=False
        ) as response:
            if response.is_redirect:
                location = response.headers.get("location")
                if not location:
                    raise ValueError(f"重定向响应缺少 Location，已中止：{current[:64]}")
                if hop >= hops:
                    raise ValueError(f"重定向次数超过 {hops} 次，已中止：{url[:64]}")
                current = str(parsed.join(location))
                # 只记主机名：NapCat 的图片地址里带 rkey 凭据，不该整条进日志
                logger.info("下载地址重定向（第 %d 跳）→ %s", hop + 1, httpx.URL(current).host)
                continue

            response.raise_for_status()
            async for chunk in response.aiter_bytes():
                total += len(chunk)
                if max_bytes and total > max_bytes:
                    raise ValueError(f"响应超过 {max_bytes} 字节上限，已中止下载：{url[:64]}")
                chunks.append(chunk)
        return b"".join(chunks)

    raise ValueError(f"重定向次数超过 {hops} 次，已中止：{url[:64]}")


async def download_asset(client: httpx.AsyncClient, url: str, settings: Settings) -> bytes:
    """按配置下载素材：统一套用超时、大小上限与内网地址策略。"""
    return await fetch_bytes(
        client,
        url,
        timeout=settings.http_timeout,
        max_bytes=settings.max_download_bytes,
        allow_private_hosts=settings.allow_private_image_hosts,
    )


# 图片下载的重试节奏：NapCat 的图片地址偶发 404 / 连接被重置，隔一会儿再试通常就好了。
_DOWNLOAD_RETRY_DELAYS: tuple[float, ...] = (0.4, 1.2)


async def download_asset_retry(
    client: httpx.AsyncClient, url: str, settings: Settings, *, attempts: int = 3
) -> bytes:
    """download_asset 的带重试版本：临时性失败（连接重置 / 偶发 5xx）再试两次。

    为什么要重试：一次网络抖动就让整条投稿作废（用户还得重发图片）代价太大，
    而图片地址在几分钟内通常仍然有效，多试两次能把这类失败挡掉。
    """
    last: BaseException | None = None
    total = max(1, int(attempts))
    for attempt in range(total):
        try:
            return await download_asset(client, url, settings)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            last = exc
            if attempt + 1 >= total:
                break
            delay = _DOWNLOAD_RETRY_DELAYS[min(attempt, len(_DOWNLOAD_RETRY_DELAYS) - 1)]
            logger.info(
                "下载失败（第 %d/%d 次），%.1f 秒后重试：host=%s",
                attempt + 1,
                total,
                delay,
                _url_host(url) or "(无主机)",
            )
            await asyncio.sleep(delay)
    raise last if last is not None else RuntimeError("下载失败")


def read_local_asset(value: str) -> bytes | None:
    """把「file:// URL 或本地绝对路径」读成字节；不是本地文件就返回 None。

    为什么需要它：有些 NapCat 部署给的 image 段只有 `file`（指向本机缓存文件）
    而没有 `url`，此时走 HTTP 必然失败 —— 同机直接读文件能救回这一整类
    「图片没能读取成功」。只接受绝对路径/`file://`，绝不拿裸文件名去猜目录。
    """
    text = (value or "").strip()
    if not text:
        return None
    if text.startswith("file://"):
        text = text[len("file://") :]
        if re.match(r"^/[A-Za-z]:", text):  # file:///C:/... 会多一个前导斜杠
            text = text[1:]
    elif not re.match(r"^(?:[A-Za-z]:[\\/]|/|\\\\)", text):
        return None  # 既不是 file:// 也不是绝对路径 → 交给 HTTP 下载
    try:
        path = Path(text)
        if not path.is_file():
            return None
        data = path.read_bytes()
    except OSError:
        return None
    return data or None


# --------------------------------------------------------------------------------------
# 五、持久化
# --------------------------------------------------------------------------------------

_SCHEMA = """
CREATE TABLE IF NOT EXISTS submissions (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id      INTEGER NOT NULL,
    content      TEXT    NOT NULL,
    images       TEXT    NOT NULL,
    status       TEXT    NOT NULL,
    risk_level   TEXT,
    reason       TEXT,
    created_at   TEXT    NOT NULL,
    display_code TEXT,
    display_time TEXT,
    qzone_tid    TEXT
);
CREATE INDEX IF NOT EXISTS idx_submissions_user_created
    ON submissions (user_id, created_at DESC);
CREATE TABLE IF NOT EXISTS blacklist (
    user_id    INTEGER PRIMARY KEY,
    reason     TEXT,
    operator   TEXT,
    created_at TEXT NOT NULL,
    until      TEXT
);
"""

# ⚠️ display_code 的索引**不能**写在上面的 _SCHEMA 里：
# CREATE TABLE IF NOT EXISTS 对已存在的老表是空操作，所以老库执行这段脚本时
# 表里还没有 display_code 列，紧接着的 CREATE INDEX 会直接抛
# `sqlite3.OperationalError: no such column: display_code` —— 整个服务起不来。
# 正确顺序是「先补列、再建索引」，因此这条索引放在 _migrate_submissions() 末尾。
# （2026-10-06 线上真实发生：服务启动即失败，见 errors/ERR-012.md）
_SUBMISSIONS_DISPLAY_CODE_INDEX = (
    "CREATE INDEX IF NOT EXISTS idx_submissions_display_code"
    " ON submissions (display_code)"
)

# 老库补列：CREATE TABLE IF NOT EXISTS 不会修改已存在的表，
# 所以线上已有数据的库要靠这里补上新列。列名与类型都是代码里的常量，不接受外部输入。
_SUBMISSION_ADDED_COLUMNS = (
    ("display_code", "TEXT"),
    ("display_time", "TEXT"),
    ("qzone_tid", "TEXT"),
)

# 黑名单补列：until 为空 = 永久拉黑；有值 = 限期封禁（到点自动失效）
_BLACKLIST_ADDED_COLUMNS = (("until", "TEXT"),)


def _utc_now() -> datetime:
    """当前时间（UTC、带时区）：数据库里的时间统一用它，避免服务器时区影响判断。"""
    return datetime.now(timezone.utc)


def _published_before(
    rows: list[dict[str, Any]], cutoff_utc: str | None
) -> list[dict[str, Any]]:
    """从 rows 里挑出 `created_at` 早于 cutoff_utc 的那些（cutoff 为 None 表示全要）。

    抽成独立函数是为了能单独测：老库的时间格式不统一，这里一旦判错，
    清理旧说说就会「跑完一条没删」而完全不报错。
    """
    if cutoff_utc is None:
        return list(rows)
    cutoff = _parse_db_time(cutoff_utc)
    if cutoff is None:
        raise ValueError(f"cutoff_utc 不是合法时间：{cutoff_utc!r}")
    picked: list[dict[str, Any]] = []
    for row in rows:
        moment = _parse_db_time(row.get("created_at"))
        # 时间解析不出来的老记录不参与清理：宁可漏删、让人工处理，也不能误删
        if moment is not None and moment < cutoff:
            picked.append(row)
    return picked


def _parse_db_time(value: Any) -> datetime | None:
    """把库里的时间文本解析成带时区的 datetime；认不出来返回 None。

    为什么要单独写一个：`created_at` 是 TEXT，历史上不同版本写进去的格式并不统一
    （`2026-10-30T12:34:56+00:00`、`2026-10-30 12:34:56`、甚至不带时区的裸时间）。
    直接拿字符串比较大小，遇到格式不同的老记录会**静默漏掉**、一条都不报错 ——
    清理旧说说时表现为「跑了，但一条也没删」，非常难查。统一解析后再比较。
    不带时区的按 UTC 处理（库里本来就都存 UTC）。
    """
    text = str(value or "").strip()
    if not text:
        return None
    try:
        moment = datetime.fromisoformat(text)
    except ValueError:
        return None
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def _parse_expiry(text: Any) -> datetime | None:
    """把库里存的到期时间解析成带时区的 datetime；空值 = 永久，解析失败按永久处理。

    解析失败刻意按「永久」处理：这一列只由本程序写入，出现无法解析的值说明数据被改坏了，
    此时**保留封禁**比「因为读不懂就放行」安全（后者等于给违规者送一次免费通行证）。
    """
    value = str(text or "").strip()
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        logger.error("封禁到期时间无法解析（按永久封禁处理）：%r", value)
        return None
    return parsed if parsed.tzinfo is not None else parsed.replace(tzinfo=timezone.utc)


class Database:
    """aiosqlite 封装：单连接 + 互斥锁，保证并发任务写入不交叉。

    所有 SQL 均使用参数占位符，杜绝拼接用户输入（安全红线：SQL 参数化）。
    """

    def __init__(self, path: str) -> None:
        self._path = path
        self._conn: aiosqlite.Connection | None = None
        self._lock = asyncio.Lock()

    async def connect(self) -> None:
        """打开数据库，并按顺序迁移旧表结构与索引。"""
        if self._conn is not None:
            return
        db_path = Path(self._path)
        if db_path.parent and str(db_path.parent) not in {"", "."}:
            db_path.parent.mkdir(parents=True, exist_ok=True)
        self._conn = await aiosqlite.connect(self._path)
        self._conn.row_factory = aiosqlite.Row
        await self._conn.executescript(_SCHEMA)
        await self._migrate_submissions()
        await self._conn.commit()
        logger.info("数据库就绪：%s", self._path)

    async def _migrate_submissions(self) -> None:
        """给已存在的老库补上新列，再补依赖这些列的索引（幂等，重复调用无副作用）。

        顺序不能反：索引建在 display_code 上，而老表里这一列要等 ALTER TABLE 之后才存在。
        """
        conn = self._require_conn()
        for table, columns in (
            ("submissions", _SUBMISSION_ADDED_COLUMNS),
            ("blacklist", _BLACKLIST_ADDED_COLUMNS),
        ):
            cursor = await conn.execute(f"PRAGMA table_info({table})")
            existing = {str(row["name"]) for row in await cursor.fetchall()}
            for column, kind in columns:
                if column in existing:
                    continue
                # 列名/类型来自上面的常量表，不含任何外部输入（ALTER TABLE 无法参数化）
                await conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {kind}")
                logger.info("数据库迁移：%s 补列 %s %s", table, column, kind)
        await conn.execute(_SUBMISSIONS_DISPLAY_CODE_INDEX)

    async def close(self) -> None:
        if self._conn is not None:
            await self._conn.close()
            self._conn = None

    def _require_conn(self) -> aiosqlite.Connection:
        """返回活动连接；未调用 connect 时及时抛错。"""
        if self._conn is None:
            raise RuntimeError("数据库尚未初始化，请先调用 Database.connect()")
        return self._conn

    async def insert_submission(
        self,
        *,
        user_id: int,
        content: str,
        images: Sequence[str],
        status: str,
        risk_level: str | None,
        reason: str | None,
        display_code: str | None = None,
        display_time: str | None = None,
    ) -> int:
        """写入一条投稿记录，返回自增 id。

        display_code / display_time 是截图底部实际渲染出来的「编号」与「投稿时间」，
        存下来的目的：管理员只能从截图里读到这两个值，靠它们才能反查到投稿人。
        """
        conn = self._require_conn()
        async with self._lock:
            cursor = await conn.execute(
                "INSERT INTO submissions"
                " (user_id, content, images, status, risk_level, reason, created_at,"
                "  display_code, display_time)"
                " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    int(user_id),
                    content,
                    json.dumps(list(images), ensure_ascii=False),
                    status,
                    risk_level,
                    reason,
                    datetime.now(timezone.utc).isoformat(timespec="seconds"),
                    display_code,
                    display_time,
                ),
            )
            await conn.commit()
            return int(cursor.lastrowid or 0)

    async def update_submission(
        self,
        submission_id: int,
        *,
        status: str,
        risk_level: str | None = None,
        reason: str | None = None,
        qzone_tid: str | None = None,
    ) -> None:
        """更新投稿状态；未传的字段保持原值（COALESCE），不会被 NULL 覆盖掉。"""
        conn = self._require_conn()
        async with self._lock:
            await conn.execute(
                "UPDATE submissions SET status = ?,"
                " risk_level = COALESCE(?, risk_level),"
                " reason = COALESCE(?, reason),"
                " qzone_tid = COALESCE(?, qzone_tid)"
                " WHERE id = ?",
                (status, risk_level, reason, qzone_tid, int(submission_id)),
            )
            await conn.commit()

    # ---------------- 按截图上的编号 / 投稿时间反查 ----------------

    async def find_submission_by_marker(self, marker: str) -> dict[str, Any] | None:
        """按「投稿编号」或「截图上的投稿时间」找最近一条投稿。

        两种输入都支持，是因为编号要等新版上线后才会出现在截图上，
        而管理员手上可能只有旧截图里的时间。
        """
        conn = self._require_conn()
        value = marker.strip()
        if not value:
            return None
        cursor = await conn.execute(
            "SELECT * FROM submissions WHERE UPPER(display_code) = ? ORDER BY id DESC LIMIT 1",
            (value.upper(),),
        )
        row = await cursor.fetchone()
        if row is None:
            cursor = await conn.execute(
                "SELECT * FROM submissions WHERE display_time LIKE ? ORDER BY id DESC LIMIT 1",
                (f"%{value}%",),
            )
            row = await cursor.fetchone()
        return dict(row) if row is not None else None

    async def list_user_submissions(
        self, user_id: int, *, status: str | None = None
    ) -> list[dict[str, Any]]:
        """列出某个用户的投稿（可按状态过滤），按时间从新到旧。"""
        conn = self._require_conn()
        if status is None:
            cursor = await conn.execute(
                "SELECT * FROM submissions WHERE user_id = ? ORDER BY id DESC", (int(user_id),)
            )
        else:
            cursor = await conn.execute(
                "SELECT * FROM submissions WHERE user_id = ? AND status = ? ORDER BY id DESC",
                (int(user_id), status),
            )
        return [dict(row) for row in await cursor.fetchall()]

    # ---------------- 黑名单 ----------------

    async def is_blacklisted(self, user_id: int) -> bool:
        """是否处于「禁止投稿」状态：永久拉黑，或限期封禁还没到期。

        到期的封禁在这里自动失效（不改库，只按时间判断）—— 这样「封 3 天」不需要
        任何定时任务，也不会因为服务停机而永久生效。
        """
        conn = self._require_conn()
        cursor = await conn.execute(
            "SELECT until FROM blacklist WHERE user_id = ? LIMIT 1", (int(user_id),)
        )
        row = await cursor.fetchone()
        if row is None:
            return False
        expiry = _parse_expiry(row["until"])
        if expiry is None:
            return True
        if expiry > _utc_now():
            return True
        logger.info("限期封禁已到期，自动恢复投稿资格：user_id=%s 到期=%s", user_id, expiry.isoformat())
        return False

    async def add_blacklist(
        self,
        user_id: int,
        *,
        reason: str,
        operator: str,
        until: datetime | None = None,
    ) -> None:
        """把用户拉进黑名单（重复拉黑只更新原因，不报错）。

        until 为空 = 永久拉黑（管理员手动拉黑走这条）；给了时间 = 限期封禁（自动封禁走这条）。
        """
        conn = self._require_conn()
        async with self._lock:
            await conn.execute(
                "INSERT INTO blacklist (user_id, reason, operator, created_at, until)"
                " VALUES (?, ?, ?, ?, ?)"
                " ON CONFLICT(user_id) DO UPDATE SET reason = excluded.reason,"
                " operator = excluded.operator, created_at = excluded.created_at,"
                " until = excluded.until",
                (
                    int(user_id),
                    reason,
                    operator,
                    _utc_now().isoformat(timespec="seconds"),
                    until.isoformat(timespec="seconds") if until is not None else None,
                ),
            )
            await conn.commit()

    async def count_recent_rejections(self, user_id: int, *, hours: float) -> int:
        """统计该用户最近一段时间里「被审核拒绝」的次数（自动封禁的依据）。

        只数 rejected：审核服务不可用（failed）不算用户的错，不能因此封人。
        """
        conn = self._require_conn()
        cutoff = _utc_now() - timedelta(hours=max(0.0, hours))
        cursor = await conn.execute(
            "SELECT COUNT(*) AS n FROM submissions"
            " WHERE user_id = ? AND status = 'rejected' AND created_at >= ?",
            (int(user_id), cutoff.isoformat(timespec="seconds")),
        )
        row = await cursor.fetchone()
        return int(row["n"]) if row is not None else 0

    async def recent_rejected_texts(self, user_id: int, *, limit: int = 3) -> list[str]:
        """该用户最近被拒绝的投稿正文（送审时作为上下文，识别「换个说法重发」）。"""
        conn = self._require_conn()
        cursor = await conn.execute(
            "SELECT content FROM submissions WHERE user_id = ? AND status = 'rejected'"
            " ORDER BY id DESC LIMIT ?",
            (int(user_id), max(1, int(limit))),
        )
        return [str(row["content"] or "") for row in await cursor.fetchall()]

    async def remove_blacklist(self, user_id: int) -> bool:
        """解除拉黑；返回是否真的删掉了一条记录。"""
        conn = self._require_conn()
        async with self._lock:
            cursor = await conn.execute("DELETE FROM blacklist WHERE user_id = ?", (int(user_id),))
            await conn.commit()
            return bool(cursor.rowcount)

    async def get_blacklist_entry(self, user_id: int) -> dict[str, Any] | None:
        """取某个用户的封禁记录（用于回复「什么时候自动恢复」）。"""
        conn = self._require_conn()
        cursor = await conn.execute(
            "SELECT * FROM blacklist WHERE user_id = ? LIMIT 1", (int(user_id),)
        )
        row = await cursor.fetchone()
        return dict(row) if row is not None else None

    async def list_blacklist(self) -> list[dict[str, Any]]:
        """返回永久拉黑或限期封禁记录，供管理员命令查询。"""
        conn = self._require_conn()
        cursor = await conn.execute("SELECT * FROM blacklist ORDER BY created_at DESC")
        return [dict(row) for row in await cursor.fetchall()]

    # ---------------- 换服务器时的旧投稿清理 ----------------

    async def list_published_before(self, cutoff_utc: str | None) -> list[dict[str, Any]]:
        """列出「已发布、且发布时刻早于 cutoff_utc」的投稿（按 id 升序）。

        时间比较放在 Python 里做，不写进 SQL 的字符串比较：老库的 created_at
        可能是空格分隔或不带时区的历史格式（见 `_parse_db_time`），字符串比较会
        静默漏记录。cutoff_utc 传 None 表示不设上限（全部已发布记录）。
        """
        conn = self._require_conn()
        cursor = await conn.execute(
            "SELECT * FROM submissions"
            " WHERE status = 'published' AND qzone_tid IS NOT NULL AND qzone_tid <> ''"
            " ORDER BY id ASC",
        )
        rows = [dict(row) for row in await cursor.fetchall()]
        return _published_before(rows, cutoff_utc)

    async def submission_stats(self) -> dict[str, Any]:
        """投稿库概况：清理旧投稿前先确认「库里到底有没有可删的东西」。

        返回 total（全部记录）、by_status（各状态条数）、deletable（已发布且有 tid，
        也就是空间上真能删掉的那些）、first/last（最早/最晚的 created_at 原文）。
        """
        conn = self._require_conn()
        cursor = await conn.execute(
            "SELECT status, COUNT(*) AS total FROM submissions GROUP BY status"
        )
        by_status = {
            str(row["status"]): int(row["total"]) for row in await cursor.fetchall()
        }
        cursor = await conn.execute("SELECT COUNT(*) AS n FROM submissions")
        total = int((await cursor.fetchone())["n"])
        cursor = await conn.execute(
            "SELECT COUNT(*) AS n FROM submissions"
            " WHERE status = 'published' AND qzone_tid IS NOT NULL AND qzone_tid <> ''"
        )
        deletable = int((await cursor.fetchone())["n"])
        cursor = await conn.execute(
            "SELECT MIN(created_at) AS first, MAX(created_at) AS last FROM submissions"
        )
        span = await cursor.fetchone() or {}
        return {
            "total": total,
            "by_status": by_status,
            "deletable": deletable,
            "first": str(span["first"] or "") if "first" in span.keys() else "",
            "last": str(span["last"] or "") if "last" in span.keys() else "",
        }


# --------------------------------------------------------------------------------------
# 六、内容审核（DeepSeek）
# --------------------------------------------------------------------------------------


@dataclass
class ModerationResult:
    approved: bool
    risk_level: str
    reason: str
    # 触犯的类别（privacy / conflict / blood / violence / horror / porn / illegal / none）。
    # 只用于日志与统计，判定本身仍然只看 approved —— 类别缺失一律按 "other" 处理，
    # 绝不因为模型少给一个字段就放行或拒绝。
    category: str = "none"


class ModerationUnavailable(RuntimeError):
    """审核服务不可用（未配置 / 网络失败 / 返回异常）。"""


_MODERATION_SYSTEM_PROMPT = (
    "你是 QQ 校园墙投稿的审核员。你会收到投稿的文字，可能还会随附投稿中的图片。"
    "**文字与图片必须合起来判断**：不能只看文字、也不能只看图片 —— 图片里的内容与文字里的说明都是判定依据（例如二维码必须结合文字里写的用途才能判断）。"
    "校园墙是**公开**的，读者包括同学与老师。判定看的是**实质内容与主张**，不是有没有出现某个词。"
    "下面这三大类内容一律拒绝（编号与《使用协议》四、会被拒绝投稿的内容一一对应）："
    "【第一类：不符合社会主义意识形态、有违社会主义核心价值观】"
    "① 反对中国共产党、反对马克思主义、反对共产主义、反对社会主义制度的内容；"
    "② 宣扬法西斯主义、极端民族主义等极端思想，或宣扬邪教、封建迷信的内容（求签算卦、看相改运、作法驱邪、传教拉人入教、宣扬世界末日等）；"
    "③ 宣扬女权主义、男权主义等有违妇女解放立场的言论，或整体贬损、仇视某一性别的立场性言论；"
    "④ 其他不符合社会主义意识形态、有违社会主义核心价值观的内容。"
    "这一类看的是**主张与立场**：不要因为投稿提到政治、时事、历史词汇就拒绝，中性描述与正常讨论不属这一类。"
    "【第二类：可能违反我国法律法规】"
    "⑤ 涉嫌违法犯罪的内容：危害国家安全、分裂国家、破坏民族团结、损害国家荣誉和利益；散布谣言或未经证实的虚假信息，扰乱社会秩序、破坏社会稳定；散布淫秽、色情、赌博、暴力、凶杀、恐怖内容或教唆犯罪。具体表现："
    "血腥（伤口、流血、尸骸、解剖、虐待动物等真实血腥画面）；"
    "暴力（打架斗殴、持械、伤害或威胁伤害他人、自伤自残）；"
    "恐怖（鬼怪惊吓、恐怖血腥的合成画面等强烈令人不适的内容）；"
    "色情（性行为、裸露、性器官、色情描写、露骨性暗示，或涉及未成年人的性化内容）；"
    "违法交易（毒品、枪支、管制刀具、赌博、诈骗、刷单、代考代写、盗版盗卖）。"
    "⑥ 侵犯他人合法权益的内容：指名道姓地公布他人的**真实姓名（包括其父母、家人的姓名）**、身份证号、学号、住址、手机号、工作单位，或公开他人聊天记录、照片、私信来挂人；"
    "拿他人的家人（父母、亲属）说事，拿父母姓名或职业嘲讽、诅咒，同样属于本条，一律拒绝；"
    "未经同意公开他人照片用于嘲讽、羞辱（侵犯肖像权）；传播他人未公开的个人信息（侵犯个人信息权益）；上传或分享盗版课程、付费资料、他人的原创作品（侵犯知识产权）；"
    "注意：只公布**自己的**班级、院系、专业、年级、姓名（例如交友、找同班同学、寻物）不算泄露隐私，必须放行。"
    "⑦ 侮辱、诽谤、欺凌他人的内容：辱骂、起侮辱性外号、人身攻击、恶意孤立、网络围殴、编造事实抹黑他人、恐吓威胁；"
    "⑧ 其他可能违法我国法律法规的内容。"
    "【第三类：有违社会公序良俗、不利于同学间友谊】"
    "⑨ 低俗、媚俗、庸俗内容：荤段子、露骨擦边、低俗玩梗、宣扬拜金炫富，以及违背社会公德、家庭美德、善良风俗的言论与行为；"
    "⑩ 挑动性别对立、班级对立、年级对立等矛盾，或使用引战词汇恶意挑起同学间矛盾：点名对骂、约架、拉人站队、把小摩擦激化升级成人身攻击或群体对立、曝光他人隐私以报复 —— 这类内容即使文字不脏也要拒绝；"
    "⑪ 无事实依据的纯情绪宣泄、恶意带节奏、散播消极负能量、传播未经证实的校园八卦，以及破坏同学间团结的内容；"
    "⑫ 其他有违公共秩序、善良风俗，或不利于维护同学间友好团结、构建和谐校园环境的内容。"
    "【⑬ 二维码（本站运营规则，不属于上面三类，但同样必须执行）】"
    "图片主体是二维码、条形码、群码、收款码时，必须结合投稿文字判断用途；**只有文字里明确说明了合规用途才可放行**（例如：校园活动报名、社团/班级招新、失物招领、学习资料、学校或学院官方通知、志愿服务招募）。"
    "以下情况一律拒绝：没有说明用途；只写“扫码”“扫码加我”却不说明做什么；商业推广、加群领福利/红包、兼职刷单、代购、贷款、赌博、诈骗、收款要钱、引流到私人号。"
    "判定以**图片主体**是否为二维码为准：若二维码只是海报角落的小图标、或聊天截图/表格里的一小块，且文字已说明合规用途，则按通过处理。"
    "**换说法重发同样算违规**：谐音、拼音缩写、拆字、错别字、表情符号代称、或是把同一件事换个叙述角度重发，只要实质内容仍属上面任何一条，就必须拒绝。"
    "下面这些**不是**拒绝理由，必须放行：针对具体事物的日常吐槽（作业多、食堂难吃、天气、考试难）；"
    "带脏话的情绪表达（脏话本身不是拒绝理由，但如果用来辱骂、攻击具体的人，按第 ⑦ 条拒绝）；正常观点争论、搞笑段子与梗图、非血腥的冲突描述、正常的穿搭自拍、求交友与联系方式、校园生活与学习相关的一切内容；"
    "对性别、时事、历史等话题的中性描述与正常讨论（只有构成第 ③ 条的立场性宣扬、或第 ⑩ 条的挑动对立，才拒绝）。"
    "第 ⑪ 条的边界要拿准：吐槽要有具体由头、说的是自己的感受；**没有事实依据、专门针对某人某事带节奏、煽动情绪的刷屏式负能量**才拒绝，不要因为“不够正能量”“情绪低落”就拒绝。"
    "不要因为“可能引起争议”“像是广告”就拒绝（二维码按第 ⑬ 条单独判断）。"
    "**除上面三大类（含第 ⑬ 条）之外**的内容，拿不准时按通过处理；但只要命中上面任何一条，就必须拒绝，不要用“可能引起争议”这种模糊理由放行隐私泄露与引战内容。"
    "随附图片时必须逐张查看，只按上述标准判定；图片是表情包、正常聊天截图、文字图片等普通内容时判为通过（二维码按第 ⑬ 条判断）。"
    "即使投稿没有任何文字，只要图片不触犯上面三类、且不是第 ⑬ 条那种需要说明用途的二维码，就必须判为通过；禁止以“没有文字内容”“无法审核”之类理由拒绝，这类理由一律视为误判。"
    "仅输出 JSON，格式：{\"approved\": true/false, \"risk_level\": \"low|medium|high\", \"category\": \"ideology|illegal|blood|violence|horror|porn|illegal_trade|privacy|defamation|vulgar|conflict|negativity|qr|none\", \"reason\": \"简要中文原因\"}。"
    "通过时 reason 写“内容合规”、category 写 none、risk_level 写 low；不通过时 reason 必须写明触犯的是哪一条与具体原因（例如“泄露他人隐私：公布了同学父母的姓名”“挑动同学对立：点名对骂”），category 填对应的那一类。"
)

# 说明：跨投稿（整批）审核随「定时统一放送」一起删除 —— 它本来就是「同一批放送的投稿
# 放在一起看」才有意义；现在每条投稿各自在空闲 1 分钟后独立发布，不再有「一批」。

# 视觉接口的已核实限制（DeepSeek 图像理解文档）：
#   支持格式 JPEG / PNG / GIF / WebP（按文件内容判断）、单图 base64 上限 32 MiB、请求体上限 48 MiB。
_SUPPORTED_IMAGE_MIME_PREFIXES = (
    (b"\x89PNG\r\n\x1a\n", "image/png"),
    (b"\xff\xd8\xff", "image/jpeg"),
    (b"GIF87a", "image/gif"),
    (b"GIF89a", "image/gif"),
)
_MAX_INLINE_IMAGE_BYTES = 32 * 1024 * 1024
_MAX_INLINE_TOTAL_BYTES = 24 * 1024 * 1024  # 请求体上限 48 MiB，内联图片留足余量


def _sniff_image_mime(data: bytes) -> str | None:
    """按文件内容判断图片类型；不在支持范围内返回 None。"""
    for prefix, mime in _SUPPORTED_IMAGE_MIME_PREFIXES:
        if data.startswith(prefix):
            return mime
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "image/webp"
    return None


def moderation_image_budget(settings: Settings) -> int:
    """单条投稿最多可能有多少张图需要送审：照片额度 + 表情额度。

    为什么必须相加大于等于「收稿允许的总数」：只要出现「收下了却送不了审」的图，
    它就会进公开截图（DEC-9），整条投稿只能被拒绝发布。两项里任一为 0/负数
    （= 不限制）时返回 0，表示不按张数限制，交给请求体积与单条字节预算兜底。
    """
    photos = settings.moderation_max_images
    stickers = settings.max_stickers_per_submission
    if photos <= 0 or stickers <= 0:
        return 0
    return photos + stickers


def build_image_blocks(
    images: Iterable[bytes], settings: Settings, *, user_id: int = 0
) -> list[dict[str, Any]]:
    """把图片字节转成视觉审核用的 image_url 内容块（base64 内联）。

    用 base64 而不是原始 URL：NapCat 给出的图片地址常是内网/本机地址
    （如 http://127.0.0.1:3000/...），DeepSeek 侧无法访问；而图片字节在截图阶段
    就已经下载到本地，直接内联最稳妥。

    只返回能送审的部分；**调用方若在意「有没有漏审」，请用
    build_image_blocks_with_skips()** —— 发布前必须确认没有图片被跳过（DEC-9）。
    """
    return build_image_blocks_with_skips(images, settings, user_id=user_id)[0]


def build_image_blocks_with_skips(
    images: Iterable[bytes], settings: Settings, *, user_id: int = 0, limit: int | None = None
) -> tuple[list[dict[str, Any]], list[str]]:
    """同上，但把「哪些图没能送审、为什么」一并返回。

    返回 (内容块, 跳过原因列表)。原因列表非空 = 有图片没被模型看过 ——
    这些图片一旦画进截图或作为原图发布就是审核空洞，所以发布流程会据此终止发布。

    limit 默认取 `moderation_image_budget()`（照片额度 + 表情额度）。
    """
    blocks: list[dict[str, Any]] = []
    skipped: list[str] = []
    total_bytes = 0
    count_limit = moderation_image_budget(settings) if limit is None else limit
    for data in images:
        if count_limit > 0 and len(blocks) >= count_limit:
            skipped.append(f"超过单次送审上限 {count_limit} 张")
            break
        if len(data) > _MAX_INLINE_IMAGE_BYTES:
            skipped.append("单张图片超过 32 MiB")
            continue
        mime = _sniff_image_mime(data)
        if mime is None:
            skipped.append("图片格式不在审核支持范围（JPEG/PNG/GIF/WebP）")
            continue
        if total_bytes + len(data) > _MAX_INLINE_TOTAL_BYTES:
            skipped.append("送审图片总体积接近请求体上限")
            break
        total_bytes += len(data)
        blocks.append(
            {
                "type": "image_url",
                "image_url": {
                    "url": f"data:{mime};base64,{base64.b64encode(data).decode('ascii')}",
                    "detail": settings.moderation_image_detail,
                },
            }
        )
    if skipped:
        logger.warning("有图片未能送审：user_id=%s 送审=%d 张 原因=%s", user_id, len(blocks), "；".join(skipped))
    return blocks, skipped


_THINKING_EFFORT_BY_MODE = {
    # 文档中的强度映射：请求 minimal 实际按 low（最低档）执行
    "low": "minimal",
    "high": "high",
    "max": "max",
}


def build_thinking_params(settings: Settings) -> dict[str, Any]:
    """生成审核请求的思考控制参数（放进 extra_body，两条路径共用）。

    放进 extra_body 而不是当具名参数，是为了不依赖 SDK 版本是否已声明这些字段：
    extra_body 的内容会被原样合并进请求体，与官方 curl 示例一致。

    文档口径：思考模式默认开启、默认强度 high，所以「什么都不传」= 最贵的一档；
    reasoning_effort 请求 minimal 时实际映射为 low（最低强度）。
    """
    mode = (settings.moderation_thinking or "").strip().lower()
    if mode in {"", "default"}:
        return {}
    if mode == "disabled":
        return {"thinking": {"type": "disabled"}}
    if mode in _THINKING_EFFORT_BY_MODE:
        return {"reasoning_effort": _THINKING_EFFORT_BY_MODE[mode]}
    logger.warning(
        "未知的 MODERATION_THINKING=%s，按 default（不下发思考参数）处理", settings.moderation_thinking
    )
    return {}


async def call_deepseek_moderation(
    text: str,
    settings: Settings,
    *,
    image_blocks: Sequence[dict[str, Any]] = (),
    user_id: int = 0,
) -> ModerationResult:
    """调用 DeepSeek 审核投稿：有图片走视觉模型，没图片走文本模型。

    失败语义（失败模式分档）：API 异常 → 抛 ModerationUnavailable，由调用方「拒绝发布 + 通知用户」；
    返回体不是合法 JSON → 按「不通过」处理（fail-closed），绝不放行未审核内容。
    """
    if not settings.deepseek_api_key:
        raise ModerationUnavailable("未配置 DEEPSEEK_API_KEY")

    if image_blocks:
        model = settings.deepseek_vision_model
        user_content: Any = [
            {
                "type": "text",
                "text": f"投稿内容如下：\n---\n{text}\n---\n（另随附 {len(image_blocks)} 张图片，请一并审核）",
            }
        ]
        user_content.extend(image_blocks)
        logger.info(
            "审核使用视觉模型：model=%s 图片=%d 张 detail=%s 思考=%s",
            model,
            len(image_blocks),
            settings.moderation_image_detail,
            settings.moderation_thinking,
        )
    else:
        model = settings.deepseek_model
        user_content = f"投稿内容如下：\n---\n{text}\n---"

    extra_body = build_thinking_params(settings)

    client = AsyncOpenAI(
        api_key=settings.deepseek_api_key,
        base_url=settings.deepseek_base_url,
        timeout=settings.moderation_timeout,
        max_retries=2,  # 网络重试上限：临时超时/5xx 最多 2 次
    )
    try:
        response = await client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": _MODERATION_SYSTEM_PROMPT},
                {"role": "user", "content": user_content},
            ],
            response_format={"type": "json_object"},
            # 思考模式下该参数会被忽略（忽略而非报错）；只有 disabled 模式下才真正生效
            temperature=0.0,
            **({"extra_body": extra_body} if extra_body else {}),
        )
    except Exception as exc:  # openai SDK 异常族较多，这里统一转换为可判定的领域异常
        raise ModerationUnavailable(f"审核接口调用失败：{exc}") from exc
    finally:
        with contextlib.suppress(Exception):
            await client.close()

    try:
        raw = (response.choices[0].message.content or "").strip()
    except (AttributeError, IndexError, KeyError, TypeError):
        logger.exception("审核返回结构异常，取不到 content")
        return ModerationResult(
            approved=False,
            risk_level="unknown",
            reason="审核服务返回结构异常，为安全起见本次未发布",
        )

    _INVALID_JSON = ModerationResult(
        approved=False,
        risk_level="unknown",
        reason="审核服务返回格式异常，为安全起见本次未发布",
    )
    _INVALID_TYPE = ModerationResult(
        approved=False,
        risk_level="unknown",
        reason="审核服务返回的判定字段非法，为安全起见本次未发布",
    )

    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, TypeError):
        logger.error("审核返回不是合法 JSON：%s", raw[:200])
        return _INVALID_JSON

    if not isinstance(payload, dict):
        logger.error("审核返回不是 JSON 对象：%s", raw[:200])
        return _INVALID_JSON

    # 只接受 JSON 布尔值：字符串 "false" 经 bool() 会变成 True，那是最危险的 fail-open。
    verdict = payload.get("approved")
    if verdict is not True and verdict is not False:
        logger.error("审核判定字段类型非法（approved=%r），按不通过处理：%s", verdict, raw[:200])
        return _INVALID_TYPE

    approved = verdict
    risk_level = str(payload.get("risk_level") or ("low" if approved else "high"))
    reason = str(payload.get("reason") or ("内容合规" if approved else "未通过审核"))
    category = str(payload.get("category") or ("none" if approved else "other")).strip().lower()
    return ModerationResult(
        approved=approved, risk_level=risk_level, reason=reason, category=category
    )


# 说明：`call_batch_moderation()`（跨投稿整批审核）随「定时统一放送」一起删除。


# --------------------------------------------------------------------------------------
# 七、空间发布（qzone-sdk）
# --------------------------------------------------------------------------------------


# QQ 空间图片上传 / 发布接口地址（与 qzone-sdk constants.URLS 同名同值）
_QZONE_UPLOAD_URL = str(
    _QZONE_URLS.get("upload_image") or "https://up.qzone.qq.com/cgi-bin/upload/cgi_upload_image"
)
_QZONE_PUBLISH_URL = str(
    _QZONE_URLS.get("publish")
    or "https://user.qzone.qq.com/proxy/domain/taotao.qzone.qq.com/cgi-bin/emotion_cgi_publish_v6"
)
_QZONE_DELETE_URL = str(
    _QZONE_URLS.get("delete")
    or "https://user.qzone.qq.com/proxy/domain/taotao.qzone.qq.com/cgi-bin/emotion_cgi_delete_v6"
)


class _RichPublishUnavailable(RuntimeError):
    """qzone-sdk 没有暴露自建发布所需的内部接口，只能回退到 SDK 自带发布。"""


class QZonePublisher:
    """基于 qzone-sdk 的说说发布器。

    认证方式（配置项 QZONE_AUTH_MODE）：
      - napcat：NapCatAuthProvider，复用 NapCat 已登录的 QQ 登录态；
      - cookie：ManualCookieProvider，手动提供 Cookie（调试 / 一次性使用）。

    带图发布**不调用** SDK 的 publish(image_paths=...)，只借用它的认证（_auth）与
    HTTP 传输（_post / _headers），richval 由本模块自己组装 —— 原因见 _build_richval。
    """

    def __init__(self, settings: Settings) -> None:
        self._settings = settings
        self._client: Any = None
        self._lock = asyncio.Lock()

    async def _ensure_client(self) -> Any:
        """惰性初始化空间客户端，避免应用导入阶段发起认证。"""
        if self._client is not None:
            return self._client
        async with self._lock:
            if self._client is not None:
                return self._client
            if QZoneClient is None:
                raise RuntimeError("未安装 qzone-sdk，请执行：pip install \"qzone-sdk[napcat]\"")
            mode = self._settings.qzone_auth_mode
            if mode == "cookie":
                if not self._settings.qzone_cookie or not self._settings.qzone_uin:
                    raise RuntimeError("QZONE_AUTH_MODE=cookie 时必须同时配置 QZONE_COOKIE 与 QZONE_UIN")
                provider = ManualCookieProvider(
                    cookies=self._settings.qzone_cookie, uin=self._settings.qzone_uin
                )
            else:
                provider = NapCatAuthProvider(ws_url=self._settings.qzone_ws_url)
            self._client = self._build_client(provider)
            return self._client

    def _build_client(self, provider: Any) -> Any:
        """构造 QZoneClient，尽可能带上请求超时上限。

        qzone-sdk 文档给出 `QZoneClient(QZoneConfig(auth_provider=..., timeout=30))` 的写法，
        但本机无法安装该库、无法实测其构造签名 —— 因此签名不匹配时回退到最简构造，
        不让「加超时」反而变成发布失败的新原因。
        """
        if QZoneConfig is not None:
            try:
                return QZoneClient(
                    QZoneConfig(auth_provider=provider, timeout=self._settings.qzone_timeout)
                )
            except TypeError:
                logger.warning(
                    "当前 qzone-sdk 不支持 QZoneConfig(auth_provider=..., timeout=...)，回退默认构造"
                )
        return QZoneClient(auth_provider=provider)

    @staticmethod
    def _build_richval(
        albumid: str, lloc: str, sloc: str, image_type: str, height: str, width: str
    ) -> str:
        """按 QQ 空间要求的字段序拼一张图的 richval 片段。

        字段序（qzone-toolkit、astrbot_plugin_private_companion 两个可用实现一致）：

            ,albumid,lloc,sloc,type,height,width,,height,width

        qzone-sdk 1.0.1 带图发布时发的是 `,{lloc},{lloc},{lloc},,0,0,,0,0`
        —— albumid 位填 lloc、sloc 位填 lloc、type 位留空、宽高全 0，pic_bo 还用
        制表符拼接；QQ 空间据此拼不出有效图片链接，直接拒收并返回
        `code=-10061 您输入的链接不是有效链接`。多张图之间用制表符连接（同两个实现）。
        """
        return ",".join(["", albumid, lloc, sloc, image_type, height, width, "", height, width])

    async def _sdk_transport(self, client: Any) -> tuple[Any, Any, dict[str, str]]:
        """取出 SDK 的认证信息与 HTTP 传输函数，顺带构造请求头。"""
        auth_method = getattr(client, "_auth", None)
        post = getattr(client, "_post", None)
        headers_method = getattr(client, "_headers", None)
        if not callable(auth_method) or not callable(post) or not callable(headers_method):
            raise _RichPublishUnavailable("当前 qzone-sdk 未提供 _auth/_post/_headers 内部接口")
        auth = await auth_method()
        headers = headers_method(auth, post=True)
        if not isinstance(headers, dict):  # 防御：SDK 改签名时不要带着空头去发请求
            raise _RichPublishUnavailable("qzone-sdk._headers 未返回请求头字典")
        return auth, post, headers

    @staticmethod
    def _read_image_for_upload(path: str) -> tuple[bytes, int, int]:
        """读图并做发布前的最后一道校验，返回 (字节, 宽, 高)。

        存盘时已经统一成 JPEG/PNG/GIF，这里再跑一次是幂等的兜底
        （截图等其它来源的图片也会经过这条路径），确保不会把空间收不了的东西传上去。
        """
        prepared = _prepare_image_for_publish(Path(path).read_bytes(), path)
        if prepared is None:
            raise RuntimeError(f"图片无法上传（格式不支持或内容损坏）：{Path(path).name}")
        payload, _suffix = prepared
        width = height = 0
        try:
            with Image.open(io.BytesIO(payload)) as probe:
                width, height = probe.size
        except Exception:  # 宽高只是 richval 的附加字段，读不到不该阻断发布
            logger.warning("读取图片尺寸失败：%s", Path(path).name)
        if width and height and min(width, height) < 16:
            raise RuntimeError(f"图片尺寸过小（{width}x{height}），QQ 空间不收：{Path(path).name}")
        return payload, width, height

    def _parse_upload_response(
        self, raw: Any, path: str, width: int, height: int
    ) -> dict[str, Any]:
        """校验上传返回并组装 richval 片段；字段不全时抛错（宁可不发，也不发残缺链接）。"""
        name = Path(path).name
        if not isinstance(raw, dict):
            raise RuntimeError(f"图片上传响应无法解析：{str(raw)[:200]}")
        data = raw.get("data")
        if not isinstance(data, dict):
            raise RuntimeError(f"图片上传响应缺少 data 字段：{str(raw)[:200]}")
        lloc = str(data.get("lloc") or "").strip()
        if not lloc:
            raise RuntimeError(f"图片上传未返回 lloc：{str(data)[:200]}")
        albumid = str(data.get("albumid") or "").strip()
        if not albumid:
            raise RuntimeError(f"图片上传未返回 albumid（richval 需要）：{str(data)[:200]}")
        sloc = str(data.get("sloc") or "").strip()
        if not sloc:
            logger.warning("图片上传未返回 sloc，richval 该位回退用 lloc：%s", name)
            sloc = lloc
        image_type = str(data.get("type") or "").strip() or "1"
        img_height = str(data.get("height") or height or "0").strip() or "0"
        img_width = str(data.get("width") or width or "0").strip() or "0"
        pic_bo = str(data.get("bo") or "").strip()
        if not pic_bo:  # 部分返回把 bo 藏在 url 的查询串里
            match = re.search(r"(?:^|[?&])bo=([^&\s]+)", str(data.get("url") or ""))
            pic_bo = match.group(1) if match else ""
        if not pic_bo:
            raise RuntimeError(f"图片上传未返回 pic_bo：{str(data)[:200]}")
        return {
            "name": name,
            "richval": self._build_richval(albumid, lloc, sloc, image_type, img_height, img_width),
            "pic_bo": pic_bo,
        }

    async def _upload_image(
        self,
        client: Any,
        auth: Any,
        headers: dict[str, str],
        referer: str,
        path: str,
        *,
        retry: bool = True,
    ) -> dict[str, Any]:
        """上传单张图片，返回 {name, richval, pic_bo}；失败抛 RuntimeError。"""
        payload, width, height = await asyncio.to_thread(self._read_image_for_upload, path)
        form = {
            "filename": Path(path).name or "image.jpg",
            "uin": auth.uin,
            "skey": getattr(auth, "skey", ""),
            "zzpaneluin": auth.uin,
            "zzpanelkey": "",
            "p_uin": auth.uin,
            "p_skey": getattr(auth, "p_skey", ""),
            "qzonetoken": "",
            "uploadtype": "1",
            "albumtype": "7",
            "exttype": "0",
            "refer": "shuoshuo",
            "output_type": "jsonhtml",
            "charset": "utf-8",
            "output_charset": "utf-8",
            "upload_hd": "1",
            "hd_width": "2048",
            "hd_height": "10000",
            "hd_quality": "96",
            "backUrls": "http://upbak.photo.qzone.qq.com/cgi-bin/upload/cgi_upload_image",
            "url": f"{_QZONE_UPLOAD_URL}?g_tk={auth.g_tk}",
            "base64": "1",
            "jsonhtml_callback": "callback",
            "picfile": base64.b64encode(payload).decode("ascii"),
            "qzreferrer": referer,
        }
        # SDK 的 _post 是同步阻塞实现（urllib），必须放线程里跑，否则会卡住事件循环
        raw = await asyncio.to_thread(
            client._post, f"{_QZONE_UPLOAD_URL}?g_tk={auth.g_tk}", form, headers
        )
        try:
            return self._parse_upload_response(raw, path, width, height)
        except RuntimeError:
            if not retry:
                raise
            logger.warning("图片上传未拿到有效结果，重试一次：%s", Path(path).name)
            return await self._upload_image(
                client, auth, headers, referer, path, retry=False
            )

    async def _publish_post(
        self, client: Any, content: str, paths: Sequence[str]
    ) -> dict[str, Any]:
        """上传图片（如有）并发表说说，返回含 success / tid 的结果。"""
        auth, post, headers = await self._sdk_transport(client)
        referer = f"https://user.qzone.qq.com/{auth.uin}"
        uploaded: list[dict[str, Any]] = []
        for path in paths:
            uploaded.append(await self._upload_image(client, auth, headers, referer, path))
        if uploaded:
            logger.info(
                "空间图片上传完成 %d 张：%s",
                len(uploaded),
                ", ".join(item["name"] for item in uploaded),
            )

        form = {
            "syn_tweet_verson": "1",
            "paramstr": "1",
            "pic_template": "",
            "richtype": "",
            "richval": "",
            "special_url": "",
            "subrichtype": "",
            "pic_bo": "",
            "who": "1",
            "con": content,
            "feedversion": "1",
            "ver": "1",
            "ugc_right": str(self._settings.qzone_visible),
            "to_sign": "0",
            "hostuin": auth.uin,
            "code_version": "1",
            "issyncweibo": "0",
            "format": "json",
            "qzreferrer": referer,
        }
        if uploaded:
            form["richtype"] = "1"
            form["subrichtype"] = "1"
            form["richval"] = "\t".join(item["richval"] for item in uploaded)
            form["pic_bo"] = ",".join(item["pic_bo"] for item in uploaded)

        raw = await asyncio.to_thread(
            post, f"{_QZONE_PUBLISH_URL}?g_tk={auth.g_tk}", form, headers
        )
        if not isinstance(raw, dict):
            raise RuntimeError(f"空间发布响应无法解析：{str(raw)[:200]}")
        code = raw.get("code")
        if code is None:
            code = raw.get("ret")
        tid = str(raw.get("tid") or raw.get("t1_tid") or "")
        if code is None:
            # 没有 code 时只有拿到 tid 才算成功：tid 是说说已创建的凭据。
            # 两者都没有 → 响应异常 → 按失败处理，绝不谎报「已发布」。
            if not tid:
                raise RuntimeError(
                    f"空间发布响应既没有 code 也没有 tid，无法确认是否发出：{str(raw)[:200]}"
                )
        elif str(code) not in {"0", "0.0"}:
            message = str(raw.get("message") or raw.get("msg") or "").strip()
            raise RuntimeError(f"空间发布被拒：code={code} message={message or '（无返回信息）'}")
        return {
            "success": True,
            "tid": tid,
            "curkey": str(raw.get("curkey") or raw.get("t1_curkey") or ""),
            "images": len(uploaded),
            "code": code,
        }

    async def publish(self, content: str, image_paths: Sequence[str]) -> dict[str, Any]:
        """发布说说；返回含 success / tid 的结果，失败抛 RuntimeError。

        正常路径由本模块自己上传图片并组装 richval（见 _build_richval）；
        只有 SDK 内部接口不可用时才回退到 SDK 自带发布，并且会留下错误日志。
        """
        client = await self._ensure_client()
        paths = [str(path) for path in image_paths]
        try:
            result = await self._publish_post(client, content, paths)
        except _RichPublishUnavailable as exc:
            logger.error(
                "回退 qzone-sdk 自带发布（richval 由 SDK 组装，带图时可能被空间拒收）：%s", exc
            )
            result = await client.publish(
                content, visible=self._settings.qzone_visible, image_paths=paths
            )
            if not isinstance(result, dict) or not result.get("success"):
                raise RuntimeError(f"空间发布失败：{result}") from exc
            return result
        logger.info("空间发布成功：tid=%s 图片=%d", result.get("tid"), result.get("images", 0))
        return result

    async def delete_post(self, tid: str, curkey: str = "") -> dict[str, Any]:
        """删除一条已发布的说说。

        参数照抄 qzone-sdk 1.0.1 的 `delete()`（同一个 CGI 与同一套字段），
        只借用它的认证与 HTTP 传输；`curkey` 留空时用 `tid` 兜底 ——
        新发布的说说两者相同，SDK 自己也是这么兜底的（v1.0.1 的修复点）。

        判定从严：响应里必须明确给出 `code = 0` 才算删成功 ——
        删说说属于"做错了会留下痕迹"的操作，不能拿「响应看起来没报错」当成功。
        """
        client = await self._ensure_client()
        auth, post, headers = await self._sdk_transport(client)
        target = str(tid).strip()
        if not target:
            raise RuntimeError("删除说说失败：tid 为空")
        form = {
            "uin": auth.uin,
            "topicId": target,
            "feedsType": "0",
            "feedsFlag": "0",
            "feedsKey": str(curkey).strip() or target,
            "feedsAppid": "311",
            "feedsTime": "0",
            "fupdate": "1",
            "ref": "feeds",
            "qzreferrer": f"https://user.qzone.qq.com/{auth.uin}",
        }
        raw = await asyncio.to_thread(
            post, f"{_QZONE_DELETE_URL}?g_tk={auth.g_tk}", form, headers
        )
        if not isinstance(raw, dict):
            raise RuntimeError(f"删除说说响应无法解析：{str(raw)[:200]}")
        code = raw.get("code")
        if code is None:
            code = raw.get("ret")
        if str(code) not in {"0", "0.0"}:
            message = str(raw.get("message") or raw.get("msg") or "").strip()
            raise RuntimeError(
                f"删除说说失败：code={code if code is not None else '（响应里没有 code）'}"
                f" message={message or '（无返回信息）'}"
            )
        return {"success": True, "code": code, "tid": target}


# --------------------------------------------------------------------------------------
# 八、WebSocket 连接与 OneBot 动作
# --------------------------------------------------------------------------------------


class OneBotConnection:
    """与单个 NapCat 反向 WS 连接绑定的动作发送器。"""

    def __init__(self, websocket: WebSocket) -> None:
        self.websocket = websocket
        self._pending: dict[str, asyncio.Future] = {}

    async def send_action(self, action: str, params: dict[str, Any], *, echo: str | None = None) -> None:
        """发送 OneBot 动作（不等待响应）。"""
        payload: dict[str, Any] = {"action": action, "params": params}
        if echo:
            payload["echo"] = echo
        await self.websocket.send_json(payload)

    async def call_api(
        self, action: str, params: dict[str, Any], *, timeout: float
    ) -> dict[str, Any]:
        """发送动作并等待 echo 匹配的响应；超时抛 asyncio.TimeoutError。"""
        echo = uuid.uuid4().hex
        loop = asyncio.get_running_loop()
        future: asyncio.Future = loop.create_future()
        self._pending[echo] = future
        try:
            await self.send_action(action, params, echo=echo)
            return await asyncio.wait_for(future, timeout=timeout)
        finally:
            self._pending.pop(echo, None)

    def resolve_echo(self, payload: dict[str, Any]) -> bool:
        """把带 echo 的响应派发给等待者；命中返回 True（该报文不再当事件处理）。"""
        echo = payload.get("echo")
        if not isinstance(echo, str):
            return False
        future = self._pending.get(echo)
        if future is None:
            return False
        if not future.done():
            future.set_result(payload)
        return True

    def fail_pending(self, exc: BaseException) -> None:
        """连接断开时结束所有等待者，避免调用方永久挂起。"""
        for future in list(self._pending.values()):
            if not future.done():
                future.set_exception(exc)
        self._pending.clear()


class ConnectionManager:
    """维护全部反向 WS 连接；无连接时动作发送会明确失败而不是静默丢弃。"""

    def __init__(self) -> None:
        self._connections: list[OneBotConnection] = []

    def register(self, websocket: WebSocket) -> OneBotConnection:
        """登记一条连接，供 OneBot 请求与回执按连接路由。"""
        connection = OneBotConnection(websocket)
        self._connections.append(connection)
        logger.info("NapCat 反向 WS 已连接，当前连接数：%d", len(self._connections))
        return connection

    def unregister(self, connection: OneBotConnection) -> None:
        """断线时移除连接并释放等待中的回执。"""
        if connection in self._connections:
            self._connections.remove(connection)
        connection.fail_pending(ConnectionError("WebSocket 连接已断开"))
        logger.info("NapCat 反向 WS 已断开，当前连接数：%d", len(self._connections))

    def latest(self) -> OneBotConnection | None:
        """返回最近建立的连接：定时器回调时用它回复用户。"""
        return self._connections[-1] if self._connections else None

    @property
    def count(self) -> int:
        """当前活跃的反向 WS 连接数（健康检查用）。"""
        return len(self._connections)

    async def send_private_msg(self, user_id: int, message: str) -> bool:
        """通过 WebSocket 发送 OneBot v11 的 send_private_msg 动作。"""
        connection = self.latest()
        if connection is None:
            logger.error("没有可用的 NapCat 连接，消息未送达 user_id=%s", user_id)
            return False
        try:
            await connection.send_action(
                "send_private_msg", {"user_id": int(user_id), "message": message}
            )
            return True
        except Exception:
            logger.exception("发送私聊消息失败 user_id=%s", user_id)
            return False

    async def send_private_file(
        self,
        user_id: int,
        path: str | Path,
        *,
        name: str = "",
        timeout: float = 60.0,
    ) -> tuple[bool, str]:
        """用 OneBot v11 的 `upload_private_file` 把一个文件发到私聊。

        为什么要把「文件」单独做一条动作：审核操作日志是多人多次追加的，
        直接贴在聊天里会很长、也翻不动；发文件才能让人存下来慢慢看。

        参数 file 传的是**服务器本地绝对路径**（NapCat 与机器人在同一台机器上时最稳，
        也避免把文件塞进 base64 撑爆报文）。name 是对方看到的文件名。

        返回 (是否成功, 失败原因)；失败原因可以直接回给管理员 —— 「发了没反应」
        比「发失败，原因是……」难排查得多。
        """
        connection = self.latest()
        if connection is None:
            logger.error("没有可用的 NapCat 连接，文件未送达 user_id=%s", user_id)
            return False, "机器人与 NapCat 当前没有连接，无法发送文件"
        resolved = Path(path).resolve()
        if not resolved.is_file():
            return False, f"文件不存在：{resolved}"
        params: dict[str, Any] = {"user_id": int(user_id), "file": str(resolved)}
        if name:
            params["name"] = name
        try:
            response = await connection.call_api("upload_private_file", params, timeout=timeout)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            logger.exception("发送私聊文件失败 user_id=%s path=%s", user_id, resolved)
            return False, f"调用 NapCat 失败：{exc}"
        reason = _onebot_failure_reason(response)
        if reason:
            logger.error(
                "发送私聊文件被拒绝：user_id=%s path=%s 原因=%s", user_id, resolved, reason
            )
            return False, reason
        logger.info("已发送私聊文件：user_id=%s path=%s 大小=%d B", user_id, resolved, resolved.stat().st_size)
        return True, ""


# --------------------------------------------------------------------------------------
# 九、投稿会话调度
# --------------------------------------------------------------------------------------


_PUBLISH_SAFE_SUFFIX = {"image/jpeg": ".jpg", "image/png": ".png", "image/gif": ".gif"}


def _prepare_image_for_publish(
    data: bytes, url_hint: str, *, max_pixels: int = 0
) -> tuple[bytes, str] | None:
    """把下载到的字节整理成「空间能上传」的图片，返回 (字节, 后缀)；无法处理返回 None。

    为什么要做这一步：送审那条路会跳过不支持的格式（送去也没用），但发布这条路
    以前是原样存盘 —— 结果就出现「审核跳过了这张图 → 审核通过 → 发布时上传失败」。
    JPEG/PNG/GIF 保持原样（仍是真正的原图）；其它 PIL 能读的（WebP/BMP/TIFF…）
    转成 JPEG，避免空间不收；完全读不出来的（错误页等）直接跳过并记录。
    """
    mime = _sniff_image_mime(data)
    if mime in _PUBLISH_SAFE_SUFFIX:
        return data, _PUBLISH_SAFE_SUFFIX[mime]
    try:
        with Image.open(io.BytesIO(data)) as raw:
            _reject_oversized_image(raw, max_pixels, source=url_hint)
            converted = raw.convert("RGB")
        buffer = io.BytesIO()
        converted.save(buffer, format="JPEG", quality=90)
        logger.info("图片格式 %s 空间可能不收，已转成 JPEG 后发布：%s", mime or "未知", url_hint[:80])
        return buffer.getvalue(), ".jpg"
    except Exception:
        logger.warning("图片无法识别也无法转码，已跳过发布：%s", url_hint[:80], exc_info=True)
        return None


def _describe_publish_paths(paths: Sequence[str]) -> str:
    """生成「文件名(大小)」摘要，便于从日志一眼看出是哪张图、多大。"""
    parts: list[str] = []
    for path in paths:
        name = Path(path).name
        try:
            parts.append(f"{name}({Path(path).stat().st_size // 1024}KB)")
        except OSError:
            parts.append(f"{name}(文件缺失)")
    return ", ".join(parts)


# 批量删除说说之间的间隔：一次删几十条时别把接口打太快（风控）。
_DELETE_POST_INTERVAL_SECONDS = 0.5

# 每个投稿存档目录里那份「审核操作日志」的文件名（全局日志用同一个名字）。
AUDIT_LOG_FILENAME = "审核操作日志.txt"


class SubmissionManager:
    """按用户维护投稿会话与空闲定时器，并在定时器到期时执行「渲染 → 审核 → 发布」。

    2026-10 起不再有「攒稿排队 / 定时统一放送」：最后一条消息之后静默
    idle_timeout_seconds（默认 60 秒）就开始渲染，本次投稿立刻结束。
    """

    def __init__(
        self,
        *,
        settings: Settings,
        database: Database,
        connections: ConnectionManager,
        publisher: QZonePublisher,
        http_client: httpx.AsyncClient,
    ) -> None:
        self.settings = settings
        self.database = database
        self.connections = connections
        self.publisher = publisher
        self.http_client = http_client
        self.sessions: dict[int, SubmissionSession] = {}
        # 防刷屏（每日额度）：{user_id: (额度日 "YYYY-MM-DD", 当天已收录条数)}。
        # 日期变了就等于计数归零 —— 「每日 0 点重置」不需要任何定时任务，也不怕停机跨天。
        self._daily_counts: dict[int, tuple[str, int]] = {}
        self._last_rate_notice: dict[int, float] = {}
        self._last_image_cap_notice: dict[int, float] = {}
        self._rate_sweep_tick = 0
        self._data_dir = Path(settings.data_dir)
        self._screenshot_dir = self._data_dir / "screenshots"
        self._image_dir = self._data_dir / "images"
        # 投稿存档根目录：每份渲染出来的投稿一个 `<编号>_<投稿人QQ>` 子目录。
        self._archive_dir = (
            Path(settings.archive_dir) if str(settings.archive_dir or "").strip()
            else self._data_dir / "archive"
        )
        # 全局审核操作日志（所有投稿的管理动作汇总；按投稿的那份在各存档目录里）
        self._audit_dir = self._data_dir / "audit"
        self._audit_log_path = self._audit_dir / AUDIT_LOG_FILENAME
        # 管理员「急停」状态。落盘保存：重启不该把暂停悄悄解除
        # （否则「暂停 → 服务器被重启 → 又开始发布」会让人以为急停没生效）。
        self._pause_file = self._data_dir / "paused.json"
        self._paused = False
        self._paused_at: float | None = None
        self._paused_by: str = ""
        self._last_pause_notice: dict[int, float] = {}
        # 说明：定时放送队列（_queue）、加急（_express_users）与调度任务（_dispatch_task）
        # 已随「攒稿统一放送」功能一起删除 —— 现在空闲超时后直接渲染并发布。
        self._load_pause_state()

    # ---------------- 投稿存档与审核操作日志 ----------------

    @staticmethod
    def safe_code(code: Any) -> str:
        """把投稿编号整理成可安全用作文件名的一段（只留字母数字与 -_）。"""
        text = re.sub(r"[^0-9A-Za-z_-]", "", str(code or "").strip())
        return text or "未编号"

    def submission_folder(self, row: Mapping[str, Any]) -> Path:
        """某条投稿的存档目录：`<存档根>/<编号>_<投稿人QQ>`。

        目录名就带上「编号 + 投稿人 QQ」——需求要求文件名至少包含这两项，
        目录名同样带上，事后在服务器上翻文件夹也能一眼对上是哪一条、谁投的。
        """
        name = f"{self.safe_code(row.get('display_code'))}_{int(row.get('user_id') or 0)}"
        return self._archive_dir / name

    def _append_text(self, path: Path, line: str) -> bool:
        """向文件追加一行（不存在就建；写失败只记日志，绝不向上抛）。"""
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("a", encoding="utf-8") as handle:
                handle.write(line.rstrip("\n") + "\n")
            return True
        except OSError:
            logger.exception("审核操作日志写入失败：%s", path)
            return False

    def _audit_global(self, message: str) -> None:
        """写全局审核操作日志（所有投稿的管理动作都汇总到这一份）。"""
        self._append_text(self._audit_log_path, f"[{format_log_time(self.settings)}] {message}")

    def _audit_submission(self, row: Mapping[str, Any], message: str) -> None:
        """把一条动作写进该投稿自己的「审核操作日志.txt」，同时写全局日志。"""
        self._audit_global(message)
        folder = self.submission_folder(row)
        self._append_text(folder / AUDIT_LOG_FILENAME, f"[{format_log_time(self.settings)}] {message}")

    async def archive_submission(
        self,
        session: SubmissionSession,
        *,
        screenshot: Path,
        submission_code: str,
        display_time: str,
        anonymous: bool,
        originals: Sequence[str],
    ) -> Path | None:
        """把本次渲染出来的投稿存进独立文件夹，并写下审核操作日志的头部。

        需求：「所有渲染的投稿都在服务器单独文件夹内进行存档，文件名至少应包括投稿编号、
        投稿人 qq 号。文件夹内同时存放一个『审核操作日志』」。

        目录：`<ARCHIVE_DIR>/<编号>_<投稿人QQ>/`
        文件：`投稿_<编号>_<QQ>.png`、`原图_<编号>_<QQ>_<序号>.<后缀>`、
              `审核操作日志.txt`

        存档失败**不影响发布**（与标记图同一原则）：只记错误日志并返回 None。
        """
        code = self.safe_code(submission_code)
        user_id = int(session.user_id)
        folder = self._archive_dir / f"{code}_{user_id}"
        text = session.text_content()
        summary = re.sub(r"\s+", " ", text).strip()[:200] or "（无文字内容）"
        photo_count = len(session.image_segments())
        sticker_count = len(session.image_messages()) - photo_count
        face_count = len(session.face_segments())

        def _copy_files() -> list[str]:
            folder.mkdir(parents=True, exist_ok=True)
            saved: list[str] = []
            shot_name = f"投稿_{code}_{user_id}.png"
            shutil.copy2(screenshot, folder / shot_name)
            saved.append(shot_name)
            for index, path in enumerate(originals, start=1):
                source = Path(path)
                if not source.is_file():
                    continue
                suffix = source.suffix or ".jpg"
                name = f"原图_{code}_{user_id}_{index}{suffix}"
                shutil.copy2(source, folder / name)
                saved.append(name)
            return saved

        try:
            saved_files = await asyncio.to_thread(_copy_files)
        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception(
                "投稿存档失败（不影响发布）：user_id=%s 编号=%s", user_id, submission_code
            )
            return None

        header = [
            "==================== 投稿存档 ====================",
            f"投稿编号：{submission_code or '（无）'}",
            f"投稿人 QQ：{user_id}",
            f"投稿时间：{format_archive_time(display_time)}",
            f"渲染存档时间：{format_log_time(self.settings)}",
            f"匿名投稿：{'是' if anonymous else '否'}",
            f"消息段数：{len(session.messages)}（文字 "
            f"{sum(1 for m in session.messages if m.kind == 'text')} / 图片 {photo_count}"
            f" / 表情 {face_count + sticker_count}）",
            f"正文摘要：{summary}",
            f"存档文件：{'、'.join(saved_files)}",
            "==================== 审核操作日志 ====================",
            "（按时间追加：管理员 / 审核员的每一次操作、QQ、时间、理由与结果；系统侧的审核、发布结果也会记在这里）",
        ]
        log_path = folder / AUDIT_LOG_FILENAME
        try:
            await asyncio.to_thread(
                log_path.write_text, "\n".join(header) + "\n", "utf-8"
            )
        except OSError:
            logger.exception("审核操作日志创建失败：%s", log_path)
        logger.info(
            "投稿已存档：user_id=%s 编号=%s 目录=%s 文件=%s",
            user_id,
            submission_code,
            folder,
            "、".join(saved_files),
        )
        return folder

    # ---------------- 管理员命令（白名单急停）----------------

    @property
    def paused(self) -> bool:
        """是否处于「暂停账号活动」状态。"""
        return self._paused

    def _load_pause_state(self) -> None:
        """启动时恢复暂停标记（文件不存在 / 损坏都按「未暂停」处理）。"""
        try:
            data = json.loads(self._pause_file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return
        if not isinstance(data, dict) or not data.get("paused"):
            return
        self._paused = True
        try:
            self._paused_at = float(data.get("at") or 0) or None
        except (TypeError, ValueError):
            self._paused_at = None
        self._paused_by = str(data.get("by") or "")
        logger.warning(
            "服务处于【暂停】状态：操作人=%s 时间=%s —— 重启后依然生效，"
            "恢复请发白名单命令",
            self._paused_by or "未知",
            format_submission_time(self.settings, self._paused_at) if self._paused_at else "未知",
        )

    def _save_pause_state(self) -> None:
        """把暂停状态落盘（恢复时删除文件）。写不进去只记日志，不影响内存状态。"""
        try:
            if not self._paused:
                if self._pause_file.exists():
                    self._pause_file.unlink()
                return
            self._pause_file.parent.mkdir(parents=True, exist_ok=True)
            self._pause_file.write_text(
                json.dumps(
                    {"paused": True, "at": self._paused_at, "by": self._paused_by},
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
        except OSError:
            logger.exception("暂停状态写入失败：本次状态在重启后会丢失")

    def discard_sessions(self) -> int:
        """取消并清空所有等待中的投稿，返回被取消的数量。"""
        pending = list(self.sessions)
        for user_id in pending:
            session = self.sessions.pop(user_id, None)
            if session is not None:
                self._cancel_timer(session)
        return len(pending)

    def set_paused(self, paused: bool, *, operator: str = "") -> None:
        """切换暂停状态：落盘 + 暂停时把等待中的投稿一并取消。"""
        self._paused = bool(paused)
        self._paused_at = time.time() if self._paused else None
        self._paused_by = str(operator) if self._paused else ""
        self._save_pause_state()
        if self._paused:
            logger.warning(
                "已暂停账号活动：操作人=%s 取消等待中的投稿=%d 个",
                operator or "未知",
                self.discard_sessions(),
            )
        else:
            logger.warning("已恢复账号活动：操作人=%s", operator or "未知")

    async def describe_status(self) -> str:
        """给管理员看的运行状态摘要。"""
        prefix = command_prefix_of(self.settings)
        if self._paused:
            when = format_submission_time(self.settings, self._paused_at) if self._paused_at else "未知"
            lines = [f"状态：已暂停（{when}，操作人 {self._paused_by or '未知'}）"]
        else:
            lines = ["状态：运行中"]
        lines.append(f"NapCat 连接：{self.connections.count} 个")
        pending = sorted(self.sessions)
        if pending:
            shown = "、".join(str(uid) for uid in pending[:10])
            more = f" 等 {len(pending)} 个" if len(pending) > 10 else ""
            lines.append(f"等待发布：{shown}{more}（最后一条消息后约 "
                         f"{self.settings.idle_timeout_seconds / 60:.0f} 分钟开始渲染）")
        else:
            lines.append("等待发布：0 个")
        lines.append(
            f"所有者：{len(owner_ids(self.settings))} 人"
            f"　管理员：{len(admin_ids(self.settings))} 人"
            f"　审核员：{len(reviewer_ids(self.settings))} 人"
        )
        lines.append(
            f"每日额度：每人 {self.settings.daily_message_limit} 条（0 点重置，管理员不限）"
            f"　今天已计入：{self._today_user_count()} 人"
        )
        lines.append(f"投稿存档：{self._archive_dir}")
        lines.append(f"审核操作日志：{self._audit_log_path}")
        blocked = await self.database.list_blacklist()
        if blocked:
            shown = "、".join(str(item["user_id"]) for item in blocked[:10])
            lines.append(f"黑名单：{len(blocked)} 人（{shown}）")
        else:
            lines.append("黑名单：0 人")
        lines.append(
            f"命令：{prefix}停止账号活动 / {prefix}恢复账号活动 / {prefix}状态 /"
            f" {prefix}重置限额 / {prefix}审核日志 / {prefix}帮助"
        )
        return "\n".join(lines)

    def _today_user_count(self) -> int:
        """今天已经用掉过额度的用户数（状态查询里给管理员一个量感）。"""
        today = quota_date(self.settings)
        return sum(1 for day, _count in self._daily_counts.values() if day == today)

    async def _notify_paused(self, user_id: int) -> None:
        """暂停期间告诉投稿人一声；带冷却，避免「提示」自己变成刷屏。"""
        now = time.monotonic()
        cooldown = max(0.0, self.settings.rate_limit_notice_cooldown_seconds)
        last_notice = self._last_pause_notice.get(user_id)
        if last_notice is not None and now - last_notice < cooldown:
            return
        self._last_pause_notice[user_id] = now
        await self._notify(user_id, "投稿功能暂时停用，请稍后再试。")

    async def _notify_blocked(self, user_id: int) -> None:
        """告诉被拉黑/被封禁的用户一声（同样带冷却）。

        文案里解释「到什么时候恢复」但不解释具体原因 —— 原因写进库里供管理员查看，
        直接回给用户容易变成「教他怎么绕过审核」。
        """
        now = time.monotonic()
        cooldown = max(0.0, self.settings.rate_limit_notice_cooldown_seconds)
        last_notice = self._last_pause_notice.get(user_id)
        if last_notice is not None and now - last_notice < cooldown:
            return
        self._last_pause_notice[user_id] = now
        contact = _join_contacts(self.settings.support_contact_qq)
        tail = f"如有疑问请联系 QQ {contact}。" if contact else "如有疑问请联系管理员。"
        entry = await self.database.get_blacklist_entry(user_id)
        expiry = _parse_expiry(entry.get("until")) if entry else None
        if expiry is not None:
            when = format_due_time(self.settings, expiry.timestamp())
            await self._notify(user_id, f"你的投稿功能已被暂停，将于 {when} 自动恢复。{tail}")
            return
        await self._notify(user_id, f"你的投稿功能已被停用。{tail}")

    async def _run_admin_command(self, user_id: int, text: str) -> None:
        """执行白名单命令并回复执行结果（命令消息绝不进入投稿流水线）。

        三层判定：像不像命令（调用方已判）→ 是不是所有者/管理员/审核员 →
        **这个角色能不能用这条命令**。第三层是核心：审核员只有删帖 / 封禁 / 解封，
        其余动作一律拒绝并给出**按角色裁剪过的**可用清单。
        """
        parsed = parse_admin_command(text, self.settings)
        prefix = command_prefix_of(self.settings)
        role = "owner" if is_owner(self.settings, user_id) else (
            "admin" if is_admin(self.settings, user_id) else "reviewer"
        )
        if parsed is None:
            logger.info(
                "白名单用户发来的未知命令，仅回复帮助：user_id=%s 内容=%r", user_id, text[:40]
            )
            await self._notify(
                user_id, f"无法识别的命令。\n{format_admin_help(self.settings, role=role)}"
            )
            return
        action, argument = parsed
        allowed = admin_actions(self.settings, user_id)
        if action not in allowed:
            # 这是「有人试图越权」，必须留痕：日志里能看出谁在什么时候试过什么
            logger.warning(
                "管理命令权限不足，已拒绝：user_id=%s 角色=%s 动作=%s",
                user_id,
                role_label(self.settings, user_id),
                action,
            )
            needed = "仅所有者" if action in {
                "grant_admin", "revoke_admin", "grant_reviewer", "revoke_reviewer", "purge_old"
            } else "仅管理员"
            await self._notify(
                user_id,
                f"该命令{needed}可用，本次未执行。\n"
                f"{format_admin_help(self.settings, role=role)}",
            )
            return
        # 命令一律记 warning 级别：这是「有人在远程操作服务」，日志里必须显眼
        logger.warning(
            "收到管理命令：user_id=%s 角色=%s 动作=%s 参数=%r",
            user_id,
            role_label(self.settings, user_id),
            action,
            argument[:80],
        )
        if action == "pause":
            self.set_paused(True, operator=str(user_id))
            self._audit_global(f"暂停账号活动：操作人 QQ {user_id}（{role_label(self.settings, user_id)}）")
            reply = (
                "已暂停账号活动：不再收投稿、不再发布，等待中的投稿已取消。\n"
                f"恢复请发 {prefix}恢复账号活动"
            )
        elif action == "resume":
            was_paused = self._paused
            self.set_paused(False, operator=str(user_id))
            self._audit_global(f"恢复账号活动：操作人 QQ {user_id}（{role_label(self.settings, user_id)}）")
            reply = "已恢复账号活动，可以正常收稿与发布。" if was_paused else "当前并未暂停，无需恢复。"
        elif action == "status":
            reply = await self.describe_status()
        elif action == "delete":
            reply = await self._cmd_delete(user_id, argument)
        elif action == "who":
            reply = await self._cmd_who(user_id, argument)
        elif action == "blacklist_user":
            reply = await self._cmd_blacklist_user(user_id, argument)
        elif action == "ban":
            reply = await self._cmd_ban(user_id, argument)
        elif action == "tempban":
            reply = await self._cmd_tempban(user_id, argument)
        elif action == "unban":
            reply = await self._cmd_unban(user_id, argument)
        elif action == "unban_list":
            reply = await self._cmd_blacklist()
        elif action == "reset_quota":
            reply = await self._cmd_reset_quota(user_id, argument)
        elif action == "reset_quota_all":
            reply = await self._cmd_reset_quota_all(user_id)
        elif action == "audit_log":
            reply = await self._cmd_audit_log(user_id, argument)
        elif action == "purge_old":
            reply = await self._cmd_purge_old(user_id, argument)
        elif action == "purge_report":
            reply = await self._cmd_purge_report(user_id, argument)
        elif action == "grant_admin":
            reply = await self._cmd_grant_role(user_id, argument, role_name="admin")
        elif action == "revoke_admin":
            reply = await self._cmd_revoke_role(user_id, argument, role_name="admin")
        elif action == "grant_reviewer":
            reply = await self._cmd_grant_role(user_id, argument, role_name="reviewer")
        elif action == "revoke_reviewer":
            reply = await self._cmd_revoke_role(user_id, argument, role_name="reviewer")
        else:
            reply = format_admin_help(self.settings, role=role)
        await self._notify(user_id, reply)

    async def _locate_submission(self, value: str) -> tuple[dict[str, Any] | None, str]:
        """按「编号 / 投稿时间」定位投稿。

        返回 (记录, 错误提示)：记录为 None 时，错误提示可直接回给管理员。
        """
        marker = value.strip()
        if not marker:
            return None, (
                "请给出截图底部的编号（如 K7F2M）或投稿时间（如 2026-10-06 18:07:40）。"
            )
        row = await self.database.find_submission_by_marker(marker)
        if row is None:
            return None, (
                f"没找到「{marker}」对应的投稿：请核对截图底部的编号或投稿时间（要一字不差）。\n"
                "注意：投稿要等它渲染发布之后才会入库，刚发完的消息请等一分钟再查。"
            )
        return row, ""

    @staticmethod
    def _split_marker_reason(argument: str) -> tuple[str, str]:
        """把「<编号 / 投稿时间> <理由>」拆成 (定位值, 理由)。

        需求原文：「审核员进行删稿和封禁时，需要在命令中附带上理由，否则无法封禁或删稿，
        进行简单校验（只看编号后有没有带字符，其他不管）」。
        因此这里只做最朴素的判断：定位值之后**还有没有任何非空字符**，不校验理由内容。

        一个必须照顾的细节：截图上的投稿时间形如 `2026-10-06 18:07:40`，自带空格；
        直接按空格切会把时间切成两段、把 `18:07:40` 误当成理由。所以日期后面紧跟
        `HH:MM:SS` 时要把它们并回定位值，真正的理由从时间之后才开始。
        """
        text = (argument or "").strip()
        if not text:
            return "", ""
        parts = text.split(maxsplit=1)
        marker = parts[0]
        rest = parts[1].strip() if len(parts) > 1 else ""
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}", marker) and rest:
            follow = rest.split(maxsplit=1)
            if re.fullmatch(r"\d{2}:\d{2}:\d{2}", follow[0]):
                marker = f"{marker} {follow[0]}"
                rest = follow[1].strip() if len(follow) > 1 else ""
        return marker, rest

    async def _cmd_delete(self, operator_id: int, argument: str) -> str:
        """删帖：只删这一条投稿，**不拉黑作者、不动他的其它投稿**。

        与「拉黑并删除」的区别就是这个 —— 手滑发错一条、内容小问题，用它更合适。
        审核员/管理员都必须写理由：删帖是「对用户内容的处置」，没有理由的处置事后说不清。
        """
        prefix = command_prefix_of(self.settings)
        marker, reason = self._split_marker_reason(argument)
        if not marker:
            return (
                f"用法：{prefix}删帖 <编号 或 投稿时间> <理由>\n"
                "例如：" f"{prefix}删帖 K7F2M 泄露他人隐私"
            )
        if not reason:
            return (
                "删帖必须写理由：在编号后面再写一句话（内容不限，能说清为什么删就行）。\n"
                f"例如：{prefix}删帖 {marker} 泄露他人隐私\n"
                "本次未执行；理由会和操作人、时间一起记进「审核操作日志」。"
            )
        row, error = await self._locate_submission(marker)
        if row is None:
            return f"用法：{prefix}删帖 <编号 或 投稿时间> <理由>\n{error}"
        submission_id = int(row["id"])
        value = marker.strip()
        status = str(row.get("status") or "")
        tid = str(row.get("qzone_tid") or "").strip()
        actor = role_label(self.settings, operator_id)
        if status == "deleted":
            return f"投稿 #{submission_id}（{value}）已经删过了，无需重复删除。"
        if not tid:
            # 没有 tid 说明这条根本没成功发到空间（被拒 / 发布失败）
            await self.database.update_submission(
                submission_id,
                status="deleted",
                reason=f"{actor} {operator_id} 删帖（未发布，直接作废）：{reason}",
            )
            self._audit_submission(
                row,
                f"删帖（该投稿未发布，直接作废）：操作人 {actor} QQ {operator_id}"
                f"｜理由：{reason}｜原状态：{status}",
            )
            logger.warning(
                "删帖（该投稿未发布，直接作废）：id=%s 原状态=%s 操作人=%s 理由=%s",
                submission_id,
                status,
                operator_id,
                reason,
            )
            return (
                f"投稿 #{submission_id}（{value}）原本状态是「{status}」，并没有成功发到空间，"
                "已直接作废，无需删除空间内容。\n"
                f"理由已记入审核操作日志：{reason}"
            )
        try:
            await self.publisher.delete_post(tid)
        except Exception as exc:  # 删失败必须如实回报，不能谎称已删
            self._audit_submission(
                row,
                f"删帖失败：操作人 {actor} QQ {operator_id}｜理由：{reason}｜原因：{exc}",
            )
            logger.error(
                "删帖失败：id=%s tid=%s 操作人=%s 原因=%s", submission_id, tid, operator_id, exc
            )
            return (
                f"删除投稿 #{submission_id}（{value}）失败：{exc}\n"
                f"空间里的那条还在，可稍后重试；反复失败请用 {prefix}状态 看服务是否正常。"
            )
        await self.database.update_submission(
            submission_id, status="deleted", reason=f"{actor} {operator_id} 删帖：{reason}"
        )
        self._audit_submission(
            row, f"删帖成功：操作人 {actor} QQ {operator_id}｜理由：{reason}｜tid={tid}"
        )
        logger.warning(
            "删帖成功：id=%s tid=%s 操作人=%s 理由=%s", submission_id, tid, operator_id, reason
        )
        return (
            f"已删除投稿 #{submission_id}（{value}）对应的一条说说。\n"
            "只删了空间内容：作者没有被拉黑，他的其它投稿不受影响。\n"
            f"理由已记入审核操作日志：{reason}"
        )

    async def _cmd_who(self, operator_id: int, marker: str) -> str:
        """查作者：看某条投稿是谁发的 —— 匿名投稿同样能查到（这正是它的用途）。

        这是**隐私敏感操作**：日志里必须留下「谁查了哪条投稿、查到了谁」，
        事后才说得清「管理员是什么时候看到这个 QQ 的」。
        """
        prefix = command_prefix_of(self.settings)
        row, error = await self._locate_submission(marker)
        if row is None:
            return f"用法：{prefix}查作者 <编号 或 投稿时间>\n{error}"
        target = int(row["user_id"])
        content = re.sub(r"\s+", " ", str(row.get("content") or "")).strip()
        anonymous = wants_anonymous(str(row.get("content") or ""), self.settings.anonymous_keywords)
        blocked = await self.database.is_blacklisted(target)
        logger.warning(
            "查作者：id=%s 投稿人=%s 匿名=%s 操作人=%s",
            int(row["id"]),
            target,
            anonymous,
            operator_id,
        )
        self._audit_submission(
            row,
            f"查作者：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜查到的投稿人 QQ {target}（匿名投稿：{'是' if anonymous else '否'}）",
        )
        return (
            f"投稿 #{int(row['id'])}（编号 {row.get('display_code') or '无'}"
            f" · {row.get('display_time') or '无时间'}）\n"
            f"投稿人 QQ：{target}\n"
            f"匿名投稿：{'是' if anonymous else '否'}"
            f"　状态：{row.get('status') or '未知'}"
            f"　当前黑名单：{'是' if blocked else '否'}\n"
            f"内容摘要：{content[:40] or '（无文字）'}"
        )

    async def _cmd_blacklist_user(self, operator_id: int, argument: str) -> str:
        """拉黑用户：按 QQ 号永久拉黑（不删除他已发布的投稿）。"""
        prefix = command_prefix_of(self.settings)
        parts = argument.split(maxsplit=1)
        if not parts or not parts[0].strip().isdigit():
            return (
                f"用法：{prefix}拉黑用户 <QQ号> [原因]，例如 {prefix}拉黑用户 123456789 泄露他人隐私\n"
                f"要连他的已发布投稿一起删掉，用 {prefix}拉黑并删除 <编号> <理由>。"
            )
        target = int(parts[0])
        reason = parts[1].strip() if len(parts) > 1 else "管理员手动拉黑"
        # 先取消他等待中的投稿 —— 否则可能出现「刚拉黑，那条又发出去了」
        pending = self.sessions.pop(target, None)
        if pending is not None:
            self._cancel_timer(pending)
        await self.database.add_blacklist(
            target,
            reason=f"{reason}（操作人 {operator_id}）",
            operator=str(operator_id),
        )
        self._audit_global(
            f"拉黑用户：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜被拉黑 QQ {target}｜理由：{reason}｜丢弃等待中投稿：{'是' if pending else '否'}"
        )
        logger.warning(
            "拉黑用户：user_id=%s 操作人=%s 原因=%s 丢弃等待中=%s",
            target,
            operator_id,
            reason,
            pending is not None,
        )
        return (
            f"已永久拉黑 QQ {target}（原因：{reason}）。他再发消息不会被投稿。\n"
            f"注意：本次只拉黑、没删他已发布的说说；要一起删用 {prefix}拉黑并删除 <编号>。\n"
            f"解除拉黑：{prefix}解封 {target}"
        )

    async def _cmd_tempban(self, operator_id: int, argument: str) -> str:
        """限期封禁：/封禁 <QQ号> [天数] <理由>（不给天数用 DEFAULT_BAN_DAYS）。

        理由必填：与删帖同一条规矩 —— 封禁是「对用户的处置」，事后要能说清为什么。
        校验只看「QQ 号（与可选天数）后面还有没有字符」，不校验理由写得好不好。
        """
        prefix = command_prefix_of(self.settings)
        parts = (argument or "").split(maxsplit=2)
        if not parts or not parts[0].strip().isdigit():
            return (
                f"用法：{prefix}封禁 <QQ号> [天数] <理由>，"
                f"例如 {prefix}封禁 123456789 3 泄露他人隐私\n"
                f"不给天数时默认封 {self.settings.default_ban_days:g} 天；到点会自动恢复。"
            )
        target = int(parts[0])
        days = self.settings.default_ban_days
        rest = parts[1:]
        if rest and rest[0].strip().replace(".", "", 1).isdigit():
            days = float(rest[0])
            rest = rest[1:]
        reason = rest[0].strip() if rest else ""
        if not reason:
            return (
                "封禁必须写理由：在 QQ 号（或天数）后面再写一句话，内容不限。\n"
                f"例如：{prefix}封禁 {target} 3 泄露他人隐私\n"
                f"不写天数就直接接理由也可以：{prefix}封禁 {target} 多次发违规内容\n"
                "本次未执行；理由会和操作人、时间一起记进「审核操作日志」。"
            )
        hours = max(0.0, days * 24.0)
        until = _utc_now() + timedelta(hours=hours) if hours > 0 else None
        await self.database.add_blacklist(
            target,
            reason=f"{reason}（操作人 {operator_id}）",
            operator=str(operator_id),
            until=until,
        )
        # 封禁生效时取消他等待中的投稿，别让已收下的违规内容照常发出去
        pending = self.sessions.pop(target, None)
        if pending is not None:
            self._cancel_timer(pending)
        self._audit_global(
            f"封禁用户：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜被封禁 QQ {target}｜天数：{days:g}"
            f"｜到期：{until.isoformat(timespec='seconds') if until else '永久'}"
            f"｜理由：{reason}｜丢弃等待中投稿：{'是' if pending else '否'}"
        )
        logger.warning(
            "管理员封禁：user_id=%s 天数=%s 操作人=%s 理由=%s 丢弃等待中=%s",
            target,
            days,
            operator_id,
            reason,
            pending is not None,
        )
        if until is None:
            return f"已永久封禁 QQ {target}（原因：{reason}）。解封用 {prefix}解封 {target}"
        when = format_due_time(self.settings, until.timestamp())
        return (
            f"已封禁 QQ {target} {days:g} 天（到 {when} 自动恢复，原因：{reason}）。"
            f"提前解封用 {prefix}解封 {target}"
        )

    async def _maybe_auto_ban(self, user_id: int, reason: str) -> bool:
        """被拒次数达到阈值就限期封禁；返回是否真的封了。

        只统计「审核判为违规」（rejected），不统计「审核服务不可用」（failed）——
        后者不是用户的错，不能因此封人。
        """
        strikes = int(self.settings.auto_ban_strikes)
        if strikes <= 0:
            return False
        count = await self.database.count_recent_rejections(
            user_id, hours=self.settings.auto_ban_window_hours
        )
        if count < strikes:
            logger.info(
                "被拒次数未达自动封禁阈值：user_id=%s 次数=%d 阈值=%d", user_id, count, strikes
            )
            return False
        hours = max(0.0, self.settings.auto_ban_hours)
        until = _utc_now() + timedelta(hours=hours) if hours > 0 else None
        await self.database.add_blacklist(
            user_id,
            reason=(
                f"自动封禁：{self.settings.auto_ban_window_hours:g} 小时内被拒 {count} 次"
                f"（最近一次：{reason}）"
            ),
            operator="auto",
            until=until,
        )
        self._audit_global(
            f"自动封禁：投稿人 QQ {user_id}｜{self.settings.auto_ban_window_hours:g} 小时内被拒 {count} 次"
            f"｜到期：{until.isoformat(timespec='seconds') if until else '永久'}｜最近一次原因：{reason}"
        )
        logger.warning(
            "已自动封禁：user_id=%s 被拒次数=%d 解禁=%s",
            user_id,
            count,
            until.isoformat(timespec="seconds") if until else "永久",
        )
        if until is None:
            await self._notify(user_id, "你因多次发送违规内容，投稿功能已被永久停用。")
        else:
            when = format_due_time(self.settings, until.timestamp())
            await self._notify(
                user_id,
                f"你因多次发送违规内容（{self.settings.auto_ban_window_hours:g} 小时内 {count} 次），"
                f"投稿功能已被暂停到 {when}。",
            )
        return True

    async def _cmd_ban(self, operator_id: int, argument: str) -> str:
        """按截图上的「编号 / 投稿时间」定位投稿 → 拉黑作者 → 删除他所有已发布的投稿。

        为什么要靠编号或时间定位：投稿可以匿名，截图里没有 QQ 号，
        能对上号的只有截图底部那两个值（所以它们会被原样存进数据库）。
        理由同样必填：这是「删稿 + 封禁」两件事一起做，比单独删帖更需要留痕。
        """
        prefix = command_prefix_of(self.settings)
        value, reason = self._split_marker_reason(argument)
        if not value:
            return (
                f"用法：{prefix}拉黑并删除 <编号 或 投稿时间> <理由>\n"
                "编号看截图底部（如 K7F2M）；也可以直接给截图上的时间（如 2026-10-06 18:07:40）。"
            )
        if not reason:
            return (
                "拉黑并删除必须写理由：在编号后面再写一句话，内容不限。\n"
                f"例如：{prefix}拉黑并删除 {value} 多次发布违规内容\n"
                "本次未执行；理由会和操作人、时间一起记进「审核操作日志」。"
            )
        row = await self.database.find_submission_by_marker(value)
        if row is None:
            return f"没找到「{value}」对应的投稿：请核对截图底部的编号或投稿时间（要一字不差）。"
        target = int(row["user_id"])
        submission_id = int(row["id"])

        # 1) 先取消他等待中的投稿 —— 否则可能出现「刚拉黑，那条又发出去了」
        pending = self.sessions.pop(target, None)
        if pending is not None:
            self._cancel_timer(pending)
            logger.warning(
                "拉黑时取消了该用户等待中的投稿：user_id=%s 段数=%d 操作人=%s",
                target,
                len(pending.messages),
                operator_id,
            )
        # 2) 拉黑
        await self.database.add_blacklist(
            target,
            reason=f"依投稿 #{submission_id}（{value}）拉黑：{reason}",
            operator=str(operator_id),
        )
        # 3) 删除他所有已发布（且记下了 tid）的投稿
        rows = await self.database.list_user_submissions(target, status="published")
        deleted: list[str] = []
        failed: list[str] = []
        for item in rows:
            tid = str(item.get("qzone_tid") or "").strip()
            if not tid:
                failed.append(f"#{item['id']}（记录里没有 tid，需手动删）")
                continue
            try:
                await self.publisher.delete_post(tid)
            except Exception as exc:  # 单条失败不能影响其余删除
                failed.append(f"#{item['id']}（{exc}）")
            else:
                await self.database.update_submission(int(item["id"]), status="deleted")
                deleted.append(f"#{item['id']}")
            await asyncio.sleep(_DELETE_POST_INTERVAL_SECONDS)
        logger.warning(
            "已拉黑用户：user_id=%s 操作人=%s 依据投稿=#%s 理由=%s 删除成功=%d 失败=%d",
            target,
            operator_id,
            submission_id,
            reason,
            len(deleted),
            len(failed),
        )
        self._audit_submission(
            row,
            f"拉黑并删除：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜理由：{reason}｜已拉黑投稿人 QQ {target}"
            f"｜删除已发布投稿 {len(deleted)} 条、失败 {len(failed)} 条",
        )

        lines = [
            f"已拉黑 QQ {target}：他再发消息不会被投稿（会给一次停用提示）。",
            f"依据投稿 #{submission_id}（{value}）　理由：{reason}",
            f"删除已发布投稿：成功 {len(deleted)} 条"
            + (f"（{'、'.join(deleted)}）" if deleted else ""),
        ]
        if not rows:
            lines.append("（这个用户没有「已发布」状态的投稿记录）")
        if failed:
            lines.append(f"删除失败 {len(failed)} 条，需要手动处理：")
            lines.extend(f"  · {item}" for item in failed)
        lines.append(f"解除拉黑：{command_prefix_of(self.settings)}解除拉黑 {target}")
        return "\n".join(lines)

    async def _cmd_unban(self, operator_id: int, argument: str) -> str:
        """解除拉黑（给 QQ 号）。

        权限分两档（沿用原需求，只改了角色名）：
          * 管理员：可以解封任何人；
          * 审核员：只能解封 **AI 自动封禁**（operator == "auto"）
            或 **他自己封禁**的用户 —— 其他人封的不能动。
        为什么按「记录上的操作人」判而不是按动作判：同样是 `/解封`，
        能否执行取决于这条封禁是谁下的，属于记录级鉴权。
        """
        prefix = command_prefix_of(self.settings)
        value = argument.strip()
        if not value.isdigit():
            return f"用法：{prefix}解封 <QQ号>，例如 {prefix}解封 123456789"
        target = int(value)
        entry = await self.database.get_blacklist_entry(target)
        if entry is None:
            return f"QQ {target} 当前不在黑名单里。查看名单用 {prefix}黑名单"

        owner = str(entry.get("operator") or "").strip()
        is_admin_role = is_admin(self.settings, operator_id)
        if not is_admin_role and owner not in {"auto", str(operator_id)}:
            logger.warning(
                "审核员尝试解封他人封禁的用户，已拒绝：operator=%s target=%s 原操作人=%s",
                operator_id,
                target,
                owner or "未知",
            )
            return (
                f"QQ {target} 是被管理员手动封禁的，审核员不能解封他人封禁的用户。\n"
                "（AI 自动封禁、以及你自己封禁的用户，你可以直接解封。）\n"
                "如需解封这一条，请联系管理员。"
            )

        await self.database.remove_blacklist(target)
        how = "AI 自动封禁" if owner == "auto" else f"管理员 {owner or '未知'} 的封禁"
        self._audit_global(
            f"解除封禁：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜被解封 QQ {target}｜原封禁来源：{how}"
        )
        logger.warning(
            "已解除拉黑：user_id=%s 操作人=%s 原封禁来源=%s", target, operator_id, how
        )
        return f"已解除拉黑 QQ {target}（原封禁来源：{how}），他可以重新投稿了。（已删除的说说不会恢复）"

    async def _cmd_blacklist(self) -> str:
        """列出黑名单（含临时封禁的到期时间）。"""
        prefix = command_prefix_of(self.settings)
        rows = await self.database.list_blacklist()
        if not rows:
            return "黑名单为空。"
        lines = [f"黑名单共 {len(rows)} 人："]
        for item in rows[:20]:
            expiry = _parse_expiry(item.get("until"))
            if expiry is None:
                state = "永久"
            else:
                remain = expiry - _utc_now()
                if remain.total_seconds() <= 0:
                    state = "已到期（自动恢复）"
                else:
                    state = f"到 {format_due_time(self.settings, expiry.timestamp())} 自动恢复"
            lines.append(
                f"· {item['user_id']}"
                f"  {state}"
                f"  操作人={item.get('operator') or '未知'}"
                f"  原因={item.get('reason') or '（无）'}"
            )
        if len(rows) > 20:
            lines.append(f"…另有 {len(rows) - 20} 人（可查数据库 blacklist 表）")
        lines.append(f"解除：{prefix}解封 <QQ号>（等价写法：{prefix}解除拉黑 <QQ号>）")
        return "\n".join(lines)

    # ---------------- 每日额度（重置 / 查询）----------------

    def quota_used(self, user_id: int) -> int:
        """该用户「今天」已经用掉多少条额度（跨天自动按 0 算）。"""
        today = quota_date(self.settings)
        day, count = self._daily_counts.get(int(user_id), ("", 0))
        return count if day == today else 0

    def reset_daily_quota(self, user_id: int) -> bool:
        """把某个用户今天的额度清零；返回「之前是否用过额度」。"""
        entry = self._daily_counts.pop(int(user_id), None)
        return bool(entry and entry[1])

    def reset_all_daily_quota(self) -> int:
        """把所有人今天的额度清零，返回被清零的人数。"""
        today = quota_date(self.settings)
        touched = sum(1 for day, count in self._daily_counts.values() if day == today and count)
        self._daily_counts.clear()
        return touched

    def default_quota_reset_notice(self) -> str:
        """管理员重置某人的额度后，用校园墙号发给那个人的默认提示语。"""
        limit = self.settings.daily_message_limit
        return (
            f"管理员已为你重置今日投稿条数，现在可以继续投稿了。\n"
            f"（每人每天最多 {limit} 条投稿消息，每天 0 点自动重置。）"
        )

    async def _cmd_reset_quota(self, operator_id: int, argument: str) -> str:
        """重置某个用户的每日额度，并让校园墙号给对方发一条提示。

        需求：「管理员可以通过命令重置指定用户和全体用户的每日发言上限，
        为某一用户重置发言上限后会通过校园墙 qq 号向用户发送指定消息进行提示。」
        因此这里支持 `/重置限额 <QQ号> <自定义提示语>`；不写提示语就用内置文案。
        """
        prefix = command_prefix_of(self.settings)
        value = (argument or "").strip()
        parts = value.split(maxsplit=1)
        if not parts or not parts[0].isdigit():
            return (
                f"用法：{prefix}重置限额 <QQ号> [提示语]\n"
                f"例如：{prefix}重置限额 123456789\n"
                f"　　　{prefix}重置限额 123456789 今天的额度已经给你加回来了，注意别再违规\n"
                f"要重置所有人，用 {prefix}重置全体限额。"
            )
        target = int(parts[0])
        custom = parts[1].strip() if len(parts) > 1 else ""
        had = self.reset_daily_quota(target)
        notice = custom or self.default_quota_reset_notice()
        delivered = await self._notify(target, notice)
        self._audit_global(
            f"重置每日额度：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜对象 QQ {target}｜之前已用：{'是' if had else '否'}"
            f"｜给对方的提示：{notice.replace(chr(10), ' ')}｜提示送达：{'是' if delivered else '否'}"
        )
        logger.warning(
            "重置每日额度：target=%s 操作人=%s 之前已用=%s 提示送达=%s",
            target,
            operator_id,
            had,
            delivered,
        )
        head = (
            f"已重置 QQ {target} 今日额度（现在 {self.quota_used(target)}/"
            f"{self.settings.daily_message_limit} 条）。"
        )
        if delivered:
            return f"{head}\n已用本号给对方发送提示：{notice}"
        return (
            f"{head}\n但提示消息没有送达（对方可能没加好友 / NapCat 未连接），"
            "额度已经重置，请自行确认是否需要另行通知。"
        )

    async def _cmd_reset_quota_all(self, operator_id: int) -> str:
        """重置全体用户的每日额度（不给个人发提示，避免一次性刷屏）。"""
        touched = self.reset_all_daily_quota()
        self._audit_global(
            f"重置全体每日额度：操作人 {role_label(self.settings, operator_id)}"
            f" QQ {operator_id}｜受影响人数：{touched}"
        )
        logger.warning("重置全体每日额度：操作人=%s 受影响人数=%d", operator_id, touched)
        return (
            f"已重置全体用户的今日额度（影响 {touched} 人，现在每个人 0/"
            f"{self.settings.daily_message_limit} 条）。\n"
            "说明：这一步**不会**给每个人单独发消息（几十个人同时收到提示就是刷屏）。"
        )

    # ---------------- 人事任免（仅所有者）----------------

    async def _cmd_grant_role(self, operator_id: int, argument: str, *, role_name: str) -> str:
        """给某个 QQ 加管理员 / 审核员（仅所有者可用），结果落盘到 roles.json。"""
        prefix = command_prefix_of(self.settings)
        label = "管理员" if role_name == "admin" else "审核员"
        command = "设置管理员" if role_name == "admin" else "设置审核员"
        value = (argument or "").strip()
        if not value.isdigit():
            return f"用法：{prefix}{command} <QQ号>，例如 {prefix}{command} 123456789"
        target = int(value)
        roles = self.settings.runtime_roles
        qq = _qq(target)
        if role_name == "admin":
            if is_admin(self.settings, target):
                return f"QQ {target} 已经是管理员了（不需要重复设置）。"
            roles.admins.add(qq)
            roles.revoked_admins.discard(qq)
        else:
            if is_reviewer(self.settings, target) and not is_admin(self.settings, target):
                return f"QQ {target} 已经是审核员了（不需要重复设置）。"
            roles.reviewers.add(qq)
            roles.revoked_reviewers.discard(qq)
        saved = roles.save()
        self._audit_global(
            f"设置{label}：操作人 所有者 QQ {operator_id}｜对象 QQ {target}"
            f"｜写入文件：{'成功' if saved else '失败（重启后会丢失）'}"
        )
        logger.warning(
            "设置%s：target=%s 操作人=%s 落盘=%s", label, target, operator_id, saved
        )
        tail = "" if saved else "\n注意：角色文件写入失败，这次改动在重启后会丢失，请检查磁盘权限。"
        return (
            f"已把 QQ {target} 设为{label}。他发「{prefix}帮助」可以看到自己现在能用的命令。"
            f"{tail}"
        )

    async def _cmd_revoke_role(self, operator_id: int, argument: str, *, role_name: str) -> str:
        """撤销某个 QQ 的管理员 / 审核员身份（仅所有者可用）。"""
        prefix = command_prefix_of(self.settings)
        label = "管理员" if role_name == "admin" else "审核员"
        command = "取消管理员" if role_name == "admin" else "取消审核员"
        value = (argument or "").strip()
        if not value.isdigit():
            return f"用法：{prefix}{command} <QQ号>，例如 {prefix}{command} 123456789"
        target = int(value)
        if is_owner(self.settings, target):
            return (
                f"QQ {target} 是所有者（OWNER_QQ），不能被撤职。\n"
                "要更换所有者请改 .env 的 OWNER_QQ 后重启服务。"
            )
        roles = self.settings.runtime_roles
        qq = _qq(target)
        if role_name == "admin":
            if not is_admin(self.settings, target):
                return f"QQ {target} 当前不是管理员，无需撤销。"
            roles.revoked_admins.add(qq)
            roles.admins.discard(qq)
        else:
            if not is_reviewer(self.settings, target):
                return f"QQ {target} 当前不是审核员，无需撤销。"
            roles.revoked_reviewers.add(qq)
            roles.reviewers.discard(qq)
        saved = roles.save()
        self._audit_global(
            f"撤销{label}：操作人 所有者 QQ {operator_id}｜对象 QQ {target}"
            f"｜写入文件：{'成功' if saved else '失败（重启后会丢失）'}"
        )
        logger.warning(
            "撤销%s：target=%s 操作人=%s 落盘=%s", label, target, operator_id, saved
        )
        tail = "" if saved else "\n注意：角色文件写入失败，这次改动在重启后会丢失，请检查磁盘权限。"
        return f"已撤销 QQ {target} 的{label}权限。" f"{tail}"

    # ---------------- 审核操作日志（调取）----------------

    def ensure_submission_log(self, row: Mapping[str, Any]) -> Path:
        """确保这条投稿的存档目录里有一份审核操作日志（没有就按库里的信息补建）。

        为什么要补建：老版本（存档功能上线前）的投稿没有存档目录；管理员照样可能
        要查它的日志。补一份带「投稿编号 / 投稿人 QQ / 投稿时间 / 正文摘要」的头部，
        比回一句「文件不存在」有用得多。
        """
        path = self.submission_folder(row) / AUDIT_LOG_FILENAME
        if path.is_file():
            return path
        summary = re.sub(r"\s+", " ", str(row.get("content") or "")).strip()[:200]
        header = "\n".join(
            [
                "==================== 投稿存档 ====================",
                f"投稿编号：{row.get('display_code') or '（无）'}",
                f"投稿人 QQ：{int(row.get('user_id') or 0)}",
                f"投稿时间：{format_archive_time(str(row.get('display_time') or ''))}",
                f"补建时间：{format_log_time(self.settings)}",
                f"正文摘要：{summary or '（无文字内容）'}",
                "==================== 审核操作日志 ====================",
                "（该投稿在存档功能上线前渲染，目录由本次调取补建）",
            ]
        )
        self._append_text(path, header)
        return path

    async def _cmd_audit_log(self, operator_id: int, argument: str) -> str:
        """把「审核操作日志」文件直接发给管理员（不带编号=全局日志）。"""
        prefix = command_prefix_of(self.settings)
        value = (argument or "").strip()
        if value:
            row, error = await self._locate_submission(value)
            if row is None:
                return (
                    f"用法：{prefix}审核日志 [编号 或 投稿时间]\n"
                    f"{error}\n不带编号则发送全局审核操作日志。"
                )
            path = self.ensure_submission_log(row)
            label = f"投稿 #{int(row['id'])}（{value}）的审核操作日志"
            name = f"审核操作日志_{self.safe_code(row.get('display_code'))}_{int(row['user_id'])}.txt"
        else:
            path = self._audit_log_path
            label = "全局审核操作日志"
            name = AUDIT_LOG_FILENAME
            if not path.is_file():
                # 一条记录都还没有：先把文件建出来，让管理员能拿到「空表」而不是一句报错
                self._append_text(
                    path,
                    f"# 全局审核操作日志（创建于 {format_log_time(self.settings)}，暂无记录）",
                )
        if not path.is_file():
            return f"{label}还没有任何记录（{path} 不存在）。"
        ok, reason = await self.connections.send_private_file(
            operator_id, path, name=name
        )
        self._audit_global(
            f"调取审核操作日志：操作人 {role_label(self.settings, operator_id)} QQ {operator_id}"
            f"｜范围：{label}｜文件：{path.name}｜结果：{'成功' if ok else f'失败（{reason}）'}"
        )
        if not ok:
            logger.error("审核操作日志发送失败：user_id=%s path=%s 原因=%s", operator_id, path, reason)
            return (
                f"日志文件发送失败：{reason}\n"
                f"文件在服务器上：{path}\n"
                "常见原因：NapCat 与机器人不是同一台机器（upload_private_file 要求能读到这个路径）、"
                "或对方不是好友。"
            )
        logger.warning("已发送审核操作日志：user_id=%s path=%s", operator_id, path)
        return f"已把{label}的文件发给你了（{path.name}，{path.stat().st_size} 字节）。"

    # ---------------- 换服务器：清理历史投稿 ----------------

    async def purge_published_before(
        self, cutoff: datetime, *, operator_id: int = 0
    ) -> dict[str, Any]:
        """把「发布时刻早于 cutoff」的已发布投稿从空间删掉，并把库里状态改成 deleted。

        能删到哪些：只删**本程序记下了 qzone_tid 的**投稿。QQ 空间没有「列出全部说说」
        的接口，机器人看不到、也就删不掉手工发的或老版本没入库的说说 —— 那些只能人工处理。

        每条删除之间停 `_DELETE_POST_INTERVAL_SECONDS` 秒：短时间连删几十条很容易被
        空间风控，宁可慢一点。删除结果逐条写进审核操作日志（全局 + 该投稿目录各一份）。
        """
        cutoff_text = cutoff.astimezone(timezone.utc).isoformat(timespec="seconds")
        stats = await self.database.submission_stats()
        rows = await self.database.list_published_before(cutoff_text)
        actor = role_label(self.settings, operator_id) if operator_id else "系统"
        if not rows:
            # 「一条都没删」必须说清楚是哪种情况，否则只能靠翻代码猜：
            # 库里根本没记录（新服务器没搬数据）≠ 记录都在但都早于/晚于截止点。
            self._audit_global(
                f"清理旧说说：操作人 {actor} QQ {operator_id or '-'}"
                f"｜截止 {cutoff_text}（UTC）｜没有命中任何可删记录"
                f"｜库内共 {stats['total']} 条，其中已发布且有 tid {stats['deletable']} 条"
                f"｜记录时间范围 {stats['first'] or '-'} ~ {stats['last'] or '-'}"
            )
            logger.warning(
                "清理旧说说：截止 %s(UTC) 没有命中记录（库内共 %d 条，"
                "已发布且有 tid %d 条，时间范围 %s ~ %s）",
                cutoff_text,
                stats["total"],
                stats["deletable"],
                stats["first"] or "-",
                stats["last"] or "-",
            )
            return {"total": 0, "deleted": [], "failed": [], "stats": stats}
        deleted: list[int] = []
        failed: list[str] = []
        for item in rows:
            submission_id = int(item["id"])
            code = str(item.get("display_code") or submission_id)
            tid = str(item.get("qzone_tid") or "").strip()
            if not tid:
                failed.append(f"#{submission_id}（记录里没有 tid，需手动删）")
                continue
            try:
                await self.publisher.delete_post(tid)
            except Exception as exc:  # 单条失败不能影响其余删除
                failed.append(f"#{submission_id}（{exc}）")
                self._audit_submission(
                    item,
                    f"清理旧说说失败：操作人 {actor} QQ {operator_id or '-'}"
                    f"｜投稿编号 {code}｜tid={tid}｜原因：{exc}",
                )
                logger.error(
                    "清理旧说说失败：id=%s code=%s tid=%s 原因=%s",
                    submission_id, code, tid, exc,
                )
            else:
                await self.database.update_submission(
                    submission_id,
                    status="deleted",
                    reason=f"{actor} {operator_id or '-'} 清理旧说说（发布于 cutoff 之前）",
                )
                deleted.append(submission_id)
                self._audit_submission(
                    item,
                    f"清理旧说说成功：操作人 {actor} QQ {operator_id or '-'}"
                    f"｜投稿编号 {code}｜tid={tid}",
                )
                logger.warning(
                    "清理旧说说成功：id=%s code=%s tid=%s", submission_id, code, tid
                )
            await asyncio.sleep(_DELETE_POST_INTERVAL_SECONDS)
        result: dict[str, Any] = {
            "total": len(rows),
            "deleted": deleted,
            "failed": failed,
            "stats": stats,
        }
        self._audit_global(
            f"清理旧说说：操作人 {actor} QQ {operator_id or '-'}"
            f"｜截止 {cutoff_text}（UTC）｜库里共 {len(rows)} 条"
            f"｜删除成功 {len(deleted)} 条｜失败 {len(failed)} 条"
            + (f"｜失败明细：{'；'.join(failed[:10])}" if failed else "")
        )
        logger.warning(
            "清理旧说说完成：操作人=%s 截止=%s 共=%d 成功=%d 失败=%d",
            operator_id, cutoff_text, len(rows), len(deleted), len(failed),
        )
        return result

    async def _cmd_purge_old(self, operator_id: int, argument: str) -> str:
        """清空「某个日期之前」发布的历史投稿（换新服务器时一次性清理）。

        - 截止点是 DISPLAY_TIMEZONE 的当天 0 点，即「这一天之前的不算，当天起保留」；
        - 只接受所有者（由 _OWNER_ACTIONS 拦），因为它一次能动掉整面墙的历史；
        - 会先回一条「开始清理」的提示再动手：几十条删除要花十几秒，不能让人干等。
        """
        prefix = command_prefix_of(self.settings)
        value = (argument or "").strip()
        if not value:
            return (
                f"用法：{prefix}清理旧说说 <YYYY-MM-DD>\n"
                f"例如：{prefix}清理旧说说 2026-10-31\n"
                "会把这一天之前（不含当天）发布到空间的投稿全部删除；当天与之后的保留。"
            )
        cutoff = parse_date_cutoff(value, self.settings)
        if cutoff is None:
            return (
                f"「{value}」不是有效日期。用法：{prefix}清理旧说说 <YYYY-MM-DD>\n"
                "例如：/清理旧说说 2026-10-31（也接受 2026/10/31、2026年10月31日）"
            )
        now = _utc_now()
        if cutoff > now + timedelta(days=1):
            # 明显是打字打错了（比如把年份写成 2027）：这种输入执行下去会清空整面墙
            return (
                f"截止日期 {value} 在未来（现在 {format_log_time(self.settings)}），"
                "看起来是打错了，本次未执行。\n"
                "如果你确实要清空全部历史，请把日期写成今天或更早。"
            )
        cutoff_local = cutoff.astimezone(resolve_display_timezone(self.settings))
        await self._notify(
            operator_id,
            f"开始清理：删除 {cutoff_local.strftime('%Y-%m-%d %H:%M')} 之前发布到空间的投稿。\n"
            "每删一条间隔半秒（避免被空间风控），数量多的话要等一会儿，删完我再回你结果。",
        )
        result = await self.purge_published_before(cutoff, operator_id=operator_id)
        deleted = result["deleted"]
        failed = result["failed"]
        lines = [
            f"清理完成（截止 {cutoff_local.strftime('%Y-%m-%d %H:%M')}）：",
            f"库里符合条件 {result['total']} 条｜删除成功 {len(deleted)} 条｜失败 {len(failed)} 条。",
        ]
        if failed:
            lines.append("失败明细：" + "；".join(failed[:10]))
            if len(failed) > 10:
                lines.append(f"（另有 {len(failed) - 10} 条未列出，完整记录见审核操作日志）")
        lines.append("逐条记录已写入审核操作日志（全局 + 各投稿存档目录）。")
        if result["total"] == 0:
            stats = result.get("stats") or {}
            lines.append(
                f"没有符合条件的历史投稿（库内共 {stats.get('total', 0)} 条，"
                f"其中已发布且有 tid {stats.get('deletable', 0)} 条）。"
            )
            if stats.get("total", 0) == 0:
                lines.append(
                    "库里一条记录都没有 —— 这通常是新服务器上 data/ 目录没从旧服务器搬过来"
                    "（数据库是空的），机器人也就不知道空间上有哪些说说。"
                )
            elif stats.get("deletable", 0) == 0:
                lines.append(
                    "库里有投稿记录，但没有一条带 qzone_tid —— 它们大概不是本机器人发布成功的"
                    "（旧版本没存 tid，或只是被拒绝、已删除的记录）。"
                )
        lines.append(
            "注意：QQ 空间没有「列出全部说说」的接口，本机器人只能删自己发布过、"
            "且数据库里记下了 tid 的投稿；手工发的、老版本没入库的说说需要你自己在空间里删。"
        )
        return "\n".join(lines)

    async def _cmd_purge_report(self, operator_id: int, argument: str) -> str:
        """清理前的自查：库里有几条、早于截止日的有几条、PURGE_BEFORE 有没有配。

        存在的意义：「清理旧说说跑了但一条没删」的原因可能在 .env、在数据库、在 tid，
        这些从 QQ 上直接就能看出来，不用登服务器翻日志。
        """
        prefix = command_prefix_of(self.settings)
        stats = await self.database.submission_stats()
        configured = (self.settings.purge_before or "").strip()
        lines = ["投稿库概况："]
        lines.append(f"· 全部记录 {stats['total']} 条")
        if stats["by_status"]:
            detail = "、".join(f"{k} {v}" for k, v in sorted(stats["by_status"].items()))
            lines.append(f"· 按状态：{detail}")
        lines.append(f"· 其中「已发布且有空间 tid」（空间上真能删掉）{stats['deletable']} 条")
        lines.append(f"· 记录时间范围：{stats['first'] or '-'} ~ {stats['last'] or '-'}（UTC）")
        value = (argument or "").strip()
        if value:
            cutoff = parse_date_cutoff(value, self.settings)
            if cutoff is None:
                lines.append(f"· 「{value}」不是有效日期，无法统计截止点")
            else:
                cutoff_text = cutoff.astimezone(timezone.utc).isoformat(timespec="seconds")
                rows = await self.database.list_published_before(cutoff_text)
                local = cutoff.astimezone(resolve_display_timezone(self.settings))
                lines.append(
                    f"· 早于 {local.strftime('%Y-%m-%d %H:%M')}（{cutoff_text} UTC）"
                    f"的已发布投稿：{len(rows)} 条"
                )
                if rows:
                    examples = "、".join(
                        str(row.get("display_code") or row["id"]) for row in rows[:8]
                    )
                    lines.append(f"  例：{examples}" + ("…" if len(rows) > 8 else ""))
        lines.append(f"· PURGE_BEFORE（启动时自动清理）：{configured or '未设置'}")
        if stats["deletable"] == 0:
            lines.append(
                "库里没有可删的说说 —— 空间上还留着的旧说说多半不是本机器人发布的"
                "（或旧版本没把 tid 入库），这类只能手动删。"
            )
        lines.append(
            f"用法：{prefix}清理旧说说 <YYYY-MM-DD> 执行清理；"
            f"{prefix}清理诊断 2026-10-31 只统计、不删除。"
        )
        return "\n".join(lines)

    # ---------------- 会话入口 ----------------

    async def handle_private_message(self, event: dict[str, Any]) -> None:
        """处理私聊消息：过滤推广 → 追加到会话 → 重置空闲定时器。"""
        user_id = int(event.get("user_id") or 0)
        if user_id <= 0:
            logger.warning("私聊消息缺少 user_id，已忽略")
            return

        raw_segments = event.get("message")
        segments = parse_message_segments(raw_segments, self.settings)
        # 经典表情只有 ID，套用可配置的图源模板（未配置则保持文字占位）
        apply_face_image_template(segments, self.settings)
        full_text = "".join(seg.text for seg in segments if seg.kind == "text")

        # 白名单命令：这条消息不投稿，直接执行命令。
        # 必须放在推广/系统消息过滤之前 —— 否则命令文本一旦命中关键词就会被悄悄丢掉。
        if looks_like_command(full_text, self.settings):
            if is_staff(self.settings, user_id):
                await self._run_admin_command(user_id, full_text)
            else:
                logger.warning(
                    "白名单外的用户尝试执行命令，已忽略：user_id=%s 内容=%r",
                    user_id,
                    full_text[:40],
                )
            return

        # 被拉黑的人：不收稿、不发布（给一次提示，免得他反复发）
        if await self.database.is_blacklisted(user_id):
            logger.info("该用户已被拉黑，本条消息未收录：user_id=%s", user_id)
            await self._notify_blocked(user_id)
            return

        # 暂停期间：不收稿、不发布（回复一次即可，别让提示自己刷屏）
        if self._paused:
            logger.info("服务处于暂停状态，本条消息未收录：user_id=%s", user_id)
            await self._notify_paused(user_id)
            return

        # 推广消息 / 系统消息（加好友验证语等）：整条事件丢弃，绝不作为投稿。
        if contains_promo(full_text, self.settings.promo_keywords):
            logger.info("命中推广关键词，已忽略该条消息：user_id=%s", user_id)
            return
        if contains_any(full_text, self.settings.blocked_keywords):
            logger.info("命中系统消息关键词（加好友验证语等），已忽略该条消息：user_id=%s", user_id)
            return

        if not segments:
            logger.debug("消息无可处理内容，已忽略：user_id=%s", user_id)
            return

        # 防刷屏：占配额（只统计真正会被收录的消息；推广/系统消息在上面已经丢弃，不占额度）
        wait_seconds = self.consume_message_quota(user_id)
        if wait_seconds is not None:
            await self._notify_rate_limited(user_id, wait_seconds)
            return

        session = self.sessions.get(user_id)
        if session is None:
            session = SubmissionSession(user_id=user_id)
            self.sessions[user_id] = session
            logger.info("开启新的投稿会话：user_id=%s", user_id)

        sender = event.get("sender") or {}
        if isinstance(sender, dict):
            nickname = str(sender.get("card") or sender.get("nickname") or "").strip()
            if nickname:
                session.nickname = nickname

        segments, dropped_photos, dropped_stickers = self._apply_image_cap(session, segments)
        if dropped_photos or dropped_stickers:
            await self._notify_image_cap(user_id, dropped_photos, dropped_stickers)
        if not segments:
            # 全是超限的图片：本条不收录，也不该重置空闲定时器（否则用户的等待被无限顺延）
            # 额度是给「发出去的消息」计数的，这条没被收下，把刚扣的那 1 条还回去。
            self.refund_message_quota(user_id)
            logger.info("本条消息的图片全部超过上限，未收录：user_id=%s", user_id)
            return

        session.messages.extend(segments)
        session.updated_at = time.time()
        await self._arm_timer(user_id)

    def _apply_image_cap(
        self, session: SubmissionSession, segments: list[CollectedMessage]
    ) -> tuple[list[CollectedMessage], int, int]:
        """按「照片额度」与「表情额度」两条独立上限裁剪本次消息。

        返回（保留的段, 被丢弃的照片数, 被丢弃的表情数）。

        为什么在收稿时就裁掉，而不是等到发布时再拒：
          ① 没送审的图片**绝不能**进公开截图，所以「收录张数」必须等于「送审张数」；
          ② 收稿时裁掉能立刻告诉用户「请分次发送」，不用让他白等一轮发布；
          ③ 顺手把单次投稿的内存封了顶（每张图最大 MAX_DOWNLOAD_BYTES，
             张数不限的话一条消息就能把内存吃光）。
        表情与照片分开计数：表情只进截图、不单独发布，用户发 4 张照片再配几个表情
        不该被「图片太多」挡住；但表情仍然要送审（DEC-9）。
        """
        photo_cap = self.settings.moderation_max_images
        sticker_cap = self.settings.max_stickers_per_submission
        photos_used = sum(
            1 for msg in session.photo_messages() if msg.image_url or msg.image_bytes
        )
        stickers_used = sum(
            1 for msg in session.sticker_messages() if msg.image_url or msg.image_bytes
        )
        kept: list[CollectedMessage] = []
        dropped_photos = dropped_stickers = 0
        for segment in segments:
            if not (segment.image_url or segment.image_bytes):
                kept.append(segment)
                continue
            if is_sticker_message(segment):
                if sticker_cap > 0 and stickers_used >= sticker_cap:
                    dropped_stickers += 1
                    continue
                stickers_used += 1
            else:
                if photo_cap > 0 and photos_used >= photo_cap:
                    dropped_photos += 1
                    continue
                photos_used += 1
            kept.append(segment)
        return kept, dropped_photos, dropped_stickers

    async def _notify_image_cap(
        self, user_id: int, dropped_photos: int, dropped_stickers: int
    ) -> None:
        """图片超限时提示用户；带冷却，避免连发时提示自己刷屏。"""
        photo_cap = self.settings.moderation_max_images
        sticker_cap = self.settings.max_stickers_per_submission
        logger.info(
            "本次投稿图片超过上限：user_id=%s 照片上限=%d 丢弃照片=%d 表情上限=%d 丢弃表情=%d",
            user_id,
            photo_cap,
            dropped_photos,
            sticker_cap,
            dropped_stickers,
        )
        now = time.monotonic()
        cooldown = max(0.0, self.settings.rate_limit_notice_cooldown_seconds)
        last_notice = self._last_image_cap_notice.get(user_id)
        if last_notice is not None and now - last_notice < cooldown:
            return
        self._last_image_cap_notice[user_id] = now
        parts: list[str] = []
        if dropped_photos:
            parts.append(
                f"照片最多 {photo_cap} 张，超出的 {dropped_photos} 张没有收录；"
                f"请分几次发送（每次不超过 {photo_cap} 张照片）。"
            )
        if dropped_stickers:
            parts.append(
                f"表情包最多 {sticker_cap} 个，超出的 {dropped_stickers} 个没有收录。"
            )
        await self._notify(
            user_id,
            "本次投稿有内容没有收录：\n" + "\n".join(parts) + "\n文字可以照常发。",
        )

    def _cancel_timer(self, session: SubmissionSession) -> None:
        """取消该会话「尚未完成」的旧定时器。

        必须排除当前正在执行的任务：空闲定时器到点后会调用 publish_session()，此刻
        session.timer 就是当前任务本身；对它调用 cancel() 等于给正在执行的发布流程挂上
        取消请求，下一个真正挂起的位置（下载图片/头像、调用审核、发布）就会抛
        CancelledError，表现为「流程停在生成截图，既不回复也不发布」。

        @decision DEC-6 定时器取消必须与 current_task() 比对，禁止取消自身。
        """
        timer = session.timer
        if timer is None or timer.done():
            return
        if timer is asyncio.current_task():
            # 定时器触发的发布流程：这个任务马上就结束了，无需（也不能）取消。
            return
        timer.cancel()

    # ---------------- 防刷屏（每日额度，0 点重置） ----------------

    def consume_message_quota(self, user_id: int) -> float | None:
        """为一条消息占用「今天的」额度。

        返回 None 表示放行；返回 float 表示今天的额度已用完，值为「距离下一个 0 点还有多少秒」。
        只统计真正会被收录的消息 —— 推广 / 系统消息在调用前就被丢弃，不占额度；
        被拒的消息不计数，因此不会白白用掉用户的额度。

        **管理员（含所有者）不受限制**（沿用旧需求）：他们要发通知/公告，不能被 9 条卡住。
        审核员仍然受限 —— 他们本来就是「帮忙看号」的人，没有豁免的必要。

        为什么要按「额度日」存而不是滑动窗口：需求是「每日 9 条，每日 0 点重置」。
        滑动窗口做不到「0 点统一归零」，还会让用户看到「过了零点还要等 3 小时」。
        停服跨天也不会有问题：日期一变，计数自然视为 0。
        """
        if is_admin(self.settings, user_id):
            return None
        limit = int(self.settings.daily_message_limit)
        if limit <= 0:
            return None

        today = quota_date(self.settings)
        day, count = self._daily_counts.get(int(user_id), ("", 0))
        if day != today:
            count = 0
        if count >= limit:
            return seconds_until_quota_reset(self.settings)
        self._daily_counts[int(user_id)] = (today, count + 1)
        self._sweep_quota_counters(today)
        return None

    def refund_message_quota(self, user_id: int) -> None:
        """把刚占用的一条额度还回去。

        用于「这条消息最终没有收录」的路径（例如图片全部超过上限被丢弃）：
        额度算的是「发出去的消息」，一条没被收下的消息不该让用户白白少一次机会。
        """
        if is_admin(self.settings, user_id):
            return
        entry = self._daily_counts.get(int(user_id))
        if not entry:
            return
        day, count = entry
        if day != quota_date(self.settings) or count <= 0:
            return
        self._daily_counts[int(user_id)] = (day, count - 1)

    def _sweep_quota_counters(self, today: str) -> None:
        """周期性清理「往日」的记录，避免长期运行后字典随用户数无限增长。

        每 500 次调用清一次；只删日期不是今天的条目 —— 今天的计数一个都不能丢，
        否则用户会发现「额度忽然又满了」。
        """
        self._rate_sweep_tick += 1
        if self._rate_sweep_tick % 500:
            return
        stale = [uid for uid, (day, _count) in self._daily_counts.items() if day != today]
        for uid in stale:
            self._daily_counts.pop(uid, None)
            self._last_rate_notice.pop(uid, None)
            self._last_pause_notice.pop(uid, None)
            self._last_image_cap_notice.pop(uid, None)

    async def _notify_rate_limited(self, user_id: int, wait_seconds: float) -> None:
        """超限时提示用户；带冷却，避免连发时「提示」自己变成刷屏。"""
        logger.info(
            "今日投稿条数已用完，本条未收录：user_id=%s 距 0 点=%.0fs", user_id, wait_seconds
        )
        now = time.monotonic()
        cooldown = max(0.0, self.settings.rate_limit_notice_cooldown_seconds)
        last_notice = self._last_rate_notice.get(user_id)
        if last_notice is not None and now - last_notice < cooldown:
            logger.info("超限提示处于冷却期，本次不重复提示：user_id=%s", user_id)
            return
        self._last_rate_notice[user_id] = now
        await self._notify(user_id, format_rate_limit_notice(self.settings, wait_seconds))

    async def _arm_timer(self, user_id: int) -> None:
        """重置该用户的空闲定时器：取消旧的，按当前时间重新计时。"""
        session = self.sessions.get(user_id)
        if session is None:
            return
        self._cancel_timer(session)
        session.timer = asyncio.create_task(self._idle_then_publish(user_id))

    async def _idle_then_publish(self, user_id: int) -> None:
        """空闲计时到期：投稿人「发完了」→ **立刻开始渲染**并结束本次投稿。

        需求：「每个投稿都是在最后一条消息发送的一分钟后开始渲染，并结束本次投稿」。
        因此这里不再排队、不再等整点：睡满 idle_timeout_seconds 直接走 publish_session()，
        发布流程内部会 pop 掉会话，本次投稿就此结束（新消息会开启新的一次）。
        """
        try:
            await asyncio.sleep(self.settings.idle_timeout_seconds)
            logger.info(
                "最后一条消息后已静默 %.0f 秒，开始渲染本次投稿：user_id=%s",
                self.settings.idle_timeout_seconds,
                user_id,
            )
            await self.publish_session(user_id)
        except asyncio.CancelledError:
            raise  # 有新消息 → 定时器被取消，属正常路径
        except Exception:
            logger.exception("投稿渲染/发布流程异常：user_id=%s", user_id)
            await self._notify(user_id, "投稿处理失败，请稍后重新发送或联系管理员。")

    # ---------------- 发布流程 ----------------

    async def publish_session(
        self, user_id: int, session: SubmissionSession | None = None
    ) -> dict[str, Any] | None:
        """取出会话并完成「截图 → 存档 → 审核 → 发布 → 回复」全流程。

        session 不传就从内存会话里取（正常路径：空闲定时器到点后调用它）。
        调用即代表本次投稿结束：会话在开头就被 pop 掉，之后的消息属于新的一次投稿。
        """
        if session is None:
            session = self.sessions.pop(user_id, None)
        elif self.sessions.get(user_id) is session:
            # 同一个会话对象：正常路径下从内存里摘掉，避免被重复发布
            self.sessions.pop(user_id, None)
        if self._paused:
            # 双保险：set_paused 已经取消过所有定时器，这里防的是「已经触发、
            # 正在执行」的竞态 —— 暂停期间绝不发布，宁可丢掉这次投稿。
            logger.warning(
                "服务处于暂停状态，本次投稿已丢弃：user_id=%s 段数=%d",
                user_id,
                len(session.messages) if session is not None else 0,
            )
            return None
        if session is None or not session.messages:
            return None
        # 手动路径下这里会是「真正挂着的旧定时器」；定时器自身触发时则是当前任务（跳过）。
        self._cancel_timer(session)

        text = session.text_content()
        anonymous = wants_anonymous(text, self.settings.anonymous_keywords)
        sticker_count = len(session.image_segments()) - len(session.publish_image_segments())
        # 管理员的投稿要在截图里带标记（一般读者据此看出这是管理员发的内容）
        is_admin_poster = is_admin(self.settings, user_id)
        badge_bytes = admin_badge_bytes(self.settings) if is_admin_poster else None
        logger.info(
            "投稿流程开始：user_id=%s 段数=%d 匿名=%s 图片=%d 贴纸=%d 表情=%d 管理员标记=%s",
            user_id,
            len(session.messages),
            anonymous,
            len(session.image_segments()),
            sticker_count,
            len(session.face_segments()),
            "开" if badge_bytes else "关",
        )

        # 1) 生成合并截图
        # 先定下「编号」与「投稿时间」：这两个值是管理员日后从截图里反查投稿人的唯一依据，
        # 所以必须与截图里真实渲染出来的字符串**完全一致**（不能用两次不同的时间）。
        submission_code = generate_submission_code()
        display_time = format_submission_time(self.settings)
        screenshot_started = time.perf_counter()
        # 逐张记录「哪张图没读进来、为什么」——「图片没能读取成功」这句太笼统，
        # 用户按它根本不知道该改什么（重发？少发？换格式？）。
        photo_failures: list[str] = []
        logger.info(
            "[1/4] 开始生成截图：user_id=%s 编号=%s 管理员标记=%s",
            user_id,
            submission_code,
            "有" if badge_bytes else "无",
        )
        try:
            screenshot = await render_screenshot(
                session,
                anonymous=anonymous,
                settings=self.settings,
                http_client=self.http_client,
                output_dir=self._screenshot_dir,
                submission_code=submission_code,
                display_time=display_time,
                badge_bytes=badge_bytes,
                failures=photo_failures,
            )
        except asyncio.CancelledError:
            raise  # 外部取消（进程退出 / 被新逻辑取消）必须继续向上传播
        except _ImageBudgetExceeded as exc:
            # 体积超预算：整条不发（截图少画几张图而用户以为发全了，比明说没发更糟）
            logger.error(
                "[1/4] 截图素材超过体积预算，终止本次发布：user_id=%s 原因=%s", user_id, exc
            )
            await self.database.insert_submission(
                user_id=user_id, content=text, images=[], status="failed",
                risk_level=None, reason=f"图片体积超过预算：{exc}",
            )
            await self._notify(
                user_id,
                f"本次投稿的图片总体积过大（{exc}），未发布。\n"
                "请减少图片数量，或把图片压缩后再发送。",
            )
            return None
        except Exception:
            logger.exception(
                "[1/4] 截图失败：user_id=%s 耗时=%.2fs", user_id, time.perf_counter() - screenshot_started
            )
            await self._notify(user_id, "投稿截图生成失败，请稍后重试。")
            await self.database.insert_submission(
                user_id=user_id, content=text, images=[], status="failed",
                risk_level=None, reason="截图生成失败",
            )
            return None
        logger.info(
            "[1/4] 截图完成：user_id=%s path=%s 耗时=%.2fs",
            user_id,
            screenshot,
            time.perf_counter() - screenshot_started,
        )

        # 2) 单独保存原图（仅 type == "image"；表情包不单独发布）
        originals_started = time.perf_counter()
        originals = await self._save_original_images(session)
        logger.info(
            "[2/4] 原图保存完成：user_id=%s 张数=%d 耗时=%.2fs",
            user_id,
            len(originals),
            time.perf_counter() - originals_started,
        )

        # 2.5) 存档：**只要渲染出来了就存**（需求：所有渲染的投稿都要单独文件夹存档）。
        # 放在审核之前：被审核拒绝的投稿同样是一份「渲染出来的投稿」，一样要留档。
        archive_folder = await self.archive_submission(
            session,
            screenshot=screenshot,
            submission_code=submission_code,
            display_time=display_time,
            anonymous=anonymous,
            originals=originals,
        )
        # 审核/发布阶段要往「这条投稿的审核操作日志」里追加记录；此时数据库行还没建，
        # 用编号 + 投稿人 QQ 就足以定位到同一个存档目录。
        audit_row: dict[str, Any] = {"display_code": submission_code, "user_id": user_id}

        # 3) 审核：**凡是画进了截图的图片都必须一起送审**（走视觉模型）
        #
        # 关键不变式（@decision DEC-9）：公开产物里的每一张图，都必须被模型看过。
        # 截图里既可能有原图，也可能有表情/贴纸（kind == "face"），所以判据是
        # 「拿到了字节、会被渲染」而不是「kind == image」—— 只按 kind 过滤会漏审表情。
        moderation_started = time.perf_counter()
        photos = session.image_segments()                    # 原图/贴纸（kind == "image"）
        rendered_images = session.rendered_image_messages()   # 真正拿到字节、会画进截图的全部图片
        rendered_photos = [msg for msg in rendered_images if msg.kind == "image"]
        # 有**照片**、却一张都没能读出来：截图里只有「[图片加载失败]」占位文本。
        # 模型看不到图只会回「仅包含图片，无法审核」这种让人一头雾水的理由，
        # 这里直接拦下并换上准确的原因，别把它推给模型猜。
        # （表情不适用这一条：取不到图就退回「[表情 28]」文字占位，不该拖垮整次投稿。）
        if photos and not rendered_photos:
            detail = "；".join(dict.fromkeys(photo_failures)) or "图片全部未能读取（原因未知）"
            logger.error(
                "[3/4] 图片全部未能读取，终止本次发布：user_id=%s 图片段=%d 张 详情=%s",
                user_id,
                len(photos),
                detail,
            )
            await self.database.insert_submission(
                user_id=user_id, content=text, images=[str(screenshot)], status="failed",
                risk_level=None, reason=f"图片未能送审：{detail}",
            )
            await self._notify(
                user_id,
                f"你发的 {len(photos)} 张图片都没能读取成功，本次未发布。\n"
                f"原因：{detail}\n"
                "可以这样处理：\n"
                "· 等几秒重新发一次（图片刚发出时服务端可能还没准备好，重发通常就好）\n"
                "· 换一张图，或先「保存到相册」再发（某些格式与超长截图读不出来）\n"
                f"· 别太大：单张不超过 {self.settings.max_image_pixels // 10000} 万像素，"
                f"单次总体积不超过 {self.settings.max_submission_image_bytes // 1048576} MiB\n"
                "一直失败就联系管理员。"
            )
            return None
        image_blocks, uncovered = build_image_blocks_with_skips(
            (message.image_bytes for message in rendered_images),
            self.settings,
            user_id=user_id,
        )
        # 有图片没能送审（超张数上限 / 格式不支持 / 体积超预算）→ **整条不发布**。
        # 以前这里只判「一张都没送审」，于是「第 5 张图」会绕过审核直接进截图和原图（ERR-016）。
        if uncovered:
            reason = "；".join(dict.fromkeys(uncovered))
            logger.error(
                "[3/4] 有图片未能送审，终止本次发布：user_id=%s 可见=%d 张 送审=%d 张 原因=%s",
                user_id,
                len(rendered_images),
                len(image_blocks),
                reason,
            )
            await self.database.insert_submission(
                user_id=user_id, content=text, images=[str(screenshot)], status="failed",
                risk_level=None, reason=f"有图片未能送审：{reason}",
            )
            limit = self.settings.moderation_max_images
            hint = (
                f"请分几次发送：一次不超过 {limit} 张照片（表情包另算）。"
                if limit > 0
                else "请减少图片数量后重新发送。"
            )
            await self._notify(
                user_id,
                f"本次投稿有 {len(rendered_images) - len(image_blocks)} 张图片没能送审（{reason}）。\n"
                f"为避免未经审核的图片被发布，本次未发布。{hint}",
            )
            return None
        logger.info(
            "[3/4] 审核开始：user_id=%s 文字长度=%d 随附图片=%d 张 模型=%s 思考=%s",
            user_id,
            len(text),
            len(image_blocks),
            self.settings.deepseek_vision_model if image_blocks else self.settings.deepseek_model,
            self.settings.moderation_thinking,
        )
        try:
            moderation = await call_deepseek_moderation(
                self._build_moderation_text(
                    session,
                    text,
                    len(image_blocks),
                    await self.database.recent_rejected_texts(user_id, limit=3),
                ),
                self.settings,
                image_blocks=image_blocks,
                user_id=user_id,
            )
        except asyncio.CancelledError:
            raise
        except ModerationUnavailable as exc:
            logger.error(
                "[3/4] 审核不可用：user_id=%s 耗时=%.2fs 原因=%s",
                user_id,
                time.perf_counter() - moderation_started,
                exc,
            )
            await self.database.insert_submission(
                user_id=user_id, content=text, images=[str(screenshot)], status="failed",
                risk_level=None, reason=f"审核服务不可用：{exc}",
            )
            await self._notify(user_id, "审核服务暂时不可用，本次未发布，请稍后重新发送投稿。")
            return None
        logger.info(
            "[3/4] 审核完成：user_id=%s approved=%s risk_level=%s 耗时=%.2fs",
            user_id,
            moderation.approved,
            moderation.risk_level,
            time.perf_counter() - moderation_started,
        )

        submission_id = await self.database.insert_submission(
            user_id=user_id,
            content=text,
            images=[str(screenshot), *originals],
            status="pending",
            risk_level=moderation.risk_level,
            reason=moderation.reason,
            display_code=submission_code,
            display_time=display_time,
        )
        self._audit_submission(
            audit_row,
            f"系统审核：{'通过' if moderation.approved else '不通过'}"
            f"｜风险等级：{moderation.risk_level}｜类别：{moderation.category}"
            f"｜原因：{moderation.reason}｜投稿记录 #{submission_id}",
        )

        if not moderation.approved:
            await self.database.update_submission(
                submission_id, status="rejected", risk_level=moderation.risk_level, reason=moderation.reason
            )
            await self._notify(user_id, f"投稿未通过审核：{moderation.reason}")
            # 多次被拒 → 限期封禁（"换隐晦说法反复重发"就靠这里兜住）
            await self._maybe_auto_ban(user_id, moderation.reason)
            return {"status": "rejected", "reason": moderation.reason, "id": submission_id}

        # 4) 发布：截图第一张，原图依次跟在后面；超出上限的部分截断并告知用户
        publish_paths = [str(screenshot), *originals]
        truncated = 0
        if len(publish_paths) > self.settings.max_publish_images:
            truncated = len(publish_paths) - self.settings.max_publish_images
            publish_paths = publish_paths[: self.settings.max_publish_images]

        publish_started = time.perf_counter()
        logger.info(
            "[4/4] 空间发布开始：user_id=%s 图片=%d 截断=%d 明细=%s",
            user_id,
            len(publish_paths),
            truncated,
            _describe_publish_paths(publish_paths),
        )
        try:
            result = await self.publisher.publish(self.settings.publish_caption, publish_paths)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            logger.exception(
                "[4/4] 空间发布失败：user_id=%s 耗时=%.2fs", user_id, time.perf_counter() - publish_started
            )
            await self.database.update_submission(
                submission_id, status="failed", risk_level=moderation.risk_level, reason=f"发布失败：{exc}"
            )
            self._audit_submission(audit_row, f"系统发布失败：{exc}")
            await self._notify(user_id, "投稿已通过审核，但空间发布失败，请联系管理员。")
            return {"status": "failed", "reason": str(exc), "id": submission_id}

        publish_elapsed = time.perf_counter() - publish_started
        await self.database.update_submission(
            submission_id,
            status="published",
            risk_level=moderation.risk_level,
            reason=moderation.reason,
            # tid 存下来是为了日后能删 —— 没有它就没法定位空间里的那条说说
            qzone_tid=str(result.get("tid") or "").strip() or None,
        )
        self._audit_submission(
            audit_row,
            f"系统发布成功：空间 tid={result.get('tid')}"
            f"｜图片 {len(publish_paths)} 张（截断 {truncated} 张）"
            + (f"｜存档目录：{archive_folder.name}" if archive_folder else "｜（存档失败，见日志）"),
        )
        reply = "投稿已发布"
        if truncated:
            reply += f"（本篇图片较多，已保留前 {self.settings.max_publish_images} 张，其余 {truncated} 张未发布）"
        delivered = await self._notify(user_id, reply)
        logger.info(
            "[4/4] 空间发布完成：user_id=%s id=%s tid=%s 耗时=%.2fs 回复已送达=%s",
            user_id,
            submission_id,
            result.get("tid"),
            publish_elapsed,
            delivered,
        )
        return {"status": "published", "id": submission_id, "result": result, "truncated": truncated}

    async def _save_original_images(self, session: SubmissionSession) -> list[str]:
        """下载并保存要单独发布的原图，返回本地路径列表。

        表情/贴纸不在其中（见 `SubmissionSession.publish_image_segments`）：它们只出现在
        合并截图里，不再作为原图单独发一条。
        字节在下载阶段已经统一成 JPEG/PNG/GIF（这里再校验一次是幂等的），
        因此不会再出现「审核跳过了这张图、发布时却要上传它」的错位。
        单张失败只跳过该图并记录日志（放行 + 标记），不影响其余原图与截图发布。
        """
        self._image_dir.mkdir(parents=True, exist_ok=True)
        saved: list[str] = []
        skipped = 0
        candidates = session.publish_image_segments()
        stickers = len(session.image_segments()) - len(candidates)
        if stickers:
            logger.info("有 %d 张表情/贴纸只进截图，不单独发布为原图", stickers)
        for index, message in enumerate(candidates):
            try:
                # 截图阶段已经下载过的图片直接复用字节，避免同一张图下载两次
                # （HTTP_TIMEOUT 是单次请求超时，重复下载会把单张投稿的整体耗时翻倍）。
                data = message.image_bytes
                if data is None:
                    data = await download_asset(self.http_client, message.image_url, self.settings)
                # 转码是同步 CPU 工作，放线程里做，别卡住事件循环
                prepared = await asyncio.to_thread(
                    _prepare_image_for_publish,
                    data,
                    message.image_url,
                    max_pixels=self.settings.max_image_pixels,
                )
                if prepared is None:
                    skipped += 1
                    continue
                payload, suffix = prepared
                filename = (
                    f"image_{session.user_id}_{int(time.time())}_{index}_{uuid.uuid4().hex[:8]}"
                    f"{suffix}"
                )
                target = _safe_join(self._image_dir, filename)
                target.write_bytes(payload)
                message.image_path = str(target)
                saved.append(str(target))
            except asyncio.CancelledError:
                raise  # 外部取消不能被当成「单图失败」吞掉
            except Exception:
                logger.warning("原图下载失败，已跳过该图：%s", message.image_url, exc_info=True)
                skipped += 1
        if skipped:
            logger.warning("有 %d 张图片未能进入发布列表（格式不支持或下载失败）", skipped)
        return saved

    @staticmethod
    def _build_moderation_text(
        session: SubmissionSession,
        text: str,
        attached_images: int,
        rejected_history: Sequence[str] = (),
    ) -> str:
        """组装送审文本：正文 + 投稿形态说明（图片送审张数要写清楚）。

        rejected_history 是该用户**最近被拒的正文**（由调用方查库后传入，本函数保持纯同步）：
        审核是逐条判定的，换一个说法重发同一条违规内容就能绕过去；
        把这些上下文交给模型，它才能判断「这条只是上一条的谐音/缩写版」。
        """
        images = len(session.image_segments())
        faces = len(session.face_segments())
        stickers = images - len(session.publish_image_segments())
        parts = [text if text.strip() else "（本次投稿没有文字内容）"]
        if images:
            parts.append(f"[本次投稿包含 {images} 张图片，其中 {attached_images} 张已随本请求送审]")
        if stickers:
            parts.append(f"[其中 {stickers} 张是表情/贴纸，只会出现在截图里，不会单独发布]")
        if faces:
            parts.append(f"[本次投稿包含 {faces} 个表情，表情只出现在截图里、不单独发布]")
        shown = "；".join(item.strip()[:120] for item in rejected_history if item and item.strip())
        if shown:
            parts.append(
                "[该投稿人最近被审核拒绝过的内容（仅用于判断是否在换说法重发同一件事；"
                f"若本条只是换个说法重发同样的违规内容，同样必须拒绝）：{shown}]"
            )
        return "\n".join(parts)

    async def _notify(self, user_id: int, message: str) -> bool:
        """回复用户（失败仅记录日志，不向上抛出，避免影响主流程状态落库）。"""
        delivered = await self.connections.send_private_msg(user_id, message)
        if not delivered:
            logger.warning("回复未送达：user_id=%s message=%s", user_id, message)
        return delivered

    async def shutdown(self) -> None:
        """取消全部定时器（进程退出时调用）；不影响正在执行的发布任务。"""
        for session in list(self.sessions.values()):
            self._cancel_timer(session)


def _guess_suffix(url: str) -> str:
    """从 URL 猜图片后缀，未知则用 .jpg；仅白名单后缀，避免写入奇怪文件。"""
    lowered = url.split("?", 1)[0].lower()
    for suffix in (".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp"):
        if lowered.endswith(suffix):
            return suffix
    return ".jpg"


# --------------------------------------------------------------------------------------
# 十、事件分发
# --------------------------------------------------------------------------------------


# 同意好友请求后往往会「立刻」发消息，而好友关系这时可能还没生效，第一次发送会失败，
# 所以退避重试几次。测试会把这里替换成 (0.0, 0.0, 0.0)，避免真的等 10 秒。
_FRIEND_WELCOME_RETRY_DELAYS: tuple[float, ...] = (1.0, 3.0, 6.0)


def _seconds_to_minutes(seconds: float) -> int:
    """把秒数换算成文案里的「分钟」；不足 1 分钟也按 1 分钟表述。"""
    if seconds <= 0:
        return 1
    return max(1, int(round(seconds / 60.0)))


def _join_contacts(contacts: Iterable[str]) -> str:
    """把联系方式渲染成「111 或 222」；只有一个就直接返回，没有则返回空串。

    支持配多个是实际需要：账号主人之外还有别人帮忙看号，用户找谁都行。
    """
    items = [str(item).strip() for item in contacts if str(item).strip()]
    if not items:
        return ""
    if len(items) == 1:
        return items[0]
    return "、".join(items[:-1]) + " 或 " + items[-1]


def render_friend_welcome(settings: Settings) -> str:
    """渲染「加好友后」的使用说明。

    文案里的等待时长与每日上限都取自**实际配置**，所以改了 IDLE_TIMEOUT_SECONDS /
    DAILY_MESSAGE_LIMIT 之后，说明不会和真实行为不一致。
    自定义文案（FRIEND_WELCOME_MESSAGE）支持占位符
    {idle_minutes} {support_qq} {rate_limit_max_messages} {rate_limit_window_minutes}
    {rate_limit_window} {daily_limit}。
    其中 {rate_limit_max_messages} / {daily_limit} 都是**每日**条数上限（老模板继续能用），
    {rate_limit_window_minutes} 固定为 1440（一天），{rate_limit_window} 固定为「一天」。
    """
    context = {
        "idle_minutes": str(_seconds_to_minutes(settings.idle_timeout_seconds)),
        "support_qq": _join_contacts(settings.support_contact_qq),
        "rate_limit_max_messages": str(settings.daily_message_limit),
        "rate_limit_window_minutes": "1440",
        "rate_limit_window": "一天",
        "daily_limit": str(settings.daily_message_limit),
    }
    template = settings.friend_welcome_message.strip()
    if template:
        try:
            return template.format(**context)
        except (KeyError, IndexError, ValueError):
            # 自定义文案里可能有 JSON 之类的大括号，占位符解析失败就按原文发送
            logger.warning("FRIEND_WELCOME_MESSAGE 的占位符无法解析，按原文发送")
            return template

    notes = [
        "每条投稿都会先自动审核，通过后才会出现；",
        "想匿名投稿，在内容里写上「匿名」即可；",
    ]
    if settings.daily_message_limit > 0:
        notes.append(
            f"每人每天最多发 {settings.daily_message_limit} 条投稿消息，每天 0 点自动重置，"
            "超了会有提示；"
        )
    notes.append("请勿发布广告推广（群号、二维码、引流文案），也不要有血腥暴力色情内容 —— 这类投稿会被拒绝或删除。")

    when_text = (
        f"收到你的最后一条消息后，我会等约 {context['idle_minutes']} 分钟确认你发完了，"
        "然后自动审核并发布到 QQ 空间 —— 这段时间里你还可以继续补充或修改，"
        "发完不用催，等一下就会出现在空间里。"
    )

    parts = [
        "你好呀，我是校园墙投稿号，已经通过你的好友申请啦～",
        "",
        "【怎么投稿】直接把文字或图片发给我就行，可以分几条消息发，"
        "我会自动合并成同一条投稿。",
        f"【什么时候发出去】{when_text}",
        "",
        "【其他说明】",
    ]
    parts.extend(f"{index}. {note}" for index, note in enumerate(notes, start=1))
    if context["support_qq"]:
        parts.append("")
        parts.append(f"有疑问可以联系 QQ {context['support_qq']}。")
    return "\n".join(parts)


def _onebot_failure_reason(response: Any) -> str:
    """判断 OneBot 动作响应是成功还是失败；失败返回原因，成功返回空串。"""
    if not isinstance(response, dict):
        # 拿不到结构化响应时不判失败：宁可认为发成功，也不要把成功当失败反复重试
        return ""
    status = str(response.get("status") or "").strip().lower()
    if status and status != "ok":
        return f"status={status} retcode={response.get('retcode')}"
    retcode = response.get("retcode")
    if retcode is not None and str(retcode) != "0":
        message = str(response.get("message") or response.get("msg") or "").strip()
        return f"retcode={retcode} message={message}"
    return ""


async def send_friend_welcome(
    connection: OneBotConnection, user_id: int, settings: Settings
) -> bool:
    """给刚通过的新好友发送使用说明，成功返回 True。

    **本函数不向外抛异常**：「说明没发出去」不能把「已同意好友」这个已经生效的结果
    变成失败。失败按 _FRIEND_WELCOME_RETRY_DELAYS 退避重试。
    """
    message = render_friend_welcome(settings)
    if not message.strip():
        logger.info("新好友使用说明为空，跳过发送：user_id=%s", user_id)
        return False
    for attempt, delay in enumerate((0.0, *_FRIEND_WELCOME_RETRY_DELAYS), start=1):
        if delay > 0:
            await asyncio.sleep(delay)
        reason = ""
        try:
            response = await connection.call_api(
                "send_private_msg",
                {"user_id": int(user_id), "message": message},
                timeout=settings.friend_action_timeout,
            )
            reason = _onebot_failure_reason(response)
        except asyncio.CancelledError:
            raise  # 停机/取消要能中断，别当成发送失败去重试
        except Exception as exc:
            reason = f"动作异常：{exc}"
        if not reason:
            logger.info("已向新好友发送使用说明：user_id=%s（第 %d 次）", user_id, attempt)
            return True
        logger.warning(
            "新好友使用说明发送失败（第 %d 次）：user_id=%s 原因=%s", attempt, user_id, reason
        )
    logger.error(
        "新好友使用说明始终发送失败：user_id=%s（好友已同意，不影响对方后续投稿）", user_id
    )
    return False


async def handle_friend_request(event: dict[str, Any], connection: OneBotConnection, settings: Settings) -> bool:
    """处理好友请求：按配置过滤后发送 set_friend_add_request；返回是否已同意。"""
    flag = event.get("flag")
    user_id = int(event.get("user_id") or 0)
    comment = str(event.get("comment") or "")
    # 收到就记一条：否则「没收到请求」和「被规则挡下」在日志上分不出来
    logger.info(
        "收到好友请求：user_id=%s flag=%s 验证消息=%r",
        user_id,
        "有" if flag else "无",
        comment[:50],
    )
    if not flag:
        logger.warning("好友请求缺少 flag，无法处理：user_id=%s", user_id)
        return False

    qq_level: int | None = None
    if settings.friend_min_qq_level > 0 and user_id > 0:
        try:
            info = await connection.call_api(
                "get_stranger_info", {"user_id": user_id, "no_cache": True},
                timeout=settings.friend_action_timeout,
            )
            data = info.get("data") if isinstance(info, dict) else None
            if isinstance(data, dict) and data.get("qqLevel") is not None:
                qq_level = int(data["qqLevel"])
        except Exception:
            # 等级取不到时不因等级拦截（关键词门槛仍然生效），并记录以便排查。
            logger.warning("获取 QQ 等级失败，跳过等级门槛：user_id=%s", user_id, exc_info=True)

    approved, reason = should_approve_friend_request(comment, qq_level, settings)
    if not approved:
        logger.warning(
            "好友请求未通过过滤（%s）：user_id=%s 验证消息=%r；"
            "如需无条件通过请设 FRIEND_REQUIRE_KEYWORD=false",
            reason,
            user_id,
            comment[:50],
        )
        return False

    try:
        await connection.send_action(
            "set_friend_add_request",
            {"flag": flag, "approve": True},
        )
    except Exception:
        # 这里必须显式记日志：动作发不出去时，调用方此前会静默失败、请求一直挂在那里
        logger.exception("同意好友请求失败（动作未能发出）：user_id=%s", user_id)
        return False
    logger.info("已自动同意好友请求：user_id=%s", user_id)
    if settings.friend_welcome_enabled and user_id > 0:
        # send_friend_welcome 自己吞异常：说明发不出去不能影响「已同意好友」这个结果
        await send_friend_welcome(connection, user_id, settings)
    return True


# NapCat 掉线巡检间隔（秒）。重启服务器后 NapCat 若卡在扫码登录或没启动，
# 本服务什么都收不到，日志里必须能持续看出来，否则会被误判成「机器人坏了」。
CONNECTION_WATCH_INTERVAL_SECONDS = 300.0


def self_fingerprint() -> str:
    """返回「当前正在运行的这份代码」的文件指纹。

    这个项目已经被版本混淆坑过两次：ERR-009（外部审查审的是旧备份副本）、
    以及 2026-10-06（新 main.py 已经上传，但旧进程还在跑，于是新修复看起来"没用"）。
    启动时把自身文件的 size/sha256 打进日志，与 `sha256sum main.py` 一比就能确认
    「跑的是不是刚传的那版」，不必再去猜 traceback 里对不上的行号。
    """
    try:
        data = Path(__file__).read_bytes()
    except OSError as exc:  # pragma: no cover - 极端情况：文件不可读
        return f"无法读取自身文件：{exc}"
    return f"main.py size={len(data)} sha256={hashlib.sha256(data).hexdigest()}"


async def watch_napcat_connection(connections: "ConnectionManager") -> None:
    """定期检查还有没有 NapCat 连接；没有就告警。

    注意：QQ 登录态由 NapCat 负责，本服务无法代替它登录，只能把「没连上」这件事喊出来。
    """
    while True:
        await asyncio.sleep(CONNECTION_WATCH_INTERVAL_SECONDS)
        if connections.count == 0:
            logger.warning(
                "当前没有任何 NapCat 连接：收不到任何投稿与好友请求"
                "（检查 NapCat 是否已启动、是否卡在扫码登录）"
            )


def _report_task_exception(task: asyncio.Task) -> None:
    """事件任务结束时把异常打出来。

    `asyncio.create_task()` 创建的任务若异常无人 await，会被静默丢弃
    （只在对象回收时冒一条警告），排查「处理失败但日志什么都没有」时极难定位。
    """
    if task.cancelled():
        return
    exc = task.exception()
    if exc is not None:
        logger.error("事件处理异常：%s", exc, exc_info=exc)


async def handle_event(
    event: dict[str, Any],
    connection: OneBotConnection,
    *,
    settings: Settings,
    manager: SubmissionManager,
) -> None:
    """OneBot v11 事件总入口（由 WebSocket 接收循环以 create_task 方式调用）。"""
    post_type = event.get("post_type")

    if post_type == "message":
        message_type = event.get("message_type")
        if message_type == "private":
            await manager.handle_private_message(event)
        else:
            logger.debug("忽略非私聊消息：message_type=%s", message_type)
        return

    if post_type == "request":
        if event.get("request_type") == "friend":
            await handle_friend_request(event, connection, settings)
        else:
            logger.debug("忽略非好友请求：request_type=%s", event.get("request_type"))
        return

    if post_type in {"meta_event", "notice"}:
        logger.debug("忽略事件：post_type=%s", post_type)
        return

    logger.debug("未知事件类型：post_type=%s", post_type)


# --------------------------------------------------------------------------------------
# 十一、FastAPI 应用
# --------------------------------------------------------------------------------------


@dataclass
class AppContext:
    """应用级共享对象集合。"""

    settings: Settings
    database: Database
    connections: ConnectionManager
    publisher: QZonePublisher
    http_client: httpx.AsyncClient
    manager: SubmissionManager


def create_app(settings: Settings | None = None) -> FastAPI:
    """构造 FastAPI 应用；settings 可注入，便于测试使用临时目录与小超时。"""
    active_settings = settings or SETTINGS
    # 字体要在第一次渲染前定下来：FONT_PATH 优先，否则走候选列表（Linux 首选鸿蒙）。
    set_font_path(active_settings.font_path)

    @contextlib.asynccontextmanager
    async def lifespan(app: FastAPI):
        # 启动第一行就报「跑的是哪一版 + 从哪个目录启动 + 读的是哪个 .env」：
        # 「传了新文件但旧进程还在跑」「配置没生效」这两类问题都能一眼看出来。
        logger.info(
            "校园墙服务启动：cwd=%s .env=%s .env已加载=%s %s",
            Path.cwd(),
            _ENV_FILE_PATH or "未找到",
            _DOTENV_LOADED,
            self_fingerprint(),
        )
        # 「用的是哪一个 key」是高频问题（旧 key 被 export 过 / 改完没重启），
        # 所以把密钥打码打出来：既能确认换没换成新的，又不会把密钥写进日志。
        logger.info(
            "DeepSeek 密钥：%s（来源=%s）",
            mask_secret(active_settings.deepseek_api_key),
            describe_config_source("DEEPSEEK_API_KEY", active_settings.deepseek_api_key),
        )
        database = Database(active_settings.db_path)
        await database.connect()
        # follow_redirects=False：重定向统一由 fetch_bytes 逐跳处理 ——
        # 否则 ALLOW_PRIVATE_IMAGE_HOSTS=false 可以被「公网地址 302 到内网」绕过。
        http_client = httpx.AsyncClient(follow_redirects=False)
        connections = ConnectionManager()
        publisher = QZonePublisher(active_settings)
        manager = SubmissionManager(
            settings=active_settings,
            database=database,
            connections=connections,
            publisher=publisher,
            http_client=http_client,
        )
        app.state.ctx = AppContext(
            settings=active_settings,
            database=database,
            connections=connections,
            publisher=publisher,
            http_client=http_client,
            manager=manager,
        )
        # 换新服务器时的一次性清理：配置了 PURGE_BEFORE 就在**后台**把更早的历史投稿删掉。
        # 必须放后台：几十上百条删除要几分钟，拖住 lifespan 会让 WebSocket 迟迟连不上，
        # 期间用户发来的投稿全丢。清理进度逐条写进审核操作日志，启动日志里只打结果。
        purge_before = (active_settings.purge_before or "").strip()
        if purge_before:
            purge_cutoff = parse_date_cutoff(purge_before, active_settings)
            if purge_cutoff is None:
                logger.error(
                    "PURGE_BEFORE=%r 不是有效日期（例：2026-10-31），已跳过旧投稿清理",
                    purge_before,
                )
            else:
                logger.warning(
                    "已配置 PURGE_BEFORE=%s：启动后在后台删除该时刻之前发布的投稿（截止 %s UTC）",
                    purge_before,
                    purge_cutoff.isoformat(timespec="seconds"),
                )

                async def _purge_on_start() -> None:
                    try:
                        result = await manager.purge_published_before(
                            purge_cutoff, operator_id=0
                        )
                        logger.warning(
                            "启动清理旧投稿完成：共 %d 条，成功 %d 条，失败 %d 条",
                            result["total"],
                            len(result["deleted"]),
                            len(result["failed"]),
                        )
                    except asyncio.CancelledError:
                        raise
                    except Exception:
                        logger.exception("启动清理旧投稿失败（不影响收稿与发布）")

                app.state.purge_task = asyncio.create_task(_purge_on_start())
        else:
            # 不配就什么都不做 —— 这行日志是给「我明明换了程序，怎么旧说说还在」准备的：
            # 清理是**按需触发**的，不配 PURGE_BEFORE 也不会自动删。
            logger.info(
                "未配置 PURGE_BEFORE：不会自动清理历史投稿。"
                "需要清理时发 %s清理旧说说 <YYYY-MM-DD>（先发 %s清理诊断 看有多少条）",
                command_prefix_of(active_settings),
                command_prefix_of(active_settings),
            )
        if not active_settings.deepseek_api_key:
            logger.warning("未配置 DEEPSEEK_API_KEY：投稿将因审核不可用而不发布（fail-closed）")
        # 把好友请求的生效策略打出来：否则「没收到请求」和「被规则挡下」很难区分
        logger.info(
            "好友请求策略：自动通过=%s 关键词门槛=%s(关键词=%s) QQ等级门槛=%s",
            active_settings.friend_auto_approve,
            active_settings.friend_require_keyword,
            ",".join(active_settings.friend_keywords) or "无",
            active_settings.friend_min_qq_level,
        )
        logger.info(
            "管理命令：所有者=%d 人 管理员=%d 人 审核员=%d 人 前缀=%r%s",
            len(owner_ids(active_settings)),
            len(admin_ids(active_settings)),
            len(reviewer_ids(active_settings)),
            command_prefix_of(active_settings),
            ""
            if (admin_ids(active_settings) or reviewer_ids(active_settings))
            else "（两个白名单都为空 → 命令功能未启用）",
        )
        if _LEGACY_WHITELIST_LAYOUT:
            logger.warning(
                "检测到旧版名单布局（SUPER_ADMIN_WHITELIST / ADMIN_WHITELIST）：已按旧语义加载 ——"
                " SUPER_ADMIN_WHITELIST = 管理员，ADMIN_WHITELIST = 审核员。\n"
                "建议把 .env 改成新名字：ADMIN_WHITELIST（管理员）、REVIEWER_WHITELIST（审核员）。"
            )
        logger.info(
            "每日额度：每人 %d 条（按 %s 的自然日，0 点重置；管理员不受限）",
            active_settings.daily_message_limit,
            active_settings.display_timezone,
        )
        logger.info(
            "投稿节奏：最后一条消息后静默 %.0f 秒开始渲染，渲染完即发布（不再攒稿/定时放送）",
            active_settings.idle_timeout_seconds,
        )
        logger.info(
            "投稿存档：%s（每份投稿一个 `<编号>_<投稿人QQ>` 子目录）　审核操作日志：%s",
            active_settings.archive_dir or str(Path(active_settings.data_dir) / "archive"),
            str(Path(active_settings.data_dir) / "audit" / AUDIT_LOG_FILENAME),
        )
        logger.info(
            "图片限制：单次投稿=照片 %d 张 + 表情包 %d 个（送审预算 %d 张）"
            " 单次投稿体积=%.0f MiB 单张像素上限=%.0f 万",
            active_settings.moderation_max_images,
            active_settings.max_stickers_per_submission,
            moderation_image_budget(active_settings),
            active_settings.max_submission_image_bytes / 1048576,
            active_settings.max_image_pixels / 10000,
        )
        logger.info(
            "等待 NapCat 反向 WS 连接：路径 %s（NapCat 侧填 ws://<本机IP>:%s%s）",
            active_settings.ws_path,
            active_settings.port,
            active_settings.ws_path,
        )
        connection_watcher = asyncio.create_task(watch_napcat_connection(connections))
        # 说明：原来这里还会启动「定时放送调度器」（manager.start_dispatch），
        # 该功能已整体删除 —— 现在每个会话的空闲定时器到点后直接渲染并发布。
        try:
            yield
        finally:
            connection_watcher.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await connection_watcher
            await manager.shutdown()
            await http_client.aclose()
            await database.close()

    app = FastAPI(title="QQ 校园墙机器人", version="1.0.0", lifespan=lifespan)

    @app.get("/healthz")
    async def healthz() -> dict[str, Any]:
        """健康检查：供容器编排与巡检使用。"""
        ctx: AppContext = app.state.ctx
        return {
            "status": "ok",
            "connections": ctx.connections.count,
            "active_sessions": len(ctx.manager.sessions),
        }

    @app.websocket(active_settings.ws_path)
    async def onebot_v11_ws(websocket: WebSocket) -> None:
        """NapCat 反向 WebSocket 入口：/onebot/v11/ws。"""
        await websocket.accept()
        ctx: AppContext = app.state.ctx
        connection = ctx.connections.register(websocket)
        try:
            while True:
                raw = await websocket.receive_text()
                try:
                    payload = json.loads(raw)
                except json.JSONDecodeError:
                    logger.warning("收到非 JSON 报文，已忽略：%s", raw[:120])
                    continue
                if not isinstance(payload, dict):
                    continue
                # 带 echo 的报文是动作响应，交还等待者；否则作为事件异步处理，避免阻塞接收循环。
                if connection.resolve_echo(payload):
                    continue
                task = asyncio.create_task(
                    handle_event(payload, connection, settings=ctx.settings, manager=ctx.manager)
                )
                task.add_done_callback(_report_task_exception)
        except WebSocketDisconnect:
            logger.info("NapCat 反向 WS 断开")
        except Exception:
            logger.exception("WebSocket 处理异常，连接即将关闭")
        finally:
            ctx.connections.unregister(connection)

    return app


app = create_app()


if __name__ == "__main__":  # pragma: no cover - 本地调试入口
    import uvicorn

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s %(message)s")
    uvicorn.run(app, host=SETTINGS.host, port=SETTINGS.port)
