# QQ 校园墙投稿机器人

基于 FastAPI + OneBot v11（NapCat 反向 WebSocket）的 QQ 私聊投稿服务：接收多条消息，合并为截图，先做内容审核，再发布到 QQ 空间。支持匿名投稿、图片与表情处理、每日额度、管理员操作和审计记录。

> **公开前须知**：本目录是从单独提供的较新 `main.py` 制作的独立开源副本，**不是**工作区旧版 `qq-campus-wall-bot/` 的直接拷贝。去掉了内嵌校园背景、管理员徽标、写死的所有者与客服联系 QQ；不附带 `.env`、历史日志、数据库、头像、投稿截图或旧更新日志。NapCat 表情编号对照表不随仓库分发：可以按技术手册配置自己的授权映射，否则退回文字标签。请勿直接上传原始附件、旧项目目录或服务器备份。

## 快速开始

要求：Python 3.10+、可用的 NapCat/OneBot v11 实例、QQ 空间账号，以及配置好的内容审核 API。`qzone-sdk[napcat]==1.0.1` 使用其认证和 HTTP 内部接口；升级依赖前请先回归测试。

```bash
python -m venv .venv
# Linux/macOS: source .venv/bin/activate
# Windows: .venv\Scripts\activate
python -m pip install -r requirements.txt
cp .env.example .env  # Windows 可使用 copy .env.example .env
```

程序仅查找与 `main.py` 同目录的 `.env`，不会读取父目录的旧项目配置。编辑 `.env`：至少填入 `DEEPSEEK_API_KEY`、`OWNER_QQ`（你自己的 QQ 号）；按你的 NapCat 部署调整 `QZONE_WS_URL`。在 NapCat 中配置 **反向 WebSocket** 连接至 `ws://127.0.0.1:8080/onebot/v11/ws`（跨机器时按实际 IP/端口设置 `HOST`，并只允许可信网络访问）。启动：

```bash
python main.py
# 或：python -m uvicorn main:app --host 127.0.0.1 --port 8080
```

访问 `http://127.0.0.1:8080/healthz` 检查服务。先用测试 QQ 完成投稿、审核、空间发布与删帖的端到端验证，确认权限与日志后再对外开放。默认未配置背景/徽标时使用纯色截图；如需专属素材，自备有权使用的文件并单独设置 `CHAT_BACKGROUND_PATH`、`ADMIN_BADGE_PATH`、`ADMIN_BADGE_ENABLED=true`，切勿把素材直接提交到公共仓库。

## 使用及风险

- 投稿人向机器人发 QQ 私聊文本/图片；空闲 `IDLE_TIMEOUT_SECONDS` 后汇总、审核、渲染并发布。匿名关键字只隐藏**公开截图**里的昵称头像，数据库与审计仍可追溯投稿者。
- 管理员与审核员由 `OWNER_QQ`、`ADMIN_WHITELIST`、`REVIEWER_WHITELIST` 指定；管理员私聊发送 `/帮助` 查看当前角色可用的命令。不要沿用旧版 `SUPER_ADMIN_WHITELIST` 布局而不核对角色含义。
- 图片审核依赖外部服务，自动审核不能替代人工复核；图片 URL 可能访问私有地址（NapCat 本地图片的需要），请将服务隔离在可信网络。开通公网供图部署时应评估 `ALLOW_PRIVATE_IMAGE_HOSTS=false` 的适用性。
- 不要开启 `PURGE_BEFORE`，除非确认要**删除**指定时间之前的空间说说；发布前应备份数据，了解重启会清空内存中未完成的会话。
- API Key、Cookie、QQ 号、真实聊天记录、审核日志和数据库都不要提交。`.gitignore` 只是最后一道保护，发布前仍需人工检查 `git status` 和提交历史。

## 项目文件

- `main.py`：服务、配置、投稿流水线、审核、截图、数据库、QQ 空间发布和管理员命令。
- `.env.example`：不含真实凭据的最小配置样例。
- `requirements.txt` / `requirements-dev.txt`：运行与测试依赖。
- `tests/test_open_source.py`：本次去标识化的回归测试。
- `docs/TECHNICAL_MANUAL.md`：详细架构、部署、配置、运维与安全手册。

## 测试

```bash
python -m pip install -r requirements-dev.txt
python -m pytest -q
python -m compileall -q main.py
```

离线测试不能代替真实 NapCat、审核服务、QQ 空间的联调。更多说明见 `docs/TECHNICAL_MANUAL.md`。

## 许可

**尚未附带 LICENSE：请先确认代码著作权归属，再添加正式许可文件后公开发布。** 如希望别人可以自由复制、修改和用于商业项目，建议 MIT；若更重视专利授权条款，可考虑 Apache-2.0。项目自身的许可**不等于** NapCat、QQ 素材、API 服务或第三方依赖的许可。具体选择与上架前检查见技术手册。