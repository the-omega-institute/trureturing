# openproblem — 开放问题线的两阶段落地管线(器律⑨:器住仓库)

CLAUDE.md 5⁵(开放问题线三档律)的操作面。所有脚本以宿主后台作业逐席运行(器律⑥),判绿只认 result.json / status.json 与哨兵,不认退出码。
运行目录约定:`OP_SCRATCH` = 本会话的 scratchpad(briefs/、results/、probes/ 三个子目录);python 工具以该目录为第一个参数或工作目录。

## 流程(每条 lane)
1. **搜题**(nyxid-oracle,ChatGPT Pro):brief 必须写明**档位**(第一档新近小猜想 / 第二档计算前沿 / 第三档核心问题)与「文献是否已有此陈述」的核对要求;结果落 `results/rN.json`。
2. **探针**(codex-cli,只读 worktree,scratch `/tmp/op-pNN/`):先用 Python 独立核算真假(可证伪预测写在跑之前),再 Lean 整证;`propose` 只认「主陈述以标准三公理编译且无 sorry」;`refuted` 也是结果。已知结果不派席(只 cover 或作前置桥)。
3. **预登记**(理论卷增订 ingest):写档位、核对结果、逃逸见证与范围墙;`op-ingest-new-noalign.sh` 在新分支追加卷文并 ingest(绕开 issue #5606 的 align 重排问题)。
4. **Stage A**(`op-resume-seat.sh … implementation`):模块 + Scribe 镜像 + `make lean`/`lean-report`/`emit`,**在任何门之前停下**(envelope `mirror-ready`)。brief 由 `gen_stage_briefs.py` 从实施 brief 切出;基底模板 `templates/impl-base-brief.md` 带产地类型化、import 最小化、公开面自觉、header 工具校验、emit 前刷新报告等块(`add_base_blocks.py` 可补进旧 brief)。
5. **镜像核对**(只读 codex 席,`templates/mirror-check-template.md` 十二项):括号/合取/绑定变量/强制转换/整除/关系节点/完备性(公开 def 也要镜像或 private)/取值核对/header/定义保真/产地(FromLiterature 须有带 DOI 或 arXiv 的 L 平面注)/import 最小化。
6. **Stage B**(`fill_mirror_fixes.py` 把核对结果填进 Stage B brief):先修镜像,改过镜像必做渲染检查(发射 md 无 `&&`/`||`/`==`;`make preflight` 中点名本模块的 `markdown red` 行即停),再 deposit + cover(锚 atom 也要 cover)、一个 builder commit、晚期去重、push、`make pr-open`(不挂 auto-merge)。
7. **三席评审**(`gen_review.py`:tests/quality 走 codex,一席 nyxid 由 `od -An -N2 -tu2 /dev/urandom` 取 raw%2 抽签);正文冻结后再派复审;非阻断即 `op-sync-dev.sh`(合 dev、推、等三门)+ `gh pr merge --auto --merge`。
8. **重做**:冻结后任何镜像/产地/import 修补都是全新 deposit(cover 收据绑定 Scribe 哈希);同一 lane 第三次非数学重做即停(第 20⁗ 条)。

## 脚本
- `op-resume-seat.sh FLIGHT ATTEMPT BRIEF WORKTREE STAGE [STAGGER] [MAX_CODEX]`:fail-closed 负载门(idle ≥ 20% ∧ lean ≤ 4 ∧ codex 进程 ≤ MAX,300 轮 × 60 s,超时不启动)+ sshx runner。
- `gen_stage_briefs.py SCRATCH LANE WORKTREE BRANCH MODULE`:切 Stage A / Stage B / mirror-check 三份 brief。
- `fill_mirror_fixes.py SCRATCH LANE RESULT_JSON`:把镜像核对的 blocking/advisory 填进 Stage B brief。
- `add_base_blocks.py FILE…`:把基底模板的三个纪律块补进缺失的 brief。
- `gen_review.py LANE PR BRANCH WORKTREE IMPL_ENVELOPE TARGET_FILE NYXID_SEAT`:生成三席评审 brief(在 SCRATCH 目录运行)。
- `op-sync-dev.sh WORKTREE BRANCH PR`:merge-only 合 dev、推送、等待三门(重算 merge ref;`gh run rerun` 不重算)。
- `op-ingest-new-noalign.sh WORKTREE NEW_BRANCH ADDENDUM SUBJ PRMSG PATTERN [VOLUME]` / `op-ingest-noalign.sh` / `op-addendum-ingest-v3.sh`:理论卷增订 ingest(前两者绕开 align)。
- `op-governance-pr.sh WORKTREE BRANCH COMMIT_MSG PR_MSG [AUTO]`:governance 改动的提交/推送/开 PR。
- `op-fold-anchor-cover.sh WORKTREE BRANCH ATOM SOURCE_ID`:把漏掉的锚 cover 折进 builder commit。

## 判据摘要(来自 2026-09-05 一日 40 余席的读数)
- 产出由选题函数决定:唯一两个真解决出自把判据改为「近期论文明确写出且文献无证明」的那一轮。
- 13 次重做零数学错误,全是镜像/产地/import;镜像核对先于冻结把重做成本从一次 deposit 降到一次只读席。
- 负载门的瓶颈是 codex 席位数(本机 ≤ 8 席含其他会话),不是 CPU。

## 2026-09-06 增补
- `op-resume-seat.sh` 的负载门新增**上游健康**条件:`CODEX_HEALTH_URL`(默认 codex 提供方 `/responses`)返回 502/503/000 时不放行——同日该网关整体 502 使 11 席同时 turn.failed;判死因看 `worker.stdout.log` 尾部,不看退出码。
- 镜像核对模板第 3 项扩为「公式中每个符号须为绑定变量 / 本模块已镜像的 Lean 公开名 / Mathlib 或原子对象,禁临时缩写」(Skolem #5597 冻结后才被 quality 席抓到 `red` ≠ `reducedState`);第 7 项明确公开 def 也须镜像或 `private`;第 11 项要求 L 平面注带 DOI 或 arXiv;第 12 项 import 最小化(禁 umbrella `import Mathlib`)。
- 实施基底模板新增:header/helper 以 `tools/scripts/agent/header-check.sh` 工具校验(目录上限已随 #5630 对齐 24);emit 前先 `make lean-report`;Stage B 改镜像后必做渲染检查(`grep -E '&&|\|\||==|!='` 发射 md 为空;`make preflight` 中点名本模块的 `markdown red` 行即停)。
- 理论卷增订 ingest 走 `op-ingest-new-noalign.sh`(绕开 issue #5606 的 align 重排)。
