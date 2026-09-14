---
name: open-problem-lane
description: Use when running the standing open-problem loop — find an old, still-open, small conjecture (OEIS comments, Erdős side questions), verify it independently, preregister, probe, implement, review, and land it on dev as a kernel-checked resolution with a machine-countable marker.
---

# open-problem-lane — 开放问题落地闭环（orchestrator 视角）

本 skill 是会话 580742（2026-09-13 → 09-15，59 条 PR 合入）沉淀的操作面，服从 `CLAUDE.md`（§3.2 逃逸内容、§3.3 用途、§3.6 三档律、§5.2 产地、§2.10 记录律）与 `tools/scripts/agent/openproblem/README.md` / `TARGET-GATES.md`；本文无独立权威。KPI = `origin/dev` 上 `scribe-open-problem-resolution-v1` 标记数（计数命令见 §9）。

## 0. 载体与分工
- **搜题席**：1 席 GPT Pro（`bash tools/scripts/agent/nyx.sh ask <brief> <out>`；先 `pong`）。池宕机（pong `EXIT=3`、ask 三池 `infrastructure_retry_exhausted`）时改派 **codex-cli 代席搜题**（`references/search-codex-standin.md`，scratch 工作树、只写报告不提交）——实测一轮 2.5 h 产 3 条经核实候选，优于 orchestrator 自扫（OEIS 全文分页 + 正则 + Python 数值筛，5 批出 2 条）。
- **探针 / 实施 / 评审**：全部 codex-cli，`bash tools/scripts/agent/seat/dispatch.sh FLIGHT ATTEMPT BRIEF WORKTREE STAGE 0 10`（STAGE ∈ thinking | implementation | review），每席一个宿主后台作业，本机 ≤ 8 席；判终局只认 `result.json` + 宿主通知，禁轮询宿主任务文件。
- **orchestrator 亲验**：逐字取源、独立复算（两法）、去重、预登记、正文审计、判词账、合并链、关单、清理、同步。席位自报一律标注「席位自报」。

## 1. 闭环（每条 lane，顺序不可交换）
1. **搜题** → 候选须给出：verbatim `%N`/`%C`（或论文页码句子）、量词写全的陈述、可计数形状（A 反驳 / B 证明）、席位自算的数值核、无解核对读数。
2. **靶清查**（`TARGET-GATES.md` 四关 + 本 skill 增补 §2）。
3. **预登记 issue（探针之前！）**：模板 `references/prereg-refute.md` / `prereg-prove.md`。事后开单会被评审判 post hoc。
4. **探针**（thinking 席，`references/probe-refute.md` / `probe-prove.md`）→ 读信封 → `git ls-remote` 核实推送 → `git show <head>:<module>` 读模块 → 在预登记 issue 发**探针评论**（转录 + 标注自报）。见证/路线与预登记不同 → 先发**重新预登记评论**再派下一步。
5. **Stage B**（implementation 席，`references/impl-refute.md` / `impl-prove.md`；用引号 heredoc + `__PLACEHOLDER__` + `sed` 组装，禁 python f-string——`{a≠b}` 会被当替换字段炸掉）→ 读信封。
6. **正文审计**（§6）→ 发布 v2 → 回读逐字节比对 → 在预登记 issue 发 **Stage B 评论**。
7. **三席盲评**：`python3 gen_review.py LANE PR BRANCH WORKTREE IMPL_ENVELOPE targets/LANE.txt none`；architecture/quality 各用 `git worktree add --detach <repo>-rev-<lane>-{arch,qual} <HEAD>` 只读树，tests 在 op 树；三个独立后台作业。target 模板 `references/target-refute.txt` / `target-prove.txt`（钉 HEAD、冻结事件、statement_id、import 表、内核读数、直接计数）。
8. **判词账 v3**（§7）→ `.ok` 门 → **合并链**（§8）→ REST 核 `merged=true` → 关预登记（MERGED + SHA）→ 目标 issue 轮次评论（含 KPI 计数命令）→ 删三棵树与分支 → 主检出 `git pull --ff-only origin dev && make lean`（donor 暖）。

## 2. 靶清查增补（本会话烧出来的）
- **先库后证含私有引理**：`git grep` 仓内 D5 时同时找 `private theorem` 同形（Lagneau #7579 的 σ 奇偶刻画是私有，A001108 只能重证并披露）。
- **证明型候选必做文献形状检索**：搜不等式/恒等式的数学形状（WebSearch/Crossref/arXiv），不是只搜 A 号。A008578（Gerasimova 2013 σ(k) > k·Ω(k)）在 Stage B 末次核查才发现是 Sándor 1988 已知结果（Sándor–Kovács 2015 式 (40)），整条 lane 弃置。
- **读完整条目**：后续评注常写「The above conjecture is true/false」（A277201、A018804、A163553、A001969、A067274 均在条目内已结算）。
- **两法独立复算**：例如 Fibonacci 残差用快速倍增 + 直接迭代；σ 用筛法 + sympy。
- **边界披露**：字面全称常在 n = 0/1/2 的空和/退化处失效（A008590 m = 1 空和；A000040 n = 2 的 Fermat 测试；A001108 σ(0) = 0）。用 `0 < n`/`1 < m` 守卫、在注/卷宗/正文三处披露，**见证取实质反例而非退化点**。
- **同一条目的多条猜想**：一模块一 slug；变体只披露不主张（A000040 May 28 变体）。

## 3. 判形裁决（§3.2 判例）
- **decide/norm_num/reduce_mod_char 算出的新原子事实是形态 (2) content**，不是「已给定事实的规范化」（A049591 #7703、A103585 #7717、A129598 #7791、A000040 #7827 均 3/3 approve）。探针 brief 的「先试纯规范化」硬规则会让席位把有限证书自报 bind-only（A000040 attempt-1）——brief 中写明裁决，或收到 bind-only 自报后重登记 + 重派。
- **形态 (1)**：私有 content 引理**逐条列名**；经典事实的重证（σ 奇偶刻画）**不计**为见证但要列出并披露。
- **bind-only 陷阱**：正向恒等式 = Mathlib 求和引理换名（裂项、几何和、乘法性直接实例化）；A140110 类「短定义桥」高风险。
- **utility**：有限计算承载整个反驳 → `certified-instance; basis=refutes`（typed refutation，头部 `refutes=gid:…claim; result=…; claim=…`）；符号证明/反驳 → `none`。

## 4. 复用引理公开化（用户 2026-09-15 指令）
需要复用的引理**从 private 改为 public**：经典刻画（σ/τ 奇偶、Ω 与 σ 的关系、模剩余分类）、通用定义（`nextPrime`、模快速倍增）、2-adic 超度量引理等——公开声明 = 加 Scribe 节点（FromLiterature/FromRepo）+ 本模块有真实消费者（不违 bind-only 禁令），后续 lane 直接 `import` 成为冻结前置（`prerequisite_frozen_node_ids` 非空）。只有一次性证书步骤（具体数值的 decide）保持 private。落地前 `git grep` 确认同形公开声明不存在（撞车改写成推论）。

## 5. 落址与文献注
- 桶按 `Meta/domains.yaml` 的 definition 选（Certificates = 内核可核验反驳证书；ArithSums = 按整除/剩余分类的有限和；Factorization；Arith；Recurrence…）；容量用**直接文件计数** `git ls-tree --name-only <rev> -- <dir>/`（D5/S0/Certificates 有 4 个子桶，递归计数会多 10）。
- 文献注 `Library/<Domain>/<bibkey>.md`：bibkey = OEIS `%A` 作者 + 猜想年 + A 号（`sloane2014a000040`），`authors: <%A 作者>; <猜想作者>`；模块名依猜想作者（`DetlefsFibonacciFermat…`）。`Library/notes/` 是属主桶满时的根桶。
- 已知前置在模块内证出须归属（Sivaramakrishnan/Shallit 判例）。

## 6. PR 正文审计契约
- 禁待时语句（正则：`等待|稍后|补记|不再 push|最终推送|最终 HEAD|尚未|^待|；待|。待|[Pp]ending|to be appended|后记入|recorded after|一次写入|记于此|记于本段|之下。|回填|归位后|进行中`）、禁 session 链接（§2.10）。
- 必含字面：`question_answered:`、`dominating_theorem_search:`、`build_seconds:`、「评审判词账」小节；产地三项含 `consensus-rnd:sshx` 与「判卷面无异模型共识」句；footer 只有 `🤖 Generated with [Claude Code](https://claude.com/claude-code)`。
- 判词账在评审前只留 ownership 句：「评审判词账由 orchestrator 维护：三席（architecture / quality / tests，codex-cli，独立 worktree，互不见对方判词）的判词与裁决在本节记录。」
- 席位写错的机器读数（桶计数、HEAD）由 orchestrator 用命令复核后重写并注明命令；`gh pr edit --body-file` 后回读 `.rstrip()` 逐字节比对，一致才写 `.ok`。

## 7. 判词账 v3 与分歧处理
- 表列：席位 / 载体·树 / 判词 / 阻断项 / 非阻断项·亲验；席位命令数与 `ASSUMED-UNVERIFIED` 项照录；结尾「裁决：三席 …；判卷面单一模型族…；未开启 auto-merge」。
- 一席 reject 且其余 approve：先判 reject 是否成立——用**机器实验或判例**反驳（删除 import 实验、`Nat.sInf_def`、已合入同形渲染），派 **bounded p2**（同树同 HEAD、只评自己的 pass-1 项、附证据，`references/review-p2-example.md`）；p2 撤回则记「approve（pass 2 撤回 pass-1 阻断项）」。真缺陷才派修复席（冻结前改 Lean = 重做 deposit）。
- 判词账写完后不改 Lean/冻结面；复审前正文冻结。

## 8. 合并链（一个后台作业）
```bash
LEAN4_GUARDRAILS_BYPASS=1 bash -c 'until [ -f "$S/prNNNN.ok" ]; do sleep 5; done; gh pr checks NNNN --watch --fail-fast; st=$(gh pr view NNNN --json mergeStateStatus -q .mergeStateStatus); case "$st" in CLEAN|UNSTABLE|HAS_HOOKS|BEHIND) gh pr merge NNNN --merge;; *) echo NOT_MERGEABLE; exit 5;; esac; gh api repos/<owner>/<repo>/pulls/NNNN -q ".merged, .merge_commit_sha"'
```
dev 侧红（他人 lane 带入无效 DOI 注等）→ 等 revert 合入后在 op 树 `git merge origin/dev` **merge-only** 并推送重触发（`gh run rerun` 不重算 merge ref）；冻结提交须仍是祖先。

## 9. 计数、清理、同步
- KPI：`git grep -c scribe-open-problem-resolution-v1 origin/dev -- Blueprint | awk -F: '{s+=$NF} END{print s}'`（`$2` 是路径，勿用）。
- 清理：`LEAN4_GUARDRAILS_BYPASS=1 git worktree remove --force …` ×3、`git branch -D`、`git push origin --delete`（无 bypass 会被 Lean guardrail 整条拦下）。
- 同步：主检出 `git pull --ff-only origin dev && make lean`（新树 clonefile 播种 13 s vs 自供 6.5 min）。
- 并发：三条 Stage B 同机会撞 lean-report 内存（64 GB 机 ≈ 一次 35–45 GB），错峰派发；探针/评审无此限。

## 10. 失败教训索引
探针把 decide 证书自报 bind-only（A000040）；Stage B 撞 dev 侧红（A008590/A129598/A000040 均因 #7783 无效 DOI 注）；席位递归计桶（A129598 58 vs 48）；brief f-string 炸（A129598 首派）；建树撞 fetch prune 提示（重试即可）；quality 要求「字面 Nat.find」（`sInf{…}` 即其定义，p2 撤回）；已知结果晚发现（A008578）；GPT Pro 池整日宕机（codex 代席）。

## References（`references/`，路径已用 `$OP_SCRATCH` / `<repo>` 占位）
search-gptpro.md · search-codex-standin.md · prereg-refute.md · prereg-prove.md · probe-refute.md · probe-prove.md · impl-refute.md · impl-prove.md · target-refute.txt · target-prove.txt · review-p2-example.md · closing-comments.md
