# openproblem — 开放问题线的两阶段落地管线(器律⑨:器住仓库)

CLAUDE.md §3.6 的操作面。长任务使用宿主作业句柄，检查结果以实际退出码为准；席位交付另须符合 result.json 与完成哨兵契约。
运行目录由 `OP_SCRATCH` 显式提供；生成器可从任意工作目录调用。项目和主 checkout 路径由仓库与 Git worktree 注册信息定位。

## 流程(每条 lane)
1. **搜题**(nyxid-oracle,ChatGPT Pro):搜题分深度轨与速度轨两轨混合(CLAUDE.md §3.6)。brief 由 `render-search-brief.sh SEAT_ID OUT [deep|quick] [WINDOW]` 生成:深度轨取 `templates/search-brief.md`,速度轨取 `templates/search-brief-quick.md` 并以 `WINDOW`(`YYMM` 或 `YYMM-YYMM`,缺省为上月与本月)换 `__WINDOW__`;`__SEAT_ID__` 换成本席 id,`__SHA__` 换成当前 `origin/dev` 的 40 位提交(raw.githubusercontent 单文件地址钉版用),`__OPEN_PREREGISTRATIONS__` 换成 open 状态的预登记 issue 列表。排重以仓库发布的已收录问题清单 https://the-omega-institute.github.io/trureturing-mdbook/open-problems.html 加上这份 issue 列表为准。深度轨 brief 只给仓库地址,让席位结合仓库已有的 Lean 结果、文献注、理论卷与已结算卷宗自选问题和搜法;不指定档案、领域、时间窗、预计结算时长或难度,并请席位按深度排序:多位作者陈述、引用或依赖,长期未决,结算需要证明或附机理与整族推广的反例;单个小情形的求值属浅层。速度轨 brief 指定 arXiv 月份窗口、数学物理优先,只收席位已亲手核对的精确小反例或可逐步写出的短证明,名题与需要研究线的候选归深度轨。GPT Pro 两轨轮流,codex 搜题席分属两轨。每个候选须带逐字出处、重要性、既有尝试、仓库适配依据、结算路线、**结算类型**(`small-case` / `family` / `proof`)、文献核对读数与**档位**(第一档新近小猜想 / 第二档计算前沿 / 第三档核心问题);两者都是对候选的标注,不是搜索范围。结算类型为 `family` 或 `proof` 而路线尚未完整的候选开研究线(CLAUDE.md §3.6),由 GPT Pro 深度研究补路线、codex 多席并行子引理;`small-case` 候选照常走两阶段管线。结果落 `results/rN.json`。
2. **靶清查**(`TARGET-GATES.md`;已判条目见 `SCREENED-OUT.md`,别重筛):派席前四关,按成本升序——① curl OEIS 原文查是否已被证(语料的 `research open` 标注只说明没人改过那个文件,不能代替现行文献核对);② 对象级去重,**先查钉版 mathlib** 再查本仓(上游一般定理会静默实例化、不留标识符痕迹);③ 档位(悬赏题、名题的精确等价物、只剩有限残余的已发表结果,全部出局);④ 从**定义**而非猜想模式算数值。四关各自独立,过三关不算过。
3. **探针**(codex-cli,只读 worktree,scratch `/tmp/op-pNN/`):先用 Python 独立核算真假(可证伪预测写在跑之前),再 Lean 整证;`propose` 只认「主陈述以标准三公理编译且无 sorry」;`refuted` 也是结果。已知结果不派席(只 cover 或作前置桥)。
4. **预登记**(GitHub issue,探针之前):写逐字出处、量词写全的陈述、档位、文献核对读数、逃逸见证与范围墙。形式化直接写 D5 Lean 与 Blueprint Scribe,不以理论卷或 ingest 为前置(CLAUDE.md §1.2);内容已有 atom 时同交付 `make deposit ATOM_ID=… GID=…` 并 cover,无 atom 时 `make deposit-uncovered GID=…`。理论卷增订仍可选,走 `op-ingest-new-noalign.sh`(不运行 align)。
5. **Stage A**(`op-resume-seat.sh … implementation`):模块 + Scribe 镜像 + `make lean`/`lean-report`/`emit`,**在任何门之前停下**(envelope `mirror-ready`)。brief 由 `gen_stage_briefs.py` 从实施 brief 切出;基底模板 `templates/impl-base-brief.md` 带产地类型化、import 最小化、公开面自觉、header 工具校验、emit 前刷新报告等块(`add_base_blocks.py` 可补进旧 brief)。
6. **判形核对**(只读 codex 席,`templates/judgement-form-check-template.md`):逐声明判 §3.2 的 `content` / `bind-only`,并要求为每条 content 点名逃逸见证。与镜像核对同属**冻结之前**的只读阶段,理由相同:冻结后改 `.lean` 撞 SL-008,只能整条重做。两种最会藏的形状是「沿显然同构传输上游定理」与「把两元素 `decide` 当成内容」。同席顺带核对交付陈述与源句是否同强度(猜想说 `rank = 2`,只证 `∃ 两个生成元` 不算)。
7. **镜像核对**(只读 codex 席,`templates/mirror-check-template.md` 十二项):括号/合取/绑定变量/强制转换/整除/关系节点/完备性(公开 def 也要镜像或 private)/取值核对/header/定义保真/产地(FromLiterature 须有带 DOI 或 arXiv 的 L 平面注)/import 最小化。
8. **Stage B**(`fill_mirror_fixes.py` 把核对结果填进 Stage B brief):**发射次序先于一切**——带 `OpenProblemResolutionClaim` 的 lane,Stage A 只发射不含该节点、也没有 `Problems/` 卷宗的 Phase A 形态(`Library/` 注相反,`FromLiterature` 要求它在树上);冻结前那次 emit 带上结算元数据必 exit 2 `invalid-problem-resolution-source`,且没有任何冻结前状态能满足该校验。deposit 之后才还原两样、二次发射、折进一个 builder commit。然后先修镜像,改过镜像必做渲染检查(发射 md 无 `&&`/`||`/`==`;`make gate BASE=<40-hex-commit-sha>` 中点名本模块的 `markdown red` 行即停),再冻结:有 atom 的 `make deposit` + cover(锚 atom 也要 cover),无 atom 的 `make deposit-uncovered`、一个 builder commit、晚期去重、push、`make pr-open AUTO_MERGE=0`(等待评审后再开启自动合并)。
9. **三席评审**：`gen_review.py --codex3 LANE PR BRANCH WORKTREE ENVELOPE TARGET ROUND` 生成 architecture、quality、tests 三个 codex-cli 核验席的 brief。默认在同一 worktree 串行运行；`chains/postb-reviews.sh` 将 round-1 三席一起派出并 wait 收拢，轮内互盲；不宣称模型多样性。
10. **重做**:冻结后任何镜像/产地/import 修补都是全新 deposit(cover 收据绑定 Scribe 哈希);同一 lane 第三次非数学重做即停（CLAUDE.md §3.6 ④）。

## Brief generators

支持 macOS Bash 3.2、Python 3.9+、Git 和 POSIX 工具；联网的 review/search/CI 入口另需 `gh`，`postb3.sh` 还需 `make`。通过系统包管理器安装并将命令加入 `PATH`。所有入口支持 `--selftest`；测试使用 `briefgen/testdata/` 的合成输入、golden 摘要和本地 Git/GitHub/make 存根，不派席、不联网、不运行 Lean。

公共配置为 `OP_SCRATCH`（必填的现有目录）、`OP_STATE`、`SSHX_HOME` 和 `OP_NAME_PREFIX`，默认值与下方 pipeline runtime 相同。输入检查使用退出码：10 用法、11 缺输入、12 缺工具或版本、13 输入内容无效、16 I/O 或外部命令失败。CI 未绿返回 1；review 的 4/6 分别保留 head 不符和 PR head 落后远端的判词。子命令非零退出码直接传出。

| 入口 | 输入与用途 |
| --- | --- |
| `gen_stage_briefs.py --lane-spec LANE NYXID_SEAT` | 读取 `lanes/LANE.json`，生成实施基底、Stage A、Stage B 和 mirror brief；`NYXID_SEAT` 为兼容位置参数 `architecture` 或 `quality`，评审布局为三 codex。 |
| `gen_stage_briefs.py SCRATCH LANE WORKTREE BRANCH MODULE [NYXID_SEAT]` | 保留从既有实施 brief 切分两阶段与镜像的接口。 |
| `briefgen/lane_brief.py SCRATCH SPEC.json` | 独立从 lane JSON 生成实施基底。字段为 `lane,title,worktree,branch,module,gid,target_md,commit_subject,pr_title_hint`；module 为不带扩展名的单个路径。 |
| `fill_mirror_fixes.py SCRATCH LANE RESULT.json` | 将 blocking/advisory findings 填入 Stage B 的唯一 `<<MIRROR_FIXES>>`。 |
| `fill_mirror_fixes.py --prepare LANE NYXID_SEAT MIRROR_FLIGHT` | 完整 Stage B 准备，默认重新生成阶段；`REGEN=0` 使用现有 Stage B。`ORCH_NOTE` 指定覆盖说明文件，`JF_FLIGHT` 指定判形结果；结果取 `SSHX_HOME` 中数字最大的 attempt。 |
| `briefgen/implb_head.py LANE` | 从单模块 lane JSON 生成 Stage B head；拒绝缺失 dossier、issue 或 settlement。 |
| `briefgen/mirrorfix_cont.py LANE SUFFIX ENV WORKTREE PREV PREV_MIRROR OUT OUT_MIRROR ROUND TARGETS...` | Read a rejected mirror with nonempty `blocking_findings` (`file_line,claim,fix`, optional `owner`), render the Stage A continuation and the next mirror. TARGETS are dotted Lean modules. The mirror requires `approve` or `reject` and forbids `comment`. A `rework-` previous brief keeps the current committed head. |
| `briefgen/lockretry_head.py LANE SUFFIX ENVELOPE WORKTREE PREV_BRIEF OUT` | Read the first `LEAN_TARGETS=` command from decoded envelope conclusion strings, validate its dotted modules, then render a continuation for the targeted build and post-build checks. Readings remain evidence from the envelope; no process-stop claim is inferred. |
| `briefgen/continuation_head.py LANE ISSUE SUFFIX MIRROR_FLIGHT WORKTREE OUT [OWNER…]` | 生成保留未提交交付的继续实施 head，包含镜像 findings 与自扫块。 |
| `briefgen/rework_brief.py SPEC.json` | 生成 `rework-LANE.md`。spec 含 `lane,pr,head,worktree,branch,gid,module,fixes,standing_rows,tally_line,next_layout_line,next_round,commit_source,commit_builder`。已有两个 `lanes/rework-LANE*.json` 时拒绝第三次非数学重做；数学缺陷须显式填 `mathematical_defect`。 |
| `briefgen/rehead.py HEAD REST OUT OLD_SHA NEW_SHA NOTE` | 核对两个完整 SHA 和唯一镜像 anchor，更新 head 并拼接 rest；缺输入时不修改 head。 |
| `gen_review.py --codex3 LANE PR BRANCH WORKTREE ENVELOPE TARGET ROUND` | 复用原 review 模板和生成器，输出 `review-LANE-{architecture,quality,tests}-rROUND.md`；三个席均为 codex-cli，只读。 |
| `gen_review.py --pipeline LANE PR BRANCH WORKTREE ENVELOPE TARGET NYXID_SEAT` | 保留旧布局的单轮拼装接口；原七位置参数接口也保留。PR head 必须与远端 head 对齐；只有干净且超前于 PR head 的 worktree 才可 `reset --keep`。 |
| `briefgen/standing_append.py PR SPEC.json` | 复用 `standing-check.py` 的 standing parser，追加 `rows`、`tally`、`next`；拒绝过程叙述、叙事裁决和 stale pending 状态。 |
| `briefgen/postb3.sh LANE PR` | 在 PR head 上等待 required check，读取实施 flight，再生成三 codex round-1 brief；输出 `READY`，不派席。 |
| `briefgen/ci_body_final.py PR HEAD` | 核对 completed CI 的 required/current job，读取 current 原始日志，替换正文 CI 行；读取失败或 CI 未绿不编辑正文。 |
| `briefgen/exclusions_compact.py [--preregistrations] [YYMM-YYMM]` | 压缩 `briefs/search-exclusions.md` 中的 arXiv、OEIS 和具名排除项；可并入 open 预登记 issue，按窗口补入 dev 的已有文献标识。 |
| `render-search-brief.sh --codex LETTER ROUND [deep|quick] [WINDOW]` | 通过原 renderer 生成 codex 只读搜题 brief；实现为 `briefgen/codex_search.py`，与原深浅轨共用模板、dev SHA 和 open 预登记查询。 |
| `add_base_blocks.py [--base SOURCE] FILE…` | 从唯一 tracked 基底模板补入 public-surface/import/provenance 三块；显式 SOURCE 支持已有基底。 |
| `briefgen/purge_stale_fib.py WORKTREE [--delete]` | Stage B head 引用的缓存工具；仅列出或删除形态过期的模块报告 zip 及其 trace/hash，不改 Lean。 |

`OP_PROVENANCE_MD` 是实施基底或 Stage B head 的调用者产地文本；工具不内置会话身份。搜题另须显式给 `OP_SEARCH_WORKTREE`、`OP_SEARCH_OUTPUT_DIR`；深度轨还需 `OP_CODEX_EXCLUSIONS` 指向排除项文字文件。`OP_NAME_PREFIX` 进入 codex 搜题 seat 名称。

`templates/blocks/` 是通用块的 tracked 居所；`Context.block()` 优先读取调用者显式提供的 `OP_SCRATCH/briefs/同名文件`，其余读取 tracked 块。所有 stage/rework 必需块均有通用 tracked 默认值；调用者可显式覆盖特定输入。`briefgen/stages.sh`、`stageb_prep.sh`、`review.sh` 只组织 canonical 生成器和共享块，面向调用者使用表中的主入口。

运行 `python3 briefgen/selftest.py --selftest` 可检查全部生成器；`python3 standing-check.py --selftest` 检查 standing parser。也可逐文件执行 `--selftest`。测试覆盖带空格的路径和不同工作目录；真实联网行为仍由对应 GitHub/make 命令返回值裁决。

## Lane chains and preregistration

`chains/` composes the existing pipeline waiter and brief generators. It supports Bash 3.2 and Python 3.9+ with `git`, `gh` and `make` on `PATH`. Run a chain as a host-managed foreground/background job that owns its full lifetime. Every dispatch goes through `pipeline/seat-wait.sh`; the chain never stops a runner. Inputs use `OP_SCRATCH`, `OP_STATE`, `SSHX_HOME` and `OP_NAME_PREFIX` as above; repository and main checkout are derived. The worktree argument is a path, resolved against the main checkout when relative, and must match `lanes/LANE.json`.

| Entry | Inputs and behavior |
| --- | --- |
| `chains/stagea.sh LANE WORKTREE CONTINUATION MIRROR` | Dispatch the named continuation brief, require `mirror-ready`, then run the mirror/Stage B/CI/round-1 sequence. CONTINUATION=`-` starts at the mirror without an implementation dispatch. |
| `chains/postb-reviews.sh LANE PR WORKTREE` | For an existing Stage B PR, call `briefgen/postb3.sh`, update its CI body with `briefgen/ci_body_final.py`, then dispatch `review-LANE-{architecture,quality,tests}-r1` together and join every child with Bash `wait`. Preparation errors prevent all dispatches; child failures propagate after all children finish. |
| `chains/from-mirror.sh LANE WORKTREE MIRROR` | Require mirror `approve`, prepare Stage B with `briefgen/stageb_prep.sh`, create a missing head with `implb_head.py`, dispatch Stage B, call `postb3.sh` and `ci_body_final.py`, then dispatch architecture, quality and tests in order. |
| `chains/rework.sh LANE PR NEXTROUND WORKTREE OLDHEAD RW MW [REWORK_SPEC.json]` | Dispatch `rework-LANE-RW`, mirror `mirror-LANE-MW` using `mirror-check-LANE-MW.md`, and resume `rework-LANE-RWb` via `rehead.py`. Require an unchanged worktree head during mirror review and a new PR head after resume. Check standing, call `gen_review.py --codex3`, then dispatch all three review roles. RW and MW are explicit names, e.g. `r1 rw1`. The optional spec is rendered by `rework_brief.py`; otherwise the rework brief must already exist. |
| `chains/prep-and-chain.sh TYPE LANE WORKTREE A [B]` | Call `pipeline/prep-lane-tree.sh` before continuing. TYPE `stagea` needs A=continuation and B=mirror; TYPE `mirror` needs A=mirror. |
| `briefgen/stageb_prep.sh --dispatch LANE NYXID_SEAT MIRROR_FLIGHT` | Prepare the filled Stage B brief, then dispatch `implb-LANE-r1` through the waiter. Omit `--dispatch` for preparation only. |
| `briefgen/lane_from_probe.py KEY ISSUE SETTLEMENT MODULE WORKTREE FLIGHT DOSSIER_SLUG COMMIT_SUBJECT` | Read the latest numeric attempt under `SSHX_HOME`, fetch the issue title, and write `lanes/KEY.json` and `lanes/KEY.target.md`. SETTLEMENT is `Proved` or `Refuted`; MODULE is one extension-free D5 path. The envelope requires `module_plan` and `triage`; scratch paths are taken from its `scratch_files`. Probe proof evidence is reported input, not independently verified by this generator. |
| `briefgen/file_prereg.py KEY:DRAFT [KEY:DRAFT ...]` | Require `OP_PENDING`, read `prereg-DRAFT.md` and `post/titles.tsv` (`filename<TAB>title`), refuse duplicate-title search hits across all issue states, file validated bodies, and atomically record `key<TAB>number` in `post/issues.tsv` after each success. Existing keys are retained and skipped. |

Preregistration filing validates the whole requested batch before creating an issue. Bodies containing `LEAN_BLOCK`, `COMPILE_LINE`, `SHA_`, empty inline backticks or whitespace-only inline backticks are rejected; triple-backtick code fences are permitted. `post/issues.lock` excludes concurrent filers. A failed search or create stops the batch and preserves successful mappings. If GitHub accepts a create but its response or the local mapping write fails, reconcile that issue before retrying; duplicate search refuses a second filing.

Chains use the lane spec's branch and the supplied seat names, with `OP_NAME_PREFIX` prepended only at dispatch. Required initial briefs must exist before the first seat starts. Generated briefs are checked before their dispatch. Logs live in `OP_SCRATCH/logs`; each shell chain ends with `CHAIN_EXIT=RC`. A valid non-advancing verdict prints `CHAIN_STOP` and returns 0, preserving the source chains' stop behavior. Malformed/missing results and dependency failures return nonzero. Error codes are 10 usage, 11 missing input, 12 missing tool/version, 13 invalid input/result, 14 duplicate/lock/head conflict, and 16 I/O or external read failure; invoked dependency failure codes propagate.

Every new entry supports `--selftest`. `chains/selftest.py --selftest` covers all chains and dispatch-mode preparation, including parallel dispatch and joined failures; `briefgen/port_selftest.py --selftest` covers the probe generator and preregistration filer. Tests use synthetic lane fixtures in paths containing both `__` and spaces, stub Git/GitHub/make/dispatch, and perform no polling waits or real network writes. `chains/selftest.py --compare-scratch SOURCE_DIRECTORY --shim SHIM_DIRECTORY` additionally runs caller-supplied source chains on equivalent fixtures and compares seat sequences; source files are read-only. Only source locations and seat prefixes are rebound for that comparison. `chains/selftest.py --compare-layer3 SOURCE_DIRECTORY` compares Stage A, Stage A with `CONT=-`, and the parallel post-B reviews. `briefgen/{mirrorfix_cont,lockretry_head}.py --selftest` covers continuation inputs and rendered verdict/build rules.

## Pipeline runtime

`pipeline/` 提供跨会话运行器，支持 macOS `/bin/bash` 3.2、Python 3.9+、Git、系统 POSIX 工具及仓库已有的 make 入口。GPT Pro 搜题还需 `gh`；实际派席使用 `seat/dispatch.sh` 及其 `seat/sshx-runner-lib.sh`，broker 使用 `nyx/nyx.py ask`。依赖通过系统包管理器安装并放入 `PATH`；sshx 安装根由现有 `SSHX_PLUGIN_ROOT` 配置，Nyx 使用现有 `NYX_CLI`、`NYX_POOL` 配置。所有项目路径从脚本位置定位；主 checkout 取 `git worktree list --porcelain` 第一项，并验证其为非 bare checkout。任意工作目录（包括带空格的路径）均可调用。

公共输入为 `OP_STATE`（默认 `${XDG_STATE_HOME:-$HOME/.local/state}/trureturing-op`）、`OP_SCRATCH`（需要 scratch 的工具必填）、`SSHX_HOME`（默认 `$HOME/.sshx`）及 `OP_NAME_PREFIX`（默认空）。`OP_STATE` 保留 `spool/NAME.job`、`running/NAME.job`、`joblogs/NAME.log`、`jobs-seen.txt` 和 `spool/STOP`；生产者写 `.job.tmp` 后原子改名。`OP_SCRATCH` 保留 `briefs/`、`results/`、`logs/`、`preset/NAME`、`flights.txt`、`max-seats` 和 mkdir 锁 `gate.lock`。preset 一行为 `DONE RESULT_PATH` 或 `WAIT FLIGHT`；flight 是 24 位十六进制串，`flights.txt` 的完成记录为 `NAME `。附加的 `waiters/NAME.json` 记录等待者 PID、flight、worktree 和开始时刻，用进程表验证存活；不替代 flight 账。`gptpro.lock` 在 `OP_STATE` 中串行化 GPT Pro 请求，`gptpro-queue.lock` 在 scratch 中串行化队列消费者。

| 工具 | 输入 | 结果与哨兵 |
| --- | --- | --- |
| `pipeline/supervisor.sh` | 无参数；`OP_STATE`；在持久终端运行 | 每个 `.job` 一个直属子任务，工作目录为主 checkout；日志最后一行 `JOB_EXIT=RC`。STOP、INT、TERM 均先收拢子任务，输出 `SUPERVISOR_WAIT`、`SUPERVISOR_END`。 |
| `pipeline/watch-jobs.sh` | 无参数；`OP_WATCH_MAX_SECONDS` 默认 6600 | 遇到未见的末行 `JOB_EXIT=RC` 即打印名称与日志尾部并返回；总等待到期输出 `WATCH_TIMEOUT`。 |
| `pipeline/seat-wait.sh` | `NAME BRIEF WORKTREE STAGE [STAGGER]`；scratch 中 `briefs/process-safety-block.md` | preset 优先；否则等 worktree 空闲、席位容量和优先级后调用本仓 `seat/dispatch.sh`。替换 safety block 的 `__FLIGHT__`，最终输出 `DISPATCH_EXIT=RC`，并传递退出码；读到 `RUNNER_EXIT=RC` 时保留 runner 的失败码。 |
| `pipeline/sweep-ghost-flights.sh` | 无参数；`OP_SCRATCH`、`SSHX_HOME` | flight 目录存在且成功读取的进程表中无对应 runner 时，追加 `NAME ` 并打印 `TOMBSTONE NAME FLIGHT`。进程表读取失败不结算。 |
| `pipeline/refresh-if-stale.sh` | `TREE`；`REFRESH_LAG_SECONDS` 默认 10800；`OP_REFRESH_LOCK` 默认 `$OP_STATE/main-lean.lock` | 主 build 的 `.main-built-at` 为 `SHA ISO_TIME`。仅在 tree 无在飞席位且 D5 相对 origin/dev 无改动时，按 stamp 年龄或已有 report semantic version 刷新；更新 `.main-cloned-at`，输出 `CACHE_REFRESH skip…` 或 `CACHE_REFRESH done… rc=0`。主 build 的写入者须使用同一锁。macOS 使用 clonefile，其他系统使用普通复制。 |
| `pipeline/prep-lane-tree.sh` | `WORKTREE` | fetch 后 fast-forward 无自有提交的 lane，或 merge 干净的分歧 lane；拒绝带自有提交的 dirty 分歧 lane；调用 `make lean-cache-ensure`，输出 `PREP=RC`。 |
| `pipeline/probe-queue.sh` | `[KEY…]`；必填 `OP_PENDING` 目录、`OP_LANES`（空格分隔 `KEY:SUFFIX`）、`OP_WORKTREE_PATTERN`（含 `{suffix}`；相对路径以主 checkout 为基准） | 读取 scratch 的 `briefs/probe-KEY-r1.md`，创建缺失 worktree，确保 cache，通过 seat waiter 派 thinking 席；`PQ_WAITERS` 默认 16，`PQ_FIRST` 为优先 KEY 列表；所有子任务结束后 `PROBE_QUEUE=RC`。`pq-dispatched.txt` 记录已派 KEY。SUFFIX 为 `-` 时跳过。 |
| `pipeline/resume-after-restart.sh` | `[--dry-run]`；`OP_STATE`、`OP_SCRATCH` | 对无 `JOB_EXIT` 的 running job 建 preset 后原子重排 spool；`respool-after-recovery.txt` 可逐行点名重跑已退出的 job。直接 waiter 命令可自动取 STEP；复合 chain 的 STEP 顺序由 `running/NAME.steps` 每行提供一个无 prefix 名称。输出 `RESUME_DONE`。 |
| `pipeline/migrate-chain.sh` | `[--dry-run] PROCESS_PATTERN STEP…`；必填 `JOB`、`CMD` | 为顺序 STEP 建 preset，只向唯一匹配且经再次验证的 chain shell 发 TERM，随后原子提交 CMD。codex、runner、dispatch 及其子树不被遍历或停止。输出 `MIGRATED JOB chain=PID dry_run=N`。 |
| `pipeline/gptpro-search.sh` | `ID deep` 或 `ID quick [WINDOW]`；`OP_SEARCH_SELECTION`、`OP_SEARCH_EXCLUSIONS` 默认 scratch 下的 `briefs/search-selection-block.md`、`briefs/search-exclusions-compact.md` | 调用仓库 `render-search-brief.sh`，追加现成 selection 与 exclusions，串行调用 broker。保留一次空流 EOF 重试及最多六次 quota 重试（间隔 600 秒）；输出 `NYX_OK` 或 `NYX_FAIL`，返回 broker 退出码。 |
| `pipeline/gptpro-queue.sh` | 无参数；`OP_GPTPRO_QUEUE` 默认 scratch 的 `gptpro-queue.txt`，每行 `LANE ROLE ROUND PR` | 默认读 `briefs/review-LANE-ROLE.md`；可用可执行的 `OP_REVIEW_PREPARE LANE ROLE ROUND PR OUT` 生成含 PR 正文的 brief。串行 broker 调用完成后出队，失败保留首行；输出 `QUEUE_RUN`、`QUEUE_DONE… rc=RC`、`NYX_SEAT_OK`、`QUEUE_EMPTY`。 |
| `pipeline/common.sh`、`pipeline/selftest.sh` | 前者供 source；后者 `--selftest` | 共用输入验证、锁、进程解析、恢复与 broker 调用；后者运行全部工具的隔离测试。 |

席位 gate 每次读取 `max-seats`；文件不存在时取 `OP_MAX_SEATS`，默认 16，并把同一值作为 `MAX_CODEX` 参数交给 dispatch。移除 `OP_NAME_PREFIX` 后，`review-`、`implb-`、`rework-`、`hotfix-` 优先级为 0；`mirror-`、`impla-`、`fixa-`、`fixb-`、`fix-` 为 1；其他为 2。更高优先级的存活等待者只有在其 worktree 空闲且尚无 runner 时阻挡低优先级者。优先级 2 等满 14400 秒且同类运行席少于两个时可越过优先级等待；`OP_WAIT_SINCE`（兼容 `DWF_WAIT_SINCE`）传入原始 epoch 起点。进程表读取失败为具名错误。WAIT preset 只在三次连续成功读取的进程表均无 runner 后结束；结果取数字最大的 `attempt-N/result.json`。结束时只清理命令包含该 flight attempt 路径且可执行文件名为 Lean、Lake 或 Python 的遗留子任务。

pipeline 的容量判据只有席位 cap 和 worktree 占用，不读取 CPU 负载或 Lean 进程数。`seat/dispatch.sh` 是独立依赖，其自身门策略由该入口负责；调用方须使用满足运行要求的 dispatch 版本。`OP_POLL_SECONDS` 默认 30，`OP_LOCK_ROUNDS` 默认 120，`OP_GATE_ROUNDS` 默认 1440，`OP_RUNNER_POLL_SECONDS` 默认 5，`OP_REFRESH_LOCK_ROUNDS` 默认 480。锁等待有界，未取得锁不会继续执行；锁由取得者释放。等待或停止期间的子任务由同一脚本 wait 收拢。

启动验证使用具名 `PIPELINE_*` 诊断：10 用法错误，11 必需输入缺失，12 工具缺失或版本不符，13 输入值无效，14 已有 job 或身份冲突，15 锁或 gate 到期，16 I/O、Git 或进程读取失败。prep 的 3–6 保留 fetch、fast-forward、merge conflict 和 dirty 分歧状态；实际子命令的失败码由对应入口传出。

运行每个脚本的 `--selftest` 可隔离验证其判断与状态逻辑；每例打印 `ok`/`FAIL`，末行 `SELFTEST_FAILS=N`，失败返回非零。测试使用临时 state、scratch、checkout 和命令存根，不启动真实 runner 或 broker，不读取宿主进程，也不作长等待。

selection/exclusion 生成器、lane 映射和复合 chain 的 STEP 元数据属于调用方输入；运行器不加载 `restore.sh`、`mk-exclusions-compact.py` 或 `nyx-seat.sh`。review brief 的生成与 PR 正文插入通过现成 brief 或显式 `OP_REVIEW_PREPARE` 提供。

## Landing and main cache warming

These tools use the same public configuration and derived repository/main checkout as the chains. They require Python 3.9+, Git, `gh`, `make`, POSIX `sleep`, and Bash 3.2. `OP_SCRATCH` is an existing directory. Run bounded waiting and warming as a host-owned job; the command stays alive until its children finish.

| Entry | Inputs and behavior |
| --- | --- |
| `pipeline/land.sh PR ROUND HEAD ARCHITECTURE QUALITY TESTS [close]` | Build a three-codex standing spec and call `briefgen/standing_append.py`. Votes are `approve`, `reject` or `abstain`; HEAD is a full SHA. Without `close`, record the round only. With `close`, require closed standing without a reject, fetch the PR head and dev, inspect the successful merge tree for state records and absence of retired accepted files, mark ready, and merge with `--merge --match-head-commit HEAD`. Required checks still pending select `--auto`; failed or absent required checks block. Recheck the reviewed head before merging. |
| `pipeline/land-watch.sh PR [WORKTREE]` | Wait for MERGED, then the merge commit's dev push `ci-current.yml` run. Use native `gh run watch` with a timeout. A non-success own run is accepted only when a later completed successful dev push run has a distinct head containing the merge commit; report both run ids. Success invokes `make worktree-remove NAMES=<basename>` when WORKTREE is supplied; its basename must not contain whitespace because the make removal interface splits names. |
| `pipeline/main-warm.sh [HOURS [INTERVAL_SECONDS]]` | Default 48 hours, 1800 seconds between rounds; a monotonic deadline bounds the loop. In each round, inspect the newest `lean-cache-v2-` Release across all paginated releases. Advance a clean `dev` main checkout only when its `producer_commit_sha` strictly descends from HEAD. Run `make lean-cache-from-github-without-mathlib REFRESH_STALE=1`, then `make lean` (the shared Lean build lock is taken by make). Failure stops the loop. Logs use `OP_STATE/main-warm-{restore,lean}.log`; successful builds stamp the path defined by `briefgen/common.py:MAIN_WARM_STAMP` (default `.lake/build/.main-built-at`) as `SHA ISO_TIME`. |

Landing returns 14 for reviewed/fetched head mismatch, 20 for rejected/invalid standing, 21 for duplicate freeze or merge conflict, 22 for a non-open PR, 23 for failed/missing required checks, and 24 for no frozen state records. A reject is recorded and never merged. Watch outcomes are `DEVPUSH_OK` (0), `DEVPUSH_OK_LATER` (0), `DEVPUSH_RED` (1 for no qualifying later run; input, command and timeout failures retain their error codes), `DEVPUSH_NORUN` (2), and `CLOSED_UNMERGED` (4). Verification failures after selecting the own run print `DEVPUSH_RED SHA run=ID reason=...` and skip worktree cleanup. Merge/run wait expiry returns 124; cleanup errors return 16. Shared input codes remain 10/11/12/13/16.

Watch bounds are positive integers: `OP_MERGE_ROUNDS=240`, `OP_RUN_ROUNDS=40`, `OP_LATER_ROUNDS=60`, and `OP_RUN_TIMEOUT=14400` seconds. `OP_POLL_SECONDS=60` controls external polls and accepts nonnegative decimal seconds; the native run-watch interval is 60 seconds. State and lock paths are defined by `briefgen/common.py`: state uses `OP_STATE`, then `$XDG_STATE_HOME/trureturing-op`, then `$HOME/.local/state/trureturing-op`. Cache warming acquires the shared `OP_REFRESH_LOCK` (default `$OP_STATE/main-lean.lock`) separately for each iteration via `pipeline/common.sh`; refresh readers use the same lock. `OP_REFRESH_LOCK_ROUNDS=480` and the pipeline's integer `OP_POLL_SECONDS` (default 30) bound acquisition; failure returns 15. The interval argument controls time between warming rounds.

Each entry's `--selftest` uses synthetic Git/GitHub/make responses in temporary paths containing `__` and spaces, with no real network, dispatch, build or long wait; warming uses a synthetic clock. Landing tests cover head mismatch, rejected standing, duplicate/empty/conflicting freeze trees and running/failed CI. Watch tests cover own green, red with containing later green, red without qualifying later green, closed unmerged and no run. Warming tests cover strict ancestry, dirty/non-dev/equal/divergent skips, newest producer choice, lock exclusion and restore/build failures. `pipeline/landing_selftest.py --selftest` runs all three suites.

## 脚本
- `op-resume-seat.sh FLIGHT ATTEMPT BRIEF WORKTREE STAGE [STAGGER] [MAX_CODEX]`:fail-closed 负载门(idle ≥ 20% ∧ lean ≤ 4 ∧ codex 进程 ≤ MAX,300 轮 × 60 s,超时不启动)+ sshx runner。
- `gen_stage_briefs.py SCRATCH LANE WORKTREE BRANCH MODULE`:从既有实施 brief 切 Stage A、Stage B 和 mirror；模板取 tracked `templates/`，错误码遵守上表。
- `fill_mirror_fixes.py SCRATCH LANE RESULT_JSON`:把镜像核对的 blocking/advisory 填进 Stage B brief。
- `add_base_blocks.py FILE…`:把基底模板的三个纪律块补进缺失的 brief。
- `gen_review.py LANE PR BRANCH WORKTREE IMPL_ENVELOPE TARGET_FILE NYXID_SEAT`:生成三席评审 brief(在 SCRATCH 目录运行,写到该目录的 `briefs/`)。模板取本目录 tracked 的 `templates/review-template.md`,GoalArtifact 取 `templates/impl-base-brief.md` 的 yaml 段——两者都不依赖 scratchpad,scratchpad 被清空不影响它。缺输入、席位名不是 architecture/quality、参数个数不对,一律 exit 1。
- `op-sync-dev.sh WORKTREE BRANCH PR`:merge-only 合 dev、推送、等待三门(重算 merge ref;`gh run rerun` 不重算)。
- `op-ingest-new-noalign.sh WORKTREE NEW_BRANCH ADDENDUM SUBJ PRMSG PATTERN [VOLUME]` / `op-ingest-noalign.sh` / `op-addendum-ingest-v3.sh`:理论卷增订 ingest(前两者绕开 align)。
- `op-governance-pr.sh WORKTREE BRANCH COMMIT_MSG PR_MSG [AUTO]`:governance 改动的提交/推送/开 PR。
- `op-fold-anchor-cover.sh WORKTREE BRANCH ATOM SOURCE_ID`:把漏掉的锚 cover 折进 builder commit。
- `standing-check.py PR [--round N | --closed]`:派下一轮评审前、或合并前,机器核对 PR 正文的评审 standing——每一轮是否都有三席行与 tally、有没有占位判词、下一轮布局是否点名正确的轮次、`tests` 有没有被派给 nyxid、nyxid 席在相邻两轮之间有没有换位。`--round N` 传「即将派的那一轮」:正文自身无法区分「跑过但没记」与「本来就到此为止」,这一项只有调用方知道。`--closed` 是合并前那一次:要求末轮无 reject 且不再有未闭合的轮次。`--selftest` 包含 fixture golden 和拒绝用例。

## 负载门、镜像核对与实施模板
- `op-resume-seat.sh` 的负载门含**上游健康**条件:`CODEX_HEALTH_URL`(默认 codex 提供方 `/responses`)返回 502/503/000 时不放行;判席位死因看 `worker.stdout.log` 尾部,不看退出码。
- 镜像核对模板第 3 项:「公式中每个符号须为绑定变量 / 本模块已镜像的 Lean 公开名 / Mathlib 或原子对象,禁临时缩写」;第 7 项:公开 def 也须镜像或 `private`;第 11 项:L 平面注带 DOI 或 arXiv;第 12 项:import 最小化(禁 umbrella `import Mathlib`)。
- 实施基底模板:header/helper 以 `tools/scripts/agent/header-check.sh` 工具校验;emit 前先 `make lean-report`;Stage B 改镜像后必做渲染检查(`grep -E '&&|\|\||==|!='` 发射 md 为空;`make gate BASE=<40-hex-commit-sha>` 中点名本模块的 `markdown red` 行即停)。
- 理论卷增订 ingest 走 `op-ingest-new-noalign.sh`(不运行 align)。
