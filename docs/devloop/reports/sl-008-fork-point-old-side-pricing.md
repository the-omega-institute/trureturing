# SL-008 fork-point 旧侧迁移离线定价

> **REPORT-ONLY / 测量 worker 产物。** 本轮不修改 harness、CI、admission 或 SL-008。测量窗口固定锚定在 `55a4369ce4962d8c979d4418b62555c69c1ec09b`（#1358）及其之前 40 个 merge PR；报告修订前先执行 `git fetch origin dev`（`EXIT=0`）与 `git merge origin/dev`（`EXIT=0`，`ort`，无冲突），合并后的真实 `origin/dev` tip 为 `29887674a0952d5003cdd0689953f1416fbf6a60`，合并提交后的本分支 `HEAD` 为 `c94bab7c78e55612aefae376fe65e878610d85af`。本轮没有把锚点后的提交混入固定窗口，也没有重做全部测量。

## 0. 一句话结论

**PROCEED TO SHADOW MEASUREMENT：命中率条件已达标，固定窗口的离线估计为 `37/40 = 92.5%`，超过 80% 门槛；吸收条件未测，故这里只授权在 CI 增加一个不供判决的影子测量步骤，不授权实施整侧迁移。** `.github/workflows/ci.yml:467-469` 明确 `baseline-admission` 的 `needs: lean-inspect`；cache miss 多产的 report 位于 admission 前置关键路径，不能由另一个并行 job 的总时长吸收。一次本地空 report cache 实产 `real 149.71s`、`EXIT=0` 只证明局部生产成本，不证明三 report CI DAG 的端到端增量。

## 1. 病灶与税

SL-008 当前逐字节要求候选保留 protected base 的冻结账本。冻结账本是 append-only 的内容寻址分片；候选分叉后 dev 新增分片，会被误读成候选删除 protected-base 文件。共享上下文的原始读数是：失败 CI run 口径 `2/35 = 5.7%`，但已合入 PR 中含 merge-dev 追平提交的口径为 `30/40 = 75%`。

其中机制归因必须扣除 #1346 与 #1335：这两个 PR 的 dev 同步没有带入冻结分片。因此 **SL-008 base 追平税的机制归因上界是 `28/40 = 70%`，不是 75%**。`30/40` 只描述同步现象，不能冒充 SL-008 因果数。

正解不是只换账本路径，而是把旧侧的树、Lean report、DAG、冻结账本作为一个能力包一起从 protected base 迁到 fork point。第三份 merge-base Lean report 是这个能力包的成本变量。

## 2. 测量方法

样本选择命令与原始样本数：

```bash
git log --first-parent --format='%H%x09%P%x09%s' \
  55a4369ce4962d8c979d4418b62555c69c1ec09b \
  --grep='^Merge pull request' -n 40
# RERUN_EXIT=0; 40 lines
# first: #1358 at 55a4369ce4962d8c979d4418b62555c69c1ec09b
# last:  #1313 at 72193105ec9bf57671dce685fbeddfe19d542543
```

这个离线窗口的选择口径是 **first-parent 上标题匹配 `^Merge pull request` 的 merge commit**，不是“所有 PR”。它会漏掉以 squash commit 或直接提交形式进入 `dev`、因而没有该标题/双亲形状的 PR，例如 #1337。故下文 `37/40` 只对这 40 个 merge-commit 样本成立，不能冒充全体 PR 的抽样比例。该漏样不改变本窗口的命中结论：窗口成员和 80 个已测地址均未变化，按同一既定样本重算仍是 `37/40 = 92.5%`；**未测**被漏 PR 的离线地址，所以不对窗口外命中率作外推。

每个 merge 均按以下原命令取父与 fork point：

```bash
base=<merge>^1
head=<merge>^2
fork=$(git merge-base "$base" "$head")
```

为每个 SHA 用 `git archive` 建独立绝对路径临时树，并调用该树内的生产 helper。实际调用原文为：

```bash
/usr/bin/env bash \
  <absolute-tree>/Meta/StrataLint/scripts/report/lean-report-input.sh \
  address --repository <absolute-tree>
```

helper `address` 的原始输出是四列：`repository_address producer_sha lean_sources_sha config_sha`；CI cache key 使用第一列 `repository_address`。80 次调用（40 base + 40 fork）全部 `EXIT=0`。

“跨 PR 命中”有两个口径。`cross-other` 严格排除当前样本自身，但允许命中固定窗口内时间上更晚（对该 PR 而言尚属未来）的 PR 的 `addr_base`；`cross-prior-only` 还施加时间方向，只允许命中该 PR 当时已经产过的、更旧 PR 的 `addr_base`。并集是 same-PR 与严格 `cross-prior-only` 的逻辑或。

## 3. 命中率读数

| 判据 | 原始计数 | 比例 |
|---|---:|---:|
| 同 PR：`addr_fork == addr_base` | 23/40 | 57.5% |
| `cross-other`：命中窗口内其它 PR 的 `addr_base`（允许未来 PR） | 34/40 | 85.0% |
| `cross-prior-only`：只命中当时已产过的更旧 PR 的 `addr_base` | **27/40** | **67.5%** |
| 同 PR与 `cross-prior-only` 并集（估计命中率） | **37/40** | **92.5%** |
| 并集 miss | 3/40 | 7.5% |

`cross-other=34/40` 是窗口内地址复用上界，`cross-prior-only=27/40` 才表达“该 PR 当时已经被产过”的严格历史时点含义。加入 same-PR 后，严格口径的 union 仍为 `37/40 = 92.5%`，所以决定性命中率数字不变。这个 92.5% 是固定 40-PR 窗口内的离线估计，不是 GitHub Actions cache 的在线命中遥测；本报告没有测在线集合。

## 4. Miss 与原因

三个 miss 都是 fork 到 base 的 **producer 闭包**变化，不是 Lean sources 变化；其 config hash 也未变。

| PR | fork -> base | `.lean` fork->base | producer 差异 | 该 PR 自身是否改 `.lean` |
|---:|---|---:|---|---:|
| #1315 | `d66b0844` -> `1fad2b44` | 0 | 7 个 Engine/CLI `.cs` 路径变化 | 是：新增 `D5/S3/Arith/Congruence/QuarticThirtySix.lean` |
| #1314 | `d88d7290` -> `72193105` | 0 | `EchoVerifyCommand.cs`、`RepositoryPathPolicy.cs` | 否 |
| #1313 | `d88d7290` -> `e1cfc429` | 0 | `EchoVerifyCommand.cs` | 否 |

因此“miss 是那批 PR 真的改了 `.lean`”不成立：#1314、#1313 没改，#1315 虽自身新增 Lean 文件，但它的 fork address miss 由 fork 后、merge 前 dev 上的 producer 演进造成，而不是 fork->base 的 Lean source hash 变化。

## 5. 冷态生产成本

这里的冷态是 **report cache 为空**、Lean build cache 保持现有 CI 常态。命令与原始结果：

```bash
cold_root=$(mktemp -d /tmp/oldside-cold-report-cache.XXXXXXXX)
/usr/bin/time -p env STRATALINT_REPORT_CACHE_ROOT="$cold_root" make lean-report

# LEAN_CACHE status=present method=none
# LEAN_REPORT_PROVENANCE side=candidate mode=produced ...
# real 149.71
# user 178.03
# sys 141.61
# COLD_REPORT_EXIT=0
```

生产输入地址为 `8e7706516aac42673a60f54e87e18bd3c4dba3c977de6af61528e78527078fea`，report SHA 为 `41757118fea1ceb37ed180effb87f27c9c7ee05dacd2f3b700717c193630726a`。以 `3/40` miss 率折算，`149.71 * 3/40 = 11.23s/PR`。**`11.23s/PR` 只是跨 PR 的期望摊销，不是发生 miss 的那一个 PR 的延迟；单个 miss PR 在迁移后关键路径上会完整承受一次生产墙钟。本地唯一读数是 `149.71s`，线上该值未测。**该读数不能与并行 `candidate-engineering=184s` 比较后推出“可吸收”：`.github/workflows/ci.yml:467-469` 的 `baseline-admission needs: lean-inspect` 使 report miss 落在 admission 前置关键路径。**未测：本轮明令不改 CI，因此没有实测在线 restore 命中率、在线 miss 墙钟或完整端到端增量。后续门槛不再依赖端到端 P95：同 SHA 的无影子反事实不存在，跨 PR 历史对照会混入工作量、runner/queue 与 CI 漂移；既然 P95 已从判据删除，本报告不再需要为它选择 quantile 定义、最小尾部样本或失败样本插补规则。**

## 6. 已知退回与本方案差别

- #1159 只把冻结账本旧侧迁到 fork point，却仍用 protected-base DAG/Lean report 佐证。
- #1166 实测后，原误拒只换成 `Closed module ... has no Freeze attestation`；误拒频次没有消失，半迁移被退回。#1169 同族亦退回。
- 本方案的区别是**整侧同迁**：fork-point tree、第三份 fork-point Lean report、由其得到的 DAG、fork-point ledger 同属一个 old-side 值；类型上不允许把 protected-base DAG 与 fork-point ledger 混装。它不是 #1159 的路径替换重演。

## 7. 只授权影子测量与后续共识骨架

本节的 miss 墙钟读数应严格称为 **shadow 全冷 miss-production cost**：shadow 不像现有 `lean-inspect` 那样 restore candidate/baseline 的 `.lake` 与 `~/.cache/mathlib`，因此它包含独立 runner 上的全冷依赖恢复/构建成本。该读数**不得**外推为 `lean-inspect` 已恢复构建缓存后的边际成本；将来做迁移前的端到端闸门时，必须在真实迁移拓扑上另测。

本报告现在只授权六席共识的步骤 1：在真实 CI 中增加一个**不供 admission 判决的独立 shadow job**。拓扑写死为：该 job 不得放进 `lean-inspect` 的串行步骤，且 job id **不得出现在 `baseline-admission.needs` 中**；它可以读取/恢复/验证或在 miss 时生产 old-side report，但产物不得供本次 admission 使用。这样影子期内它在依赖图上没有通向 `baseline-admission` 的前置边，结构上不可能延后 admission，测量本身不会改变被测 admission。把它串入 `lean-inspect` 前置链的实现不在本授权内。

在线观测单位写死为**一个真实 PR**，所以 `N` 是窗口内不同 PR 的数量，一个 PR 恰好贡献一个 hit 或 miss。样本包括最终未 merge、workflow 其它 job 失败或后来关闭的 PR，不以 merge 成功为入样条件，避免成功者偏差。对每个 PR，只选择测量起点之后按 GitHub `run_id` 最小的 workflow run，并只取该 run 的 `run_attempt=1`；该记录同时钉死当时的 `head_sha`。同一 PR 的 rerun、re-run failed jobs、取消后重跑和后续新 SHA 触发的 run 都以 artifact 保留原始记录，但一律不进入 `N`、hit/miss 或生产墙钟聚合。首次 miss 后重跑即使命中也不能改写首次样本，因此放行结果不能被重跑预热 cache 操纵。每个入样 shadow job 发出结构化的 restore `hit=1,miss=0` 或 `hit=0,miss=1`；只有 restore 后 provenance/verify 成功才可记 hit，provenance/verify 失败不是 miss 插补而是直接停案。

记录字段契约写死为：`pr_number`、`run_id`、`run_attempt` 为整数，`head_sha`、`address` 为字符串，`wall_seconds` 为非负数或 `null`，`outcome` 的取值域为 `hit|miss|hit-error|miss-error|no-record`。错误记录统一使用字段名 `stage`，不得另写 `failure_stage`；其取值域为 `cache-files|verify|toolchain|produce|unreported-step`，并带 `exit_code`（可取得时为实际整数退出码，无法取得时为 `null`）。`hit`/`miss` 才是有效命中率样本；`hit-error`、`miss-error`、`no-record` 都触发基础设施失败停案。

每个仍能执行 recorder 的 job 都把单行 JSON 上传为 `old-side-shadow-record-<run_id>-<attempt>` artifact，并保留 step summary 供人阅读。聚合端的读取路径写死为：`GET /actions/runs/{run_id}/artifacts`，从响应中找到与 `run_id`、`run_attempt` 对应的 `old-side-shadow-record-<run_id>-<attempt>`，下载并解压其中的 `old-side-shadow-record.json`，再用 `jq` 逐行解析。step summary 不作为聚合输入。

step 级 `always()` 无法在 job timeout、workflow cancellation 或 runner 丢失后自救。因此聚合端必须按 `run_id`/`run_attempt` 与 **job 终态**对账 artifact；一个成员若没有恰好一条 hit/miss 记录，即按**基础设施失败停案**处理，**不得**当作不存在而从 `N` 中消失。job 内最后一个独立 recorder 只负责覆盖仍能执行 step 的早期失败和未写记录路径，不能替代这项聚合端终态对账。

**在聚合端终态对账实现之前，本影子测量的读数不得用于任何判决或工程决策。** 原因：job 级 timeout / cancel / runner loss 无法自产记录；缺样若不被升级为停案，命中率会因幸存者偏差而虚高。因此「进入整侧迁移」的门槛不仅要求命中率与预算达标，**还要求**聚合端已实现，并已按 `run_id` / `run_attempt` / job 终态完成对账。

窗口起点写死为 shadow workflow 首次部署后的首个 workflow `run_id`。从该起点按 `run_id` 严格递增扫描，首次出现的前 40 个不同 PR 构成固定成员集；第 40 个不同 PR 首次出现时立即闭合成员集。闭合后才等待这 40 个 PR 各自被选中的 `run_attempt=1` shadow job 到达终态并计算结果；闭合后到达的任何新 PR、新 SHA 或 rerun 均记录但排除，不扩窗、不替换成员。任一固定成员的被选中 job 取消、基础设施失败、非恰好一个 hit/miss，或 provenance/verify 失败，直接停案，不用后到样本补位。这里的停案只终止本轮测量，不永久禁止重新测量；原窗口内禁止替换或补位任何成员。若要重开，必须取得新授权、选择全新起点并从该起点建立全新的 40-PR 固定窗口；新窗口不得复用原窗口任何已知 hit/miss、墙钟或验证结果，每个成员都须按新窗口规则重新产生结果。

选项写死为 **A（降格 + 另设闸门）**：独立 shadow job 是当前最低成本且不污染 admission 的测量拓扑，但正因为它没有通向 `baseline-admission` 的 `needs` 路径，它在结构上测不到未来串行链的完整端到端增量。机器判据如下；前四项须同时成立，其中第 4 项必须在进入整侧迁移之前由另行授权的串行链实验补测：

1. **拓扑判据：**shadow job 为独立 job，且静态 workflow DAG 中不存在 `shadow -> baseline-admission` 的 `needs` 路径，尤其不得出现在 `baseline-admission.needs`；不满足即停案。
2. **在线命中率：**令 `N = hit_count + miss_count = 40`，以固定成员集中每 PR 唯一一次入样计数计算 `hit_count / N >= 80%`；不是 40 个不同真实 PR 即不放行。
3. **摊销 miss 生产预算（amortised miss-production budget）：**每个 miss 在 job 内以同一 monotonic clock 记录从开始生产到 report 产出且 provenance/verify 成功的墙钟秒数 `t_i`。令 `mean_miss_wall = sum(t_i) / miss_count`，摊销预算为 `miss_count / N * mean_miss_wall`（等价于 `sum(t_i) / N`），门槛为 `<= 30.0s/PR`；`miss_count = 0` 时定义为 `0s/PR`。**这个量不测端到端增量**：它漏掉每个 PR（hit 也支付）的 merge-base 解析、checkout、address 计算、cache restore、hit 的 provenance/verify，也漏掉生产计时区间外未来新增的串行 DAG/ledger 消费等步骤。另设单次 miss 墙钟上限 `max(t_i) <= 180.0s`；这是明确的尾延迟闸，不接受以跨 PR 摊销掩盖 miss PR 的完整生产延迟。`180.0s` 以本地 `149.71s` 唯一读数为基准，留 `30.29s` 余量；线上未测，必须由本窗口给出线上 `t_i` 后才能判定。
4. **完整端到端增量闸：**进入整侧迁移前，必须另行运行实际迁移拓扑的串行链实验，把未来会新增到 `lean-inspect -> baseline-admission` 关键路径的全部步骤纳入同一 monotonic-clock 区间：merge-base 解析、fork-point checkout、address 计算、cache restore、hit/miss 两路的 provenance/verify、miss 生产，以及 report 之后新增的 DAG/ledger 消费。按上述同一套“一个 PR 一个首次 run attempt、固定 40 PR、闭窗后不补位”规则测得平均新增关键路径墙钟，门槛写死为 `<= 30.0s/PR`。当前独立 shadow job 没有该串行 `needs` 路径，**结构上测不到这个量**；本轮又明令不改 CI，所以我没有测完整端到端增量。第 2、3 项即使达标也不得替代第 4 项，不得据此进入迁移。

影子阶段三项分别只读当前 workflow 文件、固定窗口的每 PR 唯一 hit/miss 计数和同一次 miss 运行的 monotonic-clock 墙钟；不与别的 PR 历史 P95 相减。完整端到端闸只读另行授权的实际串行链实验。任一适用读数不达标、成员不是 40 个不同 PR、计数不守恒、被选中运行失败或 provenance/verify 失败，立即停案并移除影子 job，保持现行 admission，不得进入整侧迁移。

若且仅若上述吸收条件实测达标，后续方案仍只保留六席共识骨架：树 + report + DAG + ledger 作为不可拆 old-side 能力包整侧同迁；类型上拒绝混侧；迁移必须分步；每一步都须预先给出机器判据与回退点。本报告不决定影子双跑、旧入口 Contract 删除等具体实施设计。

## 7.1 后续未实现：影子测量聚合端终态对账

待实现项是**影子测量聚合端终态对账**：按 `run_id` / `run_attempt` 查询 job 终态，并经 `GET /actions/runs/{run_id}/artifacts` 找到 `old-side-shadow-record-<run_id>-<attempt>`，下载解压后对 `old-side-shadow-record.json` 执行 `jq` 逐行解析，补齐每个成员的最终记录并检查恰好一条。它解锁的是本节的使用禁令；在该聚合端能力落地前，本报告的读数只能用于观察，不能用于任何判决或工程决策。

## 8. 40 个样本的原始地址

SHA 列为 8 位展示，两个 address 为 helper 第一列的完整 64 hex。`cross-other` 排除自身。

| PR | merge | base | head | fork | addr_base | addr_fork | same | cross-other | union-hit |
|---:|---|---|---|---|---|---|:---:|:---:|:---:|
| #1358 | `55a4369c` | `e06e7cd9` | `61b798d9` | `fb0a971b` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | yes | yes | hit |
| #1354 | `e06e7cd9` | `fb0a971b` | `f7dbdc0c` | `922b87b8` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | no | yes | hit |
| #1356 | `fb0a971b` | `61a6e046` | `1fa249b0` | `922b87b8` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | no | yes | hit |
| #1353 | `61a6e046` | `c42e121e` | `275d1dc3` | `922b87b8` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | yes | yes | hit |
| #1355 | `c42e121e` | `922b87b8` | `f36dee3c` | `922b87b8` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | yes | yes | hit |
| #1352 | `922b87b8` | `dda7a419` | `a87b1429` | `08304f38` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | yes | yes | hit |
| #1350 | `dda7a419` | `08304f38` | `fb886d81` | `08304f38` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | yes | yes | hit |
| #1351 | `08304f38` | `cfaee8cf` | `cb39d712` | `84769898` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `a03e1c81c5ae020a283ca2b54fe33d2022f75e64bde3e897dca52d2e6c5dba96` | no | yes | hit |
| #1340 | `cfaee8cf` | `84769898` | `2738aabc` | `0630f49e` | `a03e1c81c5ae020a283ca2b54fe33d2022f75e64bde3e897dca52d2e6c5dba96` | `489c595187d23572a1670a8336f1efb4b327dcb79e57cecc0c971d7ab1d304c0` | no | yes | hit |
| #1345 | `84769898` | `0630f49e` | `559e3ee5` | `35c393a3` | `489c595187d23572a1670a8336f1efb4b327dcb79e57cecc0c971d7ab1d304c0` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1343 | `0630f49e` | `8c2260a0` | `1cf38ddc` | `c321e0de` | `70a5b92b10fdcb25c6ebfef3aeba2b6cca5308657031b62618a25a72c448a3bd` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1349 | `8c2260a0` | `8773ecff` | `844ee012` | `35c393a3` | `a53492f6819a9e95031c7c8578ced5398a83c2538990dd3fbadd432c61d0b701` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1346 | `8773ecff` | `35c393a3` | `ac191b15` | `7e11a956` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1347 | `c321e0de` | `7e11a956` | `5743d114` | `d18e78f7` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1339 | `7e11a956` | `d18e78f7` | `3b266523` | `d18e78f7` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1338 | `d18e78f7` | `995d75c7` | `46220826` | `5ef2909f` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | yes | yes | hit |
| #1341 | `995d75c7` | `5ef2909f` | `4ee704fb` | `5ef2909f` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | yes | yes | hit |
| #1332 | `5ef2909f` | `d8e2a181` | `33ec56a9` | `f50c827a` | `5601f8e9fdead4a8b16fa65330c94d1193b124b282b6d8e04fe51e8d04a97cd0` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | no | yes | hit |
| #1336 | `d8e2a181` | `1bc7b463` | `79d717d2` | `1bc7b463` | `6a3449e098501af542733471827c025e093e23bb829b83adc621a892749eb4bb` | `6a3449e098501af542733471827c025e093e23bb829b83adc621a892749eb4bb` | yes | no | hit |
| #1335 | `1bc7b463` | `a00317a3` | `feaf6045` | `f50c827a` | `14c2fd48c31b03d17f33ad9c5e130172b223adc5b8bee6eb49c88bf255d71b1a` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | no | yes | hit |
| #1331 | `a00317a3` | `a1480c72` | `b2bea3a7` | `25222201` | `52e88703486f01f18fa166073e5aa89595d11dc71bb92790edbd05be77e9c2a9` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | no | yes | hit |
| #1334 | `a1480c72` | `f50c827a` | `3f2d75f2` | `f50c827a` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | yes | no | hit |
| #1320 | `f50c827a` | `7ccbfffe` | `5aee88a9` | `738c2d08` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | no | yes | hit |
| #1333 | `7ccbfffe` | `25222201` | `9a10881a` | `25222201` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | yes | yes | hit |
| #1330 | `25222201` | `767e2c21` | `a6f0e178` | `1843022f` | `9bceeb6a93f9eeb4e70da09bd187765ee8c7069568a0246fcaf97faf6061b6a5` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | no | yes | hit |
| #1329 | `767e2c21` | `1843022f` | `d3c7310f` | `1843022f` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | yes | no | hit |
| #1328 | `1843022f` | `429fd56f` | `d4728d48` | `738c2d08` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1327 | `429fd56f` | `738c2d08` | `e8151a52` | `738c2d08` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1319 | `738c2d08` | `fe942bc1` | `2863a7ce` | `fe942bc1` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1324 | `fe942bc1` | `72a382f9` | `631b98d3` | `30973ef4` | `b0a37858026f6e397ceae2c22ea8ca674709e0704b4c4e9cc2161e912fb5f7f2` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | no | yes | hit |
| #1323 | `72a382f9` | `eff93ae6` | `046c2e43` | `30973ef4` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1325 | `eff93ae6` | `30973ef4` | `9148de53` | `30973ef4` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1322 | `30973ef4` | `38020e03` | `b7f0fb58` | `38020e03` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1321 | `38020e03` | `7665a09e` | `4b4ab1b3` | `7665a09e` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1318 | `7665a09e` | `81cd92cb` | `76458622` | `fc5476ad` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | yes | yes | hit |
| #1316 | `81cd92cb` | `fc5476ad` | `cd29ad09` | `fc5476ad` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | yes | yes | hit |
| #1317 | `fc5476ad` | `96855375` | `d1d2cbfe` | `1fad2b44` | `0a081d3cb9e5f0a39499d0c99b9f8aa2f0ff0d5a3b2318897e4ee9ce8774f821` | `08bf68d2c94e9123bf2a81fc7dfcff9df4c580bc4702751e258f112a0876bd2b` | no | yes | hit |
| #1315 | `96855375` | `1fad2b44` | `ec38f257` | `d66b0844` | `08bf68d2c94e9123bf2a81fc7dfcff9df4c580bc4702751e258f112a0876bd2b` | `b8172b90d0d0e6a0583cf9cbce6cde3a98331b19fa9ab2353eae2ea262e39c35` | no | no | MISS |
| #1314 | `1fad2b44` | `72193105` | `965c2b76` | `d88d7290` | `250fae11b16a1f84e5bf311aa949201f9c04aed5986e54840c46c12548a0c901` | `ea03df2274daddf16ee43b47309bb890f21b26916962992706a385fd040aab57` | no | no | MISS |
| #1313 | `72193105` | `e1cfc429` | `dd105a9e` | `d88d7290` | `7043ef2f77909135b1cc5e51bde7cb067b8282f65129521ab8552cc09139dc75` | `ea03df2274daddf16ee43b47309bb890f21b26916962992706a385fd040aab57` | no | no | MISS |

## 9. 范围与偏差

- 未修改 `.github/workflows/**`、admission、SL-008 或任何 harness 行为。
- 本报告住在 `docs/devloop/reports/`，与既有的 `ks-finite-window-pricing.md` 同一位置。
  **`docs/develop/reports/` 是一个从未落地的路径空间**，这一点由一次实际的准入判决坐实：
  本分支最初把报告放在那里并同时补上 `Meta/FILEMAP.toml` 的 `docs/develop/reports/**` 声明，
  CI 判 `SL-000 …: unknown top-level artifact`（run `31549130526`，`RULE_REJECTED count=1`）。
  根因是 base 侧 `RepositoryPathPolicy.cs:77` 只接受 `docs/devloop/`。
  先前的 `6481c5f94591cb2c165addc505aaae0f91704da1`（`git branch -a --contains` 显示可达）
  **只新增了 FILEMAP 声明、没有新增任何文件** —— 零匹配的 glob 不触发 `SL-000`，
  所以它当时能过门，随后又因零匹配被删除。**「历史上存在过一条声明」不等于
  「该路径空间被 base 谓词支持」**；判据只有一个，就是 base 版 `RepositoryPathPolicy` 的谓词本身。
- 未测 GitHub Actions 在线 cache inventory；所有命中率均来自指定 40 个 base address 的集合。
