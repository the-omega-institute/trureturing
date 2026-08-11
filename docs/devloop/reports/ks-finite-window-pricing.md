# M >= 3 Kochen-Specker 有限窗立项定价

> **REPORT-ONLY / 估价席产物。** 本文不是 Lean 真值源，不声明任何新定理，不把参考理论卷、mathlib API 或搜索输出写成仓内已拥有能力。本轮未写 `.lean`、未运行证书搜索，也不再创建或改写提交。最终核验时发现报告已由并行的外部流程落入提交 `5e333a6d`；这是对“不得提交”要求的状态偏差，本文不把它隐去。

## 0. 终局摘要

- **终局：DEFER。** 当前证据足以分阶段定价，但不足以给完整项目开无条件 GO：仓内没有可摄入的精确 qutrit KS 射线/上下文数据，没有不可着色证明工件，也没有已安装的 SAT/LRAT 生成工具。
- **定价状态：PRICEABLE_BY_PHASE。** 不触发 `UNPRICEABLE_WITH_CURRENT_EVIDENCE`；能拆开的工程层均给区间，尚未取得的数据源成本单列，不用一个伪精确总价掩盖它。
- **推荐路线：显式有限 qutrit 证书 + exact geometry checker + CNF/LRAT kernel proof + 坐标化 `M >= 3` 提升。** 在精确、可再分发的机器可读证书已经提供时，估价为 **82-172 人时**；若还要取得、转录并双源核对证书，估价为 **98-220 人时**。这是约 **3-6 个单人日历周**的月度级项目，不是一个常规单引理车道。
- **本轮只建议一个 8-12 人时的解锁 spike。** spike 的产物必须是固定 statement contract、带 provenance 的一小段真实数据、至少一个 exact context 校验和一条从数据约束到 kernel-checked UNSAT 的端到端微型链；缺任一项即继续 DEFER。

调查取证快照是 worktree `harness/oqm-r15-c15v2` 当时的 `HEAD=1fad2b44c5d9f1a6813cd250b5ab62bb9232224a`，调查开始时该值等于 `origin/dev`。最终核验时，分支已由外部流程推进到 `HEAD=ea64936ab18339da90ce26146d46df38d2d902d7`，跟踪 `origin/harness/oqm-r15-c15v2`；该 HEAD 合并了 `origin/dev=fc5476ade70d711401dc05ccd36c2e519c5fb787`，并包含报告提交 `5e333a6d`。相对取证快照，除本报告外的新增内容位于 `D5/S1/Words/ReturnWords`、`D5/S3/Arith/Congruence/QuarticThirtySix`、Blueprint、账本及聚合导入；本报告核查的 Quantum/Observer/KS 路径差异为空。因此下列能力判断在该移动窗口内未变。

## 1. 目标分层与验收边界

### L0. 命题契约先冻结

建议未来端点采用**秩一投影版**而不是裸向量版：答案表对完整有限窗代数中的秩一自伴幂等元取 `Bool` 值；对每个由 `M` 个秩一投影组成、和为单位矩阵的完备 context，恰有一个值为真。这样同一射线的非零缩放自动落到同一投影，不必在主定理里另造射线商相等性。

验收边界：

1. `M = 2` 不在 KS 结论内，继续由现有“无全代数字符”收窄定理承担，二者不得同名或互相冒充。
2. `M >= 3` 的结论必须排除上述**投影赋值**，不能只排除保持加、乘、单位的 `AlgHom`。
3. “有限窗”是矩阵维数有限和证书数据有限，不是只验证有限个随机 context。
4. 不包含 Gleason 表示唯一性、Born 规则唯一性、CHSH、局域性或制备独立性；这些是邻接命题，不自动随 KS 结算。

### L1. 有限向量/射线证书

需要一个 canonical qutrit 数据源，至少包含：稳定 ray ID、非零 exact 坐标、context 到 ray ID 的引用、来源/版本/许可、内容哈希。优先选择整数或有理坐标；每条射线再派生为归一化秩一投影。数据必须只有一个权威表示，CNF、LRAT 和展示表都是它的受验投影。

当前仓内只有小型构件：`QuarticContextWitness` 给出两组三维整数射线和对应有理投影；它不是 KS 集，也没有不可着色结论。

### L2. 正交数据校验

对全部证书数据机器核验：

- ray 非零；context 内 ID 合法且互异；
- exact 内积为零，禁浮点容差；
- 派生投影自伴、幂等、秩一；
- 每个 qutrit context 的三个投影两两正交且和为 `I_3`；
- 数据中的复用由相同 ray ID 或相同派生投影兑现，不能靠注释宣称。

几何校验与不可着色必须分层：正交表全绿只说明数据是合法 context，不说明它不可着色。

### L3. 不可着色核心

把每条 ray 的取值编码为一个布尔变量；每个三元 context 编码“至少一个真 + 任意两个不能同时为真”。验收端点是不存在满足全部 context 的赋值。

这里“核心”只表示一个经 kernel 核验的有限 UNSAT 子集，**不包含最小性**。若要求 deletion-minimal 或最少 ray/context，还需对每次删除给 SAT witness 或独立 UNSAT 证明，另加 12-32 人时。

推荐信任边界：外部搜索器只生成 UNSAT 候选和 LRAT；`Mathlib.Tactic.Sat.FromLRAT` 把 LRAT 重建为 Lean 证明；另证该 CNF 的变量/子句逐项等价于 canonical context 约束。搜索程序、转写脚本和求解器退出码均不是信任根。禁止用未桥接的“solver says UNSAT”或 `native_decide` 冒充 kernel 证书。

### L4. `M >= 3` 提升

提升不能写成“把三维向量尾部补零”后直接结束，因为全局假设约束的是 `M` 维完备 context，三维三元组本身不是 `M` 维完备 context。

推荐坐标化证明骨架：

1. 对标准 `M` 维 context 应用全局赋值律，取得唯一取真坐标 `e`。
2. 用有限置换把 `e` 放入选定的三个坐标轴，并把其余 `M-3` 个标准投影视为固定正交补。
3. 标准 context 已迫使补空间各投影取假。
4. 把每个 qutrit KS context 嵌入这三个坐标轴，再与同一补空间拼成完整 `M` 维 context。
5. 全局“恰一为真”遂限制为 qutrit 核心的“恰一为真”，与 L3 冲突。

这一步必须有 context 拼接、投影和为单位、取值限制三类 Lean 证明，不能只给线性嵌入。坐标路线可避免为任意 Hilbert 空间选择正交基；若改走抽象有限维 Hilbert 空间，mathlib 的 `stdOrthonormalBasis` 明确通过 `Classical.choose` 构造，axiom 闭包会相应增加。

### L5. Observer 集成

自然落点是 `D5/S3/QuantumContext` 的证书/提升模块，加一个 `D5/S3/Observer` 适配模块：

- 通过 `ZMod.finEquiv`/矩阵 reindex 把 `Fin M` 端点接到现有 `Matrix (ZMod M) (ZMod M) Complex` 窗口；
- 新建 KS 专属的 projection-answer/noncontextuality 谓词；
- 保留 `WindowCharacter.window_algebra_has_no_character` 和 `ClassicalAnswerTableExclusion.IsNoncontextual` 的现有强 `AlgHom` 语义；
- 对 `M = 2` 和 `M >= 3` 做显式分支，不把一个 theorem name 同时解释为两种非上下文性；
- Scribe 叙事只能引用最终 Lean truth anchor，并保留“KS 不推出 CHSH/Born/Gleason”的强度护栏。

## 2. 能力矩阵

| 层 | 仓内已拥有 | mathlib 可参考，**不得写成已拥有** | 当前全缺/未接通 |
|---|---|---|---|
| 文献与命题边界 | `Library/notes/kochen1968problem.md` 有 DOI、维数边界和 qubit 区分；两份 digestion receipt 已登记 `kochen-specker-projection-valuation-obstruction` | 无相关成品定理；文本搜索中的 Gleason 命中均是 Haar/拓扑同姓结果 | 精确有限 qutrit 证书的来源、版本、许可、机器数据 |
| qutrit 向量/投影 | `QuarticContextWitness` 有 `Fin 3 -> Complex` 射线、归一化秩一投影、两个 exact projective context | `Matrix.vecMulVec`、star、trace、有限和；`Projectivization` 可作备用射线商 | KS ray/context schema、完整数据、跨 context ID 复用校验 |
| 正交/完备校验 | 两个三元 context 已逐项证明自伴、幂等、和为单位；`born_probability_skeleton` 可处理一般有限矩阵 | `Orthonormal`、`orthonormal_iff_ite`、正交基扩张、Gram/inner-product API | 从 canonical 数据统一派生并检查所有 context 的 checker |
| 不可着色 | 无 KS theorem、无 CNF/LRAT、无 ray coloring 定义 | `Mathlib.Tactic.Sat.FromLRAT.lrat_proof` 可把 CNF/LRAT 重建为 kernel proof | CNF 生成/等价桥、LRAT 工件、UNSAT core；本环境也未发现 `kissat`/`cadical`/`drat-trim`/`lrat-check` |
| 一般 `M` 窗口 | `WindowRegister` 有任意非零 `M` 的 Weyl 矩阵；`WindowCharacter` 对 `M > 1` 排除全代数字符 | `ZMod.finEquiv`、`Matrix.reindexAlgEquiv`、`Fintype.equivFin`、有限置换与 block/reindex API | qutrit core 到每个 `M >= 3` 的完备 context 提升 |
| Observer 语义 | `DeterministicAnswerTable`、固定 `M=2` 的强 `AlgHom` 非上下文性和 CHSH 邻接定理 | 通用矩阵/有限类型基础 | KS 专属 projection valuation、与窗口索引的适配、M=2/M>=3 分栏 |
| 验证与发布 | pinned Lean/mathlib `v4.31.0`、`lake build`、Lean inspector、Scribe/Blueprint 链 | LRAT elaborator 最终产物由 Lean kernel 检查 | 证书数据回归、CNF 对应性测试、编译性能基线、最终 axiom audit |

关键反空洞事实：

- `FiniteDimensional.qubit_matrix_algebra_has_no_character` 与 `WindowCharacter.window_algebra_has_no_character` 都使用完整代数同态公理；它们不是 KS projection valuation theorem。
- `QuarticContextWitness.quartic_pricing_context_counterexample` 只比较同一态在两个 context 下的四次定价总和；它不排除 `{0,1}` 着色。
- 理论卷中的 Mermin/Magic-square、512 赋值和“完整 KS”是参考输入叙述，不是 Lean 真值；而且四维 Mermin tracer 不能覆盖 `M = 3`。

## 3. 路线对比

### 路线 A：显式有限证书检查（推荐）

数据流：canonical rays/contexts -> exact geometry validation -> CNF correspondence -> untrusted SAT search -> LRAT -> Lean kernel UNSAT -> qutrit projection obstruction -> coordinate `M >= 3` lift -> Observer adapter。

优点：

- 与“有限窗/有限射线证书”的项目目标逐字对齐；
- 失败可定位到数据、几何、逻辑或提升中的单独一层；
- LRAT 使搜索可信边界清楚，复核成本与 proof trace 近线性；
- exact 坐标和有限 context 便于回归、哈希与独立重放。

代价：

- 数据 provenance 和转录是第一风险，不是附带文书；
- 必须证明 CNF 与 Lean 约束的对应，不能双份手抄后只比哈希；
- LRAT 体积与 elaboration 时间目前未测，需 spike；
- 本环境没有已安装的 proof-producing SAT 工具，工具取得/钉版是 open capability。

### 路线 B：结构组合证明

先形式化可复用的 0/1 gadget（局部 context 迫值、传值、冲突），再把若干 gadget 组合成 qutrit 不可着色结构；几何 realization 与 `M >= 3` 提升仍独立完成。最终矛盾由具名组合引理闭合，而不是把整份 CNF/LRAT 作为主叙事。

优点：证明项更接近数学解释，局部 gadget 可复用；若组合足够小，最终文件比大 LRAT 更易阅读。

代价：仓内/mathlib 没有 gadget 库或已核对 realization；分解本身需要研究判断，容易把“搜索发现的图”重新手证一遍；它并不免除 exact 数据，也不免除三维到一般维数的提升。故在同一份已提供数据上估价仍高于路线 A。

### 不作为主路线的捷径

- **四维 Mermin/Magic-square tracer**：可作工具链演示，不能清偿 `M = 3`，不得作为总体 GO 证据。
- **Gleason/Busch 路线**：pinned mathlib 无该语义定理；从零形式化会把有限证书项目改成分析/测度项目，范围更大且偏离交付。
- **复用无代数字符**：命题强度错配；结论虽强，但前件也强，不能排除只在相容投影 context 上定义的 KS 赋值。

## 4. 阶段预算与硬止损

单位为单一熟悉 Lean/mathlib 的工程师**人时估价**，不是已测耗时。历史锚只有：本仓简单引理全链约 2.5-5 小时、首次坐标/张量接口曾被重估到 6-10 小时；KS 没有本仓实测样本。因此证书数据、UNSAT 和维数提升区间刻意较宽。

| 阶段 | 可验交付 | 路线 A | 路线 B | 止损/进入下一段的证据 |
|---|---|---:|---:|---|
| P0 命题与所有权冻结 | projection valuation、context、core/minimality、M=2 分栏书面契约 | 6-10h | 6-10h | 任一量词仍有两种解释即停 |
| P1 数据取得与双源核对 | machine-readable qutrit rays/contexts、许可、哈希、独立核对记录 | 已提供 4-8h；未提供 20-56h | 同左 | 无 exact 数据或许可不明即 DEFER |
| P2 schema 与 exact geometry | 单一数据源、非零/正交/完备/投影校验全绿 | 20-40h | 24-48h | 首个真实 context 8-12h 内仍不能 exact 闭合即停 |
| P3 不可着色核心 | CNF 等价桥 + kernel-checked UNSAT；不声称最小 | 14-32h | 32-72h | 24h 内无 kernel proof tracer 即重定价 |
| P4 `M >= 3` 提升 | 含唯一真坐标、固定补空间、完整 context 拼接 | 18-40h | 18-40h | 只得到补零嵌入而无赋值限制即停 |
| P5 Observer 集成 | ZMod/Fin reindex、KS 专属谓词、M=2/M>=3 分栏 | 8-18h | 8-18h | 需改写既有 `AlgHom` 语义则另立迁移单 |
| P6 验证与叙事 | targeted/full build、inspector、axiom audit、Scribe、强度护栏 | 12-24h | 12-24h | 任一正式声明超出 truth anchor 即红 |

合计：

- 路线 A，数据已提供：**82-172h**；数据未提供：**98-220h**。
- 路线 B，数据已提供：**104-220h**；数据未提供：**120-268h**。
- 要求 deletion-minimal core：在上述任一路线追加 **12-32h**。
- 上述不含等待外部许可、网络/包审批和 CI 排队日历时间；这些是资源等待，不伪装成人时。

建议拆成四个独立价格门：A0 数据与 statement、A1 qutrit checker/core、A2 `M >= 3` lift、A3 Observer 集成。前门未绿时不得预支后门预算。

## 5. 风险账

### R1. 数据录入与 provenance（高）

同一 ray 的符号/比例变化通常不改物理射线，却会改变手抄向量；context ID 错一位可能仍通过部分正交检查。控制：稳定 ID、canonical scaling、exact checksum、两个独立来源逐项比对、由同一数据派生投影与 CNF。来源引用错误不会必然使数学定理为假，但会使文献归属与可复现性不合格。

### R2. 搜索可信边界（高，可控）

SAT 搜索器、DRAT->LRAT 转换器和外部脚本均可出错。只有 Lean 中重建的 LRAT proof 及 CNF-约束等价桥可承重。仅保存“UNSAT”退出码、随机穷举摘要或 `native_decide` 结果不合格。当前环境未发现 proof-producing SAT 工具，不能把工具可用性写成现状。

### R3. 选择公理依赖（中）

坐标矩阵路线可用标准基、有限置换和显式三轴，目标是不给主端点新增 `Classical.choice`。若改为任意有限维 Hilbert 空间并调用 `stdOrthonormalBasis`/基扩张，mathlib 实现会带 `Classical.choose`。这不是私有 axiom，但必须在最终 `#print axioms` 中明列，并由项目决定是否接受。不得为了“无 choice”手工重证整个有限维基理论。

### R4. 命题强度错配（最高）

四种常见错配：无 `AlgHom` 冒充无投影赋值；两个 context 的 quartic 漂移冒充不可着色；四维 Mermin 证书冒充 `M >= 3`；数值近似正交冒充 exact context。L0 contract 和 Blueprint 强度护栏是准入前件。

### R5. 维数提升吸收唯一值（高）

补空间可能吸收全局 context 中唯一的真值。推荐证明必须先从标准 context 取得真坐标，再把它纳入三维块，从而迫使固定补空间全假。没有这一步的简单补零证明不成立。

### R6. 工件体积与唯一真源（中）

CNF/LRAT 可能很大；若 rays、contexts、CNF 三处手抄，立即形成多真源。推荐 canonical Lean/data schema + 可验证对应；LRAT 是证明证书，不是语义数据。若生成投影需入库，须按 FILEMAP 的数据/投影边界另做设计，不能把搜索脚本输出藏进 Lean 程序目录。

### R7. Observer 语义回归（中）

现有 `IsNoncontextual` 是固定 `M=2`、全代数字符语义。直接改名或放宽它会改变已冻结叙事。推荐新增 KS 专属层并给桥接定理，不修改旧语义；若业务要求统一 answer table，迁移和兼容面需另计。

## 6. GO / DEFER / NO-GO 门

### 当前：DEFER

缺失证据是可操作的，不是模糊不确定性：

1. 没有 pinned、可再分发、machine-readable 的 exact qutrit KS 数据。
2. 没有 CNF/LRAT 或结构组合的 kernel-checked 不可着色证据。
3. 没有 `M >= 3` context 拼接 spike。
4. 本环境没有已发现的 SAT/LRAT 生成工具，LRAT elaboration 规模和耗时未测。

### 转 GO 的触发证据

以下五项全部出现才把完整项目转为 GO：

1. L0 statement contract 固定，并由测试明确拒绝 `AlgHom`/quartic/Mermin-4D 三种替代品。
2. exact qutrit 数据、来源、许可、版本、哈希齐全，且双源核对无差异或差异已解释。
3. 一个真实 context 在 pinned mathlib `v4.31.0` 下完成非零、正交、投影与单位分解的 exact proof。
4. canonical 数据的一小个真实约束子集完成 CNF 对应 + LRAT kernel proof；求解器和转换器版本已钉定。
5. `M = 4` 的提升 tracer 明确展示“真坐标进三维块、补空间为假”，而不是只有向量补零。

### 转 NO-GO 的触发证据

- 项目方要求把现有无代数字符、quartic context 或四维 Mermin 直接签成完整 `M >= 3` KS；
- 数据只给浮点坐标/容差正交，且拒绝 exact 化；
- 要求搜索器输出直接承重，拒绝 kernel checker 或 CNF 对应证明；
- 要求在同一交付中同时证明 Gleason/Born 唯一性、KS、CHSH 与 observer 本体论总装，而不接受拆单。

## 7. 证据索引

- 仓内现实：`D5/S3/QuantumContext/QuarticContextWitness.lean`、`D5/S3/Quantum/FiniteDimensional.lean`、`D5/S3/Observer/WindowRegister.lean`、`D5/S3/Observer/WindowCharacter.lean`、`D5/S3/Observer/ClassicalAnswerTableExclusion.lean`。
- 语义 open：`Meta/Digestion/backfill/observer-quantum-v1/partial-closed/observer-residual-7232ebf337ed10c1fb71b90c1f3b3438d2dbddf1261035e4a757c3f8b6124511.yaml` 与 `observer-residual-101df483e71f9e23ee1ec13626abf3037d9a32e6f992d6b5b9485bf6c7976c77.yaml`。
- 文献边界：`Library/notes/kochen1968problem.md`；该 note 明确现有 qubit character 结果不是 KS。
- mathlib 可参考：`Mathlib/LinearAlgebra/Projectivization/Basic`、`Mathlib/Analysis/InnerProductSpace/Orthonormal`、`Mathlib/Data/ZMod/Basic` 的 `ZMod.finEquiv`、`Mathlib/LinearAlgebra/Matrix/Reindex`、`Mathlib/Tactic/Sat/FromLRAT`。
- 搜索读数：仓内带 KS/contextuality 语义的 Lean 文件只有 `ClassicalAnswerTableExclusion.lean` 与 `QuarticContextWitness.lean`，二者均以注释明确否认已完成 KS；pinned mathlib 的 Kochen/Specker/noncontextuality 搜索为零，Gleason 命中均是 Haar/拓扑同姓名词。
