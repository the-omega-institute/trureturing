# Fubini–Study 角与条件记录时间界

产地：Codex 实施席，使用 lean4 skill；单点实施与自查，零独立评审席。
orchestrator 的复算和最终评审由调用方填写，本报告不代填。

## 目标与预登记依据

用户 brief 的既定目标是单位向量取模内积角的三角不等式；预登记路线为
相位选择 → 实角三角不等式 → 条件记录时间下界。
源为 quantum-reality 的 atom
`00ebe34ede79d85818ef1975483cc304615967a0925f809c6746b0f49585643b`，定理 229.1。
物理输入是每支从共同初态出发的角距离上界；不推导 Mandelstam–Tamm。
拟议实质见证是同时将相邻两段内积相位对齐，并保持首尾内积的模。
直接消费者为本模块 `record_time_lower_bound`；顺序记录数界再消费时间界。
成须通过 serial-lean、lean-report、emit、deposit-uncovered 及本地 Scribe CI 检查；
翻须有 kernel 反例；其余交付已证明部分并明确 blocked。不开 PR，由 orchestrator 接续。

## 先库后证收据

本树 Lean 为 4.33.0，mathlib rev 为
`db584cd6d46c92f209a44c0f1c829460d327499d`。
在 D5 搜索 Fubini、Study angle、record time、angle_triangle、arccos/inner，
未命中本题已有声明；宽筛返回的 Fubini 积分及历史记录条目不等同本靶。
在 mathlib 的 Analysis/InnerProductSpace、Geometry/Euclidean/Angle 搜索
angle_triangle、InnerProductGeometry、Complex.abs_inner、arccos/norm/abs；
全 Mathlib 再搜 Fubini–Study、Bures angle、arccos/inner。
命中 `InnerProductGeometry.angle_le_angle_add_angle`
（Geometry/Euclidean/Angle/Unoriented/TriangleInequality.lean），其参数是实内积空间。
`angle` 定义使用实内积除以两范数之积，未提供取模版。
命中 `Complex.exists_norm_eq_mul_self`（Analysis/Complex/Basic.lean），
直接复用其单位相位存在性，不自行重造复数极分解。

第三方检索实际使用 authenticated `gh api search/code`，网络能力可用。
查询 `"Fubini" "Study" language:Lean` 返回 206 项，读取第一页 30 项；
查询 `"arccos" "inner" "triangle" language:Lean` 返回 86 项，读取第一页 30 项。
这不是穷尽搜索。zblore/csd-lean4 的 FubiniStudy.lean 是射影不变概率测度；
physlib 的 QuantumInfo/States/Mixed/Fidelity.lean 将 FS 度量留作 TODO，
且该文件含 sorry，不作为已证依赖。

精确有限维版本命中 QuAIR/Lean-QIT 的
`QIT.PureVector.projectiveAngle_triangle`，位于
`QIT/States/Geometry/PurifiedDistanceAngle.lean`。
已读取证明全段：相位旋转两端 → 实角三角不等式。
上游不可变修订为 `c1d59b133b56e3d79efb11ee46a728d290f761f5`，
Lean 4.30.0，mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`。
与本树两项均不等，按 spec A17.2 依赖形不可行，选择移植适配。
适配去掉有限维 PureVector 包装，使用一般复内积空间；
用 mathlib 的单位相位存在性替代上游私有 unitPhase 构造与零内积分支。
保留 QuAIR 版权标注与完整 Apache-2.0 许可于 Lean-QIT-LICENSE.txt。
上游 recursive tree 查询只发现 LICENSE，无 NOTICE。
本树钉版 mathlib 将来提供等价取模角定理时，后继模块须直接引用该上游结果，
不再复制本次移植；已冻结节点遵守仓库冻结规则。

## 物理与数学边界

本模块是条件定理，E_max 速度界为物理输入。时间定理仅需要速度假设在终时的值，
因此适用于用户的全时间速度假设在终时实例化后的情况。
E_max 和 hbar 严格正；正交条件是复内积本身等于零。
不定义含时 Hamiltonian，不证明 Schrödinger 演化、能量涨落界或 Mandelstam–Tamm。
记录数推论的时间预算是接触时长之和不超过总时间；它表达顺序、不重叠接触的输入。
取模角在单位向量上是相位不变的伪距离，在射线上才分离点；本次不构造射影商空间实例。

## 对照与证据来源

用户提供的 orchestrator 数值读数：FS 角 0/4000 反例；
1−保真度 232/4000 违反；sin³ 419/4000 违反。本席未复跑这些随机实验。
必须保留的反面教训：`arccos(Re⟨a,b⟩)` 是实球面大圆距离，本来就满足
三角不等式；其 0 反例不能鉴别取模版是否写对。判不了错的对照等于没验。
本席将以明确三态的确定性数值对照核对角与错误替代量的差别；数值不冒充 kernel 证明。

## 声明判形与用途

主定理 `fs_angle_triangle`：proof_shape=content；admission_basis=escape-witness。
活路径见证为相邻两内积的同时实正对齐及首尾模保持，经实角三角不等式推出取模角界。
其数学为已知结果，第三方移植不冒认数学新颖性。
`record_time_lower_bound`：伴随条件推论，消费 `fs_angle_triangle`，对应 atom 229.1。
`record_count_upper_bound`：伴随条件推论，消费 `record_time_lower_bound`，对应 atom 229.2。
直接冻结 D5 依赖均为空，故无须填写 GID/statement_id 对；仅依赖钉版 Mathlib。
utility=none：全部声明为一般几何或条件解析不等式，无有界枚举、检查器、数值归约
或已认证有限实例。其余用途字段 not-applicable(kind=none)。

## 可复用失败记录

route 首次以 /tmp 的绝对 manifest 路径调用，返回必须 repository-relative；
改用本报告目录的 manifest。热缓存单文件探针中，首次时间推论使用错误的
`inner_norm_symm` 名称及反向除法引理；修为 `norm_inner_symm`、`le_div_iff₀`。
取模角三角不等式首次探针即通过；探针不代替整树与 axiom 闭包门。

## 门链

正式模块与最终门链结果待本次运行结算；本段尚不主张冻结或 CI 通过。
