# Gibbs 变分恒等式实施记录

## 目标与预登记

基线 `e579ef5bb4556f42f3b5827bf17c5435e7be5f62`，分支 `lane/math/gibbsvar`。
用户指定的量子观察者线形式化靶，非开放问题的新定理主张。
对任意非空有限维复杂 Hermitian H 及正定 trace-one ρ，证明
`log (ReTr (exp H)) = ReTr (H * ρ) + S(ρ) + D(ρ || exp H / ReTr(exp H))`，
并证明 H=0 的均匀参考态伴随式。成功条件为用户 brief 的成态；反例须 kernel 见证；
blocked 须具体 Lean goal 与已尝试路线。

拟议逃逸见证：一般 Hermitian H、正标量 c 下的谱演算公式
`CFC.log (c • exp H) = H + (Real.log c) • 1`，以及归一化指数矩阵的正定性与迹归一。
下游消费者预登记为 `gibbs_variational_identity`，伴随为 `entropy_uniform_identity`。
判形待实际证明依赖核对，不预先冒领 content。

## 检索收据

1. 仓内 `rg -n -i 'relativeEntropy|vonNeumannEntropy|gibbs|cfc.*log|log.*cfc' D5`：
   命中 `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.lean` 的
   `DensityState`、`quantumRelativeEntropy`，及 `VonNeumannEntropyPinching.lean` 的
   `vonNeumannEntropy` 与熵分解。已完整读前一模块的公开面，后者下一步逐条读取。
   因此 brief 所述“D5 没有矩阵熵定义”在本基线上被证伪，实施复用已有定义。
2. `Resource/LogDet/LogDetInformationSubmodularity.lean` 已完整阅读：谱对数迹公式为 private，
   唯一公开定理是 log-det 次模性，与本靶不等价；可参考其 Matrix/CFC 接线方式。
3. 工具库已列举，依赖证据使用现成 `deposit-evidence/shapes.sh` / `proof-edges.sh`。
   mathlib 与第三方检索尚待执行，不主张检索完备。

## 未主张

尚未证明、未冻结、未 cover、未开 PR；不主张新数学结果、不主张相对熵非负或极值刻画，
不主张覆盖源 atom 全部子句。尚未打开的第三方页面一律 ASSUMED-UNVERIFIED。
产地为 Codex 实施席，使用 lean4 技能，单点实施自查，无独立评审结论。

## 第三方取页收据

- https://raw.githubusercontent.com/leanprover-community/physlib/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/QuantumInfo/Entropy/Relative.lean status=200, bytes=152074, sha256=764fbd18975561767883d6645c7acaea3d5562c84de3eda6090f7a48862943d5
- https://raw.githubusercontent.com/leanprover-community/physlib/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean status=200, bytes=20894, sha256=e3fa13c264b276509479256a32e919a2349013bb269a58ff922b6017d93dd245
- https://raw.githubusercontent.com/zblore/csd-lean4/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Thermo/FreeEnergy.lean status=200, bytes=15294, sha256=29d57d5bda44bd5c9a510e569c8eb52675e1b59dd39f1b71ad35dde225a5293f
- https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf status=200, bytes=2459123, sha256=c8f30116586435fc265273b09ca2d63f4912a5d4b8901db1ada84b03373c6325

## 独立数值探针

NumPy 2.0.2; seed=20260911; d=2..6 ×60: max residual=8.3488771451811772e-14; H=0 max=4.4408920985006262e-16; reversed D: 30/30 >1e-8, min=0.033125683965014252, max=1.3117414550843083.

用 Hermitian 对称化与 `eigh` 谱演算；ρ=(AA*+0.2I)/Tr(AA*+0.2I)，不要求与 H 对易。数值只作语义回声，不作证明或冻结实例。

## 库检索结论与覆盖范围

已逐条读完 `VonNeumannEntropyPinching` 的公开面；直接复用
`quantum_relative_entropy_eq_neg_entropy_sub_cross`。
钉版 mathlib v4.33.0 的 `ExpLog/Basic.lean` 精确提供 `CFC.log_smul`、`CFC.log_exp`，
本轮的谱对数公式将直接组合这两个上游接口，不重证谱定理。
GitHub code search 实测可用：查询 `"Gibbs" language:Lean` 和
`"log_exp" "entropy" language:Lean`；命中 physlib 的相对熵与经典 canonical ensemble，
及 csd-lean4 `Thermo/FreeEnergy.lean`。后者已有 Gibbs 对数公式与自由能最小性，
其 public 主定理是非负性/最小值，并未打包本轮的 trace-log 分解恒等式；
谱对数这一步依有序检索②直接引用较早命中的 mathlib 通用引理，
熵分解依①直接引用仓内定理。没有新建第三方依赖，没有复制上游代码。
不主张第三方无人形式化 Gibbs 理论。

源 atom `0aeb6b17305b0ea10af6e81726ca256b1a737c1a68f3bd78436f0a9d30d17a06`
的文本已读取：本轮对应(二)括号内 Gibbs 恒等式和 H=0 截面；
(一)辛化、(三)测量税勾股脚及末尾经典/量子因子分解均不在本轮范围。
因此只走 deposit-uncovered，atom 保持 residual-open，不冒领整条。
目录 `find D5/S3/Quantum/Divergence -type f | wc -l` 为 6，新增一文件仍低于 48。

缓存预热：make lean-cache-ensure EXIT=0；LEAN_CACHE status=seeded, method=clonefile,
clonefile_attempts=1, project_olean_state=warm, mathlib_olean_state=warm,
donor=/Users/chronoai/trureturing；完整日志 /tmp/gibbsvar-cache.log。

## Lean 接线尝试

热树 API 探针确认 `CFC.log_smul'`、`CFC.log_exp`、`Matrix.PosDef.trace_pos` 可用。
首版编译发现 `NormedAlgebra ℚ (CStarMatrix n n ℂ)` 需局部 restrictScalars，
且 CStarMatrix 的谱序不能与 MatrixOrder 定义等同；现改用
`CStarMatrix.ofMatrixStarAlgEquiv.symm` 的 `map_nonneg` 及 ring equivalence 的 IsUnit 传递。
迹代数已接入仓内熵分解；目前候选尚在编译修复，未声称 kernel 通过。
route 实测返回 `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.lean`，generality=G，utility=none。
全部声明为任意有限非空指标类型的一般算子结果，不属于有界枚举、检查器、数值归约或认证实例。

- https://arxiv.org/pdf/1505.07835 status=200, bytes=1536088, sha256=055b7441287bccc7ff27a3a76363eac9344e2dd047db5142c6cd5ff4574d2498

## Kernel 证明检查点

热树 `lake env lean D5/S3/Quantum/Divergence/GibbsVariationalIdentity.lean` EXIT=0。
主恒等式与 H=0 伴随式的公理检查均只有 propext、Classical.choice、Quot.sound；
无 sorry、私 axiom、native_decide。实际定义复用仓内 DensityState，故 ρ 可为任意半正定归一态；
Gibbs 参考态另证正定，所需正定 ρ 子域自然包含其中。
检索后的判形调整：谱对数候选见证已由 mathlib 提供，不主张 content；
模块采用 `proof_shape: bind-only`、`escape_witness: null`、
`admission_basis: rule-11-upstream-wrapper`。具体上游为 CFC.log_smul'、CFC.log_exp
和仓内 quantum_relative_entropy_eq_neg_entropy_sub_cross；必要性为 atom (二) 的
Gibbs 归一参考态与现有 DensityState/熵 API 之间尚缺的接口。
完整 make 门与冻结待后续记录。

- https://arxiv.org/abs/1505.07835 status=200, bytes=42187, sha256=4858b33a7a8efba9743e224c5db54c65671949dcd78764f3c09bdfa38800130c
