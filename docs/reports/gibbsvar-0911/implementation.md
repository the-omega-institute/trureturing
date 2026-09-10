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
