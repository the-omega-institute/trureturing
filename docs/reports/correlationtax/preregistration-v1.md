# 相关-税恒等式：预登记 v1

产地：Codex 实施席，lean4 skill，单点实施与自查；无独立评审结论。
基线：53ae8e3983bb738c24410db792dce23f9cbc3753；指定工作树与 lane/math/correlationtax。
源 observer-quantum-v1，atom 1e28ba01c5fc682ea2d77c4eb6673e9fb3de4ca5b6fbd2f26553e26b737a6cd0。
本轮为用户指定的既有数学形式化，不宣称解决文献开放问题。

question_answered：秩一标准基预测量的相干复制态是否满足
I(S:R) = S(diag rho) + D(rho || diag rho)，且两个边缘都由偏迹实际取得。
复制取 V|i> = |i,i>，联合态 V rho V*；不得改成消相干 CQ 态。

拟议 proof_shape: content；admission_basis: escape-witness。
拟议 escape_witness：相干复制等距膨胀保持 vonNeumannEntropy，
S(V rho V*) = S(rho)。它作为最终恒等式的必要前置，不由已冻结捏合定理投影获得。
拟用构造：证明复制映射的乘法、星、迹保持性及半正定性；
以非幺星代数同态的函数演算自然性证明零特征值扩充不改变熵。
这是同一等距膨胀见证的实现路线，不额外假设保熵。
若此见证失败且交付仅有边缘层，必须先另登记版本才以其他见证申请冻结。

伴随声明方向：最终恒等式 → 保熵、两个边缘；两个边缘 → 联合态构造；
最终恒等式 → 已冻结的捏合熵增。全部服务于上述具名源子句。
utility: none；一般有限维状态的结构定理，无有界枚举、检查器、数值归约或认证实例。

预登记数值检验：独立生成 d=2..5，每维 40 例（10 对角、10 纯态、
10 随机满秩、10 随机混合低秩；d=2 的低秩组仍为纯态）。固定种子 20260911。
独立以联合态与两次偏迹计算 I，以矩阵对数迹计算 D，容差 1e-10。
正式应 160/160 通过；在 120 个非对角样本中把 +D 换成 -D 应全失败。
另验 CQ 对照 I=S(diag rho)，并记录保熵与边缘残差。
这只作探针，不代替 Lean kernel。

先库后证：已读 D5 PartialTraceMutualInformation、VonNeumannEntropyPinching、
SpectralReadoutEntropyEquality 与 EntropyProductionCoherenceDeletionIdentity。
前者单参数互信息和偏迹直接复用。pinching 定理的 hPinch/hLogDiagonal 必须履行；
拟直接应用已有迭代恒等式在单位演化第零步的投影取得标准基熵增，避免重证。
Mathlib 命中 NonUnitalStarAlgHom.map_cfcₙ、cfcₙ_eq_cfc、PSD 矩阵共轭。
第三方 GitHub code search 的 entropy/isometry 有 62 个词面结果；
premeasurement 有 2 个词面结果。读取 physlib Entropy/SSA 与
csd-lean4 13eda16971c66de4bc9f550e418dd4fdf59a5121 的 LF6/Decoherence：
前者用于 SSA 的算子等距，后者是纯态消相干，未见本题一般混态保熵陈述。
本记录仅主张 not-found-in-searched-scope，不宣称文献或生态检索穷尽。

验收：指定串行构建 → make lean-report → make emit → make deposit-uncovered；
开 PR 前运行指定 scribe-content-checks，精确 merge-base SHA。
成：完整目标且上述门绿、无 sorryAx/私 axiom；翻：反例与 kernel 见证；
blocked：仅交已核验部分、失败路线与最锐剩余子命题。
每个可编译单元即时提交；不修改已冻结前置，不触已缓存的大枚举模块。
