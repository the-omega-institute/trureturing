# 相关-税恒等式实施结果

产地：Codex 实施席，使用 lean4 skill；本席亲跑数值与 Lean/门链。
无独立评审席，不主张异模型共识。预登记见 preregistration-v1.md，数值见 numerics.md。

## 数学交付

模块 `D5/S3/Quantum/Information/CoherentCopyCorrelationTax`。
任意有限类型 n 和 DensityState n；没有正定、非零概率或非退化谱前提。

- `coherentCopyState`：V rho V* 的 DensityState (n × n)，其中 V|i> = |i,i>。
  半正定来自 Mathlib 的矩形矩阵共轭，迹一来自 V*V=1 和矩形迹循环。
- `coherentCopyState_correlated_entry`：联合态在 (i,i),(j,j) 保留 rho(i,j)。
  此为矩阵乘法的计算结果；联合态定义是 V rho V*，不是该定理右侧的别名。
- `marginalRight_coherentCopyState` 与 `marginalLeft_coherentCopyState`：
  实际偏迹分别给出系统与记录，二者均为既有 basisPinchingState rho。
  该已有定义就是 diag(rho(i,i))，PSD 保证这些对角数实且非负。
- `vonNeumannEntropy_coherentCopyState`：S(V rho V*) = S(rho)。
- `coherent_copy_correlation_tax`：
  quantumMutualInformation (coherentCopyState rho) =
  vonNeumannEntropy (basisPinchingState rho) +
  quantumRelativeEntropy rho (basisPinchingState rho)。

这里 V 是不同维数之间的等距嵌入；没有把它误称为 n 到 n² 的方阵酉算子。
这正是初始化纯记录后酉预测量的状态嵌入，未换成 CQ 混合态。
谱上的新增零值不贡献熵；证明直接用非幺函数演算处理零谱，不假设保熵。

## 复用与实际见证

已完整核对 `von_neumann_entropy_pinching`：它仅在 Fin d 上，且带 hPinch 与
hLogDiagonal。未将这两个条件冒充已给见证，也未重新证明冻结的捏合熵增。
实际直接应用更一般的已冻结 `entropy_production_coherence_deletion_identity`：
令 U=1，令 f(k)=basisPinchingState 迭代 k 次，取第零步；于是获得无条件捏合等式。
此处的 f/hStep 是已构造的迭代，不是把待证结论塞进假设。

拟议与实际 escape_witness 一致：`vonNeumannEntropy_coherentCopyState`。
活路径为最终恒等式 → 保熵 → copyHom_log → copyHom/map_mul → V*V=1。
复制映射的乘法、星和迹性质经显式构造提供；Mathlib 的 map_cfcₙ 只负责
已构造同态的函数演算自然性，不直接提供本联合态的保熵等式。
移除该保熵见证，已有捏合熵定理不能消去联合态的熵项。
该见证与最终互信息等式不定义等价，也不是其同义重述。

| 公开定理 | proof_shape | escape_witness / 有向用途 | admission_basis |
| --- | --- | --- | --- |
| coherentCopyState_correlated_entry | bind-only | 具名伴随：识别源规定的相干膨胀；使用 copyMatrix_entry | escape-witness（模块伴随） |
| marginalRight_coherentCopyState | bind-only | correlation_tax → 本边缘；源的系统边缘义务 | escape-witness（模块伴随） |
| marginalLeft_coherentCopyState | bind-only | correlation_tax → 本边缘；源的记录边缘义务 | escape-witness（模块伴随） |
| vonNeumannEntropy_coherentCopyState | content | 显式构造 copyHom，传递 log 并保持迹 | escape-witness |
| coherent_copy_correlation_tax | content | 上述保熵定理位于活证明路径 | escape-witness |

bind-only 伴随只随此内容模块落地，未独立申请冻结。
utility: none；全部是任意有限载体及任意密度态的一般结构结果，无四类计算性内容。
数值仪器仅为源恒等式及改号/CQ 对照的探针，不进入 Lean 或冻结声明。

## 路线与失败战史

1. 局部矩阵乘法编译暴露 CStarMatrix 的自动转换与普通 Matrix 乘法实例混用；
   显式标注矩形 V 与 ofMatrix.symm 后解消，不改数学陈述。
2. 单用推断未找到实 ContinuousFunctionalCalculus 实例；为两侧 CStarMatrix
   显式选择 IsSelfAdjoint.instContinuousFunctionalCalculus。
3. 连续性所需有限维结构由 ofMatrixₗ 的线性等价转移，未增加假设。
4. 非幺映射路线成功；特征多项式/补零谱路线只作检索备选，未实施，不报失败。
5. 首次数值对数的极小正数截断与仓内 log(0)=0 不同；修正及两版原始读数均保留。

目标的数学缺口：无。单点质量审查不能代替独立评审；PR/门链状态另列，不冒领合并。

## 直接冻结前置的声明身份

以下身份直接读取 canonical Lean report；完整模块声明与公理闭包在 semantic-evidence.json。
GID 的模块路径用斜线，声明前用点。表号只用于本报告缩写。

| 编号 | GID | statement_id |
| --- | --- | --- |
| P0 | `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState` | `sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337` |
| P1 | `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy` | `sha256:1fde73d469bc7e293eef439b271276205450d8758cb7358eaadae794794d8f0a` |
| P2 | `D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy` | `sha256:9cf1e21822d8f3f61a5d349f41c4287a3ef43a0e8a600534b28ab8d06f437cd1` |
| P3 | `D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.basisPinchingState` | `sha256:097732781ac08f1ec116972e13a88ead78c40c635e33adde60bb7bd8e11c6522` |
| P4 | `D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState` | `sha256:9b1299d5fa00a59321b435771bba283a533b7e1e7a071e7d927aae4eb94d4d42` |
| P5 | `D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.entropy_production_coherence_deletion_identity` | `sha256:dd08a6058e548162341b4da32bf0bafc5b7b406598c58016d18da2821fa77797` |
| P6 | `D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalLeft` | `sha256:7579934e8cf68c9a1e1f14470e58e70c66939704953b29e953ae8d75b92bef6a` |
| P7 | `D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight` | `sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7` |
| P8 | `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft` | `sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d` |
| P9 | `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight` | `sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77` |
| P10 | `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation` | `sha256:650358808a68c73893baf137ee9bae34238244b7e0906ce19e6b5fd68484ad75` |

逐公开定理的前置（展开本模块 helper，类型与证明使用的仓内接口；Mathlib 不算冻结前置）：

- `coherentCopyState_correlated_entry`：P0。
- `marginalRight_coherentCopyState`：P0, P3, P7, P9。
- `marginalLeft_coherentCopyState`：P0, P3, P6, P8。
- `vonNeumannEntropy_coherentCopyState`：P0, P2。
- `coherent_copy_correlation_tax`：P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10。

源手写公开定理共五条；report 还列出私有证明和 Lean 自动生成的 congr_simp 声明，均保留其公理闭包。

## 落点检查

route 返回 D5/S3/Quantum/Information/CoherentCopyCorrelationTax.lean，S3/Quantum 已注册。
新增前 D5/Information、Blueprint/Information（不计 .md）、Library/Quantum 分别为 1、1、16；
新增后分别 2、2、17，均小于 SL-003 的 48。直接 import 的两个模块均 generality:G。
Lean 七行头部次序与 utility:none 合规；Lean 每行不超过 100 字符。
