# §17.2 对偶账全额条款

精确 Lean 陈述、原文映射和证明前判据见 [preregistration.md](preregistration.md)。
定理没有改变该预登记的假设或结论。数学真源为
`D5/S3/Quantum/Divergence/DualAccountFull.lean`。

产地：Codex，lean4 skill，主循环实施、数值核验和本地检查；零独立评审席。
实现起点 `bc401f09ba6919eb52582a8530c23612049e7de8`，
Lean 4.33.0 / Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。
独立评审由调用方的后续阶段承担，不主张已获独立批准或已合并。

## 数学结果

以互无偏性 `ReTr(Z_j X_k)=1/d` 表达共轭基，维数为任意正自然数。
令 `omega = gibbsState 0 = I/d`。对 Z 捏合不变的任意密度态 rho，
实际 X 捏合输出 sigma 被证明等于 omega，且

```
D(rho || sigma) = D(rho || omega) = log d - S(rho)
S(sigma) - S(rho) = D(rho || sigma)
X 捏合也不改 rho  ↔  rho = omega
```

另对所有密度态证明 `S≥0`、`D(rho||omega)≥0` 和 `S+D=log d`，
故任意选择轨迹逐点处于该闭线段。未为“时间等于弧长”引入或声称证明动力学；
该额外源句不在本次用户靶内。奇异输入态允许存在，参考 omega 则满秩。
这里使用仓内既有有限 trace-log 相对熵；在本定理实际参考 sigma=omega 上
没有支持不包含的无穷值问题。

## 先库后证与判形

仓内命中并直接使用：

- `MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes`：
  最后一条 iff 的逆向给出双捏合完全退极化，代入 Z 不变和 trace=1。
- `GibbsVariationalIdentity.gibbs_state_zero`、`entropy_uniform_identity`：
  直接识别 I/d，并给出自由量和熵的守恒式。将已有恒等式用于 omega 得到其熵 log d，
  没有另行重做矩阵对数或极大混态熵的谱计算。
- `FreeNegentropyBudget.free_negentropy_budget` 的概率谱分量、
  `von_neumann_entropy_eq_shannon_state_spectrum`、
  `MaxEntropy.entropy_le_log_card`、`EntropyNonneg.shannon_entropy_nonneg`：
  直接给出线段的两个端点界。

用户指定的 `von_neumann_entropy_pinching` 和
`SpectralReadoutEntropyEquality.spectral_readout_entropy_eq_iff_isDiag` 已检索。
前者的一般 log-diagonal 前提在这里无需新增：输出已知是 omega，Gibbs 恒等式直接给出熵差。
后者处理熵相等的读出判据；本靶已直接给出捏合不变态，因此未重复证明该判据。

钉版 Mathlib 的矩阵序、矩阵 trace、CFC 标量对数接口已检索。
在线 Loogle 名称查询 `"mutually_unbiased"` HTTP 200、0 个声明，收据见
[loogle-search.json](loogle-search.json)；这是该名称搜索的有界结果，不是全生态不存在证明。
文献检索 https://arxiv.org/abs/1311.0275 HTTP 200，标题 Quantifying Coherence，
作者 Baumgratz/Cramer/Plenio，DOI 10.1103/PhysRevLett.113.140401；只核对了摘要元数据，
不据此声称该文逐字包含本靶。Scribe 将本次既有仓内定理的组合表态为 repo-derived。

| 公开声明 | proof_shape | admission_basis | escape_witness |
| --- | --- | --- | --- |
| `dual_account_full` | bind-only | atom-required-bridge | 无；拟议见证已被仓内命中否决 |
| `entropy_freedom_segment` | bind-only | 同模块伴随结果 | 无 |

预登记 v2 在数值和证明前说明了改判。连接的新边为“互无偏捏合输出 →
零 Hamiltonian Gibbs 参考态 → 相对熵税/自由/熵差”，由源 atom 明文要求。
具名消费者 `dual_account_full` 活用私有 `conjugate_pinching_eq_uniform`；
`entropy_freedom_segment → entropy_uniform_identity`，后者亦被主定理消费，
对应同一 atom 的相图义务。没有把已有退极化结论再包装成逃逸内容。
全部公开声明为一般算子或熵结论，无有限计算性内容，故 `utility: none`；
其余计算用途字段 not-applicable(kind=none)。
直接冻结前置的声明身份与公理集见
[frozen-dependencies.json](frozen-dependencies.json)：主定理使用前两项量子模块的三条声明，
相图使用 Gibbs 守恒式与四条谱/熵声明。没有外加 axiom、native_decide 或新定义的自由量。

## 数值核验

命令 `python3 docs/reports/qdualaccount/numerical_check.py`，固定种子 172021，
NumPy 2.0.2，阈值 1e-10。维数 1,2,3,4,5,8；612 个 Z 不变态样本包含纯态、均匀态、
随机谱及共同旋转的基；另取 600 个一般密度态核验完整相图。
原式 0 个失败，最大残差 2.3037127760972e-15。

身份对照逐项检验 diag(1,0)、diag(3/4,1/4)、I/2 的实际捏合矩阵、输入熵、
输出熵、税、自由和熵差；期望由独立解析常数给出。
三个输入熵分别为 0、`2 log 2 - (3/4) log 3`、log 2，
对应税为 log 2、0.130812035941137、0。
全部逐项通过，原始数值见 [numerical_result.json](numerical_result.json)。

判别力对照：只把税=自由改成税=-自由，纯 Z 态残差 1.3862943611198908；
独立命令 `python3 docs/reports/qdualaccount/numerical_check.py --wrong-sign`
实际以断言错误退出 1，见 [wrong-sign.log](wrong-sign.log)。
另将共轭基换成同一基，错误命题的残差为 0.6931471805599453，被检出。
这些是数值仪器对照，不冒充原命题反例或 kernel 见证。

## 构建修复与边界

首次串行构建补齐 10 个缺失缓存模块，新模块 elaborate 失败。
后续错误是 CStarMatrix/普通 Matrix 的显式转换、`Fintype.card_fin` 非定义归约、
局部 omega 别名的改写；Lean LSP 逐一显示具体未闭目标，修复不改变陈述。
最后矩阵单位元的逐项归约中使用 rfl，仅作类型表示转换，未交付定义体同义反复定理。
失败的 LSP 输出确实含 sorryAx，不能当证明；本地成功判据另见门链收据。
没有发生构建被杀，也没有清理其它工作树的进程。

失败诊断原件保存在 runner attempt 的 diagnostics/ 下；本报告保留可复用的失败原因。
