# Predictive Thermodynamic Graded Spectrum

> 本卷按 `generic-v1` 理论输入组织。它记录归一化正定矩阵族的抽象谱结论，作为后续物理 Gramian 桥接的参考输入；Lean 声明及其证明项仍是数学真源。本卷只增不减，后续修订写在追加锚之后。

## 1. 定位、状态与产地

**参考输入,不是真源。** 本卷只陈述抽象矩阵接口和它与原问题的边界，不宣称已经构造物理轨迹或矩积分矩阵。形式化状态以 D5 源、内核检查和冻结账本为准。

**证明状态。** 下述定理给出普通数学的完整量词和证明路线；其对应 Lean 源由同一批交付提供。这里的散文不替代 Lean 核验，也不关闭原始 5.2/5.3、6.2/6.3 或父 atom 的其余子句。

**数学来源与范围。** 本卷的承重数学是归一化正定矩阵族的抽象谱结论；证明使用 pinned Mathlib 的主子式、特征多项式与 canonical `eigenvalues₀` API，范围限于本卷定理，不包括物理轨迹或统计桥。

## 2. 记号与约定

**约定 2.1（右侧极限）。** $T\to0^+$ 表示沿 `nhdsWithin 0 (Ioi 0)` 的极限。矩阵的 `PosDef` 是实有限维矩阵的正定性；空主子式和空乘积均取 $1$。

**约定 2.2（等级与缩放）。** 给定有限指标集 $\operatorname{Fin}(n)$ 和单调不减的整数等级 $w_i$，令

$$
d_T(i)=T^{w_i}\sqrt T,\qquad G_T=\operatorname{diag}(d_T)H_T\operatorname{diag}(d_T).
$$

矩阵的谱坐标使用 Hermitian `eigenvalues₀` 的 Mathlib canonical decreasing 顺序；它不是另给的排列或独立的特征值函数。

## 3. 抽象归一化 Gramian 的完整谱界

**定理 3.1（单调等级下的 canonical graded spectrum）。** 对任意 $n\in\mathbb N$、$H:\mathbb R\to\operatorname{Matrix}(\operatorname{Fin}(n),\operatorname{Fin}(n),\mathbb R)$、$H_0$ 和 $w:\operatorname{Fin}(n)\to\mathbb N$，假设 $w$ 单调不减，$H_T\to H_0$ 当 $T\to0^+$，$H_0$ 正定，并且每个 $T>0$ 的实际矩阵

$$
G_T=\operatorname{diag}(T^{w_i}\sqrt T)\,H_T\,\operatorname{diag}(T^{w_i}\sqrt T)
$$

正定。则存在与 $T$ 和指标无关的 $c,C,\delta>0$，使得对每个 $0<T<\delta$ 及每个 $i\in\operatorname{Fin}n$，canonical decreasing eigenvalue 满足

$$
cT^{2w_i+1}\le
\lambda_i(G_T)\le CT^{2w_i+1}.
$$

这里 $\lambda_i(G_T)$ 是实际 $G_T$ 的 `Matrix.IsHermitian.eigenvalues₀`，通过 $\operatorname{card}(\operatorname{Fin}(n))=n$ 的标准有序同构取坐标。结论允许 $n=0$、重复等级和空等级层，并包括 $k=0$ 的空主子式和空前缀。

**证明。** 对每个主子集 $S$，$H_0[S,S]$ 正定，因此其行列式为正；有限多个主子式给出共同的正下界和上界邻域。实际对角合同的主子式行列式按

$$
\det G_T[S,S]=T^{\sum_{i\in S}(2w_i+1)}\det H_T[S,S]
$$

缩放。由 `Finset.orderEmbOfFin` 和 $w$ 的单调性，任何 $k$ 元子集的等级和不小于前 $k$ 个等级的和。Mathlib 的主子式系数恒等式于是给出实际系数 $e_k(T)$ 的两侧幂界：保留前 $k$ 子集给下界，所有子集的共同上界和有限计数给上界。

同一个实际 $G_T$ 的 Hermitian characteristic polynomial 与实际 canonical eigenvalues₀ 对角矩阵的 characteristic polynomial 相等；`charpoly_coeff_eq_sum_minors` 与对角矩阵主子式恒等式把 $e_k(T)$ 识别为这些 canonical eigenvalues 的 $k$ 次基本对称和。由于 $G_T$ 正定，所有这些谱坐标非负。对递减序列，任意 $k$ 元子集的乘积不超过前 $k$ 项乘积，而前缀乘积又不超过基本对称和；有限子集数给反向上界。于是每个前缀乘积都具有前 $k$ 等级和的统一两侧幂界。正的前缀乘积允许相邻比值相消，且前缀等级和的差正好是 $2w_i+1$，得到所述单项界。

## 4. 适用边界

**命题 4.1（抽象接口的范围）。** 定理 3.1 只承担从同一个实际矩阵族 $G_T$ 的归一化极限到 canonical sorted spectrum 的抽象桥。它不构造 $H_T$、$H_0$、等级分解或任何物理观测模型。

**证明。** 定理的前提已经把这些对象作为同一族的输入；证明只使用这些前提和有限维矩阵恒等式。

**开放问题 4.2（物理与统计桥）。** 将实际积分 Gramian 放入定理 3.1 仍需证明同一对象的正交分层坐标、归一化极限、实际等级重数以及所需的局部正定性。矩积分在所有大窗口上不必正定，因此不能把抽象的“所有 $T>0$ 正定”前提静默移植到 moment 实验。行列式首项、噪声风险、任意正方差日程和原始全 14/218/PCLGCRGIR 子句仍需各自的形式化桥。

## 5. 来源、文献状态与核验边界

| 来源 | 精确范围与使用边界 |
| --- | --- |
| 仓内 pinned Mathlib | `repo-derived`：主子式系数恒等式、Hermitian characteristic polynomial、canonical `eigenvalues₀` 的排序和正定性 API；只用于定理 3.1 的已编译证明。 |
| 原始 PR8899 理论上下文 | `literature-attested`：物理 Gramian 的动机和后续桥接目标；不替代本卷抽象定理的 Lean 证明，也不提供其完整 telescope。 |
| 本卷抽象推导 | `repo-derived`：定理 3.1 的统一主子式幂界、canonical spectrum 前缀夹逼和相邻比值链。 |

**核验边界。** 有限维 Lean 证明覆盖定理 3.1 的全称参数和退化分支；它没有核验物理 Gramian、矩积分、统计风险或父 atom 的其余原始子句。

## 6. 有限精确核验

```text
The abstract theorem is checked by the canonical D5 Lean source named in this delivery.
```

## 追加锚（本行以下为增补区）
