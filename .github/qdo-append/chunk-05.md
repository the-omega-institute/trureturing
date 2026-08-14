\boxed{
\|P_{R_\infty}\chi\|=0
}
\]

于 Nyman–Beurling 塔。

### 显式 Dirichlet 近逆

构造 \(A_N\) 并证明

\[
\boxed{
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\longrightarrow0.
}
\]

### Weil form-core 正性

构造无条件闭合 Weil 型二次型 \(q_W\)，证明一列有限压缩形成 form core，并控制每个 Schur 余量及最终余块，从而得到

\[
\boxed{
q_W\ge0.
}
\]

三者都不是由“无限维余空间与原空间同型”推出。相反，第 28 节告诉我们为什么这种同型没有证明力：若忘记嵌入、壳层、目标向量与算子块，只剩

\[
R_N\cong\mathscr H,
\]

整个递归会坍缩成无信息固定点。

真正可能产生证明进展的对象是：

\[
\boxed{
\text{目标在每个正交创新层上的精确耦合}
}
\]

以及

\[
\boxed{
\text{这些耦合的可求和全局尾界}.
}
\]

---

## 29.12 可形式化拆分

建议把本节拆成以下 Lean 模块，按依赖顺序推进。

1. `CayleyZeroDefect`
   \[
   |(\rho-1)/\rho|^2-1
   =
   (1-2\Re\rho)/|\rho|^2.
   \]

2. `DiagonalUnitaryCriticalLine`
   \[
   C^*C=I
   \iff
   \forall\rho,\ \Re\rho=\frac12.
   \]

3. `NestedProjectionResidual`
   \[
   R_N=E_{N+1}\oplus R_{N+1},
   \qquad
   d_N^2=d_{N+1}^2+\|Q_{N+1}\chi\|^2.
   \]

4. `TargetQuotientVanishing`
   \[
   [\chi]=0\text{ in }\mathscr H/S_\infty
   \iff
   P_{S_\infty^\perp}\chi=0.
   \]

5. `FiniteGramProjection`
   \[
   d_N^2
   =
   \|\chi\|^2-b_N^*G_N^\dagger b_N.
   \]

6. `OneStepGramSchurGain`
   \[
   d_N^2-d_{N+1}^2
   =
   |\langle\chi,r_{N+1}\rangle|^2/\|r_{N+1}\|^2.
   \]

7. `ClosedFormCorePositivity`
   有限 core 上的非负性向闭合二次型定义域传递。

8. `PositiveDiagonalBlocksInsufficient`
   形式化二维块矩阵反例。

Nyman–Beurling–Báez-Duarte 等价本身依赖经典解析数论结果；在仓库完成该桥以前，应作为明确命名、来源可审计的外部定理接口，而不是把它悄然作为无名公理嵌入。

---

## 29.13 最终结论

Hilbert 正交商余塔对 RH 的最强严格结论不是“无限递归迫使零点上临界线”，而是以下目标化等价：

\[
\boxed{
\mathrm{RH}
\iff
[\chi]=0
\text{ 于 }
L^2(0,\infty)/
\overline{\operatorname{span}}
\left\{
\varrho\left(\frac1{ax}\right):a\in\mathbb N
\right\}.
}
\]

通过商—正交余同构，它等价于

\[
\boxed{
\mathrm{RH}
\iff
P_{R_\infty}\chi=0.
}
\]

通过壳层能量分解，它又等价于

\[
\boxed{
\mathrm{RH}
\iff
\sum_{k\ge1}\|Q_k\chi\|^2=1.
}
\]

通过 Mellin–Plancherel，它等价于

\[
\boxed{
\inf_{A_N}
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\longrightarrow0.
}
\]

零点侧则有诊断等价

\[
\boxed{
\mathrm{RH}
\iff
C^*C=I,
\qquad
Ce_\rho=\left(1-\frac1\rho\right)e_\rho.
}
\]

这四个公式共同揭示同一结构：

\[
\boxed{
\text{RH 不是“余空间不存在”，而是“指定的离线／逼近缺陷在完成后没有剩余质量”。}
}
\]

第 28 节已经提供了精确的商余账本；剩余的数学核心是建立一个无条件、可求和、能穿过无限完成的全局尾估计。缺少该估计时，有限零点核验、有限 Gram 矩阵正性、局部 Li 轨道暴露与有限 Weil 压缩都只能构成证据或等价重述，不能单独完成 RH 的证明。

## 29.14 参考接口

- L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis*, 2002.
- X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, 1997.
- A. Connes and C. Consani, *Weil positivity and Trace formula, the archimedean place*, 2020.
- M. Suzuki, *Li coefficients as norms of functions in a model space*, 2023.
- M. Suzuki, *Weil's quadratic form via the screw function*, 2026.
- 仓库接口：`D5/S3/Weil/WeilIdentity.lean`、`D5/S3/Weil/SpectralDynamics.lean`、`D5/S3/Analytic/LiCausalTrichotomy.lean`。

## 29.15 严格非主张与形式化状态

1. 本节没有证明 \(P_{R_\infty}\chi=0\)。
2. 本节没有从有限 \(d_N\) 数值趋降推出其极限为零。
3. 本节没有从有限高度零点全部位于临界线推出不存在更高离线零点。
4. 本节没有把由零点定义的 Cayley 对角算子冒充为独立构造的 Hilbert–Pólya 算子。
5. 本节没有证明局部离线四元贡献必在某个预先给定的 \(n\) 上使全局 Li 系数为负。
6. 本节没有证明有限 Weil 压缩自动形成 form core。
7. 本节没有以 Weil 正性先定义 Hilbert 内积再循环证明 Weil 正性。
8. 本节全部新增定理均为纸面结论；未经 kernel verification 不得标记为 `Closed`。
---

# 30. 追加：界面相对性、对角闭合与量子上下文完成

## 30.0 核心命题与严格边界

本节把此前关于

\[
\infty,\qquad
\text{对角化},\qquad
\text{商余},\qquad
\text{Hilbert 投影},\qquad
\text{量子概率}
\]

的讨论收紧为一个共同数学问题：

\[
\boxed{
\text{整体结构如何相对于一个有限界面被识别、遗忘、演化、逃逸与完成？}
}
\]

这里的“相对性”不是主观任意性，而是以下数据的依赖性：

1. 哪个映射被选作观察界面；
2. 哪些对象被该界面识别为同一对象；
3. 哪些差异进入核、纤维或正交余空间；
4. 整体操作能否下降为界面上的有效操作；
5. 不同界面之间能否自然转换；
6. 所有有限界面的相容数据是否来自一个可实现的整体对象；
7. 一个状态在不可见余空间中是否仍保留非零质量。

本节得到的统一解释是：

\[
\boxed{
\begin{aligned}
\text{商}
&=\text{相对于界面保留的同一性},\\
\text{余}
&=\text{相对于界面被删除的差异},\\
\text{对角化}
&=\text{相对描述无法封闭自身的证书},\\
\infty
&=\text{不存在有限终止界面，但相容界面族可以完成},\\
\text{概率}
&=\text{状态对界面事件的标量评价},\\
\text{量子性}
&=\text{局部经典界面不能统一拼成单一全局 Boolean 界面}.
\end{aligned}
}
\]

本节不主张一切物理相对性均等同于商空间，不把量子理论还原为一个裸无限维 Hilbert 空间，也不把上下文性、Bell 非局域性、退相干和测量问题混成同一个定理。新增结果均为纸面推导；未经 Lean proof term、依赖闭包与冻结收据不得标记为 `Closed`。

---

## 30.1 界面系统、相对同一性与观察偏序

### 定义 30.1（观察界面）

设 \(X\) 为整体对象空间。一个观察界面是映射

\[
q_i:X\to X_i.
\]

它在 \(X\) 上诱导等价关系

\[
\boxed{
x\sim_i y
\iff
q_i(x)=q_i(y).
}
\]

若把 \(X_i\) 替换为实际像 \(q_i(X)\)，则有规范双射

\[
\boxed{
X/{\sim_i}\cong X_i.
}
\]

因此 \(X_i\) 不是一个绝对缩小版的 \(X\)，而是由 \(q_i\) 决定的相对身份空间。

### 定义 30.2（观察精化）

若存在映射

\[
p_{j,i}:X_j\to X_i
\]

满足

\[
\boxed{
q_i=p_{j,i}\circ q_j,
}
\]

则称 \(j\) 比 \(i\) 更精细，记为

\[
j\succeq i.
\]

这表示细界面的读出足以确定粗界面的读出。

### 定理 30.3（相对同一性的反变单调性）

若 \(j\succeq i\)，则

\[
\boxed{
{\sim_j}\subseteq{\sim_i}.
}
\]

并存在唯一满射

\[
\boxed{
\bar p_{j,i}:X/{\sim_j}\twoheadrightarrow X/{\sim_i}
}
\]

使自然商图交换。

#### 证明

若 \(x\sim_jy\)，则 \(q_j(x)=q_j(y)\)。施加 \(p_{j,i}\) 得

\[
q_i(x)=p_{j,i}(q_j(x))
      =p_{j,i}(q_j(y))
      =q_i(y),
\]

故 \(x\sim_i y\)。商映射的存在唯一性由商的泛性质得到。 \(\square\)

所以：

\[
\boxed{
\text{观察越细，被称为“同一”的对象越少；}
}
\]

而：

\[
\boxed{
\text{观察越粗，被遗忘到同一纤维中的差异越多。}
}
\]

### 定义 30.4（相对余量）

一般集合界面 \(q_i\) 的余量不是一个规范对象，而是纤维族

\[
\boxed{
\mathcal R_i(x)=q_i^{-1}(q_i(x)).
}
\]

若 \(X\) 为线性空间且 \(q_i\) 线性，则不可见方向由

\[
