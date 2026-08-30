# 黄金素数圆、二元电荷层析与临界谱完成

**Formal Golden Prime Circle, Binary Charge Tomography, and Critical-Spectrum Completion**

**版本：v0.1，2026-08-30**

## 0. 文档地位

本文把黄金比例、素数分裂、观察者压缩、尺度圆与 Riemann 型临界反射组织成一条严格分层的理论链。Lean 文件是机器真源。本文负责解释对象、桥梁、适用范围和仍然开放的解析义务。

本文不宣称已经证明 RH、GRH、显式公式的新版本或 `L(1, chi_5)` 的解析特殊值。临界线到单位圆的变换是精确坐标重写。它的研究价值来自与黄金尺度、二元分裂电荷和 observer completion 的兼容性。

---

## 1. 三种压缩必须分开

### 1.1 阿贝尔化

素数是正有理数乘法群的自由生成元：

\[
\mathbb Q_{>0}^{\times}\cong\bigoplus_p\mathbb Z[p].
\]

从有序素数观察词进入该群会删除顺序，只保留素因子指数。

### 1.2 字符投影

普通 zeta 对应平凡字符通道。对黄金二次域，非平凡字符 `chi_5` 读取 split/inert 电荷。联合通道

\[
(\mathbf 1,\chi_5)
\]

是群 `C_2` 上的完整 Fourier 坐标。

### 1.3 反射偶化

completed reflection

\[
\mathcal R(s)=1-\overline{s}
\]

把法向偏差 `delta` 变为 `-delta`。对称标量观察会消去奇通道，同时保留乘积、平方和曲率等偶不变量。

---

## 2. 黄金尺度圆

定义黄金正定向周期

\[
L_\varphi=2\log\varphi.
\]

对正尺度 `x`，定义未取商坐标

\[
\eta_\varphi(x)=\frac{\log x}{L_\varphi}.
\]

机器定理证明

\[
\eta_\varphi(xy)=\eta_\varphi(x)+\eta_\varphi(y)
\]

以及

\[
\eta_\varphi(\varphi^2x)=\eta_\varphi(x)+1.
\]

因此取模 `Z` 后得到黄金尺度圆。当前 Lean owner 保留未取商实坐标，以避免把 circle quotient 的拓扑接口与本批代数定理混在一起。

其 Fourier 基频为

\[
\omega_\varphi=\frac{2\pi}{L_\varphi}=\frac{\pi}{\log\varphi}.
\]

机器闭合的精确桥为

\[
2\pi k\,\eta_\varphi(x)
=
(k\omega_\varphi)\log x.
\]

这解释了黄金圆的 Fourier 模式为什么对应 Mellin 变量的垂直平移。

---

## 3. 相同电荷与不同观察者

设壳层读出为

\[
q_r:X\to Y_r,
\]

并存在电荷投影

\[
c_r:Y_r\to C
\]

满足

\[
c_r\circ q_r=\chi.
\]

所有壳层读取同一个电荷 `chi`。它们仍可保留不同残余信息，因此 kernel 不必相同。机器反模型使用一个只读取 Boolean charge 的粗壳和一个同时保留 residual bit 的细壳，证明共同电荷不推出观察者相同。

---

## 4. 黄金 `C_2` 电荷层析

令 split 与 inert 信号为 `(S,I)`。定义

\[
N=S+I,
\qquad
C=S-I.
\]

反演为

\[
S=\frac{N+C}{2},
\qquad
I=\frac{N-C}{2}.
\]

这里 `N` 是中性通道，`C` 是二次电荷通道。该反演已经机器证明。

对单个未分歧素数，`chi_5(p)=+1` 给 split 指示器，`chi_5(p)=-1` 给 inert 指示器。`p=5` 是分歧通道，需要单独保留。

---

## 5. 黄金局部 Euler 三分律

令形式局部变量为 `X`，定义

\[
D_\chi(X)=(1-X)(1-\chi X).
\]

机器证明

\[
\begin{aligned}
D_{+1}(X)&=(1-X)^2,\\
D_{-1}(X)&=1-X^2,\\
D_0(X)&=1-X.
\end{aligned}
\]

它们分别对应 split、inert、ramified 三种黄金局部类型。仓库已有 prime classification 证明素数的黄金分裂类型由 `p mod 5` 决定。本批新增 residue-to-charge-to-Euler-denominator 的桥接 owner。

---

## 6. 黄金临界半径

对复变量 `s` 定义

\[
b(s)=\Re(s)-\frac12
\]

和黄金临界半径

\[
R_\varphi(s)=\exp(L_\varphi b(s)).
\]

机器证明

\[
R_\varphi(s)=1
\iff
\Re(s)=\frac12.
\]

临界反射满足

\[
b(\mathcal R s)=-b(s)
\]

以及

\[
R_\varphi(\mathcal R s)=R_\varphi(s)^{-1}.
\]

因此每一对反射伙伴都满足

\[
R_\varphi(s)R_\varphi(\mathcal R s)=1.
\]

这只是成对平衡。逐点中性要求

\[
R_\varphi(s)=1.
\]

所以函数方程型对称提供 pairwise balance，Riemann 型临界线命题要求 pointwise neutrality。Lean 中已经给出显式反例，说明乘积为一不能推出每个因子为一。

---

## 7. 与 RH 和 GRH 的精确边界

对任意候选零点集 `Z`，机器定理证明

\[
\forall s\in Z,\ \Re(s)=\frac12
\iff
\forall s\in Z,\ R_\varphi(s)=1.
\]

当 `Z` 被实例化为 completed zeta 或某个 completed `L`-函数的非平凡零点集时，这成为对应 RH 或 GRH 的等价坐标表达。该实例化本身需要仓库中严格定义的 completed function、zero predicate 和 trivial-zero exclusion。

本批不把坐标等价冒充为零点位置证明。

---

## 8. 后续解析桥

下列内容保留为后续形式化目标：

1. 在绝对收敛半平面中建立有限或无限黄金壳测度的 Fourier 系数与 `-L'/L` 垂直采样之间的定理；
2. 形式化 `L(1,chi_5)=2 log(phi)/sqrt(5)`，并连接黄金 Möbius Lyapunov 指数；
3. 将 explicit formula 实现为 prime-shell test space 与 zero-spectrum distribution 之间的连续线性泛函恒等式；
4. 构造足够完备的 golden Weil frame，并证明其正性是否等价于完整 Weil criterion；
5. 证明任何新增传递算子的酉性或自伴随性，不能从 determinant 的成对平衡直接推出。

---

## 9. 机器 owner

```text
D5/S3/Observer/GoldenPrimeCircle/
  GoldenScaleCircle.lean
  GoldenVerticalSampling.lean
  SharedChargeDifferentShells.lean

D5/S3/PrimeForms/GoldenEuler/
  GoldenChargeTomography.lean
  GoldenLocalEulerTrichotomy.lean
  GoldenResidueChargeBridge.lean

D5/S3/Weil/GoldenCriticalSpectrum/
  GoldenCriticalRadius.lean
  GoldenReflectionTransfer.lean
```
