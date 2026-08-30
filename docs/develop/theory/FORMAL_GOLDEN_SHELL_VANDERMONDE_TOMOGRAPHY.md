# 黄金壳刚性、有限 Vandermonde 层析与局部 Euler 尾项

**版本：v0.1，2026-08-31**

本文继续黄金观察者、素数尺度圆与临界谱路线。目标是把上一阶段提出的三种缺陷分开：

\[
\boxed{
\text{代数壳碰撞}
\quad+
\text{有限相位层析 kernel}
\quad+
\text{Euler 截断 residual}.
}
\]

本批只处理能够在当前 `dev` 上无条件闭合的有限或局部命题。无限素数积、显式公式、全局正性、RH 与 GRH 都保留为独立证明义务。

---

## 1. 黄金壳的有理刚性

令

\[
\varphi=\frac{1+\sqrt5}{2},
\qquad
u=\varphi^2.
\]

`ν` 是保持定向的黄金单位。黄金尺度圆的通用覆盖以

\[
2\log\varphi=\log\nu
\]

为一个壳周期。

若两个非零有理尺度满足

\[
q_1=\nu^n q_2,
\qquad
q_1,q_2\in\mathbb Q,
\qquad
n\in\mathbb N,
\]

则

\[
\boxed{n=0\quad\text{且}\quad q_1=q_2.}
\]

证明机制不是数值近似。对每个 `m ≥ 1`，Fibonacci 展开给出

\[
\varphi^m=F_m\varphi+F_{m-1}.
\]

系数 `F_m` 严格为正。由于 `φ` 无理，`φ^m` 仍然无理。因此任何正次幂 `ν^n` 都不可能等于非零有理数 `q_1/q_2`。

这关闭的是通用覆盖上的精确碰撞问题。它尚未提供下列更强结果：

1. 商圆 `ℝ/(2 log φ)ℤ` 上的完整类型化嵌入；
2. 不同有理尺度相位之间的统一正距离；
3. 有界高度窗口中的最小分离常数；
4. 有限精度下的稳定解码。

精确单射与稳定单射必须分开。

---

## 2. 有限相位事件的 Vandermonde 层析

取一个域 `K`，有限相位节点

\[
z_j\in K,
\qquad
j=0,\ldots,n-1,
\]

以及隐藏振幅

\[
a_j\in K.
\]

定义前 `n` 个矩：

\[
m_k=\sum_{j=0}^{n-1} z_j^k a_j,
\qquad
k=0,\ldots,n-1.
\]

这可写成

\[
m=Va,
\]

其中

\[
V_{kj}=z_j^k
\]

是 Vandermonde 矩阵。它的行列式为

\[
\det V=\prod_{i<j}(z_j-z_i).
\]

因此，若节点函数是单射的，即所有节点两两不同，则

\[
\det V\ne0.
\]

从而

\[
\boxed{
Va=Vb\iff a=b.
}
\]

这严格证明：对有限的 `n` 个相位事件，前 `n` 个 Fourier 或 Mellin 矩已经足以消除振幅 kernel。

这里需要区分两个坐标约定。Mathlib 的 `Matrix.vandermonde nodes` 使用行索引表示节点、列索引表示幂。仓库定义的读出采用它的 `mulVec`。转置只改变“节点作为行”还是“模式作为行”的排版，不改变行列式非零和有限忠实性。

---

## 3. 两节点模型暴露稳定性尺度

对两个节点 `z₀ ≠ z₁`，矩为

\[
m_0=a_0+a_1,
\qquad
m_1=z_0a_0+z_1a_1.
\]

显式反演为

\[
\boxed{
a_0=\frac{z_1m_0-m_1}{z_1-z_0},
\qquad
a_1=\frac{m_1-z_0m_0}{z_1-z_0}.
}
\]

若观测矩受到扰动

\[
(m_0,m_1)\mapsto(m_0+e_0,m_1+e_1),
\]

则第一振幅误差精确为

\[
\widehat a_0-a_0
=
\frac{z_1e_0-e_1}{z_1-z_0}.
\]

因此

\[
\boxed{
\lVert\widehat a_0-a_0\rVert
\le
\frac{
\lVert z_1\rVert\lVert e_0\rVert+
\lVert e_1\rVert
}{
\lVert z_1-z_0\rVert
}.
}
\]

这给出本批最重要的分离：

\[
\boxed{
\text{exact kernel}=0
\quad\not\Longrightarrow\quad
\text{uniformly stable reconstruction}.
}
\]

节点只要不同，代数反演就存在。节点间距很小时，逆映射仍会放大噪声。

对一般 `n`，对应稳定性由 Vandermonde 矩阵的最小奇异值、逆矩阵范数或节点分离几何控制。本批没有声明一般 `n` 的统一 conditioning bound。

---

## 4. 局部 Euler 截断的精确残差

令局部变量为

\[
x\in\mathbb C.
\]

有限局部 Euler 因子定义为

\[
S_N(x)=\sum_{m=0}^{N-1}x^m.
\]

它满足精确恒等式

\[
\boxed{
(1-x)S_N(x)=1-x^N.
}
\]

因此有限层与无限完成之间的真实残差是

\[
R_N(x)=x^N.
\]

若

\[
\lVert x\rVert<1,
\]

则

\[
R_N(x)\longrightarrow0,
\]

并得到

\[
(1-x)S_N(x)\longrightarrow1,
\]

以及

\[
\boxed{
S_N(x)\longrightarrow(1-x)^{-1}.
}
\]

该命题只在单个局部位置成立。要把它提升为全局 Euler 乘积，需要额外证明：

1. 每个素数处局部变量进入统一可控的单位圆；
2. 局部 residual 具有跨素数可求和 majorant；
3. 极限与素数积或素数和可以交换；
4. 零点与极点抵消被排除；
5. 所选字符、电荷和观察 gauge 在极限中兼容。

局部尾项消失不等于全局尾项消失。

---

## 5. 三种忠实性必须联合

完整的有限 charged prime tomography 至少需要三个条件。

### 5.1 电荷忠实性

若字符族为 `Σ`，则共同不可见电荷为

\[
K_{\mathrm{charge}}
=
\bigcap_{\chi\in\Sigma}\ker\chi.
\]

需要

\[
K_{\mathrm{charge}}=\{e\}.
\]

### 5.2 相位忠实性

若有限相位节点为 `z_j`，则需要

\[
z_i\ne z_j
\qquad(i\ne j).
\]

在该条件下，有限 Vandermonde 读出没有振幅 kernel。

### 5.3 完成忠实性

有限 Euler 层仍携带 residual：

\[
R_N(x)=x^N.
\]

要得到无限完成，必须证明该 residual 在正确的全局拓扑中消失。

因此，完整观察缺陷可以组织成

\[
\boxed{
\mathfrak D
=
\left(
K_{\mathrm{charge}},
K_{\mathrm{phase}},
R_{\mathrm{completion}}
\right).
}
\]

任意一个分量没有关闭，完整素数状态都不能由压缩后的解析通道稳定恢复。

---

## 6. 黄金比例在本批中的严格职责

本批没有声称黄金比例单独生成 RH 证明。它承担两个经过机器检查的角色。

第一，黄金单位 `φ²` 给出壳平移。正次幂保持无理，因此非零有理尺度不能在正黄金壳上发生精确碰撞。

第二，黄金尺度将正有理素数幂映入相位节点。若进一步把 universal-cover 刚性提升到圆商上的完整节点分离，有限 Vandermonde 定理将自动给出有限素数包的精确层析。

所以当前严格链条是

\[
\boxed{
\text{黄金壳有理刚性}
\longrightarrow
\text{有限节点分离目标}
\longrightarrow
\text{Vandermonde 忠实层析}.
}
\]

缺少的桥是完整的商圆相位分离 theorem，以及相位间距的 quantitative bound。

---

## 7. 与 RH 路线的边界

本批已经证明有限层析的代数端点和单局部 Euler 尾项的解析端点。它没有构造算术事件到零点谱事件的原子映射。

后续需要的承重桥仍然是

\[
\boxed{
\text{charged prime packet}
\xrightarrow{\ \mathcal B\ }
\text{zero-side spectral packet},
}
\]

并要求 `𝓑` 具有：

1. 线性或受控非线性；
2. 反射兼容性；
3. 正性或酉性来源；
4. 截断误差的一致控制；
5. 测试空间完备性。

只有在这些义务闭合后，有限正缺陷能量才可能被提升为全局临界线结论。

本文不声称：

- 黄金相位像具有统一分离；
- 任意有限窗口都具有良好 condition number；
- 局部 Euler 尾项估计可以直接相乘到全部素数；
- 当前定理给出显式公式；
- 当前定理推出 RH 或 GRH。

---

## 8. 本批机器 owner

```text
D5/S3/Observer/GoldenCoding/
  GoldenRationalShellRigidity.lean

D5/S3/Analytic/GoldenTomography/
  FiniteVandermondeTomography.lean
  TwoNodeTomographyConditioning.lean

D5/S3/PrimeForms/GoldenEuler/
  LocalEulerTailVanishing.lean
```

每个 owner 配备同 GID 的 Scribe 真源和生成 Markdown 投影。

---

## 9. 下一真源顺序

本批之后最自然的顺序为：

```text
GoldenRationalPhaseQuotientInjectivity
GoldenPrimePowerPhaseSeparation
FiniteGoldenPhaseVandermondeTomography
FiniteVandermondeMinimumSeparationConditioning
GlobalPrimeTailDominatedCompletion
FiniteExplicitFormulaPacketIntertwiner
```

其中前两项关闭商圆相位分离。第三项将黄金节点与一般 Vandermonde theorem 合成。第四项开始处理有限精度稳定性。第五项处理从单局部尾项到全局素数尾项的交换极限。第六项才进入真正的算术到谱运输。
