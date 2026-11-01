# Altizio 几何和圆盘上的最小值极限

## 1. 原问题与记号

对正整数 $n$，定义字面有限和

$$
G_n(z):=\sum_{k=0}^{n-1}z^k\qquad (z\in\mathbb C),
$$

并令

$$
B:=\{z\in\mathbb C:|z-2|\le 1\},
\qquad
m_n:=\min_{z\in B}\left|\frac{G_n(z)}{z}\right|.
$$

这里 $G_n(1)=n$ 是有限和的字面值；分母是同一个点 $z$。这是 David Altizio 在 *Zeros of Stern polynomials in the complex plane* 的 Section 2 对 $(z)_n$ 的约定和 Section 3 对 $B=B_1[2]$ 的约定。Section 4.3, Remark 4, p. 20 提出的未决断言正是

$$
\min_{z\in B}\left|\frac{(z)_n}{z}\right|\longrightarrow 2\pi .
$$

下文证明这个断言，并保持整个闭圆盘、其内部和边界以及 $z=1$。

仓库中 `D5.S3.Zeros.AltizioGeometricSumDisk.result` 及其 Blueprint、Library 公共载体已经在各自的实际范围内证明了另一条结果：对每个正整数 $n$，全闭圆盘上的不等式

$$
\forall z\in B,\qquad n|z|\le |G_n(z)|
$$

成立，当且仅当 $n\in\{5,6,7\}$。本卷只引用该分类及其原始来源对应，不把分类当作极限结论，也不重复分类证明。Remark 4 中另一个强下界和 Stern 零点的邻近问题不在本卷的结论内。

## 2. 闭圆盘上的基本性质

**引理 2.1（圆盘几何）。** 对 $z\in B$，有 $|z|\ge 1$；若 $|z|=1$，则 $z=1$。因而 $0\notin B$。

**证明。** 三角不等式给出

$$
|z|\ge 2-|z-2|\ge1.
$$

若 $|z|=1$，则

$$
|z-2|^2=|z|^2-4\operatorname{Re}z+4=5-4\operatorname{Re}z\le1,
$$

所以 $\operatorname{Re}z\ge1$。单位圆上这只可能是 $z=1$。反之 $1\in B$。∎

**引理 2.2（有限和没有圆盘内的零点）。** 对每个正整数 $n$，$G_n(z)\ne0$ 对所有 $z\in B$ 成立。

**证明。** 恒等式

$$
(z-1)G_n(z)=z^n-1
$$

在 $z=1$ 处由有限和直接成立，在其余处由等比数列公式成立。若 $G_n(z)=0$，则 $z^n=1$；于是 $|z|=1$，引理 2.1 给出 $z=1$，但 $G_n(1)=n>0$，矛盾。∎

**命题 2.3（最小值存在且为正）。** 对每个正整数 $n$，$m_n$ 存在并且 $m_n>0$。

**证明。** $B$ 是复平面中的紧集。由引理 2.1 和引理 2.2，函数

$$
f_n(z):=\left|\frac{G_n(z)}z\right|
$$

在 $B$ 上连续且处处严格为正。紧集上的连续函数取得最小值，且这个最小值严格为正。∎

**命题 2.4（边界化）。** 令

$$
H_n(z):=\frac z{G_n(z)}.
$$

则

$$
m_n=\frac1{\displaystyle\max_{z\in B}|H_n(z)|}
      =\frac1{\displaystyle\max_{z\in\partial B}|H_n(z)|}.
$$

**证明。** 引理 2.2 说明 $H_n$ 在 $B$ 上连续并在 $B$ 的内部全纯。最大模原理（先在一个略大的开邻域上取无零邻域，或直接使用闭圆盘版本）说明其最大模在 $\partial B$ 上取得。由于 $f_n=1/|H_n|$，正函数取最小值等于其倒数取最大值的倒数。∎

## 3. 边界参数与两个精确恒等式

边界可写成

$$
z(\theta):=2-e^{i\theta},\qquad -\pi\le\theta\le\pi.
$$

共轭对称性允许只取 $0\le\theta\le\pi$。记

$$
d(\theta):=|z(\theta)-1|=2\sin\frac\theta2,
\qquad
r(\theta):=|z(\theta)|.
$$

直接计算得

$$
r(\theta)^2=5-4\cos\theta=1+8\sin^2\frac\theta2=1+2d(\theta)^2. \tag{3.1}
$$

当 $0\le\theta\le\theta_0$ 且 $\theta_0>0$ 足够小时，$z(\theta)$ 位于右半平面。于是存在唯一的 $\beta(\theta)\in[0,\pi/2)$ 使

$$
z(\theta)=r(\theta)e^{-i\beta(\theta)}.
$$

由

$$
\tan\beta(\theta)=\frac{\sin\theta}{2-\cos\theta}
$$

以及 $d(\theta)=2\sin(\theta/2)$，有

$$
d(\theta)\sim\theta,
\qquad
\beta(\theta)\sim\theta,
\qquad
\frac{\log r(\theta)}{\theta^2}\longrightarrow1
\quad(\theta\downarrow0). \tag{3.2}
$$

最后一个极限来自 $r(\theta)^2=1+2\theta^2+O(\theta^4)$；前两个来自正弦的 Taylor 展开和上面的正切公式。缩小 $\theta_0$ 后还可固定为

$$
\frac12d(\theta)\le\beta(\theta)\le\theta
\qquad(0\le\theta\le\theta_0). \tag{3.3}
$$

对 $\theta>0$，引理 2.2 和等比数列恒等式给出

$$
Q_n(\theta):=|H_n(z(\theta))|
 =\frac{r(\theta)d(\theta)}{|z(\theta)^n-1|}. \tag{3.4}
$$

由 $z(\theta)=r(\theta)e^{-i\beta(\theta)}$，有精确分解

$$
|z(\theta)^n-1|^2
 =\bigl(r(\theta)^n-1\bigr)^2
   +4r(\theta)^n\sin^2\frac{n\beta(\theta)}2. \tag{3.5}
$$

在 $\theta=0$ 处，$z(0)=1$ 且

$$
Q_n(0)=\frac1n. \tag{3.6}
$$

## 4. 边界最大值的上极限

**引理 4.1（远离切点）。** 对任意固定的 $\theta_0>0$ 足够小，

$$
\sup_{\theta_0\le\theta\le\pi}Q_n(\theta)\longrightarrow0.
$$

**证明。** $d(\theta)$ 在 $[0,\pi]$ 上递增，所以由 (3.1)，$r(\theta)\ge r(\theta_0)>1$。同时 $r(\theta)\le3$、$d(\theta)\le2$。因此

$$
Q_n(\theta)
\le\frac{r(\theta)d(\theta)}{r(\theta)^n-1}
\le\frac6{r(\theta_0)^n-1},
$$

右端趋于零。∎

**引理 4.2（径向下界）。** 对 $n\ge2$ 和 $\theta>0$，令 $x=n\,d(\theta)$。则

$$
Q_n(\theta)\le\frac{r(\theta)}x. \tag{4.1}
$$

**证明。** 由 (3.1) 及指数为 $n/2\ge1$ 的 Bernoulli 不等式，

$$
r(\theta)^n=(1+2d(\theta)^2)^{n/2}\ge1+n\,d(\theta)^2.
$$

将 $|z^n-1|\ge r^n-1$ 代入 (3.4)，即得 (4.1)。∎

**引理 4.3（相位区间）。** 固定 $0<\delta<2\pi$。当 $n\to\infty$ 时，满足 $0\le n\,d(\theta)\le2\pi-\delta$ 且 $0\le\theta\le\theta_0$ 的点一致满足

$$
Q_n(\theta)\longrightarrow0. \tag{4.2}
$$

**证明。** 若 $n\,d(\theta)$ 有界，则 $\theta\to0$，并由 (3.2) 一致得到 $\beta(\theta)/d(\theta)\to1$。故当 $n$ 足够大时，

$$
0\le \frac{n\beta(\theta)}2\le\pi-\frac\delta4.
$$

函数 $u\mapsto\sin u/u$ 在 $[0,\pi-\delta/4]$ 上有正的最小值 $c_\delta$（在 $u=0$ 取连续值 $1$），从而

$$
\sin\frac{n\beta(\theta)}2
\ge c_\delta\frac{n\beta(\theta)}2.
$$

由 (3.5)、$r\ge1$ 和 (3.3)，

$$
Q_n(\theta)
\le\frac{d(\theta)}{2\sin(n\beta(\theta)/2)}
\le\frac{d(\theta)}{c_\delta n\beta(\theta)}
\le\frac2{c_\delta n}.
$$

在 $\theta=0$ 处使用 (3.6)。这证明了一致收敛。∎

**命题 4.4（边界商的上极限）。** 设

$$
M_n:=\max_{z\in\partial B}\left|\frac z{G_n(z)}\right|.
$$

则

$$
\limsup_{n\to\infty}M_n\le\frac1{2\pi}. \tag{4.3}
$$

**证明。** 取任意 $\delta\in(0,2\pi)$，再取任意 $C>2\pi-\delta$。将 $0\le\theta\le\theta_0$ 按 $x=n\,d(\theta)$ 分为三段：

$$
0\le x\le2\pi-\delta,
\qquad
2\pi-\delta\le x\le C,
\qquad
x\ge C.
$$

第一段由引理 4.3 的上界趋于零。第二段由引理 4.2 得

$$
Q_n(\theta)\le\frac{r(\theta)}{2\pi-\delta};
$$

该段中 $d(\theta)\le C/n$，故 $r(\theta)\to1$ 一致，第二段的上极限不超过 $(2\pi-\delta)^{-1}$。第三段由引理 4.2 得 $Q_n(\theta)\le r(\theta_0)/C$。最后，$\theta\ge\theta_0$ 的部分由引理 4.1 趋于零。因此

$$
\limsup_{n\to\infty}M_n
\le\max\left\{\frac1{2\pi-\delta},\frac{r(\theta_0)}C\right\}.
$$

先令 $C\to\infty$，再令 $\delta\downarrow0$，得到 (4.3)。∎

## 5. 达到相位 $2\pi$ 的边界序列

**引理 5.1（相位匹配）。** 存在正整数 $N$，使得每个 $n\ge N$ 都有唯一的 $\theta_n\in(0,\theta_0)$ 满足

$$
\beta(\theta_n)=\frac{2\pi}{n}.
$$

并且

$$
n\theta_n\longrightarrow2\pi,
\qquad
n\,d(\theta_n)\longrightarrow2\pi. \tag{5.1}
$$

**证明。** 函数 $\beta$ 在零点可微，且由 (3.2) 有 $\beta'(0)=1$。缩小 $\theta_0$ 后，$\beta'$ 在 $[0,\theta_0]$ 上为正，故 $\beta$ 严格递增。对充分大的 $n$，$2\pi/n<\beta(\theta_0)$，于是存在唯一的 $\theta_n$。再由 $\beta(\theta)/\theta\to1$ 得 $n\theta_n\to2\pi$，结合 $d(\theta)/\theta\to1$ 即得第二个极限。∎

**命题 5.2（边界商的下极限）。** 对上面取的 $\theta_n$，令 $z_n=z(\theta_n)$。则

$$
\left|\frac {z_n}{G_n(z_n)}\right|\longrightarrow\frac1{2\pi}.
$$

**证明。** 由相位匹配，$z_n=r_ne^{-2\pi i/n}$，所以 $z_n^n=r_n^n$，其中 $r_n=r(\theta_n)$。由 (3.2) 和 (5.1)，

$$
n^2\log r_n
 = (n\theta_n)^2\frac{\log r(\theta_n)}{\theta_n^2}
 \longrightarrow4\pi^2. \tag{5.2}
$$

特别地 $n\log r_n\to0$。因此

$$
n(r_n^n-1)
 =n\bigl(e^{n\log r_n}-1\bigr)
 =n^2\log r_n\,\frac{e^{n\log r_n}-1}{n\log r_n}
 \longrightarrow4\pi^2. \tag{5.3}
$$

又由 (3.4) 和 (5.1)，

$$
\left|\frac {z_n}{G_n(z_n)}\right|
 =\frac{r_n d(\theta_n)}{r_n^n-1}
 \longrightarrow\frac{2\pi}{4\pi^2}=\frac1{2\pi}.
$$

∎

**推论 5.3。** 有

$$
\liminf_{n\to\infty}M_n\ge\frac1{2\pi}. \tag{5.4}
$$

**证明。** $M_n$ 是边界上的最大值，而命题 5.2 给出一个边界点 $z_n$ 使对应商趋于 $1/(2\pi)$。∎

## 6. 主定理

**定理 6.1（全正整数的几何和圆盘极限）。** 对每个正整数 $n$，$m_n$ 存在且 $m_n>0$，并且

$$
\boxed{\displaystyle\lim_{n\to\infty}m_n=2\pi}.
$$

**证明。** 存在性和正性是命题 2.3。由命题 2.4，$m_n=1/M_n$。命题 4.4 给出

$$
\limsup M_n\le\frac1{2\pi},
$$

而推论 5.3 给出

$$
\liminf M_n\ge\frac1{2\pi}.
$$

故 $M_n\to1/(2\pi)$。由于所有 $M_n$ 都严格为正，取倒数得到 $m_n\to2\pi$。该极限沿所有正整数 $n$，没有抽取子序列，也没有删去圆盘边界或点 $z=1$。∎

## 7. 结论范围与来源对应

本卷的主定理只处理 Altizio Remark 4 中的完整极限和最小值存在性。它没有推出 Remark 3 的统一不等式 $|G_n(z)|\ge\min(n,2\pi)$，没有改变仓库中已经给出的 $n=5,6,7$ 分类，也没有涉及 Stern 多项式零点的半平面猜想、收敛速率、单调性或极小点分类。

来源对应如下：有限和的字面定义和 $z=1$ 的取值来自 Altizio Section 2；闭圆盘来自 Section 3；所证明的极限命题来自 Section 4.3, Remark 4；分类供应者是 `D5.S3.Zeros.AltizioGeometricSumDisk.result` 及其公共 Blueprint、Library 载体。所提供的完整文章原文把 $2\pi$ 极限记为数值证据下的未证明猜测；在所提供的五个完整仓库原文中，匹配的正式内容是分类而非该极限。因此本定理的证明独立补足的是极限内容，分类和文章中的其他命题仍保持其原有范围。

## 追加锚（本行以下为增补区）
