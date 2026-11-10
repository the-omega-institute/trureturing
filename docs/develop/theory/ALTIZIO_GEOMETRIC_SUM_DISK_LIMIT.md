# Altizio 几何和圆盘上的最小值极限

## 1. 原问题与记号

对正整数 $n$，定义字面有限和

$$
G_n(z):=\sum_{k=0}^{n-1}z^k\qquad(z\in\mathbb C),
$$

并令

$$
B:=\{z\in\mathbb C:|z-2|\le1\},\qquad
f_n(z):=\left|\frac{G_n(z)}z\right|\quad(z\in B).
$$

这里 $G_n(1)=n$ 是有限和的字面值，分子和分母取同一个点 $z$。David Altizio 的 [*Zeros of Stern polynomials in the complex plane*, arXiv:2511.03847v1](https://arxiv.org/abs/2511.03847v1) 第 2 节用 $(z)_n$ 表示这一有限和，第 3 节定义同一闭圆盘 $B=B_1[2]$。第 4.3 节第 20 页 Remark 4 提出 $\min_{z\in B}|(z)_n/z|$ 趋于 $2\pi$ 的问题。下文在这些定义下证明最小值的存在性、正性及该极限。

## 2. 闭圆盘上的最小值与边界化

**命题 2.1（最小值存在且为正）。** 对每个正整数 $n$，$f_n$ 在 $B$ 上取得最小值

$$
m_n:=\min_{z\in B}f_n(z)>0.
$$

**证明。** 对 $z\in B$，三角不等式给出

$$
|z|\ge2-|z-2|\ge1,
$$

所以分母 $z$ 非零。[仓库原始文件 `D5/S3/Zeros/AltizioGeometricSumDisk.lean`](https://github.com/the-omega-institute/trureturing/blob/94320eff5bf64464f555bac12a48fa5a1c135ab1/D5/S3/Zeros/AltizioGeometricSumDisk.lean) 的私有 `unit_intersection` 在全部假设 $|z-2|\le1$、$|z|=1$ 下给出 $z=1$；同文件的私有 `G_ne_zero` 在全部假设 $n>0$、$|z-2|\le1$ 下给出 $G_n(z)\ne0$。其私有定义 `G` 正是本卷的字面有限和，非零性证明使用上述单位圆交点及有限几何和恒等式 `geom_sum_mul`。于是 $f_n$ 在非空紧集 $B$ 上连续且处处严格为正。连续极值定理给出取得最小值的点，该点的函数值严格为正。∎

**命题 2.2（全圆盘最小值的边界表示）。** 令

$$
H_n(z):=\frac z{G_n(z)}\quad(z\in B),\qquad
M_n:=\max_{z\in\partial B}|H_n(z)|.
$$

则 $M_n>0$，并且

$$
m_n=\frac1{\displaystyle\max_{z\in B}|H_n(z)|}=\frac1{M_n}.
$$

**证明。** 命题 2.1 中的非零性使 $H_n$ 在 $B$ 上连续、在其内部全纯，且 $H_n(z)\ne0$。最大模原理给出

$$
\max_{z\in B}|H_n(z)|=\max_{z\in\partial B}|H_n(z)|>0.
$$

又 $f_n(z)=1/|H_n(z)|$，故取得上式最大值的点也取得 $f_n$ 的最小值，并给出所述倒数关系。

这一倒数最大模方法也见于 Altizio 第 4.3 节 Proposition 8 的 $n=5,6$ 证明，以及上述仓库文件的私有 `disk_bound`。后者的次数假设为 $n\in\{5,6,7\}$，同文件的 `result` 分类 $n|z|\le|G_n(z)|$ 在整个 $B$ 上成立的次数恰为这三个值。本命题对全部正整数所需的非零性来自命题 2.1 所引 `G_ne_zero` 的完整范围。∎

## 3. 边界参数与局部相位

取边界参数

$$
z(\theta):=2-e^{-i\theta},\qquad-\pi\le\theta\le\pi.
$$

它遍历整个 $\partial B$，且 $z(-\theta)=\overline{z(\theta)}$。有限和 $G_n$ 的系数为实数，因而 $|H_n(z(-\theta))|=|H_n(z(\theta))|$。所以

$$
M_n=\max_{0\le\theta\le\pi}Q_n(\theta),\qquad
Q_n(\theta):=|H_n(z(\theta))|.
$$

对 $0\le\theta\le\pi$，记

$$
d(\theta):=|z(\theta)-1|=2\sin\frac\theta2,\qquad
r(\theta):=|z(\theta)|.
$$

直接计算得到

$$
r(\theta)^2=5-4\cos\theta=1+2d(\theta)^2. \tag{3.1}
$$

在此区间上 $d$、$r$ 递增，$0\le d\le2$、$1\le r\le3$。由于 $\operatorname{Re}z(\theta)=2-\cos\theta\ge1$，可定义

$$
\beta(\theta):=\arctan\frac{\sin\theta}{2-\cos\theta}\in[0,\pi/2),\qquad
z(\theta)=r(\theta)e^{i\beta(\theta)}.
$$

由标准初等函数极限，

$$
\frac{d(\theta)}\theta\longrightarrow1,\qquad
\frac{\beta(\theta)}\theta\longrightarrow1,\qquad
\frac{\log r(\theta)}{\theta^2}\longrightarrow1
\quad(\theta\downarrow0). \tag{3.2}
$$

其中第二个极限由 $\arctan u/u\to1$、$\sin\theta/\theta\to1$ 及 $2-\cos\theta\to1$ 得到；第三个由 (3.1) 写成

$$
\frac{\log r(\theta)}{\theta^2}
=\frac{d(\theta)^2}{\theta^2}\,
  \frac{\log(1+2d(\theta)^2)}{2d(\theta)^2}\longrightarrow1.
$$

固定 $0<\theta_0<\pi/3$。微分给出

$$
\beta'(\theta)=\frac{2\cos\theta-1}{5-4\cos\theta}>0
\qquad(0\le\theta\le\theta_0). \tag{3.3}
$$

对 $0<\theta\le\pi$，有 $z(\theta)\ne1$，故有限几何和恒等式 $G_n(z)(z-1)=z^n-1$ 给出

$$
Q_n(\theta)=\frac{r(\theta)}{|G_n(z(\theta))|}
=\frac{r(\theta)d(\theta)}{|z(\theta)^n-1|}. \tag{3.4}
$$

在端点 $\theta=0$，使用字面值 $G_n(1)=n$，得到

$$
Q_n(0)=\frac1n. \tag{3.5}
$$

## 4. 边界最大值的上极限

**引理 4.1（远离切点）。** 对上述固定的 $\theta_0$，

$$
\sup_{\theta_0\le\theta\le\pi}Q_n(\theta)\longrightarrow0.
$$

**证明。** 由 (3.1)，$r(\theta)\ge r(\theta_0)>1$。反三角不等式和 (3.4) 给出

$$
Q_n(\theta)\le\frac{r(\theta)d(\theta)}{r(\theta)^n-1}
\le\frac6{r(\theta_0)^n-1}\longrightarrow0.
$$

这是整个闭区间上的统一上界。∎

**命题 4.2（边界最大值的上极限）。** 有

$$
\limsup_{n\to\infty}M_n\le\frac1{2\pi}.
$$

**证明。** Altizio 第 4.3 节采用的点为

$$
w_{n,t}:=\overline{2-e^{it/n}}
=(2-\cos(t/n))+i\sin(t/n).
$$

对 $0<\theta\le\pi$ 取 $t=n\theta$，则 $0<t\le n\pi$，并且 $w_{n,t}=z(\theta)$。该节 Proposition 6 在 $n\ge4$、$t\ge0$ 的范围内陈述径向下界；在这里使用的 $0<t\le n\pi$ 上，其商的分母非零，原式及有限和的对应为

$$
|G_n(w_{n,t})|
=\left|\frac{w_{n,t}^{\,n}-1}{w_{n,t}-1}\right|
\ge2n\sin\frac{t}{2n}=n\,d(\theta).
$$

因此，对 $n\ge4$、$0<\theta\le\pi$，令 $x=n\,d(\theta)>0$，就有

$$
Q_n(\theta)=\frac{r(\theta)}{|G_n(z(\theta))|}
\le\frac{r(\theta)}x. \tag{4.1}
$$

固定 $0<\delta<2\pi$ 和 $C>2\pi-\delta$。将 $[0,\theta_0]$ 按 $x=n\,d(\theta)$ 分为

$$
0\le x\le2\pi-\delta,\qquad
2\pi-\delta\le x\le C,\qquad
x\ge C.
$$

在第一段，$d(\theta)\le(2\pi-\delta)/n$。由 $d$ 的严格递增性和 $d(0)=0$，该段的 $\theta$ 一致趋于零；再由 (3.2)，对所有充分大的 $n$，在该段的 $\theta>0$ 处一致有

$$
t=n\theta=x\frac{\theta}{d(\theta)}\le2\pi-\frac\delta2.
$$

Altizio 同节 Proposition 5 在 $n\ge1$、$t\ge0$ 的范围内陈述小相位下界。在这里的 $0<t\le n\pi$ 上，原式正是

$$
|G_n(w_{n,t})|
=\left|\frac{w_{n,t}^{\,n}-1}{w_{n,t}-1}\right|
\ge n\left(1-\frac{t}{2\pi}\right).
$$

故第一段的 $\theta>0$ 处，

$$
|G_n(z(\theta))|\ge\frac{n\delta}{4\pi},\qquad
Q_n(\theta)\le\frac{4\pi r(\theta)}{n\delta}
\le\frac{12\pi}{n\delta}\longrightarrow0.
$$

该段的 $\theta=0$ 处由 (3.5) 同样趋于零；不需要在 $w_{n,0}=1$ 处使用未约分的商。

在第二段，(4.1) 给出

$$
Q_n(\theta)\le\frac{r(\theta)}{2\pi-\delta}
\le\frac{\sqrt{1+2C^2/n^2}}{2\pi-\delta}.
$$

因此该段的上极限不超过 $(2\pi-\delta)^{-1}$。在第三段，(4.1) 和 $\theta\le\theta_0$ 给出 $Q_n(\theta)\le r(\theta_0)/C$。再结合引理 4.1 对 $[\theta_0,\pi]$ 的统一界，得到

$$
\limsup_{n\to\infty}M_n
\le\max\left\{\frac1{2\pi-\delta},\frac{r(\theta_0)}C\right\}.
$$

先令 $C\to\infty$，再令 $\delta\downarrow0$，即得结论。这里所有上极限均沿全部正整数取；估计从 $n\ge4$ 起成立足以决定该上极限。∎

## 5. 相位匹配与边界最大值的下极限

**引理 5.1（逐次数相位匹配）。** 存在正整数 $N$，使每个 $n\ge N$ 都有唯一的 $\theta_n\in(0,\theta_0)$ 满足

$$
\beta(\theta_n)=\frac{2\pi}{n}.
$$

并且

$$
\theta_n\longrightarrow0,\qquad
n\theta_n\longrightarrow2\pi,\qquad
n\,d(\theta_n)\longrightarrow2\pi. \tag{5.1}
$$

**证明。** 由 (3.3)，$\beta$ 在 $[0,\theta_0]$ 上连续且严格递增，$\beta(0)=0<\beta(\theta_0)$。取 $N$ 使 $2\pi/N<\beta(\theta_0)$，介值定理便对每个 $n\ge N$ 给出唯一的 $\theta_n$。对任意 $0<\varepsilon\le\theta_0$，充分大的 $n$ 满足 $2\pi/n<\beta(\varepsilon)$，所以 $\theta_n<\varepsilon$；这证明 $\theta_n\to0$。由 (3.2)，

$$
n\theta_n=2\pi\frac{\theta_n}{\beta(\theta_n)}\longrightarrow2\pi,
\qquad
n\,d(\theta_n)=n\theta_n\frac{d(\theta_n)}{\theta_n}\longrightarrow2\pi.
$$

∎

**命题 5.2（匹配点处的商极限）。** 对引理 5.1 的每个 $n\ge N$，令 $z_n=z(\theta_n)$。则

$$
\left|\frac{z_n}{G_n(z_n)}\right|\longrightarrow\frac1{2\pi}.
$$

**证明。** 记 $r_n=r(\theta_n)>1$。相位匹配给出 $z_n=r_ne^{2\pi i/n}$，故 $z_n^n=r_n^n$。由 (3.2) 及 (5.1)，

$$
n^2\log r_n
=(n\theta_n)^2\frac{\log r(\theta_n)}{\theta_n^2}
\longrightarrow4\pi^2. \tag{5.2}
$$

从而 $u_n:=n\log r_n>0$ 且 $u_n\to0$。利用标准极限 $(e^u-1)/u\to1$，得到

$$
n(r_n^n-1)
=n^2\log r_n\,\frac{e^{u_n}-1}{u_n}
\longrightarrow4\pi^2. \tag{5.3}
$$

又 $r_n\to1$，故由 (3.4)、(5.1) 和 (5.3)，

$$
\left|\frac{z_n}{G_n(z_n)}\right|
=\frac{r_n\,n\,d(\theta_n)}{n(r_n^n-1)}
\longrightarrow\frac{2\pi}{4\pi^2}=\frac1{2\pi}.
$$

∎

**推论 5.3。** 有

$$
\liminf_{n\to\infty}M_n\ge\frac1{2\pi}.
$$

**证明。** 每个 $n\ge N$ 的 $z_n$ 都在 $\partial B$ 上，所以 $M_n\ge|z_n/G_n(z_n)|$。命题 5.2 即给出沿全部正整数的下极限。∎

## 6. 主定理

**定理 6.1（全正整数的几何和圆盘极限）。** 对每个正整数 $n$，字面有限和 $G_n(z)=\sum_{k=0}^{n-1}z^k$ 在整个闭圆盘 $B=\{z\in\mathbb C:|z-2|\le1\}$ 上确定取得且严格为正的最小值

$$
m_n=\min_{z\in B}\left|\frac{G_n(z)}z\right|>0,
$$

并且沿全部正整数有

$$
\boxed{\displaystyle\lim_{n\to\infty}m_n=2\pi}.
$$

**证明。** 存在性和正性由命题 2.1 得到。命题 4.2 和推论 5.3 合起来给出 $M_n\to1/(2\pi)$。命题 2.2 对每个正整数给出 $m_n=1/M_n$ 且 $M_n>0$，所以由倒数函数在 $1/(2\pi)>0$ 处的连续性，$m_n\to2\pi$。边界表示是在整个 $B$ 上对同点商 $G_n(z)/z$ 所取最小值的精确等式，$z=1$ 处的值始终为 $G_n(1)/1=n$。∎

## 追加锚（本行以下为增补区）
