# 指数 Taylor 余项比的所有高偶数阶负值存在定理

## 1. 余项、差分与量词

**定义 1.1（余项与正向差分）。** 对整数 $j\ge0$ 和实数 $x>0$，定义

$$
R_j(x)=e^x-\sum_{\ell=0}^{j}\frac{x^\ell}{\ell!}.
$$

对整数 $n\ge1$ 定义 $g_n(x)=R_{n-1}(x)/R_n(x)$。分母的严格正性将在定理 2.1 的证明中给出。差分始终作用于指标 $n$，步长为正一：

$$
\begin{aligned}
\Delta g_n(x)&=g_{n+1}(x)-g_n(x),\\
\Delta^k g_n(x)&=\sum_{a=0}^{k}(-1)^{k-a}\binom{k}{a}g_{n+a}(x)
\qquad(k\in\mathbb Z_{\ge0}).
\end{aligned}
$$

这一记号对应 S. M. Sitnik，*Неравенства для остатка ряда Тейлора экспоненты*，固定版本 [arXiv:1608.08784v2](https://arxiv.org/html/1608.08784v2)，公式 (1) 与附录「Дополнение」的 Problem 11（PDF 第 27–28 页）。原问题询问哪些阶数的差分对所有正参数保持正性；以下定理专门处理每个偶数阶 $k\ge4$ 的负值存在性。

## 2. 所有高偶数阶的有限负值

**定理 2.1（所有偶数阶 $2m\ge4$ 均有负值）。** 对定义 1.1 的余项比，有

$$
\forall m\in\mathbb Z_{\ge2}\quad
\exists n\in\mathbb Z_{\ge1}\quad
\exists x\in(0,\infty)\quad
\sum_{a=0}^{2m}(-1)^{2m-a}\binom{2m}{a}g_{n+a}(x)<0.
$$

更具体地，对每个这样的 $m$，存在实数 $s_m$ 和有限整数 $N_m\ge1$，使得对每个整数 $N\ge N_m$，

$$
x=N,\qquad n=\left\lfloor N+s_m\sqrt N\right\rfloor\ge1
$$

都满足 $\Delta^{2m}g_n(x)<0$。这里 $s_m,N_m,n,x$ 均允许依赖于 $m$，阶数没有上限。

证明。固定任意整数 $m\ge2$，记 $k=2m$。下列积分、导数与极限均为实变量意义。

**第一步：精确积分与分母正性。** 对整数 $j\ge0$ 和 $x>0$，有 Taylor 积分余项公式

$$
R_j(x)=\frac{x^{j+1}}{j!}\int_0^1 e^{xt}(1-t)^j\,dt>0. \tag{2.1}
$$

为核对归一化，作代换 $u=x(1-t)$，右侧变为

$$
E_j(x)=\frac{e^x}{j!}\int_0^x e^{-u}u^j\,du.
$$

直接积分给出 $E_0(x)=e^x-1$；当 $j\ge1$ 时，分部积分给出

$$
\int_0^x e^{-u}u^j\,du
=-e^{-x}x^j+j\int_0^x e^{-u}u^{j-1}\,du,
\qquad E_j(x)=E_{j-1}(x)-\frac{x^j}{j!}.
$$

归纳即得 (2.1) 的有限和表达式。积分被积函数在 $0<t<1$ 上严格为正，故每个 $R_j(x)$ 严格为正。由 $R_{n-1}(x)=R_n(x)+x^n/n!$，得到精确恒等式

$$
g_n(x)=1+\frac{1}{x\displaystyle\int_0^1 e^{xt}(1-t)^n\,dt}
\qquad(n\ge1, x>0). \tag{2.2}
$$

**第二步：实参数积分及精确过渡缩放。** 对 $X>0$ 和实数 $\alpha>-1$，定义

$$
Q_X(\alpha)=\int_0^1 e^{Xt}(1-t)^\alpha\,dt,
$$

其中在 $0\le t<1$ 上以 $\exp(\alpha\log(1-t))$ 定义实幂，在 $t=1$ 处取广义积分。因 $1\le e^{Xt}\le e^X$，这个积分有限且严格为正；当 $\alpha\le-1$ 时，它发散。因此 $\alpha>-1$ 是它的准确实参数定义域。

令

$$
\psi(z)=e^{-z}-1+z\quad(z\ge0),\qquad
D_X=\left(-\sqrt X-\frac1{\sqrt X},\infty\right).
$$

对 $s\in D_X$ 定义

$$
\begin{aligned}
I_X(s)&=\int_0^\infty
\exp\left[-X\psi\!\left(\frac v{\sqrt X}\right)
-\left(s+\frac1{\sqrt X}\right)v\right]\,dv,\\
H_X(s)&=\frac1{I_X(s)}.
\end{aligned} \tag{2.3}
$$

代换 $t=1-e^{-v/\sqrt X}$，其 Jacobian 为
$dt=X^{-1/2}e^{-v/\sqrt X}\,dv$，给出

$$
I_X(s)=\sqrt X\,Q_X(X+s\sqrt X). \tag{2.4}
$$

条件 $s\in D_X$ 恰为 $X+s\sqrt X>-1$。也可直接从 (2.3) 的指数写成

$$
X-Xe^{-v/\sqrt X}-\left(\sqrt X+s+\frac1{\sqrt X}\right)v
$$

看出相同的收敛条件。在其定义域上 $I_X(s)>0$。对于整数 $n\ge1$，取 $s=(n-X)/\sqrt X$，由 (2.2)–(2.4) 得

$$
g_n(X)=1+X^{-1/2}H_X\!\left(\frac{n-X}{\sqrt X}\right). \tag{2.5}
$$

定义极限积分及轮廓

$$
I(s)=\int_0^\infty e^{-v^2/2-sv}\,dv,
\qquad H(s)=\frac1{I(s)},\qquad s\in\mathbb R. \tag{2.6}
$$

二次项保证 $I(s)$ 对每个实数 $s$ 都有限且严格为正。

**第三步：任意固定阶导数的局部一致收敛。** 将证明：对每个非负整数 $r$ 和每个紧区间 $K\subset\mathbb R$，$K\subset D_X$ 对充分大的 $X$ 成立，并且

$$
\max_{0\le j\le r}\ \sup_{s\in K}
\left|H_X^{(j)}(s)-H^{(j)}(s)\right|\longrightarrow0
\qquad(X\to\infty). \tag{2.7}
$$

取 $c=1/(2e)$。对所有 $z\ge0$，

$$
\psi(z)\ge c\min(z^2,z). \tag{2.8}
$$

事实上，当 $0\le z\le1$ 时，

$$
\psi(z)=\int_0^z(z-t)e^{-t}\,dt\ge\frac{z^2}{2e}.
$$

当 $z\ge1$ 时，$\psi(1)=1/e$，而

$$
\frac{d}{dz}\left(\psi(z)-\frac ze\right)
=1-e^{-z}-\frac1e\ge1-\frac2e>0.
$$

所以 $\psi(z)\ge z/e$，从而得到 (2.8)。

给定 $M\ge0$，取实数 $L\ge1$ 使 $c\sqrt L\ge M+1$。对 $X\ge L$、$|s|\le M$ 和每个非负整数 $j$，(2.3) 中被积函数的第 $j$ 阶 $s$ 导数绝对值不超过

$$
D_{j,M,L}(v)=v^j\exp\left[Mv-c\min(v^2,\sqrt L\,v)\right]. \tag{2.9}
$$

这里使用了 $X\psi(v/\sqrt X)\ge c\min(v^2,\sqrt X\,v)$ 以及额外因子 $e^{-v/\sqrt X}\le1$。当 $v\ge\sqrt L$ 时，(2.9) 不超过 $v^je^{-v}$；在 $[0,\sqrt L]$ 上它可积。因此它是与 $X,s$ 无关的可积控制函数。上述 $L$ 还保证 $[-M,M]\subset D_X$。在稍大的紧区间上作同样估计，逐次应用积分下求导定理，得到所有需要的导数，且

$$
I_X^{(j)}(s)=\int_0^\infty(-v)^j
\exp\left[-X\psi\!\left(\frac v{\sqrt X}\right)
-\left(s+\frac1{\sqrt X}\right)v\right]\,dv. \tag{2.10}
$$

在 $z=0$ 处展开指数函数，有 $\psi(z)=z^2/2+O(z^3)$；所以对每个固定 $v\ge0$，

$$
X\psi(v/\sqrt X)\longrightarrow v^2/2.
$$

于是 (2.10) 的被积函数对 $|s|\le M$ 一致趋向 $(-v)^je^{-v^2/2-sv}$。极限被积函数也受 (2.9) 控制。把两者之差对 $|s|\le M$ 的上确界置于积分中，以 $2D_{j,M,L}$ 控制并应用支配收敛定理，便得

$$
\sup_{|s|\le M}|I_X^{(j)}(s)-I^{(j)}(s)|\longrightarrow0. \tag{2.11}
$$

同样的积分控制证明 $I\in C^\infty(\mathbb R)$。由于 $I>0$ 且连续，它在每个紧区间上的最小值严格为正；由 (2.11)，$I_X$ 在该区间上对充分大的 $X$ 也有统一正下界。反复对倒数求导时，只出现各阶 $I_X$ 导数的有限乘积与正整数次分母 $I_X$。因此 (2.11) 逐阶给出 (2.7)。这一步建立的是每个固定有限阶的导数收敛，而不只是函数值的收敛。

**第四步：轮廓的两端导数衰减及已知供给。** 对每个整数 $r\ge2$，将证明

$$
\lim_{s\to-\infty}H^{(r)}(s)
=\lim_{s\to+\infty}H^{(r)}(s)=0. \tag{2.12}
$$

配方并作平移，令

$$
J(s)=\int_s^\infty e^{-t^2/2}\,dt,
\qquad I(s)=e^{s^2/2}J(s),
\qquad H(s)=\frac{e^{-s^2/2}}{J(s)}. \tag{2.13}
$$

若 $\varphi(s)=(2\pi)^{-1/2}e^{-s^2/2}$、$\Psi(s)=\int_s^\infty\varphi(t)\,dt$，则 $H=\varphi/\Psi$，正是标准高斯分布的逆 Mills 比。这个轮廓及其导数估计属于已知数学。Iosif Pinelis，*Exact bounds on the inverse Mills ratio and its derivatives*，[arXiv:1512.00120v1](https://arxiv.org/html/1512.00120v1)，§1 的定义、Theorem 1.1、Corollaries 1.5–1.6，特别是 Corollary 1.6 的公式 (1.8)，在实轴 $s>0$ 给出

$$
|H^{(r)}(s)|\le\frac{r!}{s^r}
\sqrt{\left(s+\sqrt{2/\pi}\right)^2+s^2}. \tag{2.14}
$$

对每个固定 $r\ge2$，右侧趋于零，已足以提供 (2.12) 的正尾部分；期刊版本见 [DOI:10.1007/s11785-018-0765-x](https://doi.org/10.1007/s11785-018-0765-x)。下面给出自足的初等推导，其中正尾部分还得到 $O(s^{-r-1})$ 的界；这些高斯轮廓事实本身不作为新的承重结论。

先考虑 $s\le0$。此时

$$
0<J(0)\le J(s)\le\int_{-\infty}^{\infty}e^{-t^2/2}\,dt<\infty.
$$

由 $J'(s)=-e^{-s^2/2}$，每个正阶导数 $J^{(q)}(s)$ 都是一个多项式乘 $e^{-s^2/2}$；因而在 $(-\infty,0]$ 上有界，并在负无穷处趋于零。倒数 $1/J$ 的任意正阶导数都是这些 $J^{(q)}$ 的有限乘积除以 $J$ 的正整数次幂的有限和，所以也有界。另一方面，$e^{-s^2/2}$ 的各阶导数都是趋于零的多项式乘高斯函数。对 (2.13) 使用乘积求导公式，即得

$$
H^{(r)}(s)\longrightarrow0\quad(s\to-\infty)
\qquad\text{对所有整数 }r\ge0. \tag{2.15}
$$

对正尾，定义实参数积分

$$
A(t)=\int_0^\infty e^{-w}e^{-t^2w^2/2}\,dw,
\qquad t\in\mathbb R.
$$

它对所有实数 $t$ 都有限且严格为正。其第 $j$ 阶被积函数导数为

$$
e^{-w}w^jP_j(tw)e^{-(tw)^2/2},
$$

其中 $P_j$ 是多项式。由于多项式乘高斯函数在整条实轴上有界，其绝对值至多为 $C_je^{-w}w^j$，后者在 $[0,\infty)$ 可积。积分下逐阶求导于是证明 $A\in C^\infty(\mathbb R)$，且 $A$ 为偶函数、$A(0)=1$。因此在零点附近 $B=1/A$ 光滑且为偶函数，$B(0)=1$、$B'(0)=0$。Taylor 积分公式给出

$$
B(t)=1+t^2C(t),\qquad
C(t)=\int_0^1(1-u)B''(ut)\,du, \tag{2.16}
$$

其中 $C$ 在零点附近光滑。对 $s>0$，在 (2.6) 中代换 $w=sv$，得到

$$
I(s)=\frac1s A(1/s),\qquad
H(s)=sB(1/s)=s+s^{-1}C(1/s) \tag{2.17}
$$

（最后一个等式用于充分大的 $s$）。对 $s^{-1}C(1/s)$ 作 $r$ 次求导，归纳可知每一项都形如

$$
c_{r,j}s^{-(r+1+j)}C^{(j)}(1/s),\qquad0\le j\le r,
$$

其中 $c_{r,j}$ 为常数：对已有一项求导，分别产生同一 $j$ 和 $j+1$ 的两种项，其幂次正好具有上述形式。每个 $C^{(j)}$ 在零点附近有界，所以整个导数为 $O(s^{-r-1})$，常数允许依赖于 $r$。当 $r\ge2$ 时，(2.17) 中线性项 $s$ 的第 $r$ 阶导数为零，故

$$
H^{(r)}(s)=O(s^{-r-1})\longrightarrow0
\qquad(s\to+\infty, r\ge2). \tag{2.18}
$$

这证明 (2.12)，并且没有对未经控制的渐近误差项求导。

**第五步：每个所需阶数都有严格负导数。** 对当前固定的 $k=2m\ge4$，必存在 $s_m\in\mathbb R$ 使

$$
H^{(k)}(s_m)<0. \tag{2.19}
$$

若不然，则 $H^{(k)}(s)\ge0$ 对所有实数 $s$ 成立，故 $H^{(k-1)}$ 在实轴上非减。由于 $k-1\ge3$，(2.12) 说明它在正、负无穷处的极限都为零。对任意 $s$，非减性于是给出 $0\le H^{(k-1)}(s)\le0$。从而 $H^{(k-1)}\equiv0$，逐次积分可知 $H$ 是次数至多 $k-2$ 的多项式。由 (2.15)，这个多项式在负无穷处趋于零，所以只能恒为零。这与 (2.6) 中 $H(s)>0$ 矛盾，证明 (2.19)。

**第六步：从严格负导数传到有限整数指标。** 对正整数 $N$ 定义

$$
n_N=\left\lfloor N+s_m\sqrt N\right\rfloor,
\qquad h_N=N^{-1/2},\qquad
s_N=\frac{n_N-N}{\sqrt N}.
$$

取整误差满足

$$
s_m-h_N<s_N\le s_m,
$$

故 $s_N\to s_m$。而 $N+s_m\sqrt N\to\infty$，所以对充分大的 $N$，有 $n_N\ge1$。对每个 $a\in\{0,\ldots,k\}$，公式 (2.5) 给出

$$
g_{n_N+a}(N)=1+N^{-1/2}H_N(s_N+ah_N). \tag{2.20}
$$

现在详细核对差分的归一化。对任意 $h>0$、实数 $y$ 以及在 $[y,y+kh]$ 的邻域上属于 $C^k$ 的实函数 $F$，微积分基本定理反复给出

$$
h^{-k}\sum_{a=0}^k(-1)^{k-a}\binom{k}{a}F(y+ah)
=\int_{[0,1]^k}F^{(k)}\bigl(y+h(u_1+\cdots+u_k)\bigr)\,du_1\cdots du_k. \tag{2.21}
$$

确实，一次差分为 $F(y+h)-F(y)=h\int_0^1F'(y+hu)\,du$。对这个公式的两端再施加 $y\mapsto y+h$ 的差分，可把一次导数换成二次导数，并引入第二个 $h$ 和第二个积分变量。如此迭代 $k$ 次；连续性保证有限立方体上的积分可交换，二项式展开给出左侧的系数。这也核对了 (2.21) 与定义 1.1 的正向差分符号完全一致。

因为 $k\ge1$，常数序列的第 $k$ 阶差分为零。将 (2.20) 代入定义 1.1，并在 (2.21) 中取 $F=H_N$、$y=s_N$、$h=h_N$，得到

$$
\begin{aligned}
N^{(k+1)/2}\Delta^k g_{n_N}(N)
&=h_N^{-k}\sum_{a=0}^k(-1)^{k-a}\binom{k}{a}H_N(s_N+ah_N)\\
&=\int_{[0,1]^k}H_N^{(k)}\bigl(s_N+h_N(u_1+\cdots+u_k)\bigr)\,du_1\cdots du_k.
\end{aligned} \tag{2.22}
$$

这些积分点与 $s_m$ 的距离至多 $(k+1)h_N$，故一致趋于 $s_m$；对充分大的 $N$，它们全在固定紧区间 $K=[s_m-1,s_m+1]$ 中。第三步保证此时 $H_N$ 在该区间光滑，且 $H_N^{(k)}\to H^{(k)}$ 一致。更明确地，记这些积分点为 $z_N(u)$，则

$$
\begin{aligned}
\sup_{u\in[0,1]^k}|H_N^{(k)}(z_N(u))-H^{(k)}(s_m)|
&\le\sup_{s\in K}|H_N^{(k)}(s)-H^{(k)}(s)|\\
&\quad+\sup_{\substack{s\in K\\|s-s_m|\le(k+1)h_N}}
|H^{(k)}(s)-H^{(k)}(s_m)|\longrightarrow0.
\end{aligned}
$$

第一项由 (2.7) 趋零，第二项由连续性趋零。因单位立方体体积为一，(2.22) 因此给出严格的极限

$$
N^{(k+1)/2}\Delta^k g_{n_N}(N)
\longrightarrow H^{(k)}(s_m)<0. \tag{2.23}
$$

令 $\eta=-H^{(k)}(s_m)>0$。收敛的定义保证存在有限整数 $N_m$，使每个整数 $N\ge N_m$ 同时满足 $n_N\ge1$、上述定义域条件，以及 (2.23) 左侧与极限之差小于 $\eta/2$。于是

$$
N^{(k+1)/2}\Delta^k g_{n_N}(N)<-\eta/2<0.
$$

缩放因子严格为正，故 $\Delta^k g_{n_N}(N)<0$。任选一个这样的有限整数 $N$，便得到 $x=N>0$ 和整数 $n=n_N\ge1$；所有分母均由 (2.1) 严格为正。由于开头的 $m\ge2$ 任意，这就证明了整个无上限偶数阶族及定理中的更具体结论。证毕。

## 3. 数学来源与结论范围

**约定 3.1（文献对应与适用范围）。** 定理 2.1 使用的高斯逆 Mills 轮廓及足够的正尾导数衰减由 Pinelis 的上述文献提供；第四步另给初等证明，因而无需借助所引导数界即可完成论证。Taylor 积分余项、积分下求导、支配收敛与微积分基本定理均作为标准分析工具使用。承接这些工具的具体关系是 (2.5)、任意固定阶的 (2.7)，以及通向真实整数指标的 (2.22)–(2.23)。

与本问题直接对应的既有余项材料为 [*Exponential remainder ratio differences*，来源说明](https://github.com/the-omega-institute/trureturing/blob/c80da44d07586b86ce3c1cb3af14ec2933183dd4/Library/Asymptotics/sitnik1993expremainder.md) 的「Verified locator」「Mathematical correspondence」，及 [余项差分专题](https://github.com/the-omega-institute/trureturing/blob/c80da44d07586b86ce3c1cb3af14ec2933183dd4/Problems/sitnik-1993-exponential-remainder-differences.md) 的「Gap」「Triage」。它们给出奇数阶 $k\ge3$ 对每个固定 $n$ 的小正参数负性，以及偶数阶对固定 $n$ 的小正参数正性；这些结论在此作为既有结果引用。定理 2.1 增加的是所有偶数阶 $k\ge4$ 的负值存在结论及其完整推导，不以有限阶样本代替无界量词，也不将这些奇数阶或小参数结果作为新增内容。

一阶来源为 Sitnik 同一固定版本的 Theorem 8、公式 (42)。二阶的文献对应见上述来源说明，以及 K. Mehrez and S. M. Sitnik，*Proofs of some conjectures on monotonicity of ratios of Kummer, Gauss and generalized hypergeometric functions*，[arXiv:1410.6120v1](https://arxiv.org/html/1410.6120v1)，引言中的指数余项问题与 Theorem 1。该文关于 $x$ 单调性的比值使用了不同的函数记号；其记号 $g_n$ 不应与定义 1.1 混同。本文不把一、二阶结果或逆 Mills 估计归为新的数学结论，也不主张全局首证优先权。

定理 2.1 的量词允许每个 $m$ 使用不同的 $s_m$ 与阈值 $N_m$。它给出的是每阶在有限正参数和有限整数指标处的严格负值；它不要求固定同一个 $n$ 适用于所有阶数，不给出关于 $m$ 的统一阈值或数值阈值，也不分类各阶全部正负区域。小参数正性与本定理相容，因为本定理的见证沿 $n=N+O(\sqrt N)$、$x=N$ 取得。

## 追加锚（本行以下为增补区）
