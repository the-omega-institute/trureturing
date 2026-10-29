# 齐次两层树的 Laplacian 转移：最优全域常数与一致衰减

## 1. 树、谱投影与转移概率

**定义 1.1（实际树及其动力学）。** 设 $k\ge2$、$\ell\ge1$ 为整数。树 $T(k,\ell)$ 的顶点集为

$$
V=\{r\}\sqcup\{h_i:1\le i\le k\}
\sqcup\{x_{ij}:1\le i\le k,\ 1\le j\le\ell\},
$$

边恰为 $rh_i$ 与 $h_ix_{ij}$。记

$$
n=|V|=1+k(\ell+1),\qquad L=D-A,\qquad U(t)=\exp(itL),\quad t\in\mathbb R,
$$

其中 $A$ 为 $V$ 上的邻接矩阵，$D$ 为度数对角矩阵。对实际 $n$ 阶矩阵 $L$ 的每个互异特征值 $\theta$，令 $E_\theta$ 为其完整特征空间上的正交投影。固定任意叶子 $x=x_{ij}$，定义

$$
P_{k,\ell}(t)=|U(t)_{x,r}|^2,\qquad
B_{k,\ell}=\sum_{\theta\in\operatorname{spec}(L)}|(E_\theta)_{x,r}|.
\tag{1.1}
$$

求和按互异特征值进行。置换分支及分支内叶子的自同构固定 $r$，故这两个量与所选叶子无关。这里的 $B_{k,\ell}$ 是 Coutinho–Guo–Schmeits，*Peak state transfer in continuous quantum walks*，[arXiv:2505.11986v4](https://arxiv.org/abs/2505.11986v4)，§3，p. 5 的 bounding matrix 的一个条目；该文同节的谱展开与三角不等式给出 $P_{k,\ell}(t)\le B_{k,\ell}^2$。

**定义 1.2（共同谱参数）。** 对定义 1.1 的同一组 $k,\ell$，记

$$
S=k+\ell+2,\qquad d=\sqrt{(k-\ell)^2+4\ell},\qquad
a=\frac{S-d}{2},\qquad b=\frac{S+d}{2}.
\tag{1.2}
$$

以下的 $n,a,b,d$ 始终由这一组树参数产生，且记

$$
C_*=2+\frac{6\sqrt5}{5}.
\tag{1.3}
$$

## 2. 全参数谱界及其唯一等号

**定理 2.1（最优全域谱常数）。** 对全部整数 $k\ge2$、$\ell\ge1$、任意叶子 $x$ 与所有实数 $t$，有

$$
P_{k,\ell}(t)\le B_{k,\ell}^2\le C_*\,n^{-3/2}.
\tag{2.1}
$$

谱不等式 $n^{3/2}B_{k,\ell}^2\le C_*$ 取等当且仅当 $(k,\ell)=(2,1)$。

**证明。** 先把根基向量在实际顶点空间 $\mathbb R^V$ 中分解。对于分别在根、全部 hubs、全部 leaves 取值 $R,H,Z$ 的向量，$L$ 的三个坐标类型分别取值

$$
k(R-H),\qquad (\ell+1)H-R-\ell Z,\qquad Z-H.
\tag{2.2}
$$

这由各顶点的实际邻居逐项相加得到。设 $\mathbf1$ 为 $V$ 上全一向量，并对 $\theta\in\{a,b\}$ 定义整个 $V$ 上的向量

$$
w_\theta(r)=k(\theta-\ell-1),\qquad
w_\theta(h_i)=1-\theta,\qquad
w_\theta(x_{ij})=1.
\tag{2.3}
$$

由参数定义可得

$$
a+b=S,\qquad b-a=d>0,\qquad ab=n.
\tag{2.4}
$$

写 $f(z)=z^2-Sz+n$，则 $f(a)=f(b)=0$。将式（2.3）代入式（2.2），$Lw_\theta-\theta w_\theta$ 在根、hub、leaf 三类坐标的值依次为

$$
-k f(\theta),\qquad f(\theta),\qquad0.
$$

故 $Lw_a=aw_a$、$Lw_b=bw_b$，而 $L\mathbf1=0$。

又因

$$
(k+\ell)^2-d^2=4\ell(k-1)>0,
$$

有 $a>1$；因而 $0,a,b$ 互异且这些向量均非零。根基向量 $e_r$ 满足精确的全顶点等式

$$
e_r=\frac1n\mathbf1-\frac1{ad}w_a+\frac1{bd}w_b.
\tag{2.5}
$$

具体地，右端在叶子处为 $1/n-1/(ad)+1/(bd)=0$，在 hub 处为

$$
\frac1n-\frac{1-a}{ad}+\frac{1-b}{bd}
=\frac1n-\frac1{ab}=0,
$$

在根处则为

$$
\frac1n-\frac{k(a-\ell-1)}{ad}+\frac{k(b-\ell-1)}{bd}
=\frac1n+\frac{k(\ell+1)}{ab}=1.
$$

实际 $L$ 是实对称矩阵，故互异特征空间正交。将式（2.5）分别投影到它的每个完整特征空间，得到整个根列

$$
E_0e_r=\frac1n\mathbf1,\qquad
E_ae_r=-\frac1{ad}w_a,\qquad
E_be_r=\frac1{bd}w_b,\qquad
E_\theta e_r=0\quad(\theta\notin\{0,a,b\}).
\tag{2.6}
$$

这里最后一个等式适用于实际矩阵的所有其余互异特征值，无需假定其重数或求出它们。式（2.3）与（2.6）同时指定根、每个 hub 及每片叶子的投影条目；因而它们给出 $n$ 阶矩阵的完整根列。式（2.2）是在实际坐标中取值的公式，并未用归一化商矩阵的条目替代单个顶点条目。

于是对于任意叶子 $x$，有

$$
\begin{aligned}
(E_0)_{x,r}&=\frac1n,&
(E_a)_{x,r}&=-\frac1{ad},&
(E_b)_{x,r}&=\frac1{bd},\\
U(t)_{x,r}&=\frac1n-\frac{e^{iat}}{ad}+\frac{e^{ibt}}{bd},&
B_{k,\ell}&=\frac1n+\frac1{ad}+\frac1{bd}=\frac2{ad}.
\end{aligned}
\tag{2.7}
$$

最后一步使用 $1/n+1/(bd)=1/(ad)$。谱展开及其三角界正是上述文献 §3 的一般结果在此根列上的应用。已有特殊参数 $\ell=s(s+1)$、$k=\ell+1$ 的同一全顶点根分解、谱投影与演化公式，见[仓内两层树的根列分解](../../../D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lean)；式（2.2）与该处的分层常值向量作用相同，式（2.5）在这些参数下还原其根分解。

接下来优化式（2.7），并保持 $a,d$ 来自同一棵树。若 $\ell=1$，则 $d^2=(k-1)^2+4\ge5$；若 $\ell\ge2$，则 $d^2\ge4\ell\ge8$。因此总有 $d\ge\sqrt5$。更关键的是精确恒等式

$$
(d-1)^2-4(a-1)=(k-\ell-1)^2\ge0.
\tag{2.8}
$$

所以实际可行参数满足

$$
1<a\le A(d):=\frac{d^2-2d+5}{4},\qquad d\ge\sqrt5.
\tag{2.9}
$$

由 $n=a(a+d)$ 与式（2.7），待估计的缩放谱界为

$$
F(a,d):=n^{3/2}B_{k,\ell}^2
=\frac{4(a+d)^{3/2}}{\sqrt a\,d^2}.
\tag{2.10}
$$

对固定 $d$，有

$$
\frac{\partial}{\partial a}\log F(a,d)
=\frac{2a-d}{2a(a+d)}.
$$

导数符号至多从负变正，故在闭区间 $1\le a\le A(d)$ 上，最大值位于某个端点。将真实可行集放宽到这个区间给出

$$
F(a,d)\le\max\{G(d),H(d)\},
\tag{2.11}
$$

其中

$$
\begin{aligned}
G(d)&=F(1,d)=\frac{4(d+1)^{3/2}}{d^2},\\
H(d)&=F(A(d),d)
=\frac{(d^2+2d+5)^{3/2}}{d^2\sqrt{d^2-2d+5}}.
\end{aligned}
\tag{2.12}
$$

两个端点包络在 $d\ge\sqrt5$ 上均严格递减。事实上，

$$
\begin{aligned}
\frac{G'(d)}{G(d)}&=-\frac{d+4}{2d(d+1)}<0,\\
\frac{H'(d)}{H(d)}
&=-\frac{2(2d^3+3d^2-10d+25)}
{d(d^2+2d+5)(d^2-2d+5)}<0.
\end{aligned}
\tag{2.13}
$$

第二个分子的括号可写成 $2d(d^2-5)+3d^2+25>0$。在左端点，直接代入给出

$$
H(\sqrt5)=C_*,\qquad
H(\sqrt5)^2-G(\sqrt5)^2=\frac{8(3-\sqrt5)}{25}>0.
\tag{2.14}
$$

式（2.11）—（2.14）证明 $F(a,d)\le C_*$。若 $d>\sqrt5$，则两个包络均严格小于 $C_*$，所以谱等号必有 $d^2=5$。由 $\ell\ge2$ 时 $d^2\ge8$，只可能 $\ell=1$，此时 $(k-1)^2=1$，由 $k\ge2$ 得 $k=2$。反之，该参数处

$$
n=5,\qquad d=\sqrt5,\qquad
a=\frac{5-\sqrt5}{2}=A(\sqrt5),
$$

故 $F(a,d)=H(\sqrt5)=C_*$，证明全部等号情形。$\square$

## 3. 概率的最优上确界与非取得性

**定理 3.1（相位逼近取得最优上确界）。** 对定义 1.1 的实际矩阵与任意叶子，

$$
\sup_{\substack{k\ge2,\ \ell\ge1\text{ 整数}\\t\in\mathbb R}}
n^{3/2}P_{k,\ell}(t)
=\sup_{t\in\mathbb R}5^{3/2}P_{2,1}(t)=C_*.
\tag{3.1}
$$

但对每一组有限整数参数 $k,\ell$ 与每个实数 $t$，均严格有

$$
n^{3/2}P_{k,\ell}(t)<C_*.
\tag{3.2}
$$

一个显式逼近式（3.1）的时间列如下：令整数 $p_j,m_j$ 由

$$
p_0=2,\quad m_0=1,\qquad
p_{j+1}=9p_j+20m_j,\quad
m_{j+1}=4p_j+9m_j\quad(j\ge0)
\tag{3.3}
$$

确定，并令

$$
b_*:=\frac{5+\sqrt5}{2},\qquad t_j=\frac{2\pi m_j}{b_*}.
\tag{3.4}
$$

则 $t_j\to+\infty$ 且 $5^{3/2}P_{2,1}(t_j)\to C_*$。

**证明。** 式（2.7）的三个非零谱贡献的符号为 $+,-,+$。由于常数项 $1/n$ 为正实数，三角不等式取等当且仅当另外两项也为正实数，即

$$
P_{k,\ell}(t)=B_{k,\ell}^2
\quad\Longleftrightarrow\quad
e^{iat}=-1\ \text{且}\ e^{ibt}=1.
\tag{3.5}
$$

这是 Coutinho–Guo–Schmeits，上引文献 Lemma 5.2，p. 8 的相位判据在式（2.6）根列上的应用；其 Corollary 5.5，p. 11 给出整数谱支撑时相应的整除与奇偶条件。

在 $(k,\ell)=(2,1)$ 处，$a_*=(5-\sqrt5)/2$，且

$$
\frac{a_*}{b_*}=\frac{3-\sqrt5}{2}\notin\mathbb Q.
$$

若式（3.5）在某实数 $t$ 成立，则 $a_*t=(2u+1)\pi$、$b_*t=2v\pi$，其中 $u,v\in\mathbb Z$。此时 $v\ne0$，否则 $t=0$ 与第一个等式矛盾；于是 $a_*/b_*=(2u+1)/(2v)\in\mathbb Q$，矛盾。故这组参数在所有有限时间均严格小于谱界；其余参数的谱界已由定理 2.1 严格小于 $C_*n^{-3/2}$，这证明式（3.2）。

为证明上确界，式（3.3）等价于

$$
p_j+m_j\sqrt5=(2+\sqrt5)^{2j+1}.
\tag{3.6}
$$

这是因为 $(2+\sqrt5)^2=9+4\sqrt5$。递推还说明每个 $p_j$ 为偶数、$m_j$ 为正奇数，且 $m_{j+1}\ge9m_j$。取共轭得

$$
\delta_j:=p_j-m_j\sqrt5=(2-\sqrt5)^{2j+1}\longrightarrow0,
\tag{3.7}
$$

因为 $|2-\sqrt5|<1$。由式（3.4）得

$$
e^{ib_*t_j}=1,\qquad
a_*t_j=\pi(3m_j-p_j+\delta_j).
$$

整数 $3m_j-p_j$ 为奇数，因此

$$
e^{ia_*t_j}=-e^{i\pi\delta_j}\longrightarrow-1.
\tag{3.8}
$$

将其代入实际条目式（2.7），得到 $U(t_j)_{x,r}\to B_{2,1}$。特别地，还可直接写出误差

$$
|U(t_j)_{x,r}-B_{2,1}|
=\frac{|e^{i\pi\delta_j}-1|}{a_*\sqrt5}
\le\frac{\pi|2-\sqrt5|^{2j+1}}{a_*\sqrt5}.
\tag{3.9}
$$

所以 $5^{3/2}P_{2,1}(t_j)\to5^{3/2}B_{2,1}^2=C_*$；结合定理 2.1 的全域上界即得式（3.1）。$\square$

## 4. 大阶数的一致尾界与最优指数

**定义 4.1（阶数尾部的两个上确界）。** 对实数 $N\ge1$，记

$$
\begin{aligned}
M_B(N)&=\sup\{n^{3/2}B_{k,\ell}^2:
k\ge2,\ \ell\ge1\text{ 整数},\ n=1+k(\ell+1)\ge N\},\\
M_P(N)&=\sup\{n^{3/2}P_{k,\ell}(t):
k\ge2,\ \ell\ge1\text{ 整数},\ n=1+k(\ell+1)\ge N,\ t\in\mathbb R\}.
\end{aligned}
\tag{4.1}
$$

**定理 4.2（最优统一尾部系数）。** 定义 4.1 的上确界满足

$$
\lim_{N\to\infty}M_B(N)=\lim_{N\to\infty}M_P(N)=1.
\tag{4.2}
$$

更具体地，对每个 $N\ge4$，令

$$
D_N=\max\left\{\sqrt5,\sqrt{4\sqrt{N-1}-3}\right\}.
\tag{4.3}
$$

则利用式（2.12）的 $G,H$ 有对所有树参数及所有时间一致的估计

$$
1\le M_P(N)\le M_B(N)\le\max\{G(D_N),H(D_N)\}.
\tag{4.4}
$$

因此对任意 $\varepsilon>0$，存在 $N_\varepsilon$，使全部 $n\ge N_\varepsilon$ 的 $T(k,\ell)$、任意叶子和全部实数 $t$ 同时满足

$$
P_{k,\ell}(t)\le B_{k,\ell}^2\le(1+\varepsilon)n^{-3/2}.
\tag{4.5}
$$

指数 $3/2$ 不能提高：若 $\beta>3/2$，则不存在有限常数 $C_\beta$ 使所有这些 $k,\ell,t$ 均有 $P_{k,\ell}(t)\le C_\beta n^{-\beta}$。

**证明。** 首先给出覆盖所有大阶数参数的上界，而非选择某一条参数族。由式（2.9）与 $n=a(a+d)$，因 $a\mapsto a(a+d)$ 在 $a>0$ 上递增，得

$$
\begin{aligned}
n&\le A(d)(A(d)+d)\\
&=\frac{(d^2-2d+5)(d^2+2d+5)}{16}
=\frac{d^4+6d^2+25}{16}.
\end{aligned}
\tag{4.6}
$$

若 $n\ge N\ge4$，则 $(d^2+3)^2\ge16(N-1)$，从而 $d^2\ge4\sqrt{N-1}-3$。结合 $d\ge\sqrt5$，得 $d\ge D_N$。式（2.11）与 $G,H$ 的递减性于是给出

$$
n^{3/2}P_{k,\ell}(t)\le n^{3/2}B_{k,\ell}^2
\le\max\{G(D_N),H(D_N)\}
\quad(n\ge N).
\tag{4.7}
$$

同时

$$
\begin{aligned}
G(d)&=4d^{-1/2}(1+d^{-1})^{3/2}\longrightarrow0,\\
H(d)&=\frac{(1+2d^{-1}+5d^{-2})^{3/2}}
{\sqrt{1-2d^{-1}+5d^{-2}}}\longrightarrow1.
\end{aligned}
\tag{4.8}
$$

由于 $D_N\to\infty$，这证明两个尾部上确界的上极限均不超过 $1$，并给出式（4.5）。

为得到同一实际动力学的下界，使用上引[仓内两层树的根列分解](../../../D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lean)的特殊参数族

$$
\ell_s=s(s+1),\qquad k_s=\ell_s+1,\qquad
n_s=1+(s^2+s+1)^2.
\tag{4.9}
$$

该处的分解对全部 $s$ 给出整个根列；其叶子坐标的三个向量值均为 $1$。仅将此既有根列作为紧性见证代入，有

$$
a_s=s^2+1,\qquad b_s=(s+1)^2+1,\qquad d_s=2s+1.
$$

取正偶数 $s$，则 $a_s$ 为奇数、$b_s$ 为偶数。在同一树的时间 $t=\pi$，相位恰为 $e^{i\pi a_s}=-1$、$e^{i\pi b_s}=1$，故式（2.7）给出

$$
P_{k_s,\ell_s}(\pi)=B_{k_s,\ell_s}^2
=\frac4{(s^2+1)^2(2s+1)^2}.
\tag{4.10}
$$

此处的特殊族相位取等只是既有根列及上述文献相位判据的应用。由式（4.9）与（4.10），沿正偶数 $s\to\infty$，

$$
n_s^{3/2}P_{k_s,\ell_s}(\pi)
=\frac{4[1+(s^2+s+1)^2]^{3/2}}
{(s^2+1)^2(2s+1)^2}\longrightarrow1.
\tag{4.11}
$$

事实上，将分子分母同除以 $s^6$，该极限等于 $4/(1\cdot4)=1$。对每个固定 $N$，式（4.11）的充分远尾均有 $n_s\ge N$；所以上确界 $M_P(N)$ 至少为该子列的极限 $1$。再由 $M_P(N)\le M_B(N)$ 与式（4.7），得到式（4.4），继而证明式（4.2）。

最后，若 $\beta>3/2$，同一偶数子列满足

$$
n_s^\beta P_{k_s,\ell_s}(\pi)
=n_s^{\beta-3/2}\bigl(n_s^{3/2}P_{k_s,\ell_s}(\pi)\bigr)
\longrightarrow+\infty,
$$

故不可能存在所述有限 $C_\beta$。$\square$

## 追加锚（本行以下为增补区）
