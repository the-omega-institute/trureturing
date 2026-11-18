# 原始 Fourier 字母的有限标架与定量局部包含

## 175. 原始 Fourier 字母的定量局部预算与同字分支质量

**定义 175.1（固定字母、时序与辅助乘积集）。** 对每个整数 $n\ge2$ 和每个 $0<\lambda<1$，完整采用[169.2][Q175Native]的矩阵，即

$$
\begin{aligned}
\omega&=e^{2\pi i/n},& F_{jk}&=n^{-1/2}\omega^{jk},& a&=2^{1/(n+1)},\\
G&=F\operatorname{diag}(e^{2\pi ia},\ldots,e^{2\pi ia^n})F^{\ast},&
z&=i\lambda,& R&=\operatorname{diag}(z,1,\ldots,1).
\end{aligned}
$$

指标 $j,k$ 均在 $\{0,\ldots,n-1\}$ 中。记

$$
\begin{aligned}
\mathbb T_F&=\{F\operatorname{diag}(e^{i\theta_0},\ldots,e^{i\theta_{n-1}})F^{\ast}:\theta_j\in\mathbb R\},\\
P&=F\operatorname{diag}(1,\omega^{-1},\ldots,\omega^{-(n-1)})F^{\ast},\\
s&=n^{-1/2}\sum_j e_j,\qquad Q=ss^{\ast},\qquad A=iQ,\\
H&=e^{\pi A/2}=I+(i-1)Q,\qquad R_j=P^jRP^{-j},\\
\mathfrak g&=\{X\in M_n(\mathbb C):\operatorname{Re}\operatorname{Tr}X=0\}.
\end{aligned}
$$

$\mathfrak g$ 取实向量空间结构，范数为 $\|X\|_{\mathrm F}=(\operatorname{Tr}(X^{\ast}X))^{1/2}$；$\|X\|_{\mathrm{op}}$ 表示通常算子范数。对于非负整数 $k$，定义辅助乘积集

$$
\mathscr P_k=\{T_0RT_1\cdots RT_k:T_0,\ldots,T_k\in\mathbb T_F\}.
$$

其中保留所显示的 $k$ 个 $R$ 位置。原始正向时序字为有限列 $w=(B_1,\ldots,B_\ell)$，每个 $B_j\in\{G,R\}$；它先作用 $B_1$，其矩阵为 $W(w)=B_\ell\cdots B_1$，$\#_R(w)$ 按字母位置计数。辅助集合 $\mathscr P_k$ 的环面因子不属于这个原始字母表。

**定义 175.2（有限相似标架与常数）。** 令

$$
\begin{aligned}
\mathcal I&=\{(h,j,k,r,v):h\in\{0,1\},\ j\ne k,\ r\in\{0,1,2,3,4\},\ v\in\{0,1\}\},\\
D_\eta&=R_j^rR_k^v,\qquad
A_\eta=H^hD_\eta A D_\eta^{-1}H^{-h}
\quad(\eta=(h,j,k,r,v)),\\
m&=|\mathcal I|=20n(n-1),\qquad
\Phi(t)=\prod_{\eta\in\mathcal I}^{\longrightarrow}e^{t_\eta A_\eta}
\quad(t\in\mathbb R^{\mathcal I}).
\end{aligned}
$$

箭头表示按五元组的字典序从左到右作矩阵乘法，重复方向仍保留各自位置。这里的相似作用始终是 $\operatorname{Int}_D(X)=DXD^{-1}$。置

$$
\begin{aligned}
\mathsf M&=\frac{4n}{\lambda(1-\lambda^2)},&
\mathsf C&=10n^3\mathsf M=\frac{40n^4}{\lambda(1-\lambda^2)},\\
\mathsf N&=\lambda^{-4},&
\mathsf S&=\mathsf N\mathsf C=\frac{40n^4}{\lambda^5(1-\lambda^2)},\\
r_0&=\frac1{16\mathsf S^2},&
b&=50n(n-1),\qquad k_0=nb.
\end{aligned}
$$

**定理 175.3（带明确原衰减次数的非线性局部包含）。** 对定义175.1—175.2的每个 $n,\lambda$，有

$$
\boxed{
z^b\exp\bigl\{Y\in\mathfrak g:\|Y\|_{\mathrm F}\le r_0/2\bigr\}
\ \subseteq\ \mathscr P_{k_0}.
}
$$

证明（推导归属：repo-derived；本条的有限标架系数预算、定量非线性局部包含及原 $R$ 支付估计；所用标准工具采用下列引文）。相似变换补足方向再取第二类局部乘积坐标的方法见[D’Alessandro，Lemma 1][Q175DA01]及[Method 1][Q175DA09]；以下对本组相似矩阵给出系数预算、非线性半径和原 $R$ 的支付次数。

先构造实线性合成映射

$$
T:\mathbb R^{\mathcal I}\longrightarrow\mathfrak g,
\qquad Tt=\sum_\eta t_\eta A_\eta
$$

的一个右逆。每个 $A_\eta$ 的迹都是 $i$，且

$$
\|A_\eta\|_{\mathrm F}\le
\|D_\eta\|_{\mathrm{op}}\|D_\eta^{-1}\|_{\mathrm{op}}\|A\|_{\mathrm F}
\le\lambda^{-4}=\mathsf N.
$$

这里 $H$ 酉，$D_\eta$ 对角，其最小对角模长至少为 $\lambda^4$、最大模长至多为一，而 $\|A\|_{\mathrm F}=1$。

称一个表示具有系数预算 $d$，是指它是 $A_\eta$ 的实线性组合且系数绝对值之和不超过 $d$。记 $E_{jk}=e_je_k^{\ast}$、$P_j=E_{jj}$ 及 $\mathcal T_j=\operatorname{Int}_{R_j}$。对于 $j\ne k$，逐项相似作用给

$$
\begin{aligned}
B_{jk}&=(\mathcal T_j-I)(\mathcal T_k-I)A
=\alpha(E_{jk}+E_{kj}),\\
\alpha&=\frac{i}{n}(2-z-z^{-1}),\qquad |\alpha|\ge\frac2n,\\
\Delta&=\lambda^{-2}-\lambda^2>0,\\
C_{jk}&=\frac{(\mathcal T_j^2+\lambda^{-2}I)B_{jk}}{\Delta}
=\alpha E_{jk},\qquad
\mathcal T_jC_{jk}=i\lambda\alpha E_{jk}.
\end{aligned}
$$

确实，$\mathcal T_j^2$ 在 $E_{jk},E_{kj}$ 上的乘数分别为 $-\lambda^2,-\lambda^{-2}$。$B_{jk}$ 的四项展开给预算四；$C_{jk}$ 及 $\mathcal T_jC_{jk}$ 各自的预算不超过

$$
\frac{4(1+\lambda^{-2})}{\Delta}=\frac4{1-\lambda^2}.
$$

这些展开只用 $h=0$、$r\le4$、$v\le1$ 的位置。写 $\alpha=x+iy$，其中 $x,y$ 为实数，则

$$
\begin{aligned}
E_{jk}&=\frac{x}{|\alpha|^2}C_{jk}
-\frac{y}{\lambda|\alpha|^2}\mathcal T_jC_{jk},\\
iE_{jk}&=\frac{y}{|\alpha|^2}C_{jk}
+\frac{x}{\lambda|\alpha|^2}\mathcal T_jC_{jk}.
\end{aligned}
$$

由 $|\alpha|\ge2/n$，这两个实表示各有预算

$$
\frac4{1-\lambda^2}\frac{1+\lambda^{-1}}{|\alpha|}
\le\frac{4n}{\lambda(1-\lambda^2)}=\mathsf M.
$$

因此 $iI=nA-\sum_{j\ne k}iE_{jk}$ 有预算 $n+n(n-1)\mathsf M$。

令 $\Pi_{\mathrm{off}}$ 删除矩阵的对角部分。对 $Y_{jk}=E_{jk}-E_{kj}$，$H=I+(i-1)Q$ 的直接乘法给

$$
\operatorname{diag}(HY_{jk}H^{-1})=-\frac{2i}{n}(P_j-P_k).
$$

所以

$$
\begin{aligned}
i(P_j-P_k)&=-\frac n2\bigl[HY_{jk}H^{-1}-\Pi_{\mathrm{off}}(HY_{jk}H^{-1})\bigr],\\
P_j-P_k&=\frac n2\bigl[H(iY_{jk})H^{-1}-\Pi_{\mathrm{off}}(H(iY_{jk})H^{-1})\bigr].
\end{aligned}
$$

$Y_{jk}$ 和 $iY_{jk}$ 的上述表示各有预算 $2\mathsf M$，并只用 $h=0$；以 $H$ 共轭便使用同样系数的 $h=1$ 位置。酉共轭保持 Frobenius 范数，故这两只共轭矩阵均有范数 $\sqrt2$，其非对角条目的实部和虚部绝对值总和不超过

$$
\sqrt{2n(n-1)}\sqrt2\le2n.
$$

用已得 $E_{jk},iE_{jk}$ 的表示扣除这些非对角部分，每个所显示的对角差方向遂有预算 $n(n+1)\mathsf M$。

对任意 $X\in\mathfrak g$，定义

$$
\tau=\frac{\operatorname{Im}\operatorname{Tr}X}{n},\qquad
d_j=X_{jj}-i\tau.
$$

有 $\sum_jd_j=0$，并且

$$
\operatorname{diag}X=i\tau I+
\sum_{j=1}^{n-1}\bigl[\operatorname{Re}d_j(P_j-P_0)
+\operatorname{Im}d_j\,i(P_j-P_0)\bigr].
$$

实 Cauchy–Schwarz 不等式给

$$
\begin{aligned}
\sum_{j\ne k}(|\operatorname{Re}X_{jk}|+|\operatorname{Im}X_{jk}|)
&\le2n\|X\|_{\mathrm F},\\
\sum_{j=1}^{n-1}(|\operatorname{Re}d_j|+|\operatorname{Im}d_j|)
&\le\sqrt{2(n-1)}\Bigl(\sum_j|d_j|^2\Bigr)^{1/2}
\le n\|X\|_{\mathrm F},\\
|\tau|&\le\|X\|_{\mathrm F}/\sqrt n.
\end{aligned}
$$

第二行还用了 $\sum_j|d_j|^2=\sum_j|X_{jj}|^2-n\tau^2$。在这些式中代入已固定的矩阵单位、对角差及 $iI$ 表示，得到一个实线性映射 $J:\mathfrak g\to\mathbb R^{\mathcal I}$，满足

$$
\begin{aligned}
TJ&=I_{\mathfrak g},\\
\|JX\|_1&\le
\left[2n\mathsf M+n^2(n+1)\mathsf M+
\frac{n+n(n-1)\mathsf M}{\sqrt n}\right]\|X\|_{\mathrm F}
\le\mathsf C\|X\|_{\mathrm F}.
\end{aligned}
\tag{175.1}
$$

最后一个界对所有 $n\ge2$ 成立；这里 $\mathsf M\ge1$，可将中间方括号界为 $(2n+n^2(n+1)+n^{3/2})\mathsf M\le10n^3\mathsf M$。构造只要求存在 $j\ne k$，故包括 $n=2$。

现在令 $E(X)=\Phi(JX)$。矩阵指数的收敛、相似变换、范数界及单参数导数直接采用[Hall，Propositions 3.1、3.3、3.4][Q175Hall]。记 $t=JX$、$B_\ell=e^{t_\ell A_\ell}$，其中 $\ell=1,\ldots,m$ 是固定顺序，并置

$$
u=\mathsf S\|X\|_{\mathrm F},\qquad q=e^u-1.
$$

因为 $\sum_\ell|t_\ell|\|A_\ell\|_{\mathrm F}\le u$，指数级数及逐因子乘积差分解给

$$
\|E(X)-I\|_{\mathrm F}\le q.
$$

具体地，每个因子满足 $\|B_\ell\|_{\mathrm{op}}\le e^{|t_\ell|\|A_\ell\|_{\mathrm F}}$ 和 $\|B_\ell-I\|_{\mathrm F}\le e^{|t_\ell|\|A_\ell\|_{\mathrm F}}-1$；乘积差分解的上界相加正好不超过 $e^u-1$。

对 $Z\in\mathfrak g$，乘积求导给

$$
DE_X[Z]=\sum_{\ell=1}^m(JZ)_\ell
B_1\cdots B_\ell A_\ell B_{\ell+1}\cdots B_m.
$$

令 $L_\ell=B_1\cdots B_\ell$、$D_\ell=B_{\ell+1}\cdots B_m$，并记 $u_\ell=\sum_{j\le\ell}|t_j|\|A_j\|_{\mathrm F}$、$v_\ell=\sum_{j>\ell}|t_j|\|A_j\|_{\mathrm F}$。在 $A_\ell$ 左右分别作乘积差分解，所有未作差的指数因子取算子范数，得到

$$
\begin{aligned}
\|L_\ell A_\ell D_\ell-A_\ell\|_{\mathrm F}
&\le\bigl[(e^{u_\ell}-1)e^{v_\ell}+e^{v_\ell}-1\bigr]\|A_\ell\|_{\mathrm F}\\
&\le q\|A_\ell\|_{\mathrm F}.
\end{aligned}
$$

又 $DE_0[Z]=TJZ=Z$，故

$$
\|DE_X-I\|_{\mathrm F\to\mathrm F}\le\mathsf S q.
\tag{175.2}
$$

所用混合范数不等式为 $\|BCD\|_{\mathrm F}\le\|B\|_{\mathrm{op}}\|C\|_{\mathrm F}\|D\|_{\mathrm{op}}$，其中 $\|I_n\|_{\mathrm{op}}=1$，而 $\|I_n\|_{\mathrm F}=\sqrt n$。

在 $\|X\|_{\mathrm F}\le r_0$ 上，$\mathsf S\ge1$，因而

$$
u\le\frac1{16\mathsf S},\qquad
q\le2u\le\frac1{8\mathsf S}<1.
$$

采用[Hall，Theorem 3.6][Q175Hall]的近单位矩阵对数，定义 $\Psi(X)=\log E(X)$。若 $B=E(X)-I$，其导数是收敛级数

$$
D\log_{I+B}[V]=
\sum_{d=1}^{\infty}\frac{(-1)^{d+1}}d
\sum_{v=0}^{d-1}B^vVB^{d-1-v}.
$$

级数在每个 $\|B\|_{\mathrm{op}}\le q<1$ 的较小邻域上一致可逐项求导。由上述混合范数不等式，

$$
\|D\log_{E(X)}\|_{\mathrm F\to\mathrm F}\le\frac1{1-q},\qquad
\|D\log_{E(X)}-I\|_{\mathrm F\to\mathrm F}\le\frac q{1-q}.
$$

又 $\operatorname{Tr}A_\eta=i$，所以每个 $E(X)$ 的行列式模长是一。由[Hall，Theorem 3.10][Q175Hall]的 $\det e^Z=e^{\operatorname{Tr}Z}$ 及 $e^{\log E(X)}=E(X)$，有

$$
\operatorname{Re}\operatorname{Tr}\Psi(X)=\log|\det E(X)|=0.
$$

因此 $\Psi$ 在所用闭球及其一个开邻域内取值于 $\mathfrak g$。链式法则与(175.2)给

$$
\begin{aligned}
\|D\Psi_X-I\|_{\mathrm F\to\mathrm F}
&\le\frac{(\mathsf S+1)q}{1-q}\\
&\le\frac{\mathsf S+1}{8\mathsf S-1}
\le\frac27<\frac12
\qquad(\|X\|_{\mathrm F}\le r_0).
\end{aligned}
\tag{175.3}
$$

$\mathfrak g$ 是有限维矩阵空间的闭实子空间，所用闭球完备且凸，$\Psi(0)=0$；沿线段积分便给

$$
\|\Psi(X)-\Psi(X')-(X-X')\|_{\mathrm F}
\le\tfrac12\|X-X'\|_{\mathrm F}
\quad(\|X\|_{\mathrm F},\|X'\|_{\mathrm F}\le r_0).
$$

直接使用[定量局部满射原理][Q175IFT]，取近似线性映射为 $I_{\mathfrak g}$、右逆范数为一、误差常数为 $1/2$、定义域为半径 $r_0$ 的闭球，得到

$$
\{Y\in\mathfrak g:\|Y\|_{\mathrm F}\le r_0/2\}
\subseteq\Psi\bigl(\{X\in\mathfrak g:\|X\|_{\mathrm F}\le r_0\}\bigr).
$$

该原理在这里的 Banach 不动点映射是 $X\mapsto Y+X-\Psi(X)$；上式的线段估计同时支付其闭球自映射性和收缩性。于是每个所需 $Y$ 都有 $e^Y=E(X)=\Phi(JX)$，这是有限乘积等式。

最后支付这个有限乘积。指数的相似恒等式给

$$
e^{t_\eta A_\eta}
=H^hD_\eta e^{t_\eta A}D_\eta^{-1}H^{-h}.
$$

[169.3][Q175Native]已经给出 $P,H,e^{tA}\in\mathbb T_F$ 以及精确恒等式

$$
S_0=\prod_{j=1}^{n-1}P^jRP^{-j}=zR^{-1}.
$$

展开 $D_\eta=R_j^rR_k^v$ 及其逆，每个指数因子含 $q_\eta=r+v$ 个原 $R$ 和同样多的原 $R^{-1}$，其余因子全部在 $\mathbb T_F$。将每个原 $R^{-1}$ 用 $S_0$ 替换，使该因子的矩阵乘上中心标量 $z^{q_\eta}$，并留下恰好 $nq_\eta$ 个正向原 $R$。保持全部五元组位置，即使 $t_\eta=0$ 也不取消该位置的展开。于是

$$
\sum_{\eta\in\mathcal I}q_\eta
=2n(n-1)\sum_{r=0}^4\sum_{v=0}^1(r+v)
=50n(n-1)=b.
$$

将相邻环面因子合并，便得到 $V\in\mathscr P_{nb}$ 且

$$
V=z^b\Phi(JX)=z^be^Y.
$$

中心标量没有被实现为额外字母，也没有从矩阵 $V$ 中消去。这证明所需包含。∎

**定理 175.4（精度无关的原 $R$ 次数与同一正向字的质量下界）。** 对每个整数 $n\ge2$、每个 $0<\lambda<1$，定义

$$
\begin{aligned}
L&=\left\lceil32\pi\sqrt n\left[\frac{40n^4}{\lambda^5(1-\lambda^2)}\right]^2\right\rceil,\\
\beta&=50n(n-1)L,\\
K(n,\lambda)&=50n^2(n-1)L=n\beta,\\
c(n,\lambda)&=(i\lambda)^\beta,\qquad
p(n,\lambda)=\lambda^{2K(n,\lambda)}>0.
\end{aligned}
$$

对每个 $U\in U(n)$ 及每个 $\varepsilon>0$，存在一个定义175.1的实际有限正向时序字 $w$，使同一个 $W=W(w)$ 同时满足

$$
\boxed{
\begin{aligned}
\#_R(w)&=K(n,\lambda),\\
\|c(n,\lambda)^{-1}W-U\|_{\mathrm{op}}&\le\varepsilon,\\
\inf_{\rho\succeq0,\ \operatorname{Tr}\rho=1}
\operatorname{Tr}(W\rho W^{\ast})&\ge p(n,\lambda).
\end{aligned}
}
$$

次数 $K$、记账标量 $c\ne0$ 和下界 $p$ 均只依赖 $n,\lambda$。

证明（推导归属：repo-derived；由175.3导出的同一原始正向字的次数与质量联合估计）。通常酉谱分解由[Watrous，Theorem 1.3、Corollary 1.4][Q169W1]供应。取本征角 $\theta_j\in[-\pi,\pi]$，得到

$$
U=e^X,\qquad X\in\mathfrak u(n)\subseteq\mathfrak g,
\qquad\|X\|_{\mathrm F}\le\pi\sqrt n.
$$

因 $L=\lceil32\pi\sqrt n\,\mathsf S^2\rceil$，有 $\|X/L\|_{\mathrm F}\le r_0/2$。在酉目标上取根并重复局部乘积，是[D’Alessandro，Method 1、式(7)及(14)][Q175DA09]的步骤；这里由175.3给出的明确半径确定其重复次数。具体地，175.3给出

$$
V_0=z^be^{X/L}\in\mathscr P_{k_0}.
$$

重复同一有限乘积 $L$ 次，合并相邻环面因子，得到

$$
V=V_0^L=z^{bL}e^X=cU
=T_0RT_1\cdots RT_K\in\mathscr P_K.
$$

仅对酉矩阵 $U$ 使用了谱对数；没有使用非紧群的全局指数满射。

置

$$
\delta=\frac{\varepsilon\lambda^\beta}{K+1}>0.
$$

直接消费[169.3的正向幂稠密性][Q175Native]：对每个有限位置 $j=0,\ldots,K$，选取一个非负整数 $a_j$，使

$$
\|G^{a_j}-T_j\|_{\mathrm{op}}<\delta.
$$

令

$$
W=G^{a_0}RG^{a_1}\cdots RG^{a_K}.
$$

将显示的乘积从右到左展开为字母列，即得实际时序字 $w$；零次幂给空段，其余幂由有限个 $G$ 字母组成，全部 $K$ 个 $R$ 位置保留。

所有 $T_j,G^{a_j}$ 都酉，所有 $R$ 都为压缩矩阵。逐因子乘积差分解遂给

$$
\|W-cU\|_{\mathrm{op}}
\le\sum_{j=0}^K\|G^{a_j}-T_j\|_{\mathrm{op}}
<(K+1)\delta=\varepsilon\lambda^\beta.
$$

除以记账模长 $|c|=\lambda^\beta$，得到所述逼近。原字母表内没有加入 $c^{-1}I$。

现在对这个已经选定的同一个 $W$ 计算质量。对任意向量 $v$，有

$$
\lambda\|v\|\le\|Rv\|\le\|v\|,\qquad \|Gv\|=\|v\|.
$$

依时序逐步应用，得到

$$
\lambda^K\|v\|\le\|Wv\|\le\|v\|,
\qquad\lambda^{2K}I\preceq W^{\ast}W\preceq I.
$$

因此对每个 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，迹的循环性及 PSD 迹配对给

$$
\operatorname{Tr}(W\rho W^{\ast})
=\operatorname{Tr}(\rho W^{\ast}W)
\ge\lambda^{2K}\operatorname{Tr}\rho=p(n,\lambda).
$$

这是原矩阵 $W$ 的数学分支质量，而非 $c^{-1}W$ 的质量；其完全正性由[Watrous，Theorem 2.22][Q169W2]的单 Kraus 表示给出，不增迹性由 $W^{\ast}W\preceq I$ 给出。该下界在选取任意精度所需的有限正向幂之后仍成立。

最后，$K=n\beta$ 使

$$
|\det W|=\lambda^K=|c|^n=|\det(cU)|,\qquad 0<|c|<1.
$$

于是精度趋零时所逼近的是 $cU$；[169.7][Q175Native]的未缩放恒等式 $\overline{\mathcal W^+}\cap U(n)=\mathbb T_F$ 保持原义。定理没有给 $\sum_ja_j$ 的上界，也没有将辅助环面因子当作原始字母。∎

[Q169W1]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
[Q169W2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
[Q175Native]: https://github.com/the-omega-institute/trureturing/blob/74f0816e3a2340d063ad1a7cb5e8a93ffe2d1c9d/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q175DA01]: https://arxiv.org/html/quant-ph/0111133v1
[Q175DA09]: https://arxiv.org/html/0904.2793v1
[Q175Hall]: https://arxiv.org/html/math-ph/0005032v1
[Q175IFT]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean#L143

## 追加锚（本行以下为增补区）
