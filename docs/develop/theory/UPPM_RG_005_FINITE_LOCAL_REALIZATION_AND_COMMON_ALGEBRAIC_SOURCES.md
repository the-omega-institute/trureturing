# 有限地方实现与共同代数来源

## 1. 原支持、共同来源与受限预算

**定义 1.1（继承的数学数据）。** 固定 [RG004 定义 75.1、定理 75.2、定义 77.1](UPPM_RG_004_CM_ANNIHILATORS_AND_GALOIS_DENOMINATOR_RELATIONS.md#75-hurwitz-左理想网络的同点完整预算与正三次尾部) 的全部数据，特别是 $q,A,H_{\mathrm{cut}},\gamma=A/1000,r_0$、原支持 $\mathscr P=\{p_I\}$、$r=r_p$、Hurwitz 元 $u=(1+i+j+k)/2$、左 $\mathcal O$ 模 $\mathcal R=\mathcal O\oplus\mathcal O u$、$\mathcal O=\mathbb Z[i]$ 和各左理想 $I=I_p$。$\mathcal R/I$ 只作左模，不作商环。始终使用

$$
E_0:y^2=x^3-x,\quad [i](x,y)=(-x,iy),\quad
L_p=\mathbb Q_p(i),\quad v_p(p)=1.
\tag{1.1}
$$

原支持满足 $p>\max(H_{\mathrm{cut}},5)$、$p\equiv-1\pmod{4qr_p}$，故 $p$ 在 $\mathbb Q(i)$ 中惰性，且 $p\nmid qr_p$。$U_p(1)$ 是第一形式群；其由 $dx/(2y)$ 归一化的对数是保赋值的 $\mathcal O$ 模同构 $U_p(1)\simeq p\mathcal O_{L_p}$。原嵌入 $\iota_p:M_0=\mathbb Q(i,\sqrt2)\hookrightarrow L_p$ 固定；这里用 $M_0$ 区别四次数域与精度整数 $M$。原最终局部点记为 $P^*_{j,p}$，并记

$$
[q]P^*_{j,p}=T_{j,p}+U^*_{j,p},\qquad
(\log U^*_{1,p},\log U^*_{2,p})=(p,p\iota_p(\sqrt2)).
\tag{1.2}
$$

$T_{j,p}$ 是原实际 $r_p$ 挠点；$\theta_{I_p}:\mathcal R/I_p\simeq E_0[r_p]$ 将 $1,u$ 的像送到它们。特别地，两个约化共同生成的 $\mathcal O$ 模恰为 $E_0[r_p]$。原最终点本身非挠，因为其 $qr_p$ 倍的形式对数非零；所以它们均为仿射点且 $y(P^*_{j,p})\ne0$，即使约化为原点或二挠点也如此。

本卷所有高度均为绝对对数高度；$h_x(P)=h(x(P))$，约定 $h_x(O)=0$。$\widehat h$ 使用 Silverman 的规范 $2\widehat h=h_x+O_{E_0}(1)$。以下新结论是 RG004 的有限共同来源消费者（repo-derived）；CRT、Hensel、椭圆对数下界和高度有限性只作为所引经典输入。

**定义 1.2（有限清单中的全部关系）。** 令 $F\subset\mathscr P$ 是有限集合，暂不与原固定八次数域混同。一个有限共同来源指一次选定的数域 $K\supset\mathbb Q(i)$、点对 $P_1,P_2\in E_0(K)$ 及每个 $p\in F$ 的一个保持 $i$ 的嵌入 $\sigma_p:K\hookrightarrow L_p$。同一 $p$ 的全部关系必须共用这个嵌入。对

$$
0\ne x=\alpha+\beta u\in\mathcal R,\qquad
S=|\alpha|^2+|\beta|^2,
\qquad S_p(x)=\sigma_p\bigl([q]([\alpha]P_1+[\beta]P_2)\bigr),
\tag{1.3}
$$

若关系非零，令 $b_p(x)$ 为其形式深度，非入口时为 $0$。只定义清单内的完整深度和

$$
D_F(x)=\sum_{p\in F}b_p(x)\log p,\qquad
D_F^*(x)=\sum_{\substack{p\in F\\x\in I_p}}
\bigl(1+v_p(\iota_p(\alpha+\beta\sqrt2))\bigr)\log p.
\tag{1.4}
$$

“完整”指每项保留全部深度，绝不表示对所有素数求和。清单外的新贡献未由 $D_F$ 控制。直接复用 RG004 (75.8)、(75.18)–(75.19)，有

$$
D_F^*(x)\le AS,\quad
D_F^*(x)\le4\gamma S+\log(3S),\quad
2v_p(\iota_p(\alpha+\beta\sqrt2))\log p
\le2\log(3S).
\tag{1.5}
$$

最后一式对任意原支持 $p$ 成立；其依据是同一个四次数域 $M_0$ 的四共轭范数，不是共同来源域 $K$ 的范数。$\mathscr P(x)=\{p\in\mathscr P:x\in I_p\}$ 有限，因为每项 $r_p\mid N_{\mathcal R}(x)<2S$。

## 2. 直接逼近最终点的八次共同来源

**定理 2.1（固定分母、共同 CRT 与独立平方类）。** 对每个非空有限 $F\subset\mathscr P$，存在固定正整数 $D_F^{\mathrm{den}}$、整数 $\kappa_p\ge1$ 及只依赖 $F$ 和定义 1.1 固定数据的常数，使对每个整数 $M\ge1$ 可以同时构造

$$
P_{j,M}=(a_{j,M},y_{j,M}),\quad a_{j,M}\in\mathbb Q(i),\quad
K_{F,M}=\mathbb Q(i,y_{1,M},y_{2,M}),\quad [K_{F,M}:\mathbb Q]=8,
\tag{2.1}
$$

以及每个 $p\in F$ 的共同嵌入 $\sigma_{p,M}$，满足

$$
\begin{gathered}
v_p\bigl(a_{j,M}-x(P^*_{j,p})\bigr)\ge M+\kappa_p,\qquad
\sigma_{p,M}(P_{j,M})-P^*_{j,p}\in U_p(M+1),\\
Q_{j,p,M}:=[qr_p]P_{j,M}\in E_0(K_{F,M}),\quad
\sigma_{p,M}(Q_{j,p,M})\in U_p(1),\\
\ell_{j,p,M}:=\log\sigma_{p,M}(Q_{j,p,M}),\quad
v_p(\ell_{j,p,M})=1,\\
v_p\bigl(\ell_{1,p,M}-r_pp\bigr)\ge M+1,\quad
v_p\bigl(\ell_{2,p,M}-r_pp\iota_p(\sqrt2)\bigr)\ge M+1,\\
h_x(P_{j,M})\le M\sum_{p\in F}\log p+C_F,\qquad
\widehat h(P_{j,M})+\widehat h(Q_{j,p,M})\le C_F(1+M).
\end{gathered}
\tag{2.2}
$$

这里 $U_p(k)$ 表示 $v_p(t)\ge k$ 的形式层，$t=-x/y$。点对在 $\mathcal O$ 模意义下模挠独立。域、点对、各地方嵌入和精度在任何 Gaussian 关系之前固定；它们允许随 $F,M$ 改变。

证明。先说明逼近的固定损失。固定 $p\in F$、$j\in\{1,2\}$，写 $(x^*,y^*)=P^*_{j,p}$、$f(X)=X^3-X$、$s=\min(0,v_p(x^*))$。$f(x^*)=(y^*)^2\ne0$。在充分小且固定的圆盘 $v_p(\delta)\ge e$ 上，有

$$
v_p(f(x^*+\delta)-f(x^*))\ge v_p(\delta)+2s.
\tag{2.3}
$$

这是展开 $\delta(3(x^*)^2+3x^*\delta+\delta^2-1)$ 的下界；可先取 $e\ge\max(1,v_p(x^*))$。再使 $e+2s-2v_p(y^*)\ge1$。奇素数处的 Hensel 同支平方根给出解析点

$$
P(\delta)=\left(x^*+\delta,
y^*\sqrt{f(x^*+\delta)/f(x^*)}\right),\qquad \sqrt{\phantom a}\in1+p\mathcal O_{L_p}.
\tag{2.4}
$$

这里的平方根由 $1$ 附近的二项级数给出，系数在奇素数处为整；这也直接说明同支唯一且解析。平移是光滑曲线的正则映射，故缩小这个固定圆盘后，$g(\delta)=t(P(\delta)-P^*)$ 解析、$g(0)=0$。其线性项为 $\delta/(2y^*)$，因为平移保持 $dx/(2y)$ 且该微分在原点的线性项为 $dt$。

具体地，写 $g(\delta)=\sum_{n\ge1}c_n\delta^n$；取整数 $e$ 使该级数在 $p^e\mathcal O_{L_p}$ 上收敛且 $v_p(c_n)+ne\to+\infty$。于是存在固定整数 $C\ge0$ 使 $v_p(c_n)+(n-1)e\ge-C$ 对全部 $n$ 成立。因此

$$
v_p(g(\delta))\ge v_p(\delta)-C\qquad(v_p(\delta)\ge e).
\tag{2.5}
$$

这些半径与损失都只取决于固定目标，不随 $M$ 变。对同一个 $p$ 的两个目标取共同的 $e,C$，再取整数 $\kappa_p$，使其不小于 $e,C+1$ 及两个数 $2v_p(y^*)-2s+1$。则 $v_p(\delta)\ge M+\kappa_p$ 蕴涵 (2.4) 的根位于 $1+p^{M+1}\mathcal O_{L_p}$，且 (2.5) 至少为 $M+1$。这个论证只要求目标本身 $y^*\ne0$；不要求其约化的 $y$ 是单位，也不在原点或二挠约化处除以约化坐标。

现在直接逼近这两个最终点的 $x$ 坐标。取

$$
\nu_p=\max\{0,-v_p(x(P^*_{1,p})),-v_p(x(P^*_{2,p}))\},\quad
D:=D_F^{\mathrm{den}}=\prod_{p\in F}p^{\nu_p},\quad
\lambda_1=2+i,\quad\lambda_2=3+2i.
\tag{2.6}
$$

$D$ 与 $M$ 无关，且是两辅助 Gaussian 素数处的单位。所有原 $p$ 惰性，因而 $\mathcal O/(p^k)\simeq\mathcal O_{L_p}/p^k$。在 $\mathcal O$ 中规定

$$
\begin{aligned}
A_{j,M}&\equiv D x(P^*_{j,p})\pmod{p^{M+\kappa_p+\nu_p}}
&& (p\in F,\ j=1,2),\\
(A_{1,M},A_{2,M})&\equiv(D\lambda_1,2D)\pmod{\lambda_1^2},\\
(A_{1,M},A_{2,M})&\equiv(2D,D\lambda_2)\pmod{\lambda_2^2},\qquad
a_{j,M}=A_{j,M}/D.
\end{aligned}
\tag{2.7}
$$

所有模理想互素，Gaussian CRT 可同时求解。这里指定的是局部坐标的有限剩余类，并未假定目标代数。模理想由

$$
G_M=\lambda_1^2\lambda_2^2\prod_{p\in F}p^{M+\kappa_p+\nu_p}
\tag{2.8}
$$

生成；在 Gaussian 格 $G_M\mathcal O$ 的中心正方形基本域中取代表，有 $|A_{j,M}|\le |G_M|/\sqrt2$。因此
$h(a_{j,M})\le\log\max(1,|G_M|)+\log D\le M\sum_{p\in F}\log p+C_F$。除以 $D$ 后第一行正给出 (2.2) 的坐标精度；(2.4) 为每个 $p,j$ 选定同支根 $y_{j,p,M}$。

两个辅助素数处 $f(2)=6$ 均为单位，而 $f(\lambda_a+\lambda_a^2z)$ 恰有 $\lambda_a$ 赋值 $1$。于是

$$
\begin{pmatrix}
v_{\lambda_1}(f(a_{1,M}))&v_{\lambda_1}(f(a_{2,M}))\\
v_{\lambda_2}(f(a_{1,M}))&v_{\lambda_2}(f(a_{2,M}))
\end{pmatrix}
=\begin{pmatrix}1&0\\0&1\end{pmatrix}.
\tag{2.9}
$$

两平方类在 $\mathbb Q(i)^\times/\mathbb Q(i)^{\times2}$ 中独立。抽象选取 $y_{j,M}^2=f(a_{j,M})$ 后，(2.1) 的扩张在 $\mathbb Q(i)$ 上双二次，绝对次数恰为 $8$。对每个 $p$，映射 $y_{j,M}\mapsto y_{j,p,M}$、$i\mapsto i$ 给出域嵌入：独立平方类保证抽象代数 $\mathbb Q(i)[Y_1,Y_2]/(Y_1^2-f(a_1),Y_2^2-f(a_2))$ 本身是域，向 $L_p$ 的这个非零同态必单射。不同 $p$ 可独立选符号；一旦选定，同一 $p$ 不再随关系改嵌入。其完成恰为 $L_p$，因为含有完成已是 $L_p$ 的 $\mathbb Q(i)$。

由 (2.5)，点差在 $U_p(M+1)$。乘 $qr_p$ 是形式群上的单位作用，保留这个误差阶；原 $[qr_p]P^*_{j,p}=[r_p]U^*_{j,p}$ 的对数为 (2.2) 的两个目标。形式对数的保赋值性证明全部对数估计，特别是 $v_p(\ell_{j,p,M})=1$。

所以两个 $P_{j,M}$ 都非挠。在 $K_{F,M}/\mathbb Q(i)$ 中分别翻转两个根的自同构，分别把一个 $P_j$ 送到 $-P_j$ 而固定另一个。若 $[\alpha]P_1+[\beta]P_2$ 是挠点，分别翻转并作差，得到 $[2\alpha]P_1$、$[2\beta]P_2$ 都是挠点。非零 Gaussian 乘法是有限核同源，故非挠性迫使 $\alpha=\beta=0$。这里不把域的符号翻转当作对 $p$ 进对数的连续作用。

高度最后直接用 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.9.3(b)、(e)，印刷页 248–249](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)：$2\widehat h=h_x+O_{E_0}(1)$ 在全部代数点上成立，常数不随数域变化，且 $\widehat h([qr_p]P)=(qr_p)^2\widehat h(P)$。因 $F$ 固定，得到 (2.2)。这是直接构造最终点，没有对非挠点再作 $q$ 除法，也没有把最终共同域扩大为含 $\sqrt2$ 的十六次域。证毕。

用白话说，有限多个地方的坐标要求可以写在同一张余数表中，两个额外素数再保证两个平方根各自独立。这样得到的是同一对代数点，而不是每个地方各造一对；原点和二挠约化只影响固定的精度损失。

## 3. 同一精度同时支付全部 Gaussian 关系

**定理 3.1（共同八次域上的 HKT 消费者）。** 固定非空有限 $F$。定理 2.1 的构造存在与 $M,\alpha,\beta$ 无关的 $C_F>0$，使对每个 $p\in F$、整数 $M\ge1$ 和非零 $(\alpha,\beta)\in\mathcal O^2$，

$$
\begin{gathered}
L_{p,M}(x):=\alpha\ell_{1,p,M}+\beta\ell_{2,p,M}\ne0,\\
v_p(L_{p,M}(x))\log p
\le C_F(1+M)^2(1+\log(1+M))^3(1+\log S).
\end{gathered}
\tag{3.1}
$$

若 $\sigma_{p,M}([q]([\alpha]P_{1,M}+[\beta]P_{2,M}))$ 进入形式群，它的深度恰为 $v_p(L_{p,M}(x))$。

证明。两个 $Q_{j,p,M}$ 仍模挠独立，且在同一个局部形式群内。其 Gaussian 组合非零；形式对数单射故 $L_{p,M}(x)\ne0$。另一方面对原关系点 $S_p(x)$ 始终有

$$
[r_p]S_p(x)=\sigma_{p,M}([\alpha]Q_{1,p,M}+[\beta]Q_{2,p,M}).
\tag{3.2}
$$

进入后可取形式对数，得到 $L_{p,M}(x)=r_p\log S_p(x)$。$p\nmid r_p$，故深度等于 $v_p(L_{p,M})$，没有额外再加 $1$。

以下沿用 RG004 §77 的精确参数消费者，并核对共同域的变化。所用原发表输入为 [Hirata-Kohno–Takada，*Linear forms in two elliptic logarithms in the p-adic case*，Kyushu J. Math. **64**, 239–260，DOI 10.2206/kyushujm.64.239，Assumptions 2.1–2.2、Corollary 2.1，印刷页 242–243](https://www.jstage.jst.go.jp/article/kyushujm/64/2/64_2_239/_pdf)。在其记号中取

$$
\begin{gathered}
K=K_{F,M},\quad D_{\mathrm{HKT}}=8,\quad
u_j=\ell_{j,p,M},\quad A_E=1,\ B_E=0,\ h_4=1,\\
\rho=p^{-1/(p-1)},\qquad
E^*=\rho/\max(|u_1|_p,|u_2|_p)=p^{1-1/(p-1)}>1,\\
d=\max\{1,8/\log E^*\},\quad
h_j=\widehat h_{\mathrm{HKT}}(Q_{j,p,M}),\quad a_j=\max(1,h_j),\\
g=\max\{1,h_4,\log h_1,\log h_2,\log d\}.
\end{gathered}
\tag{3.3}
$$

严格圆盘条件是 $|u_j|_p=p^{-1}<\rho$。原文的 Lutz–Weil 坐标给出
$\phi^2(u_j)=1/x(Q_{j,p,M})$、$\phi(u_j)/\phi'(u_j)=-x(Q_{j,p,M})/y(Q_{j,p,M})$，均在 $K$ 的当前局部像内。由 $dx/(2y)=du$，对数规范一致。$\sqrt2$ 只在误差目标中出现，不是 HKT 系数或点坐标的附加域要求。

原文页 241 的 $h$ 为射影高度，其页 242 的 $\widehat h_{\mathrm{HKT}}$ 为 $\frac12\lim 4^{-n}h([2^n]Q)$。本整方程给出 $h(x:y:1)=\frac32h(x)+O_{E_0}(1)$：有限地方在 $|x|>1$ 时有 $|y|=|x|^{3/2}$，否则两者均不超过 $1$；无穷地方由 $y^2=x^3-x$ 得到同一有界差。因此 $h_j=\frac32\widehat h(Q_{j,p,M})$，由定理 2.1

$$
0<h_j\le C_F(1+M),\qquad
a_1a_2\le C_F(1+M)^2,\qquad
g\le C_F(1+\log(1+M)).
\tag{3.4}
$$

若 $\alpha\beta\ne0$，取 $\eta=-\alpha/\beta\in\mathbb Q(i)\subset K$、$\Delta=\eta u_1-u_2=-L_{p,M}/\beta\ne0$。有 $h_3=\max(1,h(\eta))\le1+\log S$。原 Corollary 2.1 正给

$$
|\Delta|_p>
\exp\{-1.16\cdot10^{35}a_1a_2h_3g^3d^6\log E^*\}.
\tag{3.5}
$$

加回 $v_p(\beta)\log p\le\frac12\log|\beta|^2\le\frac12\log S$，得到 (3.1)。$p$ 只在固定有限 $F$ 中变化，可取共同 $C_F$。若一个系数为零，另一个为 $a\ne0$，则直接有
$v_p(L_{p,M})=1+v_p(a)$，且 $2v_p(a)\log p\le\log|a|^2\le\log S$；扩大同一常数即可。这没有对椭圆对数本身使用 Liouville，也没有使用未发表的多对数界。证毕。

**定理 3.2（固定有限支持上的全部关系预算）。** 对每个非空有限 $F\subset\mathscr P$，存在整数 $M_F$，使定理 2.1 对任意 $M\ge M_F$ 构造的一次固定数据，对全部非零 $x=\alpha+\beta u$ 同时满足

$$
\begin{gathered}
S_p(x)\ne O,\qquad
S_p(x)\in U_p(1)\ \Longleftrightarrow\ x\in I_p\quad(p\in F),\\
D_F(x)\le D_F^*(x)+AS/100,\qquad D_F(x)\le AS.
\end{gathered}
\tag{3.6}
$$

此外，固定任意 $0<c<1$，可使每个 $p\in F$ 在短范围 $S\le p^{cM}$ 且 $x\in I_p$ 时精确保留旧深度；在长范围 $S\ge p^{cM}$ 时整个新深度满足 $b_p(x)\log p\le\epsilon_p S$，其中 $\epsilon_p>0$ 在关系之前指定且 $\sum_{p\in F}\epsilon_p\le A/100$。

证明。点差在第一形式群，故 $[q]P_{j,M}$ 的约化仍为原 $\widetilde T_{j,p}$。于是关系约化仍是 $\theta_{I_p}(x+I_p)$，入口当且仅当 $x\in I_p$。全局模挠独立性说明原关系点非零；也可在入口时用定理 3.1 的非零对数，不入口时用非零约化。

置 $z_p=\iota_p(\alpha+\beta\sqrt2)\ne0$。系数在惰性 $p$ 处为整，由 (2.2) 得

$$
v_p(L_{p,M}(x)-r_ppz_p)\ge M+1,\qquad
v_p(r_ppz_p)\le1+\frac{\log(3S)}{\log p}.
\tag{3.7}
$$

第二个界使用的正是 (1.5) 的 $M_0$ 范数。若 $S\le p^{cM}$ 且 $(1-c)M>\log3/\log p$，右侧严格小于 $M+1$。强三角不等式遂给
$v_p(L_{p,M})=1+v_p(z_p)$，即旧的完整深度。这对全部短关系同时成立。

记 $H(M)=(1+M)^2(1+\log(1+M))^3$。函数 $(1+\log S)/S$ 在 $S\ge1$ 单调不增，所以定理 3.1 对全部 $S\ge p^{cM}$ 给出

$$
\frac{b_p(x)\log p}{S}
\le C_F H(M)\frac{1+cM\log p}{p^{cM}}\longrightarrow0.
\tag{3.8}
$$

非入口项为零，亦满足此界。分子是多项式乘对数幂，分母指数增长，故对预定的每个 $\epsilon_p$，存在使所有以后 $M$ 均满足 (3.8) 不超过 $\epsilon_p$ 的阈值。

现在先取一个对全部 $F$ 共用的实数 $S_0\ge1$，使

$$
(4\gamma+A/100)S+\log(3S)\le AS\qquad(S\ge S_0).
\tag{3.9}
$$

因 $4\gamma+A/100<A$，它存在，且只依赖原参数。再取 $M_F$ 为有限多个阈值的上界，使每个 $p\in F$ 同时满足 (3.8)、$(1-c)M>\log3/\log p$ 和 $p^{cM}\ge S_0$。定理 2.1、3.1 的常数在这次选精度之前已与 $M$ 分离，所以没有循环依赖。现固定任一这样的 $M$、同一对点和全部嵌入，随后才允许任意关系输入。

逐项把短关系深度直接保留，把长关系的整个深度支付为 $\epsilon_p S$，得到 (3.6) 的第一个预算。若 $S<S_0$，全部 $p\in F$ 都在短范围，故 $D_F=D_F^*\le AS$，这里必须使用旧的完整受限预算。若 $S\ge S_0$，由 (1.5)、(3.9) 得

$$
D_F\le D_F^*+AS/100\le4\gamma S+\log(3S)+AS/100\le AS.
\tag{3.10}
$$

这没有扩大原 $r_0$、改变截止或删除原支持；也没有用大 $S$ 的吸收去代替小 $S$ 的证明。证毕。

用白话说，精度只选一次。它足以保存所有规模较小的关系；其余无限多条关系由已发表的对数估计统一支付。支付范围是清单 $F$，共同点在别的素数产生什么贡献不在这个结论之内。

## 4. 共同整数入口与有限三次尾部前缀

**定理 4.1（原入口指标在共同点上逐项不变）。** 定理 3.2 的同一对点对每个 $p\in F$ 和每个非零整数 $n$ 满足

$$
\begin{gathered}
\bigl(\sigma_p([qn]P_j)\in U_p(1)\text{ 对 }j=1,2\bigr)
\ \Longleftrightarrow\ r_p\mid n,\\
\log\sigma_p([qn]P_j)=\frac{n}{r_p}\ell_{j,p,M}\quad(r_p\mid n),\\
b_p(\sigma_p([qn]P_j))=1+v_p(n)\quad(r_p\mid n),\\
\rho_p=r_p,\qquad c_p=r_p^2,\qquad d_p=1.
\end{gathered}
\tag{4.1}
$$

证明。两个 $[q]P_j$ 的约化仍为原 $\widetilde T_{j,p}$。同时被 $n$ 消去等价于 $n$ 消去其共同生成的 $E_0[r_p]\simeq(\mathbb Z/r_p)^2$，恰为 $r_p\mid n$；不要求两个生成元分别都有阶 $r_p$。进入后，精确的全局等式是 $[qn]P_j=[n/r_p]Q_{j,p,M}$，所以对数为 (4.1) 第二行。因 $v_p(\ell_{j,p,M})=1$、$p\nmid r_p$，深度为 $1+v_p(n)$；在 $n=r_p$ 时为 $1$。共同像群阶仍为 $r_p^2$，给出其余指标。逼近后的对数并非精确的 $np$ 或 $np\iota_p(\sqrt2)$；所需结论只使用其单位深度。证毕。

**定理 4.2（有限清单的正三次前缀及量词）。** 对实数 $R_{\max}\ge1$，令 $F_{R_{\max}}$ 为原支持中全部 $r_p\le R_{\max}$ 的地方。它有限。若它非空，可用同一八次域内的一对点，实现该清单上的全部 Gaussian 关系预算，并使对每个 $1\le R\le R_{\max}$，

$$
\begin{aligned}
V_{F_{R_{\max}}}(R)
&:=\sum_{\substack{p\in F_{R_{\max}}\\p>\max(H_{\mathrm{cut}},R^2),\ \rho_p\le R}}
d_p\log p\\
&=V_{\mathrm{sel}}(R)
=\frac{4\gamma}{21\zeta(3)}R^3
 +O_{q,A,H_{\mathrm{cut}},r_0}\bigl(R^2+(\log R)^6\bigr).
\end{aligned}
\tag{4.2}
$$

最后一式表示原渐近式在这个有限区间的限制；对原参数所决定的充分大 $R$，其值为正。量词是每个 $R_{\max}$ 各存在域和点对，域与高度允许变化。

证明。每个整数 $r\le R_{\max}$ 只有 RG004 (75.4) 给出的有限多个理想，故清单有限。定理 4.1 保留清单内每个 $\rho_p,c_p,d_p$。当 $R\le R_{\max}$，原和中所有 $\rho_p=r_p\le R$ 的地方已全部在清单中，故第一处等号逐项成立。直接复用 RG004 (75.10) 得其余断言，不重新选择素数或证明三次计数。其正主项压过原误差，给出足够大阶段的正性。

若 $F_{R_{\max}}$ 为空，或一般地 $F=\varnothing$，则独立取 $P_1=P_2=O$、$K=\mathbb Q(i)$，没有局部嵌入要求，预算与清单尾部皆为零；此平凡情形不附加模挠独立或次数恰八的断言。对任何一个固定有限清单，$R$ 充分大后所有 $p\le R^2$，其尾部实际为零。因此 (4.2) 不把一个有限清单的点对变成具有无限正三次尾部的固定来源。证毕。

## 5. 有界共同来源的有限交性质与精确目标障碍

**定义 5.1（统一界内的候选及局部条件）。** 固定整数 $D\ge2$、实数 $B\ge0$，在一个固定 $\overline{\mathbb Q}$ 中令

$$
\mathcal C_{D,B}=\{\boldsymbol P=(P_1,P_2)\in E_0(\overline{\mathbb Q})^2:
[K(\boldsymbol P):\mathbb Q]\le D,\ 
h_x(P_1)+h_x(P_2)\le B\},\quad
K(\boldsymbol P)=\mathbb Q(i,P_1,P_2).
\tag{5.1}
$$

这里 joint degree 指坐标和 $i$ 的共同域次数，界对移动的域也一致。对每个选定 $p$，可选嵌入集合为
$\mathcal E_p(\boldsymbol P)=\operatorname{Hom}_{\mathbb Q(i)}(K(\boldsymbol P),L_p)$，可能为空。局部条件 $C_a$ 可对 $\boldsymbol P$ 以及有限多个 $p$ 的嵌入作任意谓词要求；同一地方在所有条件中共用一个嵌入。索引允许含 $(p,m)$ 的逼近要求，也允许含有限多个地方的联合预算。

**定理 5.2（有限候选的共同嵌入消费者）。** 对定义 5.1 的一个可数地方集和一族可数局部条件，假设任意有限条件清单及任意有限地方清单，都能由 $\mathcal C_{D,B}$ 中同一候选和清单内每个地方的一个共同嵌入同时满足。则存在一个固定 $\boldsymbol P\in\mathcal C_{D,B}$ 及每个地方一个固定嵌入，使全部条件同时成立。无需条件关于坐标的拓扑闭性。

特别地，给每个地方固定目标 $\boldsymbol T_p\in E_0(L_p)^2$，并取该空间上的任一分离的 $p$ 进度量 $\operatorname{dist}_p$。若任意有限 $(p,m)$ 清单都能在同一 $D,B$ 界内、每个 $p$ 共用一个嵌入地满足 $\operatorname{dist}_p(\sigma_p(\boldsymbol P),\boldsymbol T_p)\le p^{-m}$，则存在一个固定共同来源和每个 $p$ 的固定嵌入，精确满足 $\sigma_p(\boldsymbol P)=\boldsymbol T_p$。

证明。这里的经典有限性输入是 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.5.10–5.11，印刷页 232–233，及 VIII.6 的绝对对数高度定义，印刷页 234](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。VIII.5.11 对 $\mathbb P^N(\overline{\mathbb Q})$ 给出绝对高度和最小定义域绝对次数同时有界时的有限性；VIII.5.10 保证共轭不改变高度。它不是“一个固定域内有限”才适用的结论。

本处每个 $x(P_j)$ 的次数至多 $D$、高度至多 $B$，故其可能值有限；给定横坐标，纵坐标至多两个，再加原点，得到 $\mathcal C_{D,B}$ 有限。若改用统一 $\widehat h$ 界，VIII.9.3(e) 的域无关比较也导出同样的有限候选集。对每个候选，$\mathcal E_p$ 有限，大小至多 $[K:\mathbb Q(i)]$：选取本原元后，嵌入由其最小多项式的一个根决定。

将地方与条件分别编号。对第 $n$ 阶段，要求前 $n$ 个条件及前 $n$ 个地方，并补齐这些条件的有限地方支持；由假设选一个实现。这些阶段不必嵌套选点。候选总数有限，故有一个候选出现于无穷多个阶段；只保留这些阶段，编号仍无界。在这个固定候选上，第一个地方的嵌入只有有限个，选一个出现无穷次的嵌入并限制阶段；再对第二个地方如此，依次进行。每个地方都有固定嵌入，因为阶段充分晚时都要求它存在。

取对角阶段列，使第 $k$ 个所取阶段至少为 $k$，并在前 $k$ 个地方的嵌入上已稳定。任一条件的索引和有限地方支持都在某个有限编号以内；在充分晚的对角阶段中，该条件已被满足，且它看到的候选和嵌入与最终选择完全相同，所以最终选择满足它。证明只用有限个离散选择的稳定性，没有把极限的不等式方向或开条件偷换成闭条件。对于特别情形，每个固定 $p$ 的距离不超过全部 $p^{-m}$，故为零，分离性给出精确相等；任意有限地方的嵌入存在性可由补入这些地方的 $m=1$ 条件保证。证毕。

用白话说，次数和高度同时封顶后，可选的全球点对真的只有有限多个。再要求每个地方始终使用同一个嵌入，有限清单的兼容性才可以传到全部清单；仅有每个地方各自可解并不够。

**命题 5.3（精确非代数目标排斥统一双界）。** 固定一个原支持 $p$ 及一个 $P^*_{j,p}$。不可能存在统一的 $D,B$，使任意精度 $m$ 都能由共同域绝对次数至多 $D$、$h_x(P)\le B$ 的代数点，经某个保持 $i$ 的嵌入到 $L_p$，满足

$$
v_p(x(\sigma(P))-x(P^*_{j,p}))\ge m.
\tag{5.2}
$$

更精确地，每个固定 $D,B$ 的可达精度有一个有限上界；若次数统一有界而精度趋于无穷，高度必逃出每个固定界。此结论不包含任何线性高度下界。

证明。RG004 定理 76.1 给出 $x(P^*_{j,p})$ 非代数，其非代数性输入为 Fuchs–Pham，[arXiv:1412.1248v2，Theorem 2.3](https://arxiv.org/abs/1412.1248v2) 的代数椭圆点非零对数结论。这里仅调用该精确结论，不从它提取定量逼近估计。由定理 5.2 证明中的 Northcott 输入，满足这两个界的点有限；每点到 $L_p$ 的嵌入亦有限。它们的横坐标像构成有限集合，且均不等于目标。所有非零差的 $v_p$ 因而有有限最大值，排除更高精度。若存在一个有界高度的无穷高精度子列，就与这个最大值矛盾。这只给每个 $D,B$ 下某个有限阈值，未给阈值关于 $B$ 的增长率。证毕。

定理 2.1 对固定非空 $F$ 的次数始终为八，而其直接坐标精度随 $M$ 无界。因此该构造的高度必须无界；$O_F(1+M)$ 是上界，不是线性下界。精确逼近有这个障碍，不能据此否定只要求相同约化核与预算的较弱共同实现，因为后者没有要求横坐标趋于 $x(P^*_{j,p})$。

**命题 5.4（次数一的有限可解仍可高度逃逸）。** 对任一固定素数 $p$，存在一族单地方精度条件，使每个有限子族都有次数一的解，而不存在满足全部条件的代数数。

证明。$\mathbb Z_p$ 不可数而其中代数于 $\mathbb Q$ 的数可数，故可取 $\xi\in\mathbb Z_p\setminus\overline{\mathbb Q}$。条件为 $v_p(a-\xi)\ge m$，$m\ge1$。写 $\xi=\sum_{k\ge0}c_kp^k$，$0\le c_k<p$。对有限清单，令 $N$ 为最大精度，取整数 $a_N=\sum_{k<N}c_kp^k$，即有全部条件，次数为一且 $h(a_N)\le N\log p$。若一个代数数及其固定嵌入满足全部条件，分离性强迫它等于 $\xi$，矛盾。即使允许每个精度另选该代数数的嵌入，嵌入只有有限个，无穷精度中一个会重复，仍矛盾。

非代数 $\xi$ 的数字不可能最终全零，所以 $a_N$ 作为非负整数单调且无界，$h(a_N)\to\infty$。这给出固定一个 $p$、甚至次数一时，有限可解也不能替代统一高度条件的具体反例。它针对精确目标，不是原弱关系实现的反例。证毕。

## 6. 弱关系预算的条件性全球升级

**定义 6.1（弱实现的有限要求）。** 对全体原选定支持 $\mathscr P$ 保持定义 1.1。对任意候选及一个局部嵌入，将 (1.3) 关系的扩展深度定义为：非入口取 $0$，非零形式点取其有限深度，零点 $O$ 取 $+\infty$。记为 $\bar b_p(x)$。对有限 $F\subset\mathscr P$、有限 $Z\subset\mathcal R\setminus\{0\}$，弱要求是用同一候选和每个 $p\in F$ 的一个共同嵌入，使对所有 $x\in Z$ 同时有

$$
S_p(x)\in U_p(1)\ \Longleftrightarrow\ x\in I_p\quad(p\in F),\qquad
\sum_{p\in F}\bar b_p(x)\log p\le A(|\alpha|^2+|\beta|^2).
\tag{6.1}
$$

扩展深度使有限预算本身排除零关系，不能把零点伪记为深度零。

**定理 6.2（统一 joint degree 与高度足以升级弱关系）。** 假设存在同一 $D,B$，使每个有限 $F\subset\mathscr P$ 及每个有限关系清单 $Z$ 的弱要求 (6.1)，均能由 $\mathcal C_{D,B}$ 中的一对点同时实现。则存在一个固定 $K=\mathbb Q(i,P_1,P_2)$、同一对全球代数点和每个 $p\in\mathscr P$ 的固定共同嵌入，使全部非零 Gaussian 关系都满足原入口指标，且

$$
\sum_{p\in\mathscr P}b_p(x)\log p\le AS.
\tag{6.2}
$$

这个和仅遍历原选定支持。两点模挠独立；每个选定 $p$ 的共同整数入口仍为 $r_p$、共同约化 $\mathcal O$ 像群阶仍为 $r_p^2$。仅凭前件不额外断言 $d_p=1$。

证明。支持、Gaussian 关系及它们的有限子集均可数。把每个单独的入口条件以及每个 $(F,x)$ 的非负部分和预算作为定理 5.2 的条件；其地方支持分别是单点和有限 $F$。任意有限组条件只涉及有限地方并有限关系，其并集正由前件同时实现，且同一地方共用一个嵌入。定理 5.2 遂给固定候选和所有固定嵌入，满足全部条件。

对每个 $x\ne0$，所有有限 $F$ 上的非负部分和均不超过 $AS$，取上确界便得 (6.2)。此外入口集合恰为 $\mathscr P(x)$，它由 (1.5) 后的理想整除性已知有限，故每条关系的所选支持和实际有限。对任一 $p$ 使用单点预算可排除关系为 $O$：若它为 $O$，入口成立，深度为无穷，违背有限预算。由嵌入单射，全球关系也不为 $O$；若某个非零关系为挠点，将关系乘以其整数阶，又得到一条非零 Gaussian 关系等于 $O$，矛盾。因此两点模挠独立。

固定 $p$，由全部入口条件，约化映射

$$
\mathcal R\longrightarrow\widetilde E_0(\mathbb F_{p^2}),\qquad
\alpha+\beta u\longmapsto
\widetilde{\sigma_p([q]([\alpha]P_1+[\beta]P_2))}
\tag{6.3}
$$

的核恰为 $I_p$。故共同像是左 $\mathcal O$ 模 $\mathcal R/I_p\simeq\mathcal O/(r_p)$，其阶 $r_p^2$，加法指数 $r_p$；同时消去两个约化的最小正整数就是 $r_p$。预算与入口条件未指定首层后的精确对数，故没有据此证明 $d_p=1$。若希望也保留它，可以把两个 $[qr_p]P_j$ 的深度等于 $1$ 加为逐地方有限条件；在加强后的同一统一界前件下，定理 5.2 原样传递这些条件。证毕。

用白话说，较弱的关系实现并不需要复制那些非代数坐标。它需要的是：所有有限清单都能在同一份次数和高度预算内实现，而且同一地方不能给不同关系换嵌入。统一双界若成立，就把不断换点的有限实现压缩为一对固定点。定理 3.2 已给出每个有限支持的共同来源，但没有给出对所有有限支持共用的高度界；因此它没有证明定理 6.2 的前件。

**命题 6.3（结论的范围）。** 定理 2.1–4.2 与定理 6.2 的条件性升级，均不判定原固定八次全实域及其 CM 扩域内的原点对，不提供原 Galois 运输，也不判定 RG004 §70 的原 $V_H(R)=o(q_H^2R^3)$。精确非代数性和弱关系实现的共同来源问题仍是不同命题。

证明。定理 2.1 的域与点在选择有限 $F$ 后才产生；定理 4.2 对每个 $R_{\max}$ 允许重新选择，量词为 $\forall R_{\max}\,\exists(K,P_1,P_2)$。它没有给出 $\exists(K,P_1,P_2)\,\forall R_{\max}$，且任一固定有限清单的尾部最终为零。定理 6.2 所需的统一高度前件没有从这些有限构造推出；即使另外证成，它的结论也只计算选定支持，并未将点对识别为原点对或约束清单外素数。因此缺少把这些结论代入原固定来源与原全支持量的假设，不能由它们判断原小量。命题 5.3 仅否定精确目标的统一双界，不否定 (6.1) 的弱前件。这些都是定理中对象、支持与量词的明确限制。证毕。

## 追加锚（本行以下为增补区）

## 7. 固定八次来源的全关系一致尾部障碍

**定义 7.1（固定嵌入下的全关系一致尾部紧性）。** 令 $K\supset\mathbb Q(i)$ 为固定数域，$P_1,P_2\in E(K)$ 在 $\mathcal O=\mathbb Z[i]$ 模意义下模挠独立，其中 $E:y^2=x^3-x$、$[i](x,y)=(-x,iy)$。先固定整数 $q\ge1$，并对每个有理素数 $p>5$ 固定一个嵌入 $\sigma_p:K\hookrightarrow\overline{\mathbb Q}_p$，以后所有关系共用它。取 $v_p(p)=1$。对非零 $z=(\alpha,\beta)\in\mathcal O^2$，定义

$$
Q_z=[q]([\alpha]P_1+[\beta]P_2),\qquad
S(z)=|\alpha|^2+|\beta|^2,
\tag{7.1}
$$

以及选定地方的完整深度

$$
b_p(Q_z)=
\begin{cases}
v_p(t(\sigma_p Q_z)),&\sigma_p Q_z\text{ 约化为 }O,\\
0,&\text{否则},
\end{cases}
\qquad t=-x/y.
\tag{7.2}
$$

模挠独立性保证 $Q_z$ 非挠，故不是 $O$ 或二挠点，式中形式参数非零且有定义。每条关系只在有限多个素数有正深度，因为一个固定代数点的分母支持有限。称这组固定数据满足 UHT，若

$$
\forall\varepsilon>0\ \exists\mathcal F\subset\{\text{有理素数}\}\text{ 有限}
\ \forall z\in\mathcal O^2\setminus\{0\},\qquad
\sum_{\substack{p>5\\p\notin\mathcal F}}b_p(Q_z)\log p
\le\varepsilon q^2S(z).
\tag{7.3}
$$

清单 $\mathcal F$ 可依赖固定来源、$q$、整族嵌入和 $\varepsilon$，但必须在关系 $z$ 之前选定。这里每个 $p$ 只有一个选定地方，并非全部地方的加权和。

**定理 7.2（同一代数轨道排斥 UHT）。** 固定

$$
K=\mathbb Q(i,\sqrt6,\sqrt{15}),\qquad
P_1=(2,\sqrt6),\qquad P_2=(4,2\sqrt{15})\in E(K).
\tag{7.4}
$$

则 $[K:\mathbb Q]=8$，点对在 $\mathcal O$ 模意义下模挠独立。对每个固定整数 $q\ge1$、每族事先固定的嵌入 $\sigma_p$，以及每个固定有限有理素数集 $\mathcal F$，有完整极限

$$
\lim_{n\to\infty}
\frac{1}{q^2n^2}
\sum_{\substack{p>5\\p\notin\mathcal F}}
b_p([qn]P_1)\log p
=\widehat h_E(P_1)>0.
\tag{7.5}
$$

因此同一来源对全部这些 $q$ 和嵌入选择均不满足 UHT。这里 $\widehat h_E$ 始终采用 $2\widehat h_E=h_x+O_E(1)$ 的规范。

证明。首先核对来源与非挠性。将 $(-1)^a6^b15^c$ 为有理数平方的关系取 $a,b,c\in\{0,1\}$；在 $2$ 和 $5$ 处的赋值分别迫使 $b=0,c=0$，再由负数不是有理平方得 $a=0$。故三个平方类独立，逐次添加平方根给出八次多二次扩张；在 $\mathbb Q(i)$ 上可以分别翻转 $\sqrt6$ 和 $\sqrt{15}$ 而固定另一个根。坐标代入曲线方程即验证两个点属于 $E(K)$。

对 $d=6,15$，置 $E_d:Y^2=X^3-d^2X$。保持原点的同构

$$
E\longrightarrow E_d,\qquad (x,y)\longmapsto(dx,d\sqrt d\,y)
\tag{7.6}
$$

分别将 $P_1,P_2$ 送到有理点 $A_6=(12,36)$、$A_{15}=(60,450)$。由切线斜率所得的倍点公式，在 $Y\ne0$ 时为

$$
X([2](X,Y))=\frac{(X^2+d^2)^2}{4X(X^2-d^2)},\qquad
X([2]A_6)=\frac{25}{4},\qquad
X([2]A_{15})=\frac{289}{16}.
\tag{7.7}
$$

两倍点均不是 $O$，横坐标均非整数。经典输入 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.7.2(a)，印刷页 240](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 断言整系数短 Weierstrass 方程上的非零有理挠点具有整坐标；应用于这两个两倍点，便排除 $A_6,A_{15}$ 为挠点。因此 $P_1,P_2$ 非挠，所有非零整数倍也非挠。

若 $[\alpha]P_1+[\beta]P_2$ 为挠点，分别施加上述两个固定 $i$ 的符号自同构并作差，可得 $[2\alpha]P_1$、$[2\beta]P_2$ 都为挠点。若 $\alpha\ne0$，再施加 $[\bar\alpha]$，得到非零整数倍 $[2|\alpha|^2]P_1$ 为挠点，矛盾；同理 $\beta\ne0$ 也不可能。这证明模挠独立性，也排除了定义 7.1 中任一非零关系等于 $O$ 的情形。

以下只用同一个 $P_1$。记 $L=\mathbb Q(\sqrt6)$。其非平凡自同构将 $P_1$ 送到 $-P_1$，与整数乘法交换。因此对每个 $m\ne0$，非零倍点 $[m]P_1$ 的横坐标被该自同构固定，即

$$
x([m]P_1)\in\mathbb Q.
\tag{7.8}
$$

这些点的 $x,y$ 都非零：$y=0$ 的点是二挠点，而 $x=0$ 在本方程上也迫使 $y=0$。固定 $q$ 后，置 $Q_n=[qn]P_1$、$x_n=x(Q_n)\in\mathbb Q^\times$、$h_n=h(x_n)$。由 [Silverman VIII.9.3(b)、(d)、(e)，印刷页 248–249](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，

$$
\widehat h_E(P_1)>0,\qquad
h_n=2q^2n^2\widehat h_E(P_1)+O_E(1)\longrightarrow\infty.
\tag{7.9}
$$

比较常数只依赖固定曲线及坐标函数 $x$；在这里不随 $n,q$ 或地方变化。

现在把每个选定地方的读数准确接到有理横坐标。对 $p>5$，本整模型的判别式 $64$ 是单位。其好约化核的形式参数识别见 [Silverman IV.1、VII.2.1–2.2，印刷页 116–119、188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。具体地，若 $v_p(x_n)<0$，方程中 $x_n^3$ 的赋值严格小于 $x_n$，所以

$$
2v_p(y(Q_n))=3v_p(x_n),\qquad
v_p(t(Q_n))=-\tfrac12v_p(x_n)>0.
\tag{7.10}
$$

此时射影约化为 $O$。若 $v_p(x_n)\ge0$，方程又给出 $v_p(y(Q_n))\ge0$，故点有仿射约化，不是 $O$。由于 $x_n$ 有理，任意 $\sigma_p$ 都有同一 $v_p(x_n)$；因此逐个选定嵌入准确有

$$
b_p(Q_n)\log p=\tfrac12\log\max(1,|x_n|_p),\qquad
|p|_p=p^{-1}.
\tag{7.11}
$$

特别地，没有乘上局部次数，也没有先把若干地方的预算分给一个地方。若用全体地方高度核对规范化，则每个 $w\mid p$ 都有相同的右端，权重为 $[K_w:\mathbb Q_p]/8$，其和为 $1$，所以加权读数恰等于选定读数。这里的相等是 (7.8) 的后果，不是一般代数点的性质。

此步只用坐标与约化，没有使用形式对数的等距性。在一般分歧扩张中，若把对数用于深度等式，所引 [Silverman IV.6.3–6.4，印刷页 131–132](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的保赋值范围须满足 $v_p(t)>1/(p-1)$；仅在第一形式层不能无条件推出这个严格阈值。

对每个有理地方定义非负量

$$
\ell_{p,n}=\tfrac12\log\max(1,|x_n|_p),\qquad
\ell_{\infty,n}=\tfrac12\log\max(1,|x_n|).
\tag{7.12}
$$

关键经典输入为 [Silverman IX.3.1，印刷页 276，以及 IX.2 的距离定义，印刷页 273](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)。在该定理中取曲线 $E/L$、固定目标 $O$、非恒定偶函数 $f=x$，并在每个所需的固定地方应用。$E(L)$ 因含非挠 $P_1$ 而无限，$Q_n\in E(L)$，且 (7.9) 保证其 $h_f=h_n$ 趋于无穷，故全部假设满足。因 $1/x$ 仅在 $O$ 有二阶零点，可以准确选取距离

$$
\delta_v(Q,O)=\min(1,|x(Q)|_v^{-1/2}).
\tag{7.13}
$$

在有限地方取 $|p|_v=p^{-1}$，在实地方取通常绝对值；(7.8) 使其值只取决于下方有理地方。IX.3.1 于是直接给出

$$
\frac{\log\delta_v(Q_n,O)}{h_n}\longrightarrow0,
\qquad
\ell_{v,n}=o(h_n)=o(q^2n^2)
\quad\text{对每个固定 }v.
\tag{7.14}
$$

这里 $\log\delta_v=-\ell_{v,n}$。尤其，对每个有限有理地方清单 $\mathcal A$ 和每个 $\eta>0$，存在 $N=N(E,P_1,q,\mathcal A,\eta)$，使全部 $n\ge N$ 均满足

$$
\sum_{v\in\mathcal A}\ell_{v,n}\le\eta q^2n^2.
\tag{7.15}
$$

这个阈值对全部 $\sigma_p$ 选择通用，因为其读数只取决于有理数 $x_n$；未从定性逼近输入提取有效速率。式 (7.15) 包含任意固定有限素数及无穷地方，而不是只给一个子列。

最后，写 $x_n=a_n/c_n$，其中 $a_n,c_n$ 互素、$c_n>0$。有理数高度定义直接给出

$$
\tfrac12h_n=\ell_{\infty,n}+\sum_p\ell_{p,n},\qquad
\sum_p\ell_{p,n}=\tfrac12\log c_n.
\tag{7.16}
$$

对固定 $\mathcal F$，令 $\mathcal A_f=\mathcal F\cup\{2,3,5\}$。由 (7.11)、(7.16) 准确有

$$
\sum_{\substack{p>5\\p\notin\mathcal F}}b_p(Q_n)\log p
=\tfrac12h_n-\ell_{\infty,n}-\sum_{p\in\mathcal A_f}\ell_{p,n}.
\tag{7.17}
$$

将 (7.9)、(7.14)–(7.15) 代入，便得 (7.5)。这同时证明有限清单中每个地方的贡献可以移除，以及所余质量的准确规范常数为 $\widehat h_E(P_1)$。

取 $\varepsilon=\widehat h_E(P_1)/2$。无论先选哪个有限 $\mathcal F$，(7.5) 都使全部充分大的 $n$ 在关系 $(\alpha,\beta)=(n,0)$、$S=n^2$ 上违反 (7.3)。这证明 UHT 失败。所用经典逼近、挠点整性和高度定理均只是这个固定来源消费者的中间输入；结论是 repo-derived 应用，不主张文献优先性。证毕。

用白话说，一对固定代数点已经足以排除这项过强要求：沿第一个点不断取倍点，任意事先删除的有限素数清单之外，仍留下与倍数平方同阶的分母质量。每个固定地方单独占比都趋于零，不能据此把一个有限清单选成对所有关系都有效的清单。这没有改变 §§2–6 的有限共同来源结论及其量词。

## 8. 原同点对的联合小像稀疏性充分桥

**定义 8.1（原固定来源的实际小像集合）。** 本节恢复 [RG004 定义 68.1、定理 68.2、定义 70.1](UPPM_RG_004_CM_ANNIHILATORS_AND_GALOIS_DENOMINATOR_RELATIONS.md#68-原周期后的实际-cm-像群阶与全部首入口质量) 的全部原数据：$F=\mathbb Q(a,b,c)$ 为原八次全实域，$K=F(i)$、$[K:\mathbb Q]=16$，$P_1,P_2$ 指原固定点对。这里不使用 (7.4) 的新点对。固定整数 $H\ge7,M\ge1$，并在 $R\to\infty$ 时保持同一个 $q=q_H=q(H,H;M)$。原共同入口 $n_p,t_p$、完整深度、实际 CM 像群及其群阶为

$$
\rho_p=\frac{n_p}{\gcd(n_p,q)},\qquad d_p=t_p+v_p(q),\qquad
C_w=\mathcal O\,\overline{[q]P_1}+\mathcal O\,\overline{[q]P_2},\qquad
c_p=\#C_w\quad(w\mid v\mid p>H).
\tag{8.1}
$$

全部地方、约化和 Galois 运输均按原接口保留。特别地，直接调用 RG004 (68.5)、(68.8)、(68.17)、(68.21)：$C_w$ 在地方运输下同构，$c_p$ 与 $w$ 无关，$\exp C_w=\rho_p$、$\rho_p\le c_p\le\rho_p^2$，且

$$
\begin{gathered}
\sum_{w\mid v}\frac{f_w}{16}=\frac{f_v}{8},\qquad
\sum_{w\mid p}\frac{f_w}{16}=1,\\
d_p\log p\le64h_0q^2\sqrt{c_p}+16\log2.
\end{gathered}
\tag{8.2}
$$

$h_0>0$ 为原四方向准确高度中的常数。这些是既有输入；逐素数界已经支付所有原地方及全部 $1,\ldots,d_p$ 层，其常数保留各地方分别支付的费用。定义

$$
T_R=\{p>\max(H,R^2):\rho_p\le R\},\qquad
J_H(R)=\sum_{p\in T_R}\sqrt{c_p}.
\tag{8.3}
$$

这些集合有限，因为 $p\in T_R$ 蕴涵 $c_p\le R^2$，而原 (68.18) 已给出该群阶范围的有限分母支持。原尾部完整地等于 $V_H(R)=\sum_{p\in T_R}d_p\log p$。

**定理 8.2（不含深度的稀疏计数足以支付原完整尾部）。** 对定义 8.1 的同一原数据，有

$$
\begin{aligned}
0\le V_H(R)
&\le64h_0q^2J_H(R)+(16\log2)\#T_R,\\
\#T_R&\le J_H(R)\le R\,\#T_R.
\end{aligned}
\tag{8.4}
$$

因此以下任一算术假设都足以推出原目标 $V_H(R)=o(q^2R^3)$：

$$
J_H(R)=o(R^3),\qquad\text{或特别地}\qquad
\#T_R=o(R^2).
\tag{8.5}
$$

这两个假设均未在此证成；它们只涉及原同点对的共同约化像阶及共同入口指数，不含分母深度或 $\log p$ 权重。

证明。对有限集合 $T_R$ 逐项相加 (8.2)，得到 (8.4) 第一行。由于 $1\le c_p\le\rho_p^2\le R^2$，每项满足 $1\le\sqrt{c_p}\le R$，给出第二行。若第一个假设成立，则

$$
0\le\frac{V_H(R)}{q^2R^3}
\le\left(64h_0+\frac{16\log2}{q^2}\right)\frac{J_H(R)}{R^3}
\longrightarrow0.
\tag{8.6}
$$

若第二个假设成立，则 $J_H(R)\le R\#T_R=o(R^3)$，故也适用刚才的推论。这里 $H,M,q$ 固定；未断言关于移动 $H,M$ 的统一速度。证明从未将 $d_p$ 截成 $1$，也未将 $c_p$ 认作 $\rho_p$。这是既有完整逐素数界的新计数消费者（repo-derived），不是对上述稀疏性假设的证明。证毕。

**命题 8.3（反例与原尾部之间的未决边界）。** 定理 7.2 不判定定义 8.1 的原 $V_H(R)$ 小量，也不判定该原点对的同时小阶陈述；定理 8.2 只给充分条件，不给必要性、与 UHT 的等价或严格分离。

证明。定理 7.2 固定的是八次域 (7.4) 中的新点对，而定义 8.1 固定的是原十六次 CM 扩域内的原点对。其关系族仅为 $(n,0)$，读数为 $[qn]P_1$ 的完整选定素数分母；它既没有控制四个整数系数的 $R^3$ 盒尺度总量，也没有要求同一素数同时消去原两个点的约化。即使第一个点进入形式群，也不能据此推出第二个点同时进入，故不能把 (7.5) 代入 $T_R$ 或原 $d_p$。定理 8.2 的证明只有从 (8.5) 到完整尾部小量的方向，没有反向估计；并且两个来源不同，不能用新来源上的 UHT 失败为原来源建立必要性或逻辑严格性。原 RG004 §70 的完整尾部及 (8.5) 的稀疏性仍各有未证算术义务。证毕。

用白话说，回到原问题后，需要估计的是同一原点对在大素数处共同落入多小的实际有限像，而不是另选点或只观察其中一个点。若这样的素数少到 (8.5) 的程度，已有逐素数界会连任意深的入口一起支付；目前给出的是这条充分桥，尚未给出它所需的稀疏计数。

## 追加锚（本行以下为增补区）

## 9. 同一八次来源的完整四维盒与固定素数尾部

**定义 9.1（共同来源、全盒与局部高度规范）。** 本节始终取 (7.4) 的同一固定数据

$$
E:y^2=x^3-x,\qquad K=\mathbb Q(i,\sqrt6,\sqrt{15}),\qquad
P_1=(2,\sqrt6),\quad P_2=(4,2\sqrt{15}).
\tag{9.1}
$$

直接复用定理 7.2 的八次性、非挠性及 Gaussian 模挠独立性，不另证明这些前件。固定整数 $q\ge1$，并在关系之前对每个 $p>5$ 各固定一次嵌入 $\sigma_p:K\hookrightarrow\overline{\mathbb Q}_p$；其所选地方记为 $v_p^*$。对整数 $L\ge1$，令

$$
\begin{gathered}
B_L=\{z=(a,b,c,d)\in\mathbb Z^4:|a|,|b|,|c|,|d|\le L\}\setminus\{0\},\\
Q_z=[q]\bigl([a+bi]P_1+[c+di]P_2\bigr),\qquad
H_j=\widehat h_E(P_j)>0,\qquad
H_L=\sum_{z\in B_L}\widehat h_E(Q_z).
\end{gathered}
\tag{9.2}
$$

模挠独立性保证全部 $Q_z$ 非挠，也保证 $z\mapsto Q_z$ 单射。$\widehat h_E$ 仍为 $2\widehat h_E=h_x+O_E(1)$ 的绝对规范。对 $v\in M_K$，有限地方取 $|p|_v=p^{-1}$，无穷地方取通常复绝对值，令 $\nu_v=-\log|\cdot|_v$；有限地方 $n_v=[K_v:\mathbb Q_p]=e_vf_v$，复地方 $n_v=2$。使用 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，C.18.1–18.3，印刷页 454–455](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的 $\lambda_v$。原文 C.18.1(ii) 是 $\lambda_v+\frac12\nu_v(x)$ 在 $O$ 处有有限极限；结合 IV.1 的 $x=t^{-2}(1+O(t))$，对参数 $t=-x/y$ 有

$$
\lambda_v(A)=-\log|t(A)|_v+O_v(1)\longrightarrow+\infty
\quad(A\longrightarrow O),\qquad
\widehat h_E(A)=\frac18\sum_{v\in M_K}n_v\lambda_v(A).
\tag{9.3}
$$

第二式正是 C.18.2；$\frac18$ 只用于局部高度之和。以下经典高度与局部邻域事实仅作新盒消费者的中间输入；不主张文献优先性。

**定理 9.2（实际 Galois 系数作用与完整盒的地方恒等式）。** 对任意有理地方 $r$，以及其上任一选定地方 $w$，令
$S_v(L)=\sum_{z\in B_L}\lambda_v(Q_z)$。则每个有限 $L$ 都有

$$
S_w(L)=\frac18\sum_{v\mid r}n_vS_v(L).
\tag{9.4}
$$

特别地，若 $p>5$，定义 7.1 的深度满足

$$
\sum_{z\in B_L}b_p(Q_z)\log p
=S_{v_p^*}(L)
=\frac18\sum_{v\mid p}n_v\sum_{z\in B_L}\lambda_v(Q_z).
\tag{9.5}
$$

这是完整盒的恒等式，没有断言一般单点的选定地方读数等于全部地方平均。

证明。把 $g\in\operatorname{Gal}(K/\mathbb Q)$ 写成
$g(i)=\epsilon i,\ g(\sqrt6)=\delta_1\sqrt6,\ g(\sqrt{15})=\delta_2\sqrt{15}$，其中三个符号独立取 $\pm1$。由于 $g(P_j)=[\delta_j]P_j$，而 $g[i]=[\epsilon i]g$，实际系数作用为

$$
g(Q_z)=Q_{\rho_gz},\qquad
\rho_g(a,b,c,d)=(\delta_1a,\epsilon\delta_1b,\delta_2c,\epsilon\delta_2d).
\tag{9.6}
$$

全部八个作用如下；它们不互换两个固定点，只在四个整数坐标上作所列符号置换。

| $\epsilon$ | $\delta_1$ | $\delta_2$ | $\rho_g(a,b,c,d)$ |
|---|---|---|---|
| $+$ | $+$ | $+$ | $(a,b,c,d)$ |
| $+$ | $+$ | $-$ | $(a,b,-c,-d)$ |
| $+$ | $-$ | $+$ | $(-a,-b,c,d)$ |
| $+$ | $-$ | $-$ | $(-a,-b,-c,-d)$ |
| $-$ | $+$ | $+$ | $(a,-b,c,-d)$ |
| $-$ | $+$ | $-$ | $(a,-b,-c,d)$ |
| $-$ | $-$ | $+$ | $(-a,b,c,-d)$ |
| $-$ | $-$ | $-$ | $(-a,b,-c,d)$ |

每个 $\rho_g$ 都双射地保持 $B_L$。按 $|u|_{g^{-1}v}=|g(u)|_v$ 定义地方运输；因为曲线在 $\mathbb Q$ 上，C.18.1 的唯一性给出
$\lambda_v(gA)=\lambda_{g^{-1}v}(A)$。把 (9.6) 代入有限盒和并重编号，得 $S_v(L)=S_{g^{-1}v}(L)$。Galois 群在 $r$ 上方地方上可迁，且 $\sum_{v\mid r}n_v=8$，故 (9.4) 成立；无穷地方的四个复地方各权 $2$ 也在此式之内。

对 $p>5$，本方程的判别式 $64$ 是单位，故即使完成域有分歧，也是好约化的极小整方程。C.18.3(b) 与 VII.2.1–2.2 给出

$$
\lambda_v(A)=\tfrac12\log\max(1,|x(A)|_v)
=
\begin{cases}
v_p(t(A))\log p,&A\text{ 约化为 }O,\\
0,&\text{否则}.
\end{cases}
\tag{9.7}
$$

这里 $v_p=\nu_v/\log p$，故在分歧完成域可取分数值，没有额外乘 $e_v$；分歧和剩余次数已在 $n_v=e_vf_v$ 中。入口时 $2v_p(y)=3v_p(x)$ 给出该深度，无需形式对数的等距范围。所选嵌入诱导的绝对值就是 $v_p^*$，于是 (9.7)、(9.4) 证明 (9.5)。全程只重排同一盒的关系，没有逐关系更换来源或嵌入。证毕。

**定理 9.3（准确的规范高度多项式）。** 对每个整数 $L\ge1$，

$$
H_L=\frac23q^2(H_1+H_2)L(L+1)(2L+1)^4.
\tag{9.8}
$$

证明。记 $(R_1,R_2,R_3,R_4)=(P_1,[i]P_1,P_2,[i]P_2)$。使用 [Silverman VIII.9.3(a)–(e)，印刷页 248–249](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的双线性配对
$\langle A,B\rangle=\widehat h_E(A+B)-\widehat h_E(A)-\widehat h_E(B)$，即 $\langle A,A\rangle=2\widehat h_E(A)$。因此准确地

$$
\widehat h_E(Q_z)
=q^2\left(\sum_{j=1}^4z_j^2\widehat h_E(R_j)
+ \sum_{j<k}z_jz_k\langle R_j,R_k\rangle\right).
\tag{9.9}
$$

此配对约定下交叉项前没有再乘 $2$。由 $x([i][m]P)=-x([m]P)$，横坐标绝对高度相等；用 VIII.9.3(b)、(e) 并令 $m\to\infty$，得 $\widehat h_E([i]P)=\widehat h_E(P)$。四个对角高度依次为 $H_1,H_1,H_2,H_2$。

把原点加回求和不改变值。全盒允许任一坐标独立变号，故每个 $j\ne k$ 的 $\sum_z z_jz_k$ 为零，无需假定配对正交。置 $N=2L+1$，每个对角和为

$$
\sum_{z\in[-L,L]^4\cap\mathbb Z^4}z_j^2
=N^3\sum_{a=-L}^La^2
=\tfrac13L(L+1)N^4.
\tag{9.10}
$$

把四个对角高度相加即得 (9.8)。另外，(9.9) 给出后文所需的逐点上界

$$
0\le\widehat h_E(Q_z)\le C_0q^2L^2,\qquad
C_0=\sum_j\widehat h_E(R_j)+\sum_{j<k}|\langle R_j,R_k\rangle|,
\tag{9.11}
$$

其中 $C_0$ 只依赖固定点对。这是规范高度本身的盒总和，不是未除局部次数的总和。证毕。

**定理 9.4（每一固定地方的定量装箱余项）。** 对每个固定 $v\in M_K$ 和固定 $q\ge1$，存在在 $L$ 之前固定的常数 $C_{v,q}$，使全部整数 $L\ge1$ 都满足

$$
\sum_{z\in B_L}|\lambda_v(Q_z)|\le C_{v,q}L^{16/3}.
\tag{9.12}
$$

证明。先支付所有地方的负部。由 C.18.1 的连续性、(9.3) 在原点趋于正无穷的性质及射影曲线 $E(K_u)$ 的紧性，每个地方都有固定 $c_u\ge0$ 使 $\lambda_u(A)\ge-c_u$。在有限好约化地方，C.18.3(b) 使它非负，故可取 $c_u=0$。本模型在全部奇素数处好约化，所以只需对
$\mathcal B=\{u:u\mid2\text{ 或 }u\mid\infty\}$ 取非零常数。令
$C_-=\sum_{u\in\mathcal B}n_uc_u$。对每个非零 $A\in E(K)$，(9.3) 于是给出

$$
-c_v\le\lambda_v(A)\le\frac8{n_v}\widehat h_E(A)+d_v,\qquad
d_v=C_-/n_v.
\tag{9.13}
$$

这一步没有把坏地方或复地方的高度误作非负。由 (9.11)，盒内的 $\lambda_v$ 统一有 $O_v(q^2L^2)$ 上包络。

下面只在此固定 $v$ 选择一次邻域常数。C.18.1(ii) 和 [Silverman IV.1 的原点展开，印刷页 115–120；VII.2，印刷页 187–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 提供参数 $t=-x/y$ 的局部图及解析群运算。取原点邻域 $U_0$，使某个固定 $C_v\ge0$ 满足
$|\lambda_v(A)+\log|t(A)|_v|\le C_v$ 于 $U_0\setminus\{O\}$。再取较小邻域 $U$ 和 $\kappa_v\ge1$，使对 $A,B\in U$ 有 $A-B\in U_0$ 且

$$
|t(A-B)|_v\le\kappa_v\max\{|t(A)|_v,|t(B)|_v\}.
\tag{9.14}
$$

这些经典局部事实在这里的具体适用范围如下。有限地方用原整方程的形式差级数，它无常数项、系数整；在足够小的参数闭球上收敛，故可取 $\kappa_v=1$。若完成域在 $p$ 上的分歧指数为 $e_v$，球半径可取固定的 $p^{-m_v/e_v}<1$，其中整数 $m_v$ 在 $L$ 之前选定。坏约化处只用光滑泛纤维在 $O$ 的参数图，必要的缩小包含在这个 $m_v$ 中，不把整个约化核认作该图。复地方则在固定双圆盘内使用解析差映射 $F(s,t)$；它满足 $F(0,0)=0$，缩小圆盘并用其有界一阶导数得 (9.14)，再缩小使像在 $U_0$ 中。整个 $K$ 没有实地方。这些选择不使用局部形式对数，不需要无分歧、好约化或某个随 $L$ 变化的对数收敛阈值。

紧集 $E(K_v)\setminus U$ 上的 $\lambda_v$ 有有限上界。故存在固定 $h_v\ge0$，使 $\lambda_v(A)>h_v$ 蕴涵 $A\in U$。由 (9.14) 和两次参数高度比较，对不同的 $A,B$ 得到

$$
\lambda_v(A),\lambda_v(B)>h_v
\quad\Longrightarrow\quad
\lambda_v(A-B)\ge
\min\{\lambda_v(A),\lambda_v(B)\}-D_v,\qquad
D_v=2C_v+\log\kappa_v.
\tag{9.15}
$$

这明确把所用邻域、差映射损失及坏地方依赖都固定下来。

现只用一个实际非挠方向 $R=[q]P_1$。对每个非零整数 $k$，$[k]R\ne O$，由 (9.13) 与规范高度的二次性有

$$
\lambda_v([k]R)\le a_vq^2k^2+d_v,\qquad a_v=8H_1/n_v.
\tag{9.16}
$$

令 $1\le M\le N=2L+1$ 为整数，预置阈值
$\tau_M=1+\max\{h_v,a_vq^2M^2+d_v+D_v\}$。固定 $(b,c,d)$，把 $a=-L,\ldots,L$ 依次分成前面各长 $M$、末块长度至多 $M$ 的连续块。每块的点是某个固定平移加上连续的 $[a]R$。若同一块内两个不同的非零关系都满足 $\lambda_v(Q_z)>\tau_M$，其差必为 $[k]R$，其中

$$
z-z'=(k,0,0,0),\qquad 0<|k|\le M-1.
\tag{9.17}
$$

因此该差非零；(9.15) 使其局部高度严格大于 $a_vq^2M^2+d_v$，与 (9.16) 矛盾。此处只需上述一维循环差集，未对整个四维差集作不成立的分离断言。删去 $z=0$ 只会减少每块的点数。

于是高于 $\tau_M$ 的关系最多有
$N^3\lceil N/M\rceil\le N^4/M+N^3$ 个；后一项支付每条线末端不足一块的边界。其余关系由 (9.13) 的负部下界给出 $|\lambda_v(Q_z)|\le\tau_M+c_v$。高层则由 (9.11)、(9.13) 的上包络支付。故有一个只依赖 $v,q$ 及固定来源的常数 $C$，使

$$
\begin{aligned}
\sum_{z\in B_L}|\lambda_v(Q_z)|
&\le N^4(\tau_M+c_v)
 +(N^4/M+N^3)\bigl(8C_0q^2L^2/n_v+d_v\bigr)\\
&\le C\bigl(L^4M^2+L^6/M+L^5+L^4\bigr).
\end{aligned}
\tag{9.18}
$$

现在才取 $M=\lceil L^{2/3}\rceil$；它满足 $1\le M\le N$ 和
$L^{2/3}\le M\le2L^{2/3}$。前两项各为 $O(L^{16/3})$，边界项 $L^5$ 与 $L^4$ 也被此阶支付，得到 (9.12)。常数的依赖顺序为：固定来源和高度负部、固定地方的参数图与差映射、固定 $q$，最后才是 $L,M$。没有使用逐点多对数估计，没有从紧性提取一个关于所有素数统一的常数。证毕。

**定理 9.5（固定有限素数尾部围绕准确多项式的展开）。** 令 $\mathcal F$ 为任意固定有限有理素数集，保留定义 9.1 的同一嵌入族，并定义

$$
\begin{gathered}
T_{\mathcal F}(L)=
\sum_{z\in B_L}\sum_{\substack{p>5\\p\notin\mathcal F}}
b_p(Q_z)\log p,\\
\mathcal D_{\mathcal F}
=\{v\in M_K:v\mid p,\ p\in\mathcal F\cup\{2,3,5\}\}
 \ \cup\ \{v:v\mid\infty\}.
\end{gathered}
\tag{9.19}
$$

对每个有限 $L$，$T_{\mathcal F}(L)$ 是有限和，独立于全部所选嵌入，而且准确有

$$
T_{\mathcal F}(L)
=H_L-\frac18\sum_{v\in\mathcal D_{\mathcal F}}
n_v\sum_{z\in B_L}\lambda_v(Q_z).
\tag{9.20}
$$

从而在 $L\to\infty$、$\mathcal F,q$ 固定时，

$$
\begin{gathered}
T_{\mathcal F}(L)
=\frac23q^2(H_1+H_2)L(L+1)(2L+1)^4
+O_{\mathcal F,q}(L^{16/3}),\\
\lim_{L\to\infty}\frac{T_{\mathcal F}(L)}{q^2L^6}
=\frac{32}{3}(H_1+H_2)>0.
\end{gathered}
\tag{9.21}
$$

证明。每个 $x(Q_z)\in K$ 只在有限多个有限地方有负赋值，且 $B_L$ 有限；其分母支持的并集仍有限。所有未删素数都是好约化素数，(9.7) 使其余局部高度全为零。因此可以交换此处全部求和而无需无穷级数的收敛假设。逐素数应用 (9.5)，再对每个 $Q_z$ 使用 (9.3)，就给出 (9.20)。每个素数的盒和已由 (9.4) 独立于地方选择，所以嵌入独立性在每个有限 $L$ 就成立，不是取极限后才成立。

$\mathcal D_{\mathcal F}$ 固定且有限。定理 9.4 给出

$$
\left|T_{\mathcal F}(L)-H_L\right|
\le\frac18\sum_{v\in\mathcal D_{\mathcal F}}n_v
\sum_{z\in B_L}|\lambda_v(Q_z)|
=O_{\mathcal F,q}(L^{16/3}).
\tag{9.22}
$$

代入 (9.8) 即得第一式。将其除以 $q^2L^6$，误差趋于零，而
$L(L+1)(2L+1)^4/L^6\to16$，得到第二式及其正性。特别地，(9.20) 的 $H_L$ 已经是规范高度总和，不再除以 $8$；被删除的地方包括所有无穷地方和 $\mathcal F\cup\{2,3,5\}$ 上方的全部地方。证毕。

**命题 9.6（单点反例及固定清单的边界）。** (9.4) 不能一般化为本来源上每个单点的恒等式；(9.21) 也不提供移动素数截止或原共同小像筛选尾部的判定。

证明。单点反例可在同一来源中直接给出。取 $q=1$，$S=P_1+P_2$，$A=[2]S=Q_{(2,0,2,0)}$。加法公式给出

$$
\xi=x(S)=\tfrac{21}{2}-3\sqrt{10},\qquad
N_{\mathbb Q(\sqrt{10})/\mathbb Q}(\xi+1)=\tfrac{169}{4},
\qquad
x(A)=\frac{(\xi^2+1)^2}{4\xi(\xi^2-1)}.
\tag{9.23}
$$

这里 $\sqrt{10}=\sqrt6\sqrt{15}/3\in K$。在 $13$ 处，$10$ 的两个平方根分别约化为 $6,-6$，由 Hensel 引理分别确定 $\mathbb Q_{13}$ 中的根。在第一支 $\xi\equiv-1$，第二支 $\xi\equiv9$。第二支的 $\xi+1$ 为单位，范数等式使第一支 $v_{13}(\xi+1)=2$；其中 $\xi,\xi-1,\xi^2+1$ 均为单位。因此第一支 $v_{13}(x(A))=-2$，第二支 $v_{13}(x(A))\ge0$。由 (9.7)，两支的局部高度分别是 $\log13$ 和 $0$。由 $[K:\mathbb Q(\sqrt{10})]=4$ 及局部次数的塔式，两支在 $K$ 上方的局部次数总和各为 $4$，所以全部地方的加权平均是 $\frac12\log13$，而选第二支的读数为零。这反驳单点恒等式；全盒恒等式依赖 (9.6) 的重编号，仍然成立。

定理 9.4 中的邻域半径、差映射损失和高度常数分别依赖固定地方。定理 9.5 只将固定有限个这种常数相加，不附带这些常数的有效求取结论，也没有全部素数上的统一速度。因此不能把 $\mathcal F$ 换成随 $L$ 移动的清单，不能从 (9.21) 推出只保留 $p>L^4$ 或原 $p>R^2$ 的尾部渐近式。

此外本节的 $B_L$ 是无筛选的完整四维盒，来源为 (9.1)；定义 8.1 的原来源、共同入口及共同小像条件并未出现在 (9.19) 中。全盒分母总量不能决定经该条件筛选后的质量，故没有证明或否定原 RG004 §70 的 $V_H(R)=o(q_H^2R^3)$，也没有证明 (8.5) 的算术稀疏性。原量子结构与数论对象之间的解释性桥梁仍属未证，本节没有给出物理实现或任何此类结构对应的证明。上述结论只使用明示的代数点、Galois 作用、局部群运算和高度关系。证毕。

用白话说，把同一对点的四个整数系数全部装进一个对称盒后，共轭只会把盒中的标签重新排列，所以任意事先选定的地方都能接回全球高度。某个固定地方若要在一个短块里同时收取两笔很高的费用，两点之差就会迫使一个短倍点付出超过全球高度所给上限的费用；因此每块至多容纳一笔。平衡块长后，任意固定有限地方的总费用都低于六次主项，余下分母质量便有准确的正主项。这没有估计移动截止，也没有替原共同小像条件作筛选。

## 追加锚（本行以下为增补区）

## 10. 完整形式层的四维装箱与二次移动窗口

**定义 10.1（同一全盒的逐素数质量与实际层纤维）。** 保持定义 9.1 的固定曲线、八次域、点对、整数 $q\ge1$、完整盒 $B_L$ 及事先选定的整族嵌入；直接复用定理 7.2 的非挠性与 Gaussian 模挠独立性。对每个 $p>5$，写 $F_p=K_{v_p^*}$，仍用 $v_p(p)=1$。定义

$$
A_p(L)=\sum_{z\in B_L}b_p(Q_z)\log p.
\tag{10.1}
$$

对整数 $k\ge1$，令 $E_k(F_p)$ 为包含 $O$ 以及全部满足 $v_p(t(A))\ge k$ 的非零形式点的集合，令

$$
\Lambda_{p,k}=\{z\in\mathbb Z^4:Q_z\in E_k(F_p)\},\qquad
N_{p,k}(L)=\#(B_L\cap\Lambda_{p,k}).
\tag{10.2}
$$

这里 $Q_z$ 在 $F_p$ 中均指同一个 $\sigma_p(Q_z)$。仅在定义群同态 $z\mapsto Q_z$ 时置 $Q_0=O$；$0$ 不参加任何深度或局部高度求和，也不在 $O$ 上计算这些量。层纤维使用实际的 $F_p$，不预设某个对数商所在的子域。

**定理 10.2（所有预选地方上的完整深度四次界）。** 存在只依赖固定来源和 $q$ 的常数 $C_q$，使所有素数 $p>5$、所有整数 $L\ge2$ 及所有事先选定的嵌入同时满足

$$
0\le A_p(L)\le C_qL^4.
\tag{10.3}
$$

证明。先核对实际完成域和形式层。三个二次域 $\mathbb Q(i)$、$\mathbb Q(\sqrt6)$、$\mathbb Q(\sqrt{15})$ 的判别式分别为 $-4,24,60$，故在 $p>5$ 均不分歧；它们的局部合成也不分歧。每个二次局部因子均包含在唯一的不分歧二次扩张中，所以

$$
e(F_p/\mathbb Q_p)=1,\qquad n_{v_p^*}=[F_p:\mathbb Q_p]\in\{1,2\}.
\tag{10.4}
$$

若 $p\equiv1\pmod4$，所选的 $\sigma_p(i)$ 在 $\mathbb Q_p$ 中，而 $F_p$ 仍可为不分歧二次域；若 $p\equiv3\pmod4$，则 $F_p=\mathbb Q_p(\sigma_p(i))$。两种情形中非零元素的赋值均为整数。本模型的判别式为 $64$，故在这些完成域上为好约化的极小整模型。

以下均为本证明调用的经典局部输入。[Silverman VII.2.1–2.2，印刷页 188–191](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 将约化核识别为整形式群在极大理想上的点。整形式差级数使每个 $E_k(F_p)$ 为子群；因而 $\Lambda_{p,k}$ 为加法子群，特别有

$$
z,z'\in\Lambda_{p,k}\quad\Longrightarrow\quad
Q_z-Q_{z'}=Q_{z-z'}\in E_k(F_p).
\tag{10.5}
$$

CM 作用也保持这些层：[Streng，*Divisibility sequences for elliptic curves with complex multiplication*，Theorem 2.9、Corollary 2.10，印刷页 189](https://msp.org/ant/2008/2-2/ant-v2-n2-p04-s.pdf) 给出整系数的 CM 形式作用及 $\mathcal O$ 模过滤。本模型还直接满足 $t([i]A)=i\,t(A)$；整数形式乘法和形式加法于是实现任意 Gaussian 标量。这里标量经同一个 $\sigma_p$ 运输，不要求嵌入固定某个预先命名的 $p$ 进平方根。

如使用形式对数，准确范围为 [Silverman IV.6.3–6.4，印刷页 131–132](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的严格不等式 $v_p(t)>1/(p-1)$。由 (10.4)，全部非零第一层点已经满足 $v_p(t)\ge1>1/(p-1)$。故规范形式对数 $\ell_p:E_1(F_p)\to\mathfrak m_{F_p}$ 在全部这些层上保赋值，且

$$
\ell_p(O)=0,\qquad
\ell_p([\alpha]A)=\sigma_p(\alpha)\ell_p(A),\qquad
v_p(\ell_p(A))=v_p(t(A))\quad(A\ne O).
\tag{10.6}
$$

式 (10.6) 中 $\alpha\in\mathcal O$、$A\in E_1(F_p)$；标量恒等式也由不变微分的拉回或 Streng Lemma 2.6 得到。其 Lemma 3.4，印刷页 195–196，所用严格阈值在此同样满足。尤其当 $A\ne O$ 已在形式群中时，$b_p([q]A)=b_p(A)+v_p(q)$；这不把非入口点擅自认作形式点。对任意局部点之对，证明均不需要其对数商属于 $\mathbb Q_p(i)$ 或任一整数环，也不把单点的 rank-of-apparition 消去理想当作两点纤维。下面实际只用子群关系 (10.5)。

再取得对全部这些地方统一的全球上包络。直接复用 (9.11)、(9.13) 及其固定常数 $C_0,C_-$，置

$$
a=8C_0q^2>0,\qquad d=C_-\ge0.
\tag{10.7}
$$

对每个非零 $w\in\mathbb Z^4$，在 (9.11) 中取 $L=\|w\|_\infty$，而在 (9.13) 中用 $n_v\ge1$，得到对每个 $v\mid p>5$ 都成立的

$$
0\le\lambda_v(Q_w)\le a\|w\|_\infty^2+d.
\tag{10.8}
$$

这里 $Q_w$ 非零由定理 7.2 保证。负部费用 $d$ 只来自 $2$ 上方及无穷地方的固定下界，不能把这些地方的局部高度当成非负；好约化地方本身非负。此上包络复用的规范正是 Silverman VIII.9.3、C.18.1–18.3，即 $2\widehat h=h_x+O_E(1)$ 及 $\widehat h=\frac18\sum_v n_v\lambda_v$，没有漏掉局部次数或另改高度规范。

由 (9.7)，非零 $w\in\Lambda_{p,k}$ 满足

$$
k\log p\le\lambda_{v_p^*}(Q_w)\le a\|w\|_\infty^2+d.
\tag{10.9}
$$

因此盒内每个深度都有限，且

$$
N_{p,k}(L)=0\quad\text{若}\quad
k>\frac{aL^2+d}{\log p}.
\tag{10.10}
$$

这也排除了可能的无穷深关系：$Q_z\ne O$，其非零参数在有限完成域中只有有限赋值。若没有入口，全部 $N_{p,k}(L)$ 及 $A_p(L)$ 均为零。

现支付实际的全部高层。固定 $k$，记 $s=k\log p$。当 $s>2d$ 且 $N_{p,k}(L)>0$ 时，置

$$
r=\sqrt{\frac{s-d}{a}}>0.
\tag{10.11}
$$

由某个盒内非零关系的 (10.9) 有 $r\le L$。把实盒 $[-L,L]^4$ 的每个坐标区间等分为 $m=\lceil4L/r\rceil$ 个区间，并将边界点只分配给一侧。每个小盒的边长至多 $r/2$。若同一小盒含有两个不同的 $z,z'\in B_L\cap\Lambda_{p,k}$，则 $w=z-z'\ne0$ 且 $\|w\|_\infty\le r/2$。由 (10.5)、(10.8) 必有

$$
s\le\lambda_{v_p^*}(Q_w)
\le a(r/2)^2+d
=\frac{s-d}{4}+d<s,
\tag{10.12}
$$

矛盾。这里每个实际非零四维差都由同一全球点对产生，其非零性与上包络均已支付；没有把坐标不同直接当成局部距离分离。每个小盒至多一个关系，且 $r\le L$ 给出 $m\le5L/r$，所以

$$
N_{p,k}(L)\le\frac{625a^2L^4}{(s-d)^2}
\le\frac{2500a^2L^4}{(k\log p)^2}
\qquad(k\log p>2d).
\tag{10.13}
$$

若该层为空，同一上界当然仍成立。小盒的全部边界已经计入 $m^4$，没有遗留二维或三维边界费用。

由 (10.4) 深度为非负整数，(10.10) 允许准确地按全部层求和：

$$
A_p(L)=\log p\sum_{k\ge1}N_{p,k}(L).
\tag{10.14}
$$

右侧实际是有限和，不是只计算首次入口。对 $k\log p\le2d$ 的层，使用 $\#B_L\le(3L)^4$，其总费用至多 $162dL^4$。对其余全部层使用 (10.13)，以及初等界 $\sum_{k\ge1}k^{-2}\le2$，得

$$
\begin{aligned}
A_p(L)
&\le162dL^4+
\frac{2500a^2L^4}{\log p}\sum_{k\ge1}\frac1{k^2}\\
&\le\left(162d+\frac{5000a^2}{\log7}\right)L^4.
\end{aligned}
\tag{10.15}
$$

可取括号中数为 $C_q$。它只依赖固定来源与 $q$，不依赖 $p,L$ 或任何嵌入。所有 $p\mid q$ 仍保留在原纤维中；没有除去 $[q]$、假定它在局部可逆、或删掉其额外深度。分裂与惰性两种情形只通过各自实际的 $F_p$ 出现，未比较不同地方的单点读数。故 (10.3) 对整族预选嵌入统一成立。证毕。

**定理 10.3（二次窗口外的完整盒正质量）。** 对同一固定来源与固定整数 $q\ge1$，任意整族事先选定的嵌入以及所有整数 $L\ge2$，有

$$
\sum_{5<p\le L^2}A_p(L)=O_q\!\left(\frac{L^6}{\log L}\right),
\qquad
\sum_{p>L^2}A_p(L)=H_L+O_q\!\left(\frac{L^6}{\log L}\right).
\tag{10.16}
$$

这两个误差常数对嵌入族统一，且每个有限 $L$ 的素数和均有有限支持。准确地，

$$
\lim_{L\to\infty}
\frac{1}{q^2L^6}\sum_{p>L^2}A_p(L)
=\frac{32}{3}(H_1+H_2)>0.
\tag{10.17}
$$

证明。只需经典 Chebyshev 上界 $\pi(x)\ll x/\log x$。作为此处的经典中间输入，其初等依据是：$\prod_{n<p\le2n}p$ 整除 $\binom{2n}{n}\le4^n$，故 $\vartheta(2n)-\vartheta(n)\le2n\log2$；沿 $2$ 的幂求和得到 $\vartheta(x)\ll x$。将素数分成 $p\le\sqrt x$ 和 $p>\sqrt x$，得到 $\pi(x)\le\sqrt x+2\vartheta(x)/\log x\ll x/\log x$。这不是新的素数计数定理。

逐素数应用 (10.3)，立刻有

$$
0\le\sum_{5<p\le L^2}A_p(L)
\le C_qL^4\pi(L^2)
\ll_q\frac{L^6}{\log L}.
\tag{10.18}
$$

另一方面，直接引用定理 9.5 在固定 $\mathcal F=\varnothing$ 时的完整总量，以及定理 9.3 的准确多项式：

$$
\sum_{p>5}A_p(L)=H_L+O_q(L^{16/3}),\qquad
H_L=\frac23q^2(H_1+H_2)L(L+1)(2L+1)^4.
\tag{10.19}
$$

此处只复用固定地方消费者；不将其固定清单换成移动清单。它删除的仅是 $2,3,5$ 上方及全部无穷地方，常数因而固定。由定理 9.2，其有限盒的总量本来就独立于各素数所选地方。

每个 $z\in B_L$ 的 $x(Q_z)\in K$ 只有有限分母支持；盒本身有限，故所有非零深度的素数支持之并仍有限。可以从 (10.19) 精确减去 (10.18) 而不交换未经证明收敛的级数。因 $L^{16/3}=O(L^6/\log L)$，得到 (10.16) 的第二式。

最后，$L(L+1)(2L+1)^4/L^6\to16$，而除以固定的 $q^2L^6$ 后误差为 $O_q(1/\log L)$。代入 (10.19) 得 (10.17)；$H_1,H_2>0$ 已由定理 7.2 保证。$H_L$ 已是规范高度之和，不再除以 $8$。证毕。

用白话说，同一个深层里若挤进两个系数很近的关系，它们的差也必须同样深；但短系数产生的全球高度有限，无法支付这笔局部费用。四个方向一起装箱，使深层数量按层高的平方倒数下降，全部层的费用因此能相加。每个素数的总费用都有同一个四次上界，再用二次窗口内的素数个数，就只删去六次主项中趋于零的一部分。

本节的量词始终是固定 $q$、固定 $K$ 和同一点对，结论仅为完整无筛选四维盒的 $p>L^2$ 尾部。它不提供移动 $q$ 或移动来源的统一常数，也不估计 $p>L^4$ 的尾部，不判定原 RG004 §70 的 $V_H$ 或 §8 的原共同小像筛选条件；这些量没有由 (10.16) 得到结算。

## 追加锚（本行以下为增补区）

## 11. 实际 Mordell–Weil 高度椭球与扩大对数窗口

**定义 11.1（固定来源、完整挠点纤维与绝对规范）。** 固定椭圆曲线 $E/\mathbb Q$、有限 Galois 扩张 $K/\mathbb Q$ 及在 $G=\operatorname{Gal}(K/\mathbb Q)$ 下稳定的实际有限生成子群 $\Gamma\subset E(K)$。记

$$
N=[K:\mathbb Q],\quad T=\Gamma_{\rm tors},\quad t=|T|,\quad
\Lambda=\Gamma/T,\quad V=\Lambda\otimes_{\mathbb Z}\mathbb R,\quad d=\operatorname{rank}\Lambda\ge3.
\tag{11.1}
$$

以 $\pi:\Gamma\to\Lambda\subset V$ 表示商映射。规范高度仍采用 $2\widehat h=h_x+O_E(1)$；其在 $V$ 上的二次型记为 $Q$，范数记为 $\|x\|_Q=\sqrt{Q(x)}$。这里使用的经典输入为 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.9.3、VIII.9.5–9.6，印刷页 248–252](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)：高度配对消去挠点，并在 $E(K)\otimes\mathbb R$ 上给出正定二次型。$\Gamma/T$ 注入 $E(K)/E(K)_{\rm tors}$，故限制到 $V$ 仍正定。实正定性调用 VIII.9.6，连同其使用 VIII.6.1 的有界高度有限性；不以仅在非零格点上取正值替代这个输入。

任取 $V$ 上 Lebesgue 测度 $\mu$，定义

$$
\mathcal B_Q=\{x\in V:Q(x)\le1\},\qquad
c_\Gamma=\frac{\mu(\mathcal B_Q)}{\operatorname{covol}_\mu(\Lambda)}>0,\qquad
S_R=\{P\in\Gamma:0<\widehat h(P)\le R^2\},\qquad
H(R)=\sum_{P\in S_R}\widehat h(P).
\tag{11.2}
$$

$R\ge1$ 为实数。比值 $c_\Gamma$ 与测度的标量选择无关，只附属于这个声明的子群及其高度；不将 $\Lambda$ 称为整个 $E(K)$ 的基，也不将该比值称为整个群的调节子。每个非零 $x\in\Lambda\cap R\mathcal B_Q$ 的全部 $t$ 个实际提升都在 $S_R$；$\pi^{-1}(0)=T$ 全部排除。这里没有选择 $G$ 等变截面。

先固定一个有理整 Weierstrass 方程、全部地方绝对值及每个有理地方 $r$ 上方的一个选定地方 $v_r^*$；实现这些地方的嵌入也一次固定，同一地方的全部点共用它。有限地方使用 $|p|_v=p^{-1}$，实、复地方均使用通常绝对值，令 $\nu_v=-\log|\cdot|_v$。有限地方 $n_v=[K_v:\mathbb Q_p]$，实地方 $n_v=1$，复地方 $n_v=2$。使用 [Silverman C.18.1–18.3，印刷页 454–455](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的局部高度；对 $A\ne O$，

$$
\widehat h(A)=\frac1N\sum_v n_v\lambda_v(A),\qquad
\lambda_v(A)=-\log|t_v(A)|_v+O_v(1)\quad(A\to O).
\tag{11.3}
$$

后一式由原文 C.18.1(ii) 的 $\lambda_v+\frac12\nu_v(x)$ 有有限极限及 $x=t_v^{-2}(1+O(t_v))$ 得到。每个地方均取该固定方程的原点参数 $t_v=-x/y$，并一次选定所需参数图。固定有限素数集 $\mathcal E$，包含该整方程判别式的素因子、$K/\mathbb Q$ 的分歧素数及 $2,3$。对 $p\notin\mathcal E$，完成域不分歧，所选整方程为好约化极小模型。仅对 $A\ne O$ 定义

$$
b_v(A)=
\begin{cases}
 v_p(-x(A)/y(A)),&A\in E_1(K_v),\\
 0,&A\notin E_1(K_v),
\end{cases}
\qquad
A_p(R)=\log p\sum_{P\in S_R}b_{v_p^*}(P),\qquad v_p(p)=1.
\tag{11.4}
$$

参数仅在第一种情形计算。VII.2.1–2.2 与 C.18.3(b) 给出 $b_v(A)\in\mathbb Z_{\ge0}$ 及 $\lambda_v(A)=b_v(A)\log p$。深度包含所有高阶层，不借用任何对数商的域归属。

**定理 11.2（共同椭球的地方平均与高度主项）。** 对定义 11.1 的同一来源，$S_R$ 是有限、实际 $G$ 稳定的点集。令 $S_v(R)=\sum_{P\in S_R}\lambda_v(P)$。对任意有理地方 $r$ 及任意 $v\mid r$，准确有

$$
S_v(R)=\frac1N\sum_{w\mid r}n_wS_w(R).
\tag{11.5}
$$

此外，当来源固定且 $R\to\infty$ 时，

$$
|S_R|=t c_\Gamma R^d+O_{E,K,\Gamma}(R^{d-1}),\qquad
H(R)=t c_\Gamma\frac d{d+2}R^{d+2}+O_{E,K,\Gamma}(R^{d+1}).
\tag{11.6}
$$

证明。正定性与格的离散性先保证 $S_R$ 有限，下面同时给出精确计数。绝对横坐标高度在 $G$ 下不变，乘法与 $G$ 交换；由规范高度的极限定义得到 $\widehat h(gP)=\widehat h(P)$。因 $g\Gamma=\Gamma$，$g$ 在实际 $S_R$ 上双射，包括所有挠点平移的提升，不需要在商群上先选等变提升。按 $|u|_{g^{-1}v}=|g(u)|_v$ 运输地方，C.18.1 的唯一性给出 $\lambda_v(gP)=\lambda_{g^{-1}v}(P)$。重编号有限点集得 $S_v(R)=S_{g^{-1}v}(R)$。$G$ 在 $r$ 上方地方上传递，且 $\sum_{w\mid r}n_w=N$，证明 (11.5)。无穷地方也在此论证内：实嵌入权 $1$，一对共轭复嵌入合为一个地方、权 $2$。这只是点集求和恒等式，不是一般单点恒等式。

为同时支付椭球边界，取 $\Lambda$ 的有界半开基本平行体 $F$，使 $\|y\|_Q\le\rho$ 于 $F$。记 $M(u)=\#\{x\in\Lambda:0<\|x\|_Q\le u\}$。以 $x+F$ 铺满 $V$，对所有 $u\ge0$ 有

$$
c_\Gamma(u-\rho)_+^d\le M(u)+1\le c_\Gamma(u+\rho)^d,
\qquad M(u)=c_\Gamma u^d+O_{Q,\Lambda}((1+u)^{d-1}).
\tag{11.7}
$$

左边由半径 $(u-\rho)_+$ 的球落入中心范数不超过 $u$ 的格胞，右边由这些格胞均落入半径 $u+\rho$ 的球；零半径下界为零。闭球上的格点均计入，半开格胞使重叠边界不重复计量。这是固定格的经典体积计数在此处的直接使用。

每个非零商点正好有 $t$ 个提升，高度相同，故 $|S_R|=tM(R)$。逐个格点积分可得准确等式

$$
H(R)=t\left(R^2M(R)-\int_0^R2uM(u)\,du\right).
\tag{11.8}
$$

代入 (11.7)，主项为 $t c_\Gamma(1-2/(d+2))R^{d+2}$，误差为 $O(tR^{d+1})$。这证明 (11.6)，亦证明 $S_R$ 有限。被删去的是全部 $T$；没有在这些点上使用 $\lambda_v$，也没有遗失闭椭球边界。证毕。

**定理 11.3（固定地方的完整绝对质量）。** 对每个固定地方 $v$，存在只依赖 $E,K,\Gamma,v$ 的常数，使所有 $R\ge1$ 满足

$$
\sum_{P\in S_R}|\lambda_v(P)|=O_{E,K,\Gamma,v}(R^d).
\tag{11.9}
$$

证明。先统一支付负部。C.18.1 的连续性、原点的正无穷奇性与 $E(K_u)$ 的紧性给出 $c_u\ge0$，使所有 $A\ne O$ 满足 $\lambda_u(A)\ge-c_u$。在 $u\mid p\notin\mathcal E$ 可由好约化公式取 $c_u=0$。因此

$$
C_-=\sum_u n_uc_u<\infty,\qquad
-c_v\le\lambda_v(A)\le a_v\widehat h(A)+b_v',\quad
 a_v=N/n_v>0,\quad b_v'=C_-/n_v\ge0.
\tag{11.10}
$$

右边来自 (11.3)，对所有实际非零点都成立，特别包括非零挠点。

固定 $v$ 的小参数邻域 $U_0$，使 $|\lambda_v(A)+\log|t_v(A)|_v|\le C_v$。再取较小邻域 $U$，使互异非零 $A,B\in U$ 时 $A-B\in U_0$ 且

$$
|t_v(A-B)|_v\le\kappa_v\max(|t_v(A)|_v,|t_v(B)|_v),\qquad \kappa_v\ge1.
\tag{11.11}
$$

这里的局部事实是 IV.1 的参数展开及 VII.2 的群参数化：有限地方把固定收敛的差级数限制到足够小的球，其无常数项给出该界；坏地方必要的缩小固定在 $U$ 内。实、复地方由局部解析差映射在较小圆盘上的有界一阶导数给出同一形式的界。此处不要求好约化、不分歧或形式对数的等距范围。

紧集 $E(K_v)\setminus U$ 上 $\lambda_v$ 有上界。取固定 $h_v\ge0$，使 $\lambda_v(A)>h_v$ 蕴涵 $A\in U$。对不同的实际点 $A,B$，两次参数比较给出

$$
\lambda_v(A),\lambda_v(B)>h_v
\ \Longrightarrow\
\lambda_v(A-B)\ge\min(\lambda_v(A),\lambda_v(B))-D_v,
\quad D_v=2C_v+\log\kappa_v\ge0.
\tag{11.12}
$$

差点非零才使用其高度与参数；从未在 $O$ 上赋予无穷高度来代替这一步。

令 $Z_v(s,R)=\{P\in S_R:\lambda_v(P)>s\}$。固定
$s_0>1+h_v+2(D_v+b_v')$。当 $s\ge s_0$ 且 $P,P'\in Z_v(s,R)$ 不同时，(11.10)–(11.12) 给出

$$
a_v\|\pi(P)-\pi(P')\|_Q^2
=a_v\widehat h(P-P')>s-D_v-b_v'>s/2.
\tag{11.13}
$$

尤其若两点来自同一挠点纤维，它们的非零差是挠点，(11.10) 的上界为 $b_v'$，与 (11.12) 矛盾。因此高层上的商映射单射；在低层仍完整计入每个纤维的 $t$ 个点。该论证无需任何群截面。

置 $r_s=\sqrt{s/(2a_v)}$。若 $Z_v(s,R)$ 非空，由 $s<\lambda_v(P)\le a_vR^2+b_v'$ 及 $s>2b_v'$ 得 $r_s\le R$。在 $Q$ 范数中，以投影点为中心的半径 $r_s/2$ 开球两两不交，均包含在半径 $R+r_s/2$ 的球内。所以

$$
\#Z_v(s,R)\le(1+2R/r_s)^d
\le3^d(2a_v)^{d/2}R^d s^{-d/2}\quad(s\ge s_0).
\tag{11.14}
$$

空层也满足该界。低层用 $|S_R|=O(R^d)$，高层用 (11.14)，对每个有限 $S_R$ 的正部积分得到

$$
\sum_{P\in S_R}\max(\lambda_v(P),0)
=\int_0^\infty\#Z_v(s,R)\,ds
\ll_v R^d\left(s_0+\int_{s_0}^\infty s^{-d/2}\,ds\right)\ll_v R^d.
\tag{11.15}
$$

积分实际在 $a_vR^2+b_v'$ 之后为零。因 $d>2$，写到无穷的上界收敛；负部至多 $c_v|S_R|=O_v(R^d)$，证明 (11.9)。这同时核对了高局部高度的实际差点、固定阈值、挠点同纤维与全部地方的负部。证毕。

**定理 11.4（整族预选地方上的全部形式层）。** 存在 $C=C(E,K,\Gamma,\mathcal E)$ 及 $p_0=p_0(E,K,\mathcal E)$，对所有 $p\notin\mathcal E$、所有事先选定的 $v_p^*$ 和全部 $R\ge1$，有

$$
0\le A_p(R)\le CR^d,\qquad
A_p(R)\le\frac{CR^d}{(\log p)^{d/2-1}}\quad(p\ge p_0).
\tag{11.16}
$$

每个 $R$ 的素数支持有限，且每个素数的全部高层都在有限截断内；常数不依赖所选地方族。

证明。令 $v=v_p^*$，$F=K_v$。$p\notin\mathcal E$ 保证 $e(F/\mathbb Q_p)=1$，但允许任意剩余次数 $f=n_v$。因此 $v_p(F^\times)=\mathbb Z$，$\nu_v=v_p\log p$，局部次数仍只放在 (11.3) 的 $n_v$ 中。定义实际子群

$$
E_k(F)=\{O\}\cup\{A\in E_1(F)\setminus\{O\}:v_p(t_v(A))\ge k\},\qquad
N_{p,k}(R)=\#(S_R\cap E_k(F))\quad(k\ge1).
\tag{11.17}
$$

VII.2.2 的整形式群律及形式逆使 $E_k(F)$ 为子群，故同层的两个实际点之差仍在同层。这里只在群的集合定义中放入 $O$；不在 $O$ 上计算深度。对非零层点，C.18.3(b) 给出
$\lambda_v(A)=v_p(t_v(A))\log p\ge k\log p$。从 (11.10) 取不依赖地方的较弱包络，得到

$$
\lambda_v(A)\le N\widehat h(A)+C_-,\qquad
N_{p,k}(R)=0\quad\text{若}\quad k\log p>NR^2+C_-.
\tag{11.18}
$$

因局部参数在非零形式点上不为零，每个实际深度有限。于是可先作有限层分解，再用收敛上界：

$$
A_p(R)=\log p\sum_{k\ge1}N_{p,k}(R).
\tag{11.19}
$$

令 $s=k\log p>2C_-$。若同层两点不同，其实际差非零，且

$$
s\le\lambda_v(P-P')\le N\|\pi(P)-\pi(P')\|_Q^2+C_-.
\tag{11.20}
$$

同纤维的非零挠点差将给出 $s\le C_-$，故此时投影单射。不同投影间距至少 $r=\sqrt{(s-C_-)/N}$；若该层非空，(11.18) 给出 $r\le R$。同 (11.14) 的开球体积比较，包括全部椭球边界，得到

$$
N_{p,k}(R)\le3^d\left(\frac{N}{s-C_-}\right)^{d/2}R^d
\le B R^d(k\log p)^{-d/2},\qquad B=3^d(2N)^{d/2}.
\tag{11.21}
$$

单点层也满足该界，空层同样如此。对于 $k\log p\le2C_-$ 的低层，定理 11.2 的格计数给出 $N_{p,k}(R)\le C_\Gamma'R^d$，其中 $C_\Gamma'$ 包含全部 $t$ 个提升；这些层乘上 $\log p$ 的总费用至多 $2C_-C_\Gamma'R^d$。对其余全部层用 (11.21)，令 $\beta=d/2>1$，得

$$
A_p(R)\le2C_-C_\Gamma'R^d+
B R^d(\log p)^{1-\beta}\sum_{k\ge1}k^{-\beta}.
\tag{11.22}
$$

级数收敛，$\log p\ge\log2$，即得第一界。若 $\log p>2C_-$，低层全无，(11.22) 的第一项删除，便得第二界；可把这个阈值及 $\mathcal E$ 吸收进固定 $p_0$。不要求该阈值有效计算。$d>2$ 正是完整深度级数收敛的条件；当 $d=2$，此证明只给出截断谐和和的对数损失，不能据此否定二维的更强结论。

最后，$S_R$ 有限；每个非零 $P$ 的 $x(P)\in K$ 只有有限分母支持，好约化处深度非零恰意味着横坐标有负赋值。因此这些支持的有限并含有全部非零 $A_p(R)$。整族地方均在开始时固定；证明使用实际完成域与实际差点，没有换源、逐点换嵌入或使用形式对数。证毕。

**定理 11.5（扩大对数窗口外的正质量）。** 令 $\alpha=d/2-1>0$，对 $R\ge2$ 置

$$
X_R=R^2(\log R)^\alpha.
\tag{11.23}
$$

保持定义 11.1 的固定数据，$R\to\infty$ 时有

$$
\sum_{\substack{p>X_R\\p\notin\mathcal E}}A_p(R)
=H(R)+O_{E,K,\Gamma,\mathcal E}\!\left(\frac{R^{d+2}}{\log R}\right),\qquad
\lim_{R\to\infty}\frac1{R^{d+2}}
\sum_{\substack{p>X_R\\p\notin\mathcal E}}A_p(R)
=t c_\Gamma\frac d{d+2}>0.
\tag{11.24}
$$

充分大的 $R$ 有 $X_R>\max\mathcal E$，此时可直接把求和写成 $\sum_{p>X_R}A_p(R)$；不额外删除任何随 $R$ 变化的例外素数。

证明。记 $\mathcal D=\{v:v\mid\infty\text{ 或 }v\mid p\in\mathcal E\}$。由定理 11.4 的有限支持、(11.5) 的逐素数平均与 (11.3)，准确有

$$
\sum_{p\notin\mathcal E}A_p(R)
=H(R)-\frac1N\sum_{v\in\mathcal D}n_vS_v(R)
=H(R)+O_{E,K,\Gamma,\mathcal E}(R^d).
\tag{11.25}
$$

第二步只对固定有限清单应用 (11.9)，并未把其地方依赖常数用于移动清单。$H(R)$ 已经是绝对规范高度之和，此式绝不能再将它除以 $N$。

所需素数计数输入仅是经典 Chebyshev 上界 $\pi(x)\ll x/\log x$，其初等依据已在定理 10.3 的证明中列明。对固定 $\alpha>0$，将素数分为 $p\le\sqrt x$ 及 $\sqrt x<p\le x$，可得

$$
\sum_{p\le x}(\log p)^{-\alpha}
\le(\log2)^{-\alpha}\sqrt x+
(2/\log x)^\alpha\pi(x)
\ll_\alpha\frac{x}{(\log x)^{\alpha+1}}\quad(x\ge3).
\tag{11.26}
$$

这里 $\sqrt x=O_\alpha(x/(\log x)^{\alpha+1})$。有限个 $p<p_0$ 的费用由 (11.16) 第一界支付，其余用第二界，于是

$$
\sum_{\substack{p\le X_R\\p\notin\mathcal E}}A_p(R)
\ll R^d+R^d\frac{X_R}{(\log X_R)^{\alpha+1}}
\ll\frac{R^{d+2}}{\log R},
\tag{11.27}
$$

因为 $\log X_R=2\log R+\alpha\log\log R\asymp\log R$。从有限和 (11.25) 减去 (11.27) 即得首式。再用 (11.6)，$R^{d+1}=O(R^{d+2}/\log R)$，得到极限及其正性。每个有限 $R$ 都有 (11.5)，所以全部素数和及尾部均独立于预选地方族，误差常数也对此族统一。证毕。

**推论 11.6（现有八次来源的实际椭球消费者）。** 取 (9.1) 的同一曲线、八次域与点对，固定整数 $q\ge1$，令

$$
\Gamma_q=[q]\bigl(\mathbb ZP_1+\mathbb Z([i]P_1)+\mathbb ZP_2+\mathbb Z([i]P_2)\bigr)
=[q]\bigl(\mathbb Z[i]P_1+\mathbb Z[i]P_2\bigr).
\tag{11.28}
$$

其中 $\mathbb Z[i]P_j$ 表示 Gaussian 整数模生成的群。此实际子群 $G$ 稳定，$T=0,d=4$，且以 $([q]P_1,[q][i]P_1,[q]P_2,[q][i]P_2)$ 为整数基时

$$
Q(a,b,c,e)=q^2\bigl(H_1(a^2+b^2)+H_2(c^2+e^2)\bigr),\qquad
c_{\Gamma_q}=\frac{\pi^2}{2q^4H_1H_2},\qquad
H(R)=\frac{\pi^2}{3q^4H_1H_2}R^6+O_q(R^5).
\tag{11.29}
$$

因此选 $\mathcal E=\{2,3,5\}$ 后，对同一实际 $S_R\subset\Gamma_q$、充分大的 $R$ 有

$$
\sum_{p>R^2\log R}A_p(R)
=\frac{\pi^2}{3q^4H_1H_2}R^6+O_q(R^6/\log R),\qquad
\lim_{R\to\infty}\frac1{R^6}\sum_{p>R^2\log R}A_p(R)
=\frac{\pi^2}{3q^4H_1H_2}>0.
\tag{11.30}
$$

证明。定理 7.2 已给出 Gaussian 模挠独立性，故这四个整数方向的任何非零组合均非挠。乘以固定 $q$ 后仍如此，故 $([q]P_1,[q][i]P_1,[q]P_2,[q][i]P_2)$ 是 $\Gamma_q$ 的整数基，$T=0$。使用定理 9.2 已核对的实际 Galois 作用：三个独立符号 $\epsilon,\delta_1,\delta_2$ 在四个方向上的字符分别为

$$
\chi_1=\delta_1,\quad\chi_2=\epsilon\delta_1,\quad
\chi_3=\delta_2,\quad\chi_4=\epsilon\delta_2.
\tag{11.31}
$$

它们两两不同且取值 $\pm1$。高度配对在 $G$ 下不变；任意两个不同字符的商是非平凡字符，存在一个 $g$ 使其值为 $-1$。于是相应两个生成点的配对等于其负值，故为零。这证明逐点正交性，不以盒中交叉项求和为零替代正交。定理 9.3 已证明 $\widehat h([i]P_j)=H_j$，故得到 (11.29) 的二次型。

在该整数基中取协体积为 $1$ 的测度。单位四维球的体积为 $\pi^2/2$：按前两个实坐标的半径积分，体积为 $2\pi^2\int_0^1r(1-r^2)\,dr$。椭球四个半轴为 $(q\sqrt{H_1})^{-1}$ 两次及 $(q\sqrt{H_2})^{-1}$ 两次，故体积及 $c_{\Gamma_q}$ 为 (11.29) 所列值。将 $t=1,d=4$ 代入 (11.6)，主项为 $\frac23c_{\Gamma_q}R^6$，即给出的常数。

本曲线判别式为 $64$；由定理 10.2 已核对，八次域在 $p>5$ 不分歧，因此 $\mathcal E=\{2,3,5\}$ 足够。即使 $p\mid q$ 也保留它在实际群中的全部深度，不需从层中消去 $[q]$。定理 11.5 取 $\alpha=1$ 即得 (11.30)，其中 $q$ 与来源固定。证毕。

**说明 11.7（文献对应、可删前提与结论边界）。** 本节一般消费者及其层求和推导属于 repo-derived 应用，不作优先性主张。Silverman VIII.9.3、VIII.9.6 只承担规范高度、配对及实正定性，C.18.1–18.3 承担局部奇性、连续性、次数加权及好约化公式，VII.2.1–2.2 承担实际约化核和整形式群。格胞体积比较与 Chebyshev 上界也都是经典输入。§10 已有四维盒的完整层装箱，本节使用其实际差点机制，新增消费者是带完整挠点纤维的一般高度椭球及其对数扩大窗口。

[Bhakta，*Perfect powers in the product of denominators of elliptic curves*，arXiv:2606.00466v3，§5.1，Lemmas 5.1–5.4，页 19–21](https://arxiv.org/pdf/2606.00466v3) 的对象是 $E(\mathbb Q)$ 的约化格、挠点约化陪集及入口支持计数。其 Lemma 5.3 是有界高度下非零横坐标赋值的点数界，Lemma 5.4 是小约化像群阶的素数支持界；它们没有给出 $\sum_kN_{p,k}$ 的完整深度质量。本节没有把这些入口结论当作 (11.19)–(11.22) 的证明，也不需要其更强筛法结论来替代实际层求和。

用白话说，椭球画在“整数点的组合系数”所张成的 Mordell–Weil 实空间中。全球规范高度给这个空间一把正定的尺；共轭保持这把尺，所以把全部挠点提升都装入同一高度球后，共轭只会重排真实点。局部高度的次数加权公式由此能对整个球接回全球总量。单点在不同地方的读数仍可不同。

一个地方收取的费用很高时，该点很靠近局部群原点。两个这样的实际点相减，差点也靠近原点；若它们的系数组合太近，差点的全球高度就不足以支付该局部费用。因此高层只能容纳相互分离的系数点。$d$ 维体积给出 $s^{-d/2}$ 的层数衰减，$d>2$ 使全部层可加。这里用的是实际局部群差和高度预算，不把原点的几何余维当作高度估计，也不从维数类比推断物理几何。

一般定理删除了 CM、Gaussian 系数、独立坐标变号的矩形盒、对数商的有理性及等变截面前提；保留的是固定 Galois 来源、实际稳定子群、完整挠点纤维、正定高度、$d>2$、固定例外集与预选地方。CM 只用于明确 (11.28) 这个现有消费者，未参与一般层界。椭球族的结论不能改称原矩形全盒的同一统计，(11.30) 的常数也不是 (10.17) 的盒常数。

原 $p>L^4$ 尾部、原 RG004 §70 的 $V_H$ 与量子起源桥仍未由本节证明。固定 $q$ 的误差不声称对移动 $q$ 统一；$d\le2$ 时本证明的完整层求和不能给出同一界。这里没有物理空间或量子公理的实现结论，也没有给出 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义。

## 追加锚（本行以下为增补区）

## 12. 自由秩一实际含挠来源的完整深度与三次尾部

**定义 12.1（秩一来源、完整点集与地方规范）。** 固定椭圆曲线 $E/\mathbb Q$、有限 Galois 扩张 $K/\mathbb Q$ 以及 $G=\operatorname{Gal}(K/\mathbb Q)$ 稳定的实际有限生成子群 $\Gamma\subset E(K)$，要求 $\Gamma/T$ 的自由秩为一，其中 $T=\Gamma_{\rm tors}$。记 $N=[K:\mathbb Q]$、$t=|T|$。选取商群的一个正生成元及其任意实际提升 $P$，于是作为普通阿贝尔群有

$$
\Gamma=\mathbb ZP\oplus T,\qquad
\pi(nP+\tau)=n,\qquad h=\widehat h(P)>0.
\tag{12.1}
$$

不要求这个分裂与 $G$ 作用相容。规范高度采用 $2\widehat h=h_x+O_E(1)$ 的绝对规范，$h_x(A)=h(x(A))$，并置 $h_x(O)=0$。对实数 $R\ge1$，令

$$
L=\left\lfloor\frac{R}{\sqrt h}\right\rfloor,\qquad
S_R=\{nP+\tau:0<|n|\le L,\ \tau\in T\}
=\{A\in\Gamma:0<\widehat h(A)\le R^2\},\qquad
H(R)=\sum_{A\in S_R}\widehat h(A).
\tag{12.2}
$$

这里每个非零自由坐标的全部实际挠点提升均保留，零自由坐标的整个纤维 $T$ 均排除。$S_R$ 中没有 $O$；$L=0$ 时它是空集。高度的正性、整数倍二次律及挠点平移不改变高度，使用 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.9.3(b)–(e)，印刷页 248–249](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的规范与双线性配对。

固定一个有理整 Weierstrass 方程，其判别式为 $\Delta\ne0$；每个有理地方 $r$ 上方选定一个地方 $v_r^*$，同一地方的全部点共用同一嵌入。有限地方取 $|p|_v=p^{-1}$，实、复地方均取通常绝对值。记 $\nu_v=-\log|\cdot|_v$；有限地方的权为 $n_v=[K_v:\mathbb Q_p]$，实地方为 $1$，复地方为 $2$。局部高度取 [Silverman C.18.1–18.3，印刷页 454–455](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的 $\lambda_v$。对 $A\ne O$，其准确分解与原点奇性为

$$
\widehat h(A)=\frac1N\sum_{v\in M_K}n_v\lambda_v(A),\qquad
\lambda_v(A)=-\log|t_v(A)|_v+O_v(1)\quad(A\longrightarrow O),
\qquad t_v=-x/y.
\tag{12.3}
$$

只在原点参数图内使用后一式。固定有限素数集 $\mathcal E$，包含 $\Delta$ 的素因子、$K/\mathbb Q$ 的分歧素数及 $2,3$；不要求加入 $t$ 或某个固定乘数的素因子。称 $p\notin\mathcal E$ 为允许素数。对 $v\mid p$，令 $F_v=K_v$。这些完成域不分歧，给定方程是好约化极小整模型。令 $E_1(F_v)$ 为实际约化核，并对整数 $k\ge1$ 定义

$$
E_k(F_v)=\{O\}\cup
\{A\in E_1(F_v)\setminus\{O\}:v_p(t_v(A))\ge k\},
\qquad v_p(p)=1.
\tag{12.4}
$$

只有这里的非零形式点才计算参数；对任意实际非零点定义

$$
b_v(A)=
\begin{cases}
v_p(t_v(A)),&A\in E_1(F_v),\\
0,&A\notin E_1(F_v),
\end{cases}
\qquad
A_p(R)=\log p\sum_{A\in S_R}b_{v_p^*}(A),\qquad
N_{p,k}(R)=\#(S_R\cap E_k(F_{v_p^*})).
\tag{12.5}
$$

由 VII.2.1–2.2，印刷页 188–191，及 C.18.3(b)，允许地方满足

$$
b_v(A)\in\mathbb Z_{\ge0},\qquad
\lambda_v(A)=b_v(A)\log p
=\tfrac12\log\max(1,|x(A)|_v).
\tag{12.6}
$$

若横坐标为零，最后一项仍为零；不在非形式点上计算 $-x/y$。

**定理 12.2（实际循环入口、全深度与大素数正三次质量）。** 对定义 12.1 的固定来源及任意整族预选地方，下列结论同时成立。

（一）点集有限，且有准确公式

$$
|S_R|=2tL,\qquad
H(R)=\frac{th}{3}L(L+1)(2L+1)
=\frac{2t}{3\sqrt h}R^3+O_{E,K,\Gamma}(R^2).
\tag{12.7}
$$

（二）对每个允许素数 $p$，实际子群 $\mathcal K_p=\Gamma\cap E_1(F_{v_p^*})$ 无挠且在 $\Gamma$ 中有限指数。自由坐标投影在 $\mathcal K_p$ 上单射，其像是唯一的 $m_p\mathbb Z$，其中 $m_p\ge1$。存在唯一的正自由坐标生成元及实际挠点偏移

$$
Q_p=m_pP+\tau_p,\qquad \tau_p\in T,\qquad
\mathcal K_p=\mathbb ZQ_p,\qquad [\Gamma:\mathcal K_p]=tm_p.
\tag{12.8}
$$

置 $d_p=v_p(t_{v_p^*}(Q_p))\ge1$。全部层与全部倍数的深度准确为

$$
\begin{aligned}
v_p(t_{v_p^*}([a]Q_p))&=d_p+v_p(a)
&& (a\in\mathbb Z\setminus\{0\}),\\
N_{p,k}(R)&=
2\left\lfloor\frac{L}{m_pp^{\max(0,k-d_p)}}\right\rfloor
&& (k\ge1),\\
A_p(R)&=2\log p\left[
\left\lfloor\frac L{m_p}\right\rfloor d_p
+\sum_{j\ge1}\left\lfloor\frac{L}{m_pp^j}\right\rfloor
\right].
\end{aligned}
\tag{12.9}
$$

每个有限 $R$ 的层和、整数倍和及素数支持均有限；$L=0$ 或 $m_p>L$ 时该素数的全部质量为零。式 (12.8) 使用实际的 $\tau_p$，不以 $P$ 的约化阶替代 $m_p$。

（三）存在只依赖固定来源及 $\mathcal E$ 的 $C$，对所有允许素数、所有预选地方和所有 $R\ge1$ 一致有

$$
0\le A_p(R)\le CR^2.
\tag{12.10}
$$

（四）对每个固定地方 $v$，包括无穷、坏约化及分歧地方，有

$$
\sum_{A\in S_R}|\lambda_v(A)|=O_{E,K,\Gamma,v}(R^2).
\tag{12.11}
$$

（五）完整实际点集 $S_R$ 在 $G$ 下重排。令 $S_v(R)=\sum_{A\in S_R}\lambda_v(A)$。对每个有理地方 $r$ 和每个 $v\mid r$，准确有

$$
S_v(R)=\frac1N\sum_{w\mid r}n_wS_w(R).
\tag{12.12}
$$

这是整个实际点集的等式。结合固定有限例外质量，

$$
\sum_{p\notin\mathcal E}A_p(R)=H(R)+O_{E,K,\Gamma,\mathcal E}(R^2).
\tag{12.13}
$$

（六）当 $R\to\infty$，有

$$
\begin{aligned}
\sum_{\substack{p>R\\p\notin\mathcal E}}A_p(R)
&=\frac{2t}{3\sqrt h}R^3+
O_{E,K,\Gamma,\mathcal E}\!\left(\frac{R^3}{\log R}\right),\\
\lim_{R\to\infty}\frac1{R^3}
\sum_{\substack{p>R\\p\notin\mathcal E}}A_p(R)
&=\frac{2t}{3\sqrt h}>0.
\end{aligned}
\tag{12.14}
$$

当 $R>\max\mathcal E$，这两个求和中的素数限制可直接写成 $p>R$。总量、尾部及误差常数对整族预选地方一致。

证明。先确定实际点集。若 $nP+\tau=n'P+\tau'$，在 $\Gamma/T$ 中取像得 $n=n'$，继而 $\tau=\tau'$。高度二次律与配对消去挠点给出 $\widehat h(nP+\tau)=n^2h$，因此 (12.2) 的两种定义一致；它排除了全部零自由坐标，而不只是排除 $O$。有限点集恰有 $2tL$ 个点，且

$$
H(R)=2th\sum_{n=1}^Ln^2
=\frac{th}{3}L(L+1)(2L+1).
\tag{12.15}
$$

$L=R/\sqrt h+O(1)$，固定 $h,t$ 后展开即得 (12.7)，包括闭球边界上所有点。$L=0$ 时有限和为空，准确多项式仍为零。

下面先取得高度截断，再处理所有深度。C.18.1 的连续性与原点正无穷奇性，结合 $E(K_u)$ 的紧性，给出每个地方的固定常数 $c_u\ge0$，使 $\lambda_u(A)\ge-c_u$ 于全部非零点。在 $u\mid p\notin\mathcal E$，由 (12.6) 可取 $c_u=0$。于是只有固定有限多个 $c_u$ 非零，可以定义

$$
C_-=\sum_un_uc_u<\infty,\qquad
-c_v\le\lambda_v(A)\le a_v\widehat h(A)+b_v',
\qquad a_v=\frac N{n_v},\quad b_v'=\frac{C_-}{n_v}.
\tag{12.16}
$$

上界由 (12.3) 对其余地方使用负部下界得到；它对非零挠点同样成立。特别地，对每个允许地方以及 $A\in S_R$，

$$
0\le\lambda_v(A)\le NR^2+C_-.
\tag{12.17}
$$

若 $A$ 属于第 $k$ 层，就有 $k\log p\le NR^2+C_-$。所以

$$
N_{p,k}(R)=0\quad\text{当 }k\log p>NR^2+C_-.
\tag{12.18}
$$

每个允许素数的高层先已截断。若 $A_p(R)>0$，某个点的深度至少为一，故 $\log p\le NR^2+C_-$；这也先给出了素数支持的有限性。另一种等价的支持说明是：深度非零要求横坐标有负赋值，而有限点集的横坐标分母只有有限素数支持。以下所有按层及按素数的求和均在这些有限集合中进行。

现固定一个允许素数和其选定完成域 $F=F_{v_p^*}$。VII.2.1–2.2 把 $E_1(F)$ 识别为整形式群 $\widehat E(\mathfrak m_F)$，参数为 $t=-x/y$，原点对应参数零。这里 $F/\mathbb Q_p$ 不分歧，所以 $v_p(F^\times)=\mathbb Z$、$v_p(p)=1$，且 $p>2$。调用 [Silverman IV.6.3–6.4，印刷页 131–132](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 时，其准确假设是规范化离散赋值下的整数半径 $r>v(p)/(p-1)$。本处可取 $r=1$，因为

$$
1>\frac1{p-1}.
\tag{12.19}
$$

由恒等线性项归一化的形式对数，在整个第一形式层给出保赋值的群同构

$$
\ell_p:E_1(F)\xrightarrow{\ \sim\ }(\mathfrak m_F,+),\qquad
\ell_p(O)=0,\qquad
v_p(\ell_p(A))=v_p(t(A))\quad(A\ne O).
\tag{12.20}
$$

这里的保赋值来自 IV.6.3 对对数及指数的首项估计；使用的是与 $t$ 对应、首项为 $t$ 的形式对数。只在 (12.19) 的范围内应用它，没有把一般分歧地方的整个 $E_1$ 认作这一范围。加法群 $\mathfrak m_F$ 无挠，所以 $E_1(F)$ 无挠，尤其 $T\cap E_1(F)=\{O\}$；允许素数即使整除 $t$，这一步仍成立。

好约化的约化映射 $\Gamma\to\widetilde E(k_F)$ 的像有限，核正是 $\mathcal K_p$，故核在 $\Gamma$ 中有限指数。其自由坐标投影的核是 $T\cap E_1(F)$，所以该投影单射。约化点 $\overline P$ 的阶有限，因而某个正整数倍 $[r]P$ 属于核；投影像非零，必为唯一的 $m_p\mathbb Z$。在核中取投影为 $m_p$ 的点，就得到唯一的 $Q_p=m_pP+\tau_p$。对核中任意点减去相应倍数的 $Q_p$，差既在 $T$ 中又在 $E_1(F)$ 中，只能是 $O$。这证明 $\mathcal K_p=\mathbb ZQ_p$。

更明确地，$\Gamma/\mathbb ZQ_p$ 中每个陪集有唯一代表 $nP+\tau$，其中 $0\le n<m_p$、$\tau\in T$：用 $Q_p$ 消去自由坐标的整除部分；若两个这种代表之差是 $Q_p$ 的倍数，比较自由坐标再比较挠点即得相同。因此指数为 $tm_p$。同时，因约化在 $T$ 上单射，

$$
m_p=\operatorname{ord}\bigl(\overline P\text{ 在 }
\widetilde E(k_F)/\overline T\text{ 中的像}\bigr),\qquad
\operatorname{ord}(\overline P)=m_p\,\operatorname{ord}(\tau_p).
\tag{12.21}
$$

第二式也可直接由 $[r]P=[a]Q_p$ 等价于 $r=am_p$ 且 $[a]\tau_p=O$ 得到。所以除非 $\tau_p=O$，$m_p$ 确实不同于 $P$ 的约化阶。

$Q_p$ 的自由坐标非零，故它非挠、非零，其形式参数也非零，$d_p$ 是有限正整数。对任意非零整数 $a$，形式对数满足 $\ell_p([a]Q_p)=a\ell_p(Q_p)$；$[a]Q_p$ 仍非零，由 (12.20) 得

$$
v_p(t([a]Q_p))=v_p(a\ell_p(Q_p))=d_p+v_p(a).
\tag{12.22}
$$

这同时处理负整数倍，因 $v_p(-a)=v_p(a)$。零倍只用于核的群结构，不参加参数、深度或局部高度求和。入口点在 $S_R$ 中恰为

$$
S_R\cap E_1(F)=
\{[a]Q_p:0<|a|\le M_p\},\qquad
M_p=\left\lfloor\frac L{m_p}\right\rfloor.
\tag{12.23}
$$

对自由坐标 $am_p$，唯一的入口挠点偏移是 $[a]\tau_p$。其余实际挠点提升仍在 $S_R$，但在这个地方不是入口点；这就是 (12.9) 不额外乘以 $t$ 的原因。

由 (12.22)，$[a]Q_p$ 属于第 $k$ 层，当且仅当 $a$ 被 $p^{\max(0,k-d_p)}$ 整除。结合 (12.23) 得 (12.9) 的层计数。再对全部正、负整数倍求和，

$$
\begin{aligned}
A_p(R)
&=2\log p\sum_{a=1}^{M_p}(d_p+v_p(a))\\
&=2\log p\left(M_pd_p+
\sum_{j\ge1}\left\lfloor\frac{M_p}{p^j}\right\rfloor\right).
\end{aligned}
\tag{12.24}
$$

这里 $v_p(a)=\sum_{j\ge1}\mathbf1_{p^j\mid a}$；若 $M_p\ge1$，只会有 $p^j\le M_p$ 的项，若 $M_p=0$ 则所有项均为零。使用整数除法恒等式 $\lfloor\lfloor L/m_p\rfloor/p^j\rfloor=\lfloor L/(m_pp^j)\rfloor$，即为所述准确公式。它包含所有高阶深度，也等于已由 (12.18) 截断的 $\log p\sum_{k\ge1}N_{p,k}(R)$。

这一步中使用的倍数增深律是经典形式群及 EDS 的局部规律。作为文献对应，[Streng，*Divisibility sequences for elliptic curves with complex multiplication*，Proposition 2.8，印刷页 188–189，及 Lemma 3.4，印刷页 195–196](https://msp.org/ant/2008/2-2/ant-v2-n2-p04-s.pdf) 在严格条件 $v(B_{\mathfrak a})>v(p)/(p-1)$ 下给出 $v(B_{\mathfrak a\mathfrak b})=v(B_{\mathfrak a})+v(\mathfrak b)$；其主理想情形来自形式对数。这里仅在实际入口 $Q_p$ 上使用整数倍情形，不需要 CM、理想指标或其原始因子定理；新的消费者是 (12.23) 中保留全部实际挠点纤维的点集。

为证明逐素数统一界，若 $M_p=0$ 则无需估计。否则 $1\le m_p\le L$，将 (12.16) 用于实际生成元 $Q_p$，得到

$$
d_p\log p=\lambda_{v_p^*}(Q_p)
\le Nh\,m_p^2+C_-.
\tag{12.25}
$$

由 (12.24)、$M_p\le L/m_p$ 及几何级数，

$$
\begin{aligned}
A_p(R)
&\le 2\frac L{m_p}(Nh\,m_p^2+C_-)
   +2M_p\frac{\log p}{p-1}\\
&\le 2NhL^2+2(C_-+1)L\\
&\le\left(2N+\frac{2(C_-+1)}{\sqrt h}\right)R^2.
\end{aligned}
\tag{12.26}
$$

第二步用 $\log p\le p-1$、$m_p\ge1$，最后一步用 $L\le R/\sqrt h$ 和 $R\ge1$。这给出 (12.10) 的来源常数，对 $p,R$ 和选定地方均统一，没有删除任何整除固定乘数或 $t$ 的允许素数。

接着支付每个固定地方的完整绝对质量。固定 $v$，这里不要求好约化或不分歧。由 (12.3)，在一个原点参数邻域 $U_0$ 内有 $|\lambda_v(A)+\log|t_v(A)|_v|\le C_v$。局部群差映射在参数中解析且在 $(0,0)$ 处为零，故可取更小的原点邻域 $U$ 和固定 $\kappa_v\ge1$，使 $A,B\in U$ 时 $A-B\in U_0$，且对 $A\ne B$，

$$
|t_v(A-B)|_v
\le\kappa_v\max(|t_v(A)|_v,|t_v(B)|_v).
\tag{12.27}
$$

有限地方可把收敛的形式差级数限制到固定小球，利用无常数项及有界系数得到此界；在给定方程非极小的地方也只需缩小这个固定球。无穷地方则对参数图中的解析差映射，在一个较小实或复圆盘上用有界一阶导数得到此界。这些局部事实由 IV.1 的原点展开和 VII.2 的形式群参数化实现；此处没有使用浅层形式对数。

紧集 $E(K_v)\setminus U$ 上的局部高度有上界。因此可取固定 $h_v\ge0$、$D_v=2C_v+\log\kappa_v\ge0$，使互异的实际非零点满足

$$
\lambda_v(A),\lambda_v(B)>h_v
\quad\Longrightarrow\quad
\lambda_v(A-B)\ge
\min(\lambda_v(A),\lambda_v(B))-D_v.
\tag{12.28}
$$

差点非零，因为 $A,B$ 是不同实际点；只有在此前提下才使用差点的高度与参数。

取固定 $s_0>1+h_v+2(D_v+b_v')$，对 $s\ge0$ 令 $Z_v(s,R)=\{A\in S_R:\lambda_v(A)>s\}$。若 $s\ge s_0$，不同的 $A=nP+\tau$、$B=n'P+\tau'$ 属于 $Z_v(s,R)$，由 (12.16)、(12.28) 有

$$
a_v h(n-n')^2
=a_v\widehat h(A-B)
>s-D_v-b_v'>s/2.
\tag{12.29}
$$

特别是 $n=n'$ 不可能：此时差为非零挠点，而其高度为零，不能支付 (12.29)。所以高层上的自由坐标投影单射；低层仍完整计入全部 $t$ 个提升。

在以 $n\sqrt h$ 为坐标的实线上，这些投影位于 $[-R,R]$，两两距离大于 $r_s=\sqrt{s/(2a_v)}$。若该高层非空，由 (12.16) 有 $s<a_vR^2+b_v'$；因 $s>2b_v'$，故 $r_s<R$。将有限投影点从左到右排列，相邻间隔大于 $r_s$，得到

$$
\#Z_v(s,R)\le1+\frac{2R}{r_s}
\le3\sqrt{2a_v}\,R\,s^{-1/2}\qquad(s\ge s_0).
\tag{12.30}
$$

单点层也满足此界；空层按零计。由同一高度包络，

$$
Z_v(s,R)=\varnothing\quad\text{当 }s\ge U_v(R):=a_vR^2+b_v'.
\tag{12.31}
$$

所以秩一所需的是有限截断积分，而非将 $s^{-1/2}$ 积分到无穷。对有限点集逐点积分其正部，得到

$$
\begin{aligned}
\sum_{A\in S_R}\max(\lambda_v(A),0)
&=\int_0^{U_v(R)}\#Z_v(s,R)\,ds\\
&\le s_0|S_R|+
3\sqrt{2a_v}\,R\int_{s_0}^{\max(s_0,U_v(R))}s^{-1/2}\,ds\\
&\le s_0|S_R|+
6\sqrt{2a_v}\,R\sqrt{\max(s_0,U_v(R))}
=O_v(R^2).
\end{aligned}
\tag{12.32}
$$

末式使用 $|S_R|=2tL=O(R)$、$R\ge1$ 及固定的 $s_0,a_v,b_v'$。由 (12.16)，负部总和至多 $c_v|S_R|=O_v(R)$，因而得到 (12.11)。它保留了真实差点、同一自由坐标上的挠点差、单点层、空层以及所有负部；没有将 §11 的 $d>2$ 无穷积分公式代入 $d=1$。

最后把局部质量接回同一实际来源。$G$ 保持 $T$，在 $\Gamma/T\simeq\mathbb Z$ 上作用为符号。因此对每个 $\sigma\in G$，存在 $\epsilon_\sigma\in\{1,-1\}$ 及 $c_\sigma\in T$，使

$$
\sigma(P)=\epsilon_\sigma P+c_\sigma,\qquad
\sigma(nP+\tau)=\epsilon_\sigma nP+(nc_\sigma+\sigma(\tau)).
\tag{12.33}
$$

这不是假定 $c_\sigma=O$。对每个 $n$，$\tau\mapsto nc_\sigma+\sigma(\tau)$ 是实际 $T$ 的双射；$0<|n|\le L$ 也由符号保持。所以 $\sigma$ 重排整个 $S_R$。绝对规范高度在共轭下不变，也可直接从 VIII.9 的极限定义及绝对横坐标高度的共轭不变性得到。

按 $|u|_{\sigma^{-1}v}=|\sigma(u)|_v$ 运输地方。因 $E$ 的方程定义在 $\mathbb Q$ 上，C.18.1 的唯一性给出

$$
\lambda_v(\sigma A)=\lambda_{\sigma^{-1}v}(A).
\tag{12.34}
$$

对有限 $S_R$ 重编号，得 $S_v(R)=S_{\sigma^{-1}v}(R)$。$G$ 在每个有理地方上方的地方集合中传递，且 $\sum_{w\mid r}n_w=N$，于是得到 (12.12)。无穷地方也在其中：实地方权一，复地方权二。该重编号只给出点集总和的相等，并不使一般单点在不同地方的读数相等。

令固定有限地方清单 $\mathcal D=\{v:v\mid\infty\text{ 或 }v\mid p\in\mathcal E\}$。由 (12.6)、(12.12)，对允许素数准确有

$$
A_p(R)=S_{v_p^*}(R)=\frac1N\sum_{v\mid p}n_vS_v(R).
\tag{12.35}
$$

在已经确定有限支持的和中使用 (12.3)，得到

$$
\sum_{p\notin\mathcal E}A_p(R)
=H(R)-\frac1N\sum_{v\in\mathcal D}n_vS_v(R).
\tag{12.36}
$$

对固定有限清单逐项使用 (12.11)，即为 (12.13)。这里 $H(R)$ 已是绝对规范高度之和；局部次数与 $1/N$ 已在 (12.35)–(12.36) 中支付，不能再把主项除以 $N$。

仅需经典 Chebyshev 上界 $\pi(x)\ll x/\log x$，便由 (12.10) 得

$$
0\le\sum_{\substack{p\le R\\p\notin\mathcal E}}A_p(R)
\le CR^2\pi(R)
\ll\frac{R^3}{\log R}\qquad(R\ge3).
\tag{12.37}
$$

该经典素数计数输入的初等依据与定理 10.3 中相同：区间 $(n,2n]$ 中素数的乘积整除 $\binom{2n}{n}\le4^n$，二进区间求和给出 $\vartheta(x)\ll x$，再分开 $p\le\sqrt x$ 和 $p>\sqrt x$ 即得所用的 $\pi(x)$ 上界。没有使用素数定理或关于约化阶分布的假设。

从有限和 (12.36) 减去 (12.37)，再使用 (12.7)，因 $R^2=O(R^3/\log R)$，得到 (12.14) 及其正极限。每个有理地方的总量已由 (12.12) 固定，所以尾部不依赖所选地方族；(12.26) 的常数对这些选择也一致。证毕。

本定理的局部对数与倍数增深律是上述经典输入；固定来源的完整挠纤维、实际循环入口、秩一有限高度截断与三次尾部在这里组成一个 repo-derived 消费者，不提出全球优先性主张。§11 已有 $d>2$ 的实际高度椭球与差点装箱；这里保留其局部差点机制，但在秩一使用 (12.31) 的有限包络。[Bhakta，*Perfect powers in the product of denominators of elliptic curves*，arXiv:2606.00466v3，§5.1，Lemmas 5.1–5.4，页 19–21](https://arxiv.org/pdf/2606.00466v3) 的约化格与挠点陪集计数提供相关入口背景；其 Lemma 5.3 计数非零横坐标赋值的点，Lemma 5.4 控制小约化像群阶的素数支持。这些入口结论本身不提供 (12.9) 的全部深度质量，也不替代 (12.32) 的固定地方截断证明。

用白话说，每个自由整数坐标原本都带着整束真实挠点。某个允许素数处，进入原点小邻域的点却组成一条真实循环群；在一个自由坐标上至多有一个挠点偏移能进入。找到它的第一个正生成元后，所有更深的费用都由整数倍的素数赋值准确补齐。另一方面，靠近同一局部原点的两个点相减仍很靠近原点，因此它们的自由坐标不能太近。秩一的层数衰减虽不足以积到无穷，全球高度却给出了有限屋顶，足够把每个固定地方和每个允许素数的费用压到二次。完整点集的共轭只重排真实点，绝对高度便把剩余总量接成三次主项；不超过 $R$ 的素数只有 $O(R/\log R)$ 个，支付它们之后，$p>R$ 仍保留这个正主项。

**定理 12.3（现有二次来源及其完整二挠纤维）。** 取

$$
E:y^2=x^3-x,\qquad K=\mathbb Q(\sqrt6),\qquad
P_1=(2,\sqrt6),\qquad H_1=\widehat h_E(P_1)>0.
\tag{12.38}
$$

固定整数 $q\ge1$。对 $\Gamma_q=\mathbb Z([q]P_1)$，定义 12.1 的 $h=q^2H_1$、$t=1$，可取 $\mathcal E=\{2,3\}$。令 $A_{p,q}(R)$ 为该实际来源的完整深度质量，$L_q=\lfloor R/(q\sqrt{H_1})\rfloor$。则

$$
\begin{aligned}
H_q(R)&=\frac{q^2H_1}{3}L_q(L_q+1)(2L_q+1),\\
\sum_{p>R}A_{p,q}(R)
&=\frac{2}{3q\sqrt{H_1}}R^3+
O_q\!\left(\frac{R^3}{\log R}\right),\\
\lim_{R\to\infty}\frac1{R^3}\sum_{p>R}A_{p,q}(R)
&=\frac{2}{3q\sqrt{H_1}}>0.
\end{aligned}
\tag{12.39}
$$

尾部式取 $R>3$。还可在同一曲线和同一域内取

$$
T_2=E[2](\mathbb Q)=\{O,(0,0),(1,0),(-1,0)\},\qquad
\Gamma_{q,2}=\mathbb Z([q]P_1)\oplus T_2.
\tag{12.40}
$$

对此来源，$h=q^2H_1$、$t=4$、$\mathcal E=\{2,3\}$，高度总和为 $4H_q(R)$，且其完整深度质量满足

$$
\sum_{p>R}A_{p,q,2}(R)
=\frac{8}{3q\sqrt{H_1}}R^3+
O_q\!\left(\frac{R^3}{\log R}\right),\qquad
\lim_{R\to\infty}\frac1{R^3}\sum_{p>R}A_{p,q,2}(R)
=\frac{8}{3q\sqrt{H_1}}>0.
\tag{12.41}
$$

证明。定理 7.2 已证明 $P_1$ 非挠，故其在二次子域中的规范高度仍为绝对高度 $H_1>0$，不会随定义域次数重标定。非平凡共轭将 $P_1$ 送到 $-P_1$，所以 $\Gamma_q$ 是稳定的实际无挠秩一子群。乘法二次律给出 $\widehat h([q]P_1)=q^2H_1$。给定整方程判别式为 $64$，二次域判别式为 $24$；因此 $p>3$ 处方程好约化且域不分歧，$\{2,3\}$ 足够，包括 $p=5$。将这些数据代入定理 12.2 得到 (12.39)。

四个列明的二挠点均为有理点，组成 $T_2$，并由共轭逐个固定。因 $[q]P_1$ 非挠，其循环群与 $T_2$ 交于 $O$，所以 (12.40) 确为普通直和、稳定且秩一；全部挠点纤维有四个点。再次使用定理 12.2，即得高度总和与 (12.41)。这里没有断言 $A_{p,q,2}(R)=4A_{p,q}(R)$；不同实际子群有各自的 $m_p,\tau_p,d_p$，只有各自的全球主项按其完整纤维大小给出。所有 $p\mid q$ 的允许素数仍在公式内；$q$ 固定，误差不对移动 $q$ 声称统一。证毕。

本节尾部属于所声明的固定秩一实际来源与完整 $S_R$，不识别原十六次来源的共同小像筛选，不给出原 $V_H$、$p>R^2$ 或 $p>L^4$ 的尾部结论。它不建立量子起源桥，也不给出 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义；这些问题与 (12.14) 的正三次质量之间没有在此声称的实现或归约桥。

## 追加锚（本行以下为增补区）

## 13. 实际整数秩二的跨深度二次预算与二次窗口

**定义 13.1（秩二来源与完整高度球）。** 固定椭圆曲线 $E/\mathbb Q$、有限 Galois 扩张 $K/\mathbb Q$ 和实际有限生成子群 $\Gamma\subset E(K)$，要求 $G=\operatorname{Gal}(K/\mathbb Q)$ 保持 $\Gamma$，且

$$
N=[K:\mathbb Q],\qquad T=\Gamma_{\rm tors},\qquad t=|T|,\qquad
\pi:\Gamma\longrightarrow\Lambda=\Gamma/T,\qquad
\operatorname{rank}_{\mathbb Z}\Lambda=2.
\tag{13.1}
$$

使用 $2\widehat h=h_x+O_E(1)$ 的绝对规范。令 $V=\Lambda\otimes_{\mathbb Z}\mathbb R$，$Q$ 为规范高度在 $V$ 上的正定二次型，$\|x\|=\sqrt{Q(x)}$。正定性直接采用 [Silverman，*The Arithmetic of Elliptic Curves*，第二版，VIII.9.3、VIII.9.6，印刷页 248–252](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)，包括 VIII.9.6 对实向量空间的结论；不以非零整数点上正值代替实正定性。记 $\mu_Q$ 为这个欧氏结构的面积测度，置

$$
D_0=\operatorname{covol}_{\mu_Q}(\Lambda)>0,\qquad
m_0=\min_{0\ne x\in\Lambda}\|x\|>0,\qquad
c_\Gamma=\frac{\mu_Q(\{Q\le1\})}{D_0}=\frac\pi{D_0}.
\tag{13.2}
$$

也可同时用任一 Lebesgue 测度计算分子、分母，比值相同。$c_\Gamma$ 不含 $t$。对实数 $R\ge2$，定义

$$
S_R=\{P\in\Gamma:0<\widehat h(P)\le R^2\},\qquad
H(R)=\sum_{P\in S_R}\widehat h(P).
\tag{13.3}
$$

每个非零 $x\in\Lambda$ 恰有 $t$ 个实际提升，高度均为 $Q(x)$，故 $S_R$ 保留这些提升的完整纤维；整个 $T=\pi^{-1}(0)$ 均排除。无需等变截面。

固定有理整 Weierstrass 方程及全部地方的绝对值。有限地方取 $|p|_v=p^{-1}$，实、复地方取通常绝对值；有限地方 $n_v=[K_v:\mathbb Q_p]$，实地方 $n_v=1$，复地方 $n_v=2$。局部高度采用 Silverman C.18.1–18.3，印刷页 454–455 的规范；对 $P\ne O$，

$$
\widehat h(P)=\frac1N\sum_{v\in M_K}n_v\lambda_v(P),\qquad
\lambda_v(P)=-\log|t_v(P)|_v+O_v(1)\quad(P\longrightarrow O),
\qquad t_v=-x/y.
\tag{13.4}
$$

参数只在原点参数图内使用。每个有理地方 $r$ 上方预选一个 $v_r^*$，同一地方的全部点使用同一嵌入。固定有限素数集 $\mathcal E$，包含方程判别式的素因子、$K/\mathbb Q$ 的分歧素数及 $2$。称 $p\notin\mathcal E$ 为允许素数；不要求加入任何固定乘数 $q$ 或 $t$ 的素因子。对 $v\mid p$，$F=K_v$ 不分歧，原方程是好约化极小整模型，$v_p(F^\times)=\mathbb Z$、$v_p(p)=1$。令

$$
\begin{aligned}
E_k(F)&=\{O\}\cup\{P\in E_1(F)\setminus\{O\}:v_p(t_v(P))\ge k\},\qquad k\ge1,\\
b_v(P)&=
\begin{cases}
v_p(t_v(P)),&P\in E_1(F)\setminus\{O\},\\
0,&P\notin E_1(F),
\end{cases}\qquad(P\ne O),\\
A_p(R)&=\log p\sum_{P\in S_R}b_{v_p^*}(P).
\end{aligned}
\tag{13.5}
$$

$E_1(F)$ 是实际约化核。由 VII.2.1–2.2 与 C.18.3(b)，在允许地方准确有

$$
b_v(P)\in\mathbb Z_{\ge0},\qquad
\lambda_v(P)=b_v(P)\log p
=\tfrac12\log\max(1,|x(P)|_v)\quad(P\ne O).
\tag{13.6}
$$

非形式点不计算 $-x/y$，特别不在参数图之外解释其赋值为深度。

**引理 13.2（实际入口、无挠性与跨层指数）。** 固定一个允许 $p$ 和 $v\mid p$。令

$$
\mathcal K_k=\Gamma\cap E_k(K_v),\qquad
\Lambda_k=\pi(\mathcal K_k)\subset\Lambda,\qquad
D_k=\operatorname{covol}_{\mu_Q}(\Lambda_k),\qquad
\eta_k=\min_{0\ne x\in\Lambda_k}\|x\|.
\tag{13.7}
$$

这些都是实际群与其像：$\mathcal K_k$ 无挠、秩二且在 $\Gamma$ 中有限指数；$\pi|_{\mathcal K_k}$ 单射，$\Lambda_k$ 是满秩子格，且

$$
[\Gamma:\mathcal K_k]=t[\Lambda:\Lambda_k],\qquad
\#(S_R\cap E_k(K_v))
=\#\{x\in\Lambda_k:0<\|x\|\le R\}.
\tag{13.8}
$$

存在有限正整数

$$
d=d_{p,v}=\min_{P\in\mathcal K_1\setminus\{O\}}b_v(P)\ge1
\tag{13.9}
$$

使所有 $k\ge1$ 满足

$$
\Lambda_k=\Lambda_1\quad(1\le k\le d),\qquad
D_k\ge D_1p^{\max(0,k-d)}.
\tag{13.10}
$$

证明。这里可直接使用 §12 的严格形式对数范围，因为 $p>2$、$F/\mathbb Q_p$ 不分歧，整数半径 $1$ 满足 $1>1/(p-1)$。Silverman IV.6.3–6.4，印刷页 131–132，给出首项为 $t$ 的形式对数及其逆；连同 VII.2.2 的实际参数化，有保赋值的群同构

$$
\ell:E_1(F)\xrightarrow{\sim}(p\mathcal O_F,+),\qquad
\ell(O)=0,\qquad v_p(\ell(P))=b_v(P)\quad(P\ne O).
\tag{13.11}
$$

它把 $E_k(F)$ 恰好送到 $p^k\mathcal O_F$，故这些层为子群。加法群 $p\mathcal O_F$ 无挠，因而 $T\cap E_1(F)=\{O\}$，即使 $p\mid t$ 也如此。局部嵌入对 $E(K)$ 单射；所以一个实际非零形式点的对数与形式参数都非零，其赋值是有限整数。

好约化映射 $\Gamma\to\widetilde E(k_F)$ 的像有限，核为 $\mathcal K_1$。又由 (13.11)，$\mathcal K_1/\mathcal K_k$ 注入有限加法群 $p\mathcal O_F/p^k\mathcal O_F$；故全部 $\mathcal K_k$ 都在 $\Gamma$ 中有限指数。它们与 $T$ 交于零，因而无挠、自由秩二，且 $\pi$ 在其上单射。由

$$
\Gamma/(\mathcal K_k+T)\simeq\Lambda/\Lambda_k,\qquad
(\mathcal K_k+T)/\mathcal K_k\simeq T
\tag{13.12}
$$

得到指数公式。每个 $x\in\Lambda_k$ 有唯一属于 $\mathcal K_k$ 的实际提升；$x=0$ 的这个提升只能为 $O$，而非零 $x$ 的提升属于 $S_R$ 当且仅当 $\|x\|\le R$，证明计数等式。其余挠点提升仍在 $S_R$ 中，但不在这个地方的第一层；不能把 (13.8) 额外乘以 $t$。

$\mathcal K_1$ 的秩二保证其有非零点；其全部非零深度组成非空正整数集，故有最小值 $d$，由某个实际 $U\ne O$ 取得。所有入口点在 $k\le d$ 时仍留在该层，所以这些层等于第一层。对任意非零整数 $a$，由 (13.11)，

$$
b_v([a]U)=d+v_p(a).
\tag{13.13}
$$

这里 $[a]U\ne O$，因为入口群无挠。对 $k>d$，$U$ 在 $\mathcal K_1/\mathcal K_k$ 中的阶准确为 $p^{k-d}$：$[a]U\in\mathcal K_k$ 等价于 $p^{k-d}\mid a$，零倍仅用于群的陪集。该有限商群至少有 $p^{k-d}$ 个元素。$\pi$ 在整个 $\mathcal K_1$ 上单射，故

$$
[\Lambda_1:\Lambda_k]=[\mathcal K_1:\mathcal K_k]\ge p^{k-d},
\tag{13.14}
$$

得到 (13.10)。此论证没有选择两个局部对数的商，也没有要求它们在 $\mathbb Q_p$ 上线性相关或线性独立。证毕。

**引理 13.3（二维格的面积项与边界项）。** 对欧氏平面中任一满秩格 $L$，记其协面积为 $D$、最短非零向量长度为 $\eta$。有

$$
\eta^2\le\frac2{\sqrt3}D.
\tag{13.15}
$$

若 $R\ge\eta$，则

$$
\#\{x\in L:0<\|x\|\le R\}\le\frac{6R^2}{D}+\frac{2R}{\eta};
\tag{13.16}
$$

若 $R<\eta$，左边为零。这是经典二维格计数的一种粗上界，所用误差项明确保留最短向量尺度。

证明。取最短向量 $u$。它在 $L$ 中原始，否则除以某个大于一的整数得到更短格向量；原始向量可补为整数基 $(u,w)$。将 $w$ 减去 $u$ 的一个整数倍，使其沿 $u$ 方向的分量落在 $[-\eta/2,\eta/2]$ 内。因 $\|w\|\ge\eta$，其垂直分量 $h=D/\eta$ 满足 $h\ge\sqrt3\eta/2$，这证明 (13.15)。

按 $w$ 的整数系数 $j$ 把格点分到平行于 $u$ 的直线上。这些线到原点的垂直距离为 $|j|h$，故除中央线外至多有 $2\lfloor R/h\rfloor$ 条线与闭圆盘相交；每条线上的点间距为 $\eta$，截弦长至多 $2R$，故至多有 $1+2R/\eta$ 个点。中央线排除原点后有 $2\lfloor R/\eta\rfloor$ 个点。因此

$$
\begin{aligned}
\#\{0<\|x\|\le R\}
&\le 2R/\eta+(2R/h)(1+2R/\eta)\\
&=2R/\eta+2R\eta/D+4R^2/D\\
&\le2R/\eta+6R^2/D,
\end{aligned}
\tag{13.17}
$$

最后一步使用 $\eta\le R$。这包含圆周上的点和全部线端点，没有未支付的常数点误差。证毕。

**定理 13.4（一般实际秩二的完整深度二次预算）。** 对定义 13.1 的固定来源，存在常数 $C$，对每个允许素数 $p$、每个 $v\mid p$ 和所有 $R\ge2$ 同时有

$$
0\le\log p\sum_{P\in S_R}b_v(P)\le CR^2.
\tag{13.18}
$$

常数只依赖固定曲线、域、实际子群、方程和有限例外集；不依赖素数、所选地方或整族地方选择。全部形式层均参加，固定乘数的素因子不被删去。

证明。先直接采用 §11 的全球负部包络，而不使用其 $d>2$ 的层求和结论。具体地，C.18.1 的连续性、原点正无穷奇性与各 $E(K_u)$ 的紧性给出固定 $c_u\ge0$，使 $\lambda_u(P)\ge-c_u$ 于所有非零局部点。在允许有限地方可由 (13.6) 取 $c_u=0$。仅有限多个 $c_u$ 非零，故

$$
B=\sum_u n_uc_u<\infty,\qquad
-c_v\le\lambda_v(P)\le\frac N{n_v}\widehat h(P)+\frac B{n_v}
\quad(P\in E(K)\setminus\{O\}).
\tag{13.19}
$$

右边由 (13.4) 对其余地方使用下界得到，对非零挠点也成立。在每个允许地方，统一放宽为

$$
b_v(P)\log p\le N\widehat h(P)+B.
\tag{13.20}
$$

令 $N_k(R)=\#(S_R\cap E_k(K_v))$。引理 13.2 保证它是 $\Lambda_k$ 内非零格点的准确计数。由 (13.20)，

$$
N_k(R)=0\quad\text{若 }k\log p>NR^2+B,\qquad
A_{p,v}(R)=\log p\sum_{k\ge1}N_k(R).
\tag{13.21}
$$

等式使用深度的整数性，右边是有限和。若任何点的深度为正，则 $\log p\le NR^2+B$，故一个固定 $R$ 的全部素数支持也有限。也可由有限点集的横坐标分母支持得到这个结论。这里没有在 $O$ 或任一高度零点上定义求和项。

下面支付面积项的全部深度。取 $\Lambda_1$ 的最短非零向量及其唯一入口提升 $W$。其深度至少为 $d$，从 (13.20) 与 (13.15) 得

$$
d\log p\le N\eta_1^2+B\le\frac{2N}{\sqrt3}D_1+B.
\tag{13.22}
$$

每个 $D_1$ 都是 $D_0$ 的正整数倍，故 $D_1\ge D_0$。结合 (13.10) 和几何级数，因 $p\ge3$、$d\ge1$，有

$$
\begin{aligned}
\log p\sum_{k\ge1}\frac1{D_k}
&\le\frac{\log p}{D_1}
\left(d+\sum_{j\ge1}p^{-j}\right)\\
&=\frac{\log p}{D_1}\left(d+\frac1{p-1}\right)\\
&\le\frac32\frac{d\log p}{D_1}\\
&\le\frac32\left(\frac{2N}{\sqrt3}+\frac B{D_0}\right).
\end{aligned}
\tag{13.23}
$$

这是跨深度使用实际形式群的步骤：共同初始深度 $d$ 的费用由入口格的协面积支付；此后即使某些短向量方向很晚才改变，一个实际 $U$ 的整数倍已经迫使商群至少有 $p^{k-d}$ 个元素。写到无穷的只是正数上界，不涉及实际局部高度级数的收敛交换。

浅层 $k\log p\le2B$ 可直接支付。引理 13.3 对固定 $\Lambda$ 给出，对 $R\ge2$，

$$
\#\{x\in\Lambda:0<\|x\|\le R\}
\le C_\Lambda R^2,\qquad C_\Lambda=\frac6{D_0}+\frac1{m_0}.
\tag{13.24}
$$

当 $R<m_0$ 左边为零；否则由 (13.16) 及 $2R/m_0\le R^2/m_0$ 得到。由投影单射，$N_k(R)$ 不大于这个数。因此全部浅层质量至多 $2BC_\Lambda R^2$；$B=0$ 时无此类层。

对高层 $k\log p>2B$，将 (13.20) 用于 $\Lambda_k$ 的最短向量的实际非零提升，得

$$
\eta_k^2\ge\frac{k\log p-B}{N}>\frac{k\log p}{2N}.
\tag{13.25}
$$

若 $N_k(R)>0$，则 $\eta_k\le R$，引理 13.3 可用；空层直接忽略。记

$$
M=\left\lfloor\frac{NR^2+B}{\log p}\right\rfloor.
\tag{13.26}
$$

面积项由 (13.23) 控制，其全部贡献至多
$9(2N/\sqrt3+B/D_0)R^2$。边界项使用 (13.25) 与完整截断 (13.26)，得到

$$
\begin{aligned}
\log p\sum_{\substack{1\le k\le M\\k\log p>2B}}\frac{2R}{\eta_k}
&\le2\sqrt{2N}R\sqrt{\log p}\sum_{k=1}^M k^{-1/2}\\
&\le4\sqrt{2N}R\sqrt{M\log p}\\
&\le4\sqrt{2N}R\sqrt{NR^2+B}\\
&\le4\sqrt{2N(N+B/4)}R^2.
\end{aligned}
\tag{13.27}
$$

$M=0$ 时此和为空；$M\ge1$ 时用 $\sum_{k=1}^M k^{-1/2}\le2\sqrt M$。所以可取

$$
C=2BC_\Lambda+
9\left(\frac{2N}{\sqrt3}+\frac B{D_0}\right)
+4\sqrt{2N(N+B/4)}.
\tag{13.28}
$$

这个常数没有使用 $p$ 或 $v$。所有边界、全部浅层和从第一层到高度屋顶的所有高层均已计入。若 $\Gamma$ 含固定 $[q]$ 的乘数，(13.13) 对其实际入口仍保留 $v_p(a)$，而入口本身保留乘数造成的深度；此处没有除以 $q$ 或假设 $p\nmid q$。证毕。

**定理 13.5（每个固定地方的绝对质量）。** 对每个固定地方 $v$，包括坏约化、分歧和无穷地方，有

$$
\sum_{P\in S_R}|\lambda_v(P)|
=O_{E,K,\Gamma,v}\bigl(R^2\log(2+R)\bigr).
\tag{13.29}
$$

证明。使用 (13.19)，写 $a=N/n_v>0$、$b=B/n_v\ge0$。引理 13.3 给出 $|S_R|\le tC_\Lambda R^2$。所以负部至多 $c_vtC_\Lambda R^2$。以下只处理正部，并保留 §11 的局部差点机制及其有限屋顶。

由 (13.4)，可在原点邻域 $U_0$ 中取固定 $C_v\ge0$，使
$|\lambda_v(A)+\log|t_v(A)|_v|\le C_v$ 于非零点。再取较小原点邻域 $U$，使不同的 $A,B\in U$ 满足 $A-B\in U_0$，且

$$
|t_v(A-B)|_v\le\kappa_v\max(|t_v(A)|_v,|t_v(B)|_v),\qquad \kappa_v\ge1.
\tag{13.30}
$$

这个事实只用局部解析群律：在有限地方，将收敛的差级数限制到足够小的参数球，其无常数项给出该界；在实、复地方，把解析差映射限制到较小圆盘，其一阶导数有界，同样得到该界。坏约化或分歧只影响这个固定邻域和常数，不要求其整个第一层满足形式对数阈值。紧集 $E(K_v)\setminus U$ 上局部高度有上界，故有固定 $h_v\ge0$，使 $\lambda_v(A)>h_v$ 蕴涵 $A\in U$。两次使用参数比较得到，对不同的实际点，

$$
\lambda_v(A),\lambda_v(B)>h_v
\quad\Longrightarrow\quad
\lambda_v(A-B)\ge\min(\lambda_v(A),\lambda_v(B))-D_v,
\qquad D_v=2C_v+\log\kappa_v.
\tag{13.31}
$$

差点非零，才使用它的局部高度；未在 $O$ 上计算参数或高度。

取固定 $s_0>1+h_v+2(D_v+b)$，令
$Z(s,R)=\{P\in S_R:\lambda_v(P)>s\}$。当 $s\ge s_0$，两个不同的 $P,P'\in Z(s,R)$ 由 (13.19)、(13.31) 满足

$$
a\|\pi(P)-\pi(P')\|^2
=a\widehat h(P-P')>s-D_v-b>s/2.
\tag{13.32}
$$

这同时证明高层上的投影单射：若两个不同点属于同一挠点纤维，其非零差点高度为零，便与 (13.32) 矛盾。低层仍保留每个纤维的全部 $t$ 个点。

置 $r_s=\sqrt{s/(2a)}$。若 $Z(s,R)$ 非空，则 $s<aR^2+b$；因 $s>2b$，有 $r_s<R$。以投影点为中心、半径为 $r_s/2$ 的开圆盘两两不交，且均包含在半径 $R+r_s/2$ 的圆盘内。所以

$$
\#Z(s,R)\le(1+2R/r_s)^2\le\frac{18aR^2}{s}
\quad(s\ge s_0).
\tag{13.33}
$$

空层也满足此界。又由 (13.19)，$s\ge aR^2+b$ 后 $Z(s,R)$ 为空。对有限点集逐点积分正部，得到

$$
\begin{aligned}
\sum_{P\in S_R}\max(\lambda_v(P),0)
&=\int_0^\infty\#Z(s,R)\,ds\\
&\le s_0tC_\Lambda R^2+
18aR^2\max\left(0,\log\frac{aR^2+b}{s_0}\right)\\
&=O_v\bigl(R^2\log(2+R)\bigr).
\end{aligned}
\tag{13.34}
$$

加回已支付的负部即得 (13.29)。这里仅使用积分至二次屋顶的 $s^{-1}$ 界，既未将其积分到无穷，也未声称逐点 $O_v(\log R)$。证毕。

**定理 13.6（完整 Galois 点集的平均与四次高度主项）。** 定义 13.1 的 $S_R$ 是有限且 $G$ 稳定的实际点集。令 $S_v(R)=\sum_{P\in S_R}\lambda_v(P)$。对每个有理地方 $r$ 和每个 $v\mid r$，包括实、复地方，准确有

$$
S_v(R)=\frac1N\sum_{w\mid r}n_wS_w(R).
\tag{13.35}
$$

此外

$$
|S_R|=t c_\Gamma R^2+O_{E,K,\Gamma}(R),\qquad
H(R)=\frac{t c_\Gamma}{2}R^4+O_{E,K,\Gamma}(R^3).
\tag{13.36}
$$

证明。规范高度对 $G$ 不变，因为绝对横坐标高度不变，整数乘法与 $G$ 交换，故其极限定义不变。$g\Gamma=\Gamma$ 因而使 $g$ 重排完整 $S_R$；它也保持 $T$，所以删去的是同一个完整零高度纤维。局部高度的唯一性及 $E/\mathbb Q$ 的固定方程给出

$$
\lambda_v(gP)=\lambda_{g^{-1}v}(P),\qquad
S_v(R)=S_{g^{-1}v}(R).
\tag{13.37}
$$

Galois 群在 $r$ 上方地方上传递，而 $\sum_{w\mid r}n_w=N$，所以得到 (13.35)。在无穷地方，实嵌入权为 $1$；一对共轭复嵌入合为一个地方、权为 $2$，同一总次数公式仍成立。该论证只在实际点集上重编号，不选 $G$ 等变截面，也不把一般单点在不同地方的局部高度认作相等。§9 的单点地方差异例子正说明后一个强化不能从 Galois 来源推出。

高度计数直接使用定理 11.2 中与维数无关的格胞比较；为明确闭球边界，取 $\Lambda$ 的有界半开基本平行体 $F$，在其中有 $\|y\|\le\rho$。记 $M(u)=\#\{x\in\Lambda:0<\|x\|\le u\}$。格胞铺满平面给出

$$
c_\Gamma(u-\rho)_+^2\le M(u)+1\le c_\Gamma(u+\rho)^2,
\qquad M(u)=c_\Gamma u^2+O_{Q,\Lambda}(u+1).
\tag{13.38}
$$

左边因为半径 $(u-\rho)_+$ 的圆盘落在中心范数不超过 $u$ 的格胞并中；右边因为这些格胞落在半径 $u+\rho$ 的圆盘中。半开格胞消去面积重叠，闭圆盘上的格点全部计入。正定性与格的离散性保证每个 $M(u)$ 有限。完整实际提升给出 $|S_R|=tM(R)$；对每个非零格点积分，有准确恒等式

$$
H(R)=t\left(R^2M(R)-\int_0^R2uM(u)\,du\right).
\tag{13.39}
$$

代入 (13.38)，主项为 $t c_\Gamma(R^4-R^4/2)$，误差为 $O(R^3)$，得 (13.36)。零格点从始至终不参加求和；挠点只通过完整提升数 $t$ 出现。$H(R)$ 已是绝对规范高度之和，不再除以 $N$。证毕。

**定理 13.7（二次移动素数窗口外的正四次质量）。** 对同一固定来源，全部允许素数的完整质量满足

$$
\sum_{p\notin\mathcal E}A_p(R)
=H(R)+O_{E,K,\Gamma,\mathcal E}\bigl(R^2\log(2+R)\bigr).
\tag{13.40}
$$

当 $R\longrightarrow\infty$ 时，

$$
\begin{aligned}
\sum_{\substack{p>R^2\\p\notin\mathcal E}}A_p(R)
&=H(R)+O_{E,K,\Gamma,\mathcal E}(R^4/\log R)\\
&=\frac{t c_\Gamma}{2}R^4+
O_{E,K,\Gamma,\mathcal E}(R^4/\log R),\\
\lim_{R\to\infty}\frac1{R^4}
\sum_{\substack{p>R^2\\p\notin\mathcal E}}A_p(R)
&=\frac{t c_\Gamma}{2}>0.
\end{aligned}
\tag{13.41}
$$

若 $R^2>\max\mathcal E$，尾部的素数条件可写成 $p>R^2$。每个固定 $R$ 的和均有有限支持，所有误差常数对整族预选地方一致。

证明。先按完整有限点集求和 (13.4)，再在每个有理地方应用 (13.35)。允许地方的 $S_{v_p^*}(R)$ 就是 $A_p(R)$，因此准确有

$$
H(R)=S_{v_\infty^*}(R)
+\sum_{p\in\mathcal E}S_{v_p^*}(R)
+\sum_{p\notin\mathcal E}A_p(R).
\tag{13.42}
$$

有限支持由 (13.21) 已知，也可直接由各非零点的有限分母支持得到；无需交换未证收敛的级数。定理 13.5 支付固定有限例外及无穷地方，得到 (13.40)。这些地方每个有理地方上方只有有限多个选择，故其固定地方误差可对全部选择取共同上界。

使用经典 Chebyshev 上界 $\pi(x)\ll x/\log x$，与定理 13.4 相乘，得

$$
0\le\sum_{\substack{p\le R^2\\p\notin\mathcal E}}A_p(R)
\le CR^2\pi(R^2)\ll\frac{R^4}{\log R}.
\tag{13.43}
$$

该素数计数输入与定理 10.3 相同：二项式系数界给出 $\vartheta(x)\ll x$，再把素数分成 $p\le\sqrt x$ 和 $p>\sqrt x$ 即得所需上界。这里不使用素数定理或等分布。由 (13.40) 减去 (13.43)，并用
$R^2\log(2+R)=O(R^4/\log R)$，得到第一式。再代入 (13.36) 并用 $R^3=O(R^4/\log R)$，得到其余结论。局部次数仅在 (13.4)、(13.35) 中用于绝对高度分解；(13.41) 的主项不会再除以域次数。证毕。

**定理 13.8（同一既有点的实际整数秩二消费者）。** 取

$$
E:y^2=x^3-x,\qquad K=\mathbb Q(i,\sqrt6),\qquad
P_1=(2,\sqrt6),\qquad H_P=\widehat h_E(P_1)>0,
\qquad \Gamma_q=\mathbb Z[i]\cdot[q]P_1,
\tag{13.44}
$$

其中 $q\ge1$ 为固定整数，$[i](x,y)=(-x,iy)$。则 $\Gamma_q$ 是实际无挠、Galois 稳定的整数秩二群，以 $([q]P_1,[q][i]P_1)$ 为整数基，且

$$
Q(a,b)=q^2H_P(a^2+b^2),\qquad t=1,\qquad
c_{\Gamma_q}=\frac\pi{q^2H_P}.
\tag{13.45}
$$

可取 $\mathcal E=\{2,3\}$。对完整实际高度球及其质量 $A_{p,q}(R)$，有

$$
\begin{aligned}
H_q(R)&=\frac\pi{2q^2H_P}R^4+O_q(R^3),\\
\sum_{p>R^2}A_{p,q}(R)
&=\frac\pi{2q^2H_P}R^4+O_q(R^4/\log R),\\
\lim_{R\to\infty}\frac1{R^4}\sum_{p>R^2}A_{p,q}(R)
&=\frac\pi{2q^2H_P}>0.
\end{aligned}
\tag{13.46}
$$

尾部式在 $R\ge2$ 时已无例外素数落在求和范围内；渐近式的常数依赖固定 $q$ 和所声明的来源。

证明。定理 7.2 已证明 $P_1$ 非挠，此处直接复用，不重作非挠性判定。$K$ 是两个独立二次扩张的合成，次数为 $4$；其 Galois 自同构写成 $g(i)=\epsilon i$、$g(\sqrt6)=\delta\sqrt6$，$\epsilon,\delta\in\{\pm1\}$。因此

$$
g([q]([a]P_1+[b][i]P_1))
=[q]([\delta a]P_1+[\delta\epsilon b][i]P_1),
\tag{13.47}
$$

证明实际群稳定。若 $[q]([a]P_1+[b][i]P_1)$ 为挠点，应用端同态 $[a]-[b][i]$，由 $[i]^2=[-1]$ 得到 $[q(a^2+b^2)]P_1$ 为挠点。$P_1$ 非挠迫使 $a=b=0$。这同时证明无挠性和两整数方向的独立性，不只证明没有零关系。

定理 9.3 已有 $\widehat h([i]P_1)=H_P$：其依据是 $x([i]A)=-x(A)$、绝对横坐标高度不变及规范高度极限。再取固定 $\sqrt6$ 而翻转 $i$ 的自同构，它固定 $P_1$、把 $[i]P_1$ 送到 $-[i]P_1$。规范高度配对在 Galois 下不变，所以这两个方向的交叉配对等于其负值，因而为零。整数倍二次律给出 (13.45) 的 $Q$。

在该整数基中取协面积为 $1$ 的测度，单位高度椭球为半径 $(q\sqrt{H_P})^{-1}$ 的圆盘，其面积为 $\pi/(q^2H_P)$。因此 (13.45) 的 $c_{\Gamma_q}$ 正确，且完整 $S_R$ 正是所有满足

$$
(a,b)\in\mathbb Z^2\setminus\{(0,0)\},\qquad
q^2H_P(a^2+b^2)\le R^2
\tag{13.48}
$$

的实际点，无额外筛选。给定曲线判别式为 $64$，两个二次子域的判别式为 $-4,24$，所以合成域在 $p>3$ 不分歧，方程在那里好约化且极小；$\{2,3\}$ 足够。将这些数据代入定理 13.6–13.7 得到 (13.46)。其四次系数不再除以 $4$，因为 $H_P$ 和 $H_q(R)$ 本来就是绝对高度。$p\mid q$ 且 $p>3$ 时仍使用实际入口及全部深度，未被删除。经典 CM 结构只在本例中提供 $[i]$ 及第二个整数方向；一般预算定理 13.4 不使用 CM。证毕。

**说明 13.9（逐层装箱的边界与实际跨层关系）。** §11 的逐层差点装箱，在两个整数方向上只给出高层数量 $O(R^2/(k\log p))$。若直接从第一层加到二次高度屋顶，$\log p$ 抵消后留下截断调和和；这个方法只能给 $O(R^2\log(2+R))$，不能由此取得定理 13.4。问题在于逐层估计丢掉了不同层之间的群关系。

仅加上“嵌套满秩格”和“非零向量的层深不超过其长度平方”，确实仍不够。为给出具体边界，在普通欧氏平面的 $\mathbb Z^2$ 中，定义

$$
j(k)=\min\{j\in\mathbb Z_{\ge0}:k\le9^j\},\qquad
L_k=3^{j(k)}\mathbb Z^2\quad(k\ge1).
\tag{13.49}
$$

这是嵌套满秩子格。对非零整数向量 $z$，令 $h(z)$ 为同时整除其两个坐标的 $3$ 的最高幂的指数；此指数有限。它的完整抽象深度为

$$
\beta(z)=\max\{k:z\in L_k\}=9^{h(z)}\le\|z\|^2,
\qquad \min_{0\ne z\in L_k}\|z\|^2=9^{j(k)}\ge k.
\tag{13.50}
$$

但这个深度的总量没有二次界。具体地，取整数 $J\ge1$、$R_J=2\cdot3^J$。对于每个 $1\le j\le J$ 及所有整数 $9^{j-1}<k\le9^j$，都有 $L_k=3^j\mathbb Z^2$。半径 $R_J$ 的圆盘包含方盒 $[-3^J,3^J]^2$，其中属于 $L_k$ 的非零点至少有 $4\cdot9^{J-j}$ 个。这一层段有 $8\cdot9^{j-1}$ 层，故有限的逐层求和给出

$$
\sum_{\substack{z\in\mathbb Z^2\\0<\|z\|\le R_J}}\beta(z)
\ge\sum_{j=1}^J8\cdot9^{j-1}\cdot4\cdot9^{J-j}
=\frac89J R_J^2.
\tag{13.51}
$$

所以这些抽象条件允许 $R^2\log R$ 的质量；它们不能代替实际椭圆群。这个例子不满足实际形式对数的整数倍规律：$\beta(3z)=9\beta(z)$，而在允许素数 $3$ 的实际第一形式层中，应有 $b_v([3]P)=b_v(P)+1$。它也不满足 (13.10) 的跨层指数下界，因而不是定理 13.4 的反例。

用白话说，逐层装箱每次只看当前层，忘记同一个入口点及其整数倍必须贯穿后面各层。实际形式对数把这些倍数连在一起：共同入口若已经很深，它的短向量高度必须支付初始费用；此后每增加一层，商群至少要容纳相应的更多整数倍。二维格计数的面积部分因此按几何级数支付，细长边界部分则只需要加到全球高度给出的有限屋顶。这样消失的是逐层粗估的对数损失，不是额外假设某个局部对数商为有理数。这个机制讨论的是整数秩和算术群，并不把二维整数参数解释成物理空间或量子公理。

**说明 13.10（原始来源对应与保留边界）。** 本节直接复用定理 7.2 的 $P_1$ 非挠性、定理 9.3 的 $[i]$ 高度不变性、定理 11.2 的格胞体积比较与 Galois 重编号，以及 §§11–12 的负部包络、局部差点关系和严格形式对数范围。§11 的 $d>2$ 求和结论并未被当成秩二结论；§12 的循环入口也未被当成秩二入口。一般秩二消费者所需的额外桥是引理 13.2 的实际满秩入口与跨层指数，以及 (13.22)–(13.27) 对面积项和边界项的分别支付。二维格的基约化、协面积比较和圆盘计数是经典几何事实，引理 13.3 仅给出这里使用的具体粗界和完整证明，不作为新的经典格定理提出。

[Silverman IV.6.3–6.4，印刷页 131–132](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf) 的假设是特征零完备离散赋值域、整形式群，以及整数半径 $r>v(p)/(p-1)$；本节在不分歧且 $p>2$ 时取 $r=1$，由此取得保赋值、无挠性和准确整数倍增深。VII.2.1–2.2，印刷页 188–191，负责好约化映射、有限约化像及实际约化核与形式群的对应。VIII.9.3、VIII.9.6，印刷页 248–252，负责绝对高度规范、消去挠点的二次型和实正定性。C.18.1–18.3，印刷页 454–455，负责局部连续性、原点奇性、绝对次数加权与好约化公式；坏地方不需要另加逐点对数估计。这些原始结果各自只承担列明的输入，完整深度质量由本节消费者组合取得。

[Bhakta，*Perfect powers in the product of denominators of elliptic curves*，arXiv:2606.00466v3，§5.1，Lemmas 5.1–5.4，页 19–21](https://arxiv.org/pdf/2606.00466v3) 的场景为 $E(\mathbb Q)$ 的自由生成元、整数坐标和好约化素数。Lemma 5.1 给出约化核及模挠约化核的满秩格；Lemma 5.2 估计整数格陪集中的盒点；Lemma 5.3 计数高度受限且横坐标赋值非零的点；Lemma 5.4 控制小约化像群阶的素数支持。它们提供入口、计数和支持的相关背景，不是全部深度质量的结论。本节没有把其中的有理点条件直接替换成任意数域条件：数域中的实际群、有限指数、无挠性与每个挠纤维至多一个入口的对应，已在引理 13.2 重新建立；所需二维计数用的是 (13.16) 的明确尺度，尾部仅需经典 Chebyshev。这里陈述的是这些既有输入在固定实际秩二来源上的综合应用，不提出文献首次性主张。

一般预算没有 CM、局部对数商的子域归属或等变截面前提；它保留固定 $E,K,\Gamma$、完整实际挠纤维、正定规范高度和固定有限例外集。具体例子的 $q$ 固定，所有 $p\mid q$ 的允许素数深度仍在账内，但常数不对移动 $q$ 或移动来源宣称统一。定理 13.7 的对象是完整 Galois 稳定高度球及 $p>R^2$，没有把它认作原矩形盒、原共同小像筛选或原 $p>L^4$ 的统计；原 RG004 的 $V_H$、共同小像桥、移动来源统一性、量子起源及 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义均未由本节建立。点集重编号也不提供单点地方等式。

## 追加锚（本行以下为增补区）
