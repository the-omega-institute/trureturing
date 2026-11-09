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
