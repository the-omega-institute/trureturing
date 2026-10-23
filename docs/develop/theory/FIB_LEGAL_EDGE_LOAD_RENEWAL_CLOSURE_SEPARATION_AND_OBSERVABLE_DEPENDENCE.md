# FIB 合法边调和负载：更新律弱闭包、统一分离与可观察依赖

本卷给出普通数学证明。对象始终是同一个归一化两侧平稳 no11 概率律及其实际柱概率；本卷没有 Lean 核验。新增综合是：有限均值 iid 间隙律的六间隙非达到障碍、事件条件独立族的完整分类及精确弱闭包、该族与调和最优值的统一分离、近最优律共有的有限依赖见证，以及整个至多三个正平稳质量边发射状态域的排除。任意有限维非重置隐藏达到问题保持开放。

## 1. 原目标与供应接口

**定义 1.1（完整词图及实际律）。** 对每个整数 $n\ge1$，令

$$
B_n=\{b\in\{0,1\}^n:b_ib_{i+1}=0\ (1\le i<n)\},\qquad
X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

$\Gamma_n$ 含全部 $B_n$ 顶点和全部合法 Hamming 一位差边，不把首尾相接。测试插入时取 $b_0=b_{n+1}=0$。对整个概率单纯形定义

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu_b,\mu_c),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

记 $(Tx)_i=x_{i+1}$，$\mathcal S$ 为 $X$ 上全部 $T$ 不变 Borel 概率律，带弱拓扑；$[w]_a$ 指从坐标 $a$ 开始的词柱，$[w]=[w]_0$。平稳性使柱概率不依赖起点。$P_n$ 恒为一个 $P\in\mathcal S$ 的长度 $n$ 实际边缘。零质量不删词或边；全零、合法端点、任意分组接缝均在原域中。

**约定 1.2（复用的普通结果）。** 下表的编号属于所链接供应卷。

| 供应 | 本卷使用及归属 |
| --- | --- |
| [增长卷][P6] 引理 3.1、定理 3.2、5.2、7.3、推论 5.3 | 调和连续、凹性、有限对偶；$c_\star=\lim_n\kappa_n/n$，$nc_\star\le\kappa_n\le(n+1)c_\star$，$1800/12559\le c_\star\le3-2\sqrt2$。只用正文的有理下界及初等上界。 |
| [平稳卷][P1] §2、定理 3.1 | 每个平稳律的无限外部风险等于 $d(P)$，上半连续性、普适上界及一个实际达到律。 |
| [普适缺陷卷][P4] 定理 3.1、定义 4.1、命题 4.2、定理 5.1、6.2 | 每个达到者全支撑；完整 $\Theta_N$ 与联合律；实际隐藏分量风险；固定维数有限分离等价。 |
| [非达到卷][P2] §5–6、[唯一最优卷][P5] 定理 3.1、式（3.11） | 已有平稳正流及后验平方余项方法；有限正最优点和缺陷恒等式是普适支撑定理的供应。 |
| [遍历卷][P0] 定理 2.1、[完备卷][P3] 定理 1.4、命题 6.2 | 已有分量后验转移、有限可见阶逼近和四隐藏状态反例；不从有限隐藏推出有限可见阶。 |

特别地，$c_\star>1/7>0$，因为 $12559<12600$；$c_\star<7/40$ 由 $3-2\sqrt2<7/40$ 得到。这些输入不使用供应卷的数学程序或其小数证书。

**约定 1.3（风险与拓扑）。** 置 $\mathcal E_0=\sigma(X_j:j\ne0)$，$\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r)$。供应接口为

$$
D_r(P)=\sum_{\substack{u,v\in B_r\\u_r=v_1=0}}h(P([u0v]),P([u1v])),\qquad
d(P)=\lim_{n\to\infty}\frac{\Phi_n(P_n)}n
=\inf_rD_r(P)=\mathbb E_P[(X_0-q_P)^2]\le c_\star,
\tag{1.1}
$$

其中 $q_P=\mathbb E_P[X_0\mid\mathcal E_0]$。双点纤维质量为 $s,t$ 时，其风险是 $s(t/(s+t))^2+t(s/(s+t))^2=h(s,t)$；强制零单点风险为零；零总质量纤维任选后验而加权项为零。条件投影收敛给 $D_r\downarrow d$，每个 $D_r$ 是连续柱函数，故 $d$ 上半连续。有限词内部的风险至多 $D_r$，两端共 $2r$ 项各至多 $1/4$，故

$$
d(P)\le\Phi_n(P_n)/n\le((n-2r)D_r(P)+r/2)/n\quad(n\ge2r+1).
$$

这说明使用的是原全词目标，全部长度及 $n=3N$ 的密度相同。$X$ 为紧可度量空间，$\mathcal S$ 是其概率空间的闭子集，因而紧。全局最大值 $c_\star$ 由供应达到律取到。

## 2. 从间隙序列到一个实际平稳律

**定义 2.1（有限均值悬挂）。** 间隙 $g_i\in\mathbb N_{\ge1}$ 是相邻两个 $1$ 之间的零数。设 $\nu$ 是 $(\mathbb N_{\ge1})^{\mathbb Z}$ 上一个移位 $S$ 不变概率律，$\mu=\mathbb E_\nu(g_0+1)<\infty$。在

$$
\Omega_\nu=\{(g,j):0\le j\le g_0\},\qquad
\widehat\nu(dg,j)=\mu^{-1}\nu(dg)
$$

上定义 $U(g,j)=(g,j+1)$（$j<g_0$），$U(g,g_0)=(Sg,0)$。可见位 $x_i(g,j)$ 等于 $U^i(g,j)$ 的相位为零的示性值。其推前律记 $P_\nu$。若 $\nu=w^{\mathbb Z}$，其中

$$
w_n\ge0\ (n\ge1),\qquad \sum_{n\ge1}w_n=1,\qquad
\mu=\sum_{n\ge1}(n+1)w_n<\infty,
\tag{2.1}
$$

则记 $P_w=P_\nu$，称为平衡 iid 零间隙更新律。iid 指在已观测事件处重新编号的间隙序列，不指平稳时钟上的可见位独立。

**引理 2.2（归一化、两侧性与柱概率）。** 每个定义 2.1 的 $P_\nu$ 都属于 $\mathcal S$，且 $P_\nu([1])=1/\mu$。对 $P_w$，置 $\overline w_r=\sum_{n\ge\max(1,r)}w_n$，$r\ge0$。对任意含 $1$ 的合法词，唯一写成 $0^r1\,0^{n_1}1\cdots0^{n_k}1\,0^s$（$k\ge0$），有

$$
P_w([0^r1\,0^{n_1}1\cdots0^{n_k}1\,0^s])
=\mu^{-1}\overline w_r\overline w_s\prod_{i=1}^kw_{n_i},\qquad
P_w([0^m])=\mu^{-1}\sum_{n\ge m}(n-m+1)w_n\quad(m\ge1).
\tag{2.2}
$$

$P_w$ 在所有合法柱上为正，当且仅当所有 $w_n>0$。

证明。$\widehat\nu(\Omega_\nu)=\mu^{-1}\mathbb E(g_0+1)=1$。$U$ 可逆：相位正时减一，相位零时退到 $(S^{-1}g,g_{-1})$。对任意有界可测 $f$，相位求和给

$$
\int(f\circ U-f)\,d\widehat\nu
=\mu^{-1}\int(f(Sg,0)-f(g,0))\,d\nu=0.
$$

因此归一化律在两侧整数时间平稳。相邻事件距离为 $g_i+1\ge2$，包括跨屋顶接缝，故输出合法。相位零的质量为 $1/\mu$，在此条件下完整间隙序列的律为 $\nu$；这是实际事件条件律（Palm 律）。iid 情形中，从词内第一个事件定位，前一间隙至少为 $r$，后一端间隙至少为 $s$，内部间隙取所列值，独立性给第一式，包括 $r=0$、$s=0$。一个长 $n$ 的零段有恰 $n-m+1$ 个可容纳 $0^m$ 的起点；逐相位求和给第二式。全正 $w$ 使两式为正；若 $w_n=0$，合法柱 $10^n1$ 为零。$\square$

## 3. 原调和密度与有限平衡变分

**引理 3.1（iid 更新律的实际外部风险）。** 对每个（2.1）的 $w$，

$$
d(P_w)=\frac1\mu\sum_{k,l\ge1}h(w_{k+l+1},w_kw_l).
\tag{3.1}
$$

证明。每个悬挂轨道在两侧都有无限多个事件。在自由中心 $X_{-1}=X_1=0$ 的外部，最近的左右事件分别在 $-k-1,l+1$，$k,l\ge1$。中心零时完整间隙为 $n=k+l+1$；中心一时拆为 $k,l$。固定含这些边界事件的柱及更远事件，实际 iid 间隙乘积中的共同因子相消，中心后验为

$$
p_{kl}=\frac{w_kw_l}{w_{k+l+1}+w_kw_l},\quad
B_{kl}=(1-p_{kl})^2,\quad
A_n=\sum_{\substack{k,l\ge1\\k+l+1=n}}p_{kl}^2.
\tag{3.2}
$$

零分母时取 $p_{kl}=0$，此种外部总质量为零；强制中心取后验零。有限外部字段递增后，由条件投影收敛得到相同无限外部版本。零段 $n$ 中自由零中心的相位恰对应 $k+l+1=n$，事件中心相邻间隙的条件联合质量为 $w_kw_l$。逐屋顶占据求和，

$$
\mu d(P_w)=\sum_nw_nA_n+\sum_{k,l}w_kw_lB_{kl}
=\sum_{k,l}\{w_{k+l+1}p_{kl}^2+w_kw_l(1-p_{kl})^2\}.
\tag{3.3}
$$

逐项二点恒等式即给（3.1）。$A_n\le n$ 保证占据损失可积，且 $h(w_{k+l+1},w_kw_l)\le w_kw_l$ 保证最后级数收敛。零支撑、确定间隙、周期情形均无需额外除法。$\square$

**引理 3.2（两符号可行方向及一致后验控制）。** 设所有 $w_n>0$。取任意有限支撑实矩阵 $\Delta=(\Delta_{kl})_{k,l\ge1}$，满足

$$
a_k:=\sum_l\Delta_{kl}=\sum_l\Delta_{lk},\qquad\sum_ka_k=0.
$$

对充分小的正负 $t$，以下式子给出一个平稳全支撑间隙 Markov 律及其悬挂 $P_t\in\mathcal S$，且 $P_0=P_w$：

$$
F_t(k,l)=w_kw_l+t\Delta_{kl},\quad w_t(k)=w_k+ta_k,\quad
K_t(l\mid k)=F_t(k,l)/w_t(k),\quad
\mu_t=\mu+tb,\quad b=\sum_k(k+1)a_k.
\tag{3.4}
$$

存在一个显式有限 $H\ge1$ 及共同 Borel 后验版本 $p_t,p_0$，使两側无限事件的外部集合上

$$
|p_t-p_0|\le5H|t|\qquad(|t|\le1/(2H))
\tag{3.5}
$$

在缩小到可行区间后成立。

证明。取 $H$ 为 $1$ 与非零条目的 $|\Delta_{kl}|/(w_kw_l)$、$|a_k|/w_k$ 的最大值。所涉及条目有限，故 $H<\infty$。若 $|t|\le1/(2H)$，所有 $F_t,w_t$ 正，$F_t$ 总质量一，行列边缘均为 $w_t$。因此 $K_t$ 行和一且 $w_tK_t=w_t$。区间概率 $w_t(g_a)\prod_{i=a}^{b-1}K_t(g_{i+1}\mid g_i)$ 左右相容，标准可数离散空间概率扩张给出一个两侧平稳链。其有限均值为 $\mu_t$；定义 2.1 产生一个实际平稳位律。所有有限间隙串为正，借事件边界补足给出全部合法词的正性；在 $t=0$ 链为 iid。

由 $|\log(1+z)|\le2|z|$（$|z|\le1/2$），即使在改变行中的未改条目，也有

$$
\left|\log\frac{K_t(l\mid k)}{w_l}\right|
=\left|\log\left(1+\frac{t\Delta_{kl}}{w_kw_l}\right)-\log\left(1+\frac{ta_k}{w_k}\right)\right|
\le4H|t|.
\tag{3.6}
$$

在自由外部中，最近左右事件之间仍给出 $k,l,n=k+l+1$；再取左侧前一完整间隙 $u$、右侧后一完整间隙 $v$。实际插入比为

$$
R_t=\frac{K_t(k\mid u)K_t(l\mid k)K_t(v\mid l)}
{K_t(n\mid u)K_t(v\mid n)},\qquad p_t=R_t/(1+R_t).
\tag{3.7}
$$

为核对这个比，固定外部的四个边界事件以及其间零位。两种中心完成的间隙串分别为 $u,k,l,v$ 与 $u,n,v$。在事件锚定概率中初始 $w_t(u)/\mu_t$ 相同，内部恰为所列三个与两个转移；进一步指定外侧坐标只增添相同左、右因子，边缘化它们仍保留此比。对任一外部窗口，只要已经看见这四个事件，比就稳定为（3.7）；窗口递增几乎必然达到这一步。条件投影收敛遂识别无限外部后验。

在 $t=0$，$R_0=w_kw_l/w_n$。式（3.6）的五因子给 $|\log R_t-\log R_0|\le20H|t|$；logistic 导数至多 $1/4$，得到（3.5）。所有悬挂都在两侧无限事件集合上为一；按外部最近事件位置定义（3.7），在强制外部及其余外部取零，给出了共同 Borel 函数。这里没有把一个仅在 $P_0$ 下定义的等价类直接代入可能奇异的 $P_t$。$\square$

**引理 3.3（有限方向的一阶风险）。** 在引理 3.2 的条件下，以（3.2）的 $A_n,B_{kl}$ 和 $c=d(P_w)$ 置

$$
E_\Delta=\sum_na_nA_n+\sum_{k,l}\Delta_{kl}B_{kl},\qquad
L_\Delta=(E_\Delta-cb)/\mu.
$$

对充分小的正负 $t$，

$$
d(P_t)\ge c+L_\Delta t-
\left(25H^2+\frac{2|L_\Delta b|}{\mu}\right)t^2.
\tag{3.8}
$$

若 $L_\Delta\ne0$，其相应符号的所有充分小非零参数都严格提高密度。

证明。固定 $p_0$，其损失在零段 $n$ 的自由相位和为 $A_n$，在事件中心前后间隙 $k,l$ 的损失为 $B_{kl}$。$P_t$ 的相位质量和事件相邻间隙质量分别为 $w_t(n)/\mu_t$、$F_t(k,l)/\mu_t$，故

$$
\mathbb E_{P_t}(X_0-p_0)^2=\frac{\mu c+tE_\Delta}{\mu+tb}.
$$

条件于 $\mathcal E_0$，$X_0-p_t$ 与外部函数正交，因此

$$
d(P_t)=\frac{\mu c+tE_\Delta}{\mu+tb}-\mathbb E_{P_t}(p_t-p_0)^2
=c+L_\Delta t-\frac{L_\Delta b\,t^2}{\mu+tb}-\mathbb E_{P_t}(p_t-p_0)^2.
$$

缩小区间使 $\mu+tb\ge\mu/2$，再用（3.5）即得（3.8）。变化的分子条目只有有限个；不对无限体积极限求导。线性非零项支配二次余项，给出最后结论。$\square$

## 4. 六间隙相容条件与全部更新律的非达到

**引理 4.1（全方向驻定所强制的分数平衡）。** 若全正 $w$ 的每个引理 3.2 方向都满足 $L_\Delta=0$，则对某个数列 $u_n>0$，

$$
B_{kl}=u_k+u_l,\qquad A_n+2u_n=c(n+1),\qquad u_n=B_{nn}/2,
\tag{4.1}
$$

特别地

$$
u_1=c,\quad u_2=3c/2,\quad
u_3=c-1/2+\sqrt{2c},\quad u_4=-1+2\sqrt{5c/2}.
\tag{4.2}
$$

证明。对 $k\ne l$ 取 $\Delta_{kk}=\Delta_{ll}=1$、$\Delta_{kl}=\Delta_{lk}=-1$，其他为零，行列边缘皆零。$B$ 对称，驻定使 $B_{kk}+B_{ll}-2B_{kl}=0$，给第一式（对角亦成立）。全正概率使 $0<B_{kl}<1$，故 $u_n>0$。

取单环差 $\Delta_{nn}=1$、$\Delta_{mm}=-1$，得到 $G_n:=A_n+B_{nn}-c(n+1)$ 不依赖 $n$。由于 $A_n\le n$ 且均值有限，$G_n$ 可积。第一式及 $\sum w_n=1$ 给

$$
\sum_{k,l}w_kw_lB_{kl}=2\sum_nw_nu_n=\sum_nw_nB_{nn}.
$$

结合（3.3）可知 $\sum_nw_nG_n=0$，所以常数为零。$A_1=A_2=0$；又 $p_{kl}=1-\sqrt{u_k+u_l}$，因 $1-p_{kl}>0$。因此 $A_3=(1-\sqrt{2c})^2$、$A_4=2(1-\sqrt{5c/2})^2$。代入（4.1）便得（4.2）。$\square$

**引理 4.2（六间隙矛盾）。** 不存在 $c\in[1/7,3-2\sqrt2]$ 及全正 $w$ 同时满足（3.2）、（4.1）。

证明。令 $g(s)=\sqrt{s}/(1-\sqrt{s})$（$0<s<1$）。由 $B_{kl}=u_k+u_l$ 及（3.2），

$$
w_{k+l+1}=w_kw_l g(u_k+u_l).
\tag{4.3}
$$

所有参数都在 $(0,1)$。计算 $w_3=w_1^2g(2c)$、$w_4=w_1w_2g(5c/2)$，再分别用 $(k,l)=(1,4),(2,3)$ 计算 $w_6$，消去正因子 $w_1^2w_2$，强制

$$
g(5c/2)g(v)=g(2c)g(z),\qquad
v=c-1+2\sqrt{5c/2},\quad z=5c/2-1/2+\sqrt{2c}.
\tag{4.4}
$$

下面给出不依赖数值试验的严格反向比较。区间 $J=[7/50,7/40]$ 包含所需的 $c$。设 $A=\sqrt{10}-\sqrt2$，$e=z-v=1/2+3c/2-A\sqrt c$。由平方比较 $3/2<A<7/4$、$\sqrt{7/40}<21/50$，在 $J$ 上 $e'<0$，且

$$
e\ge e(7/40)>1/2+21/80-(7/4)(21/50)=11/400>0.
$$

此外 $(e/c)'=(A\sqrt c-1)/(2c^2)<0$，因为 $A\sqrt c<147/200<1$。在左端 $c=7/50$，$e/c<2/5$ 等价于 $\sqrt{35}-\sqrt7>327/100$。这个比较可以平方：$\sqrt5<22361/10000$（其平方大于五），所以

$$
(\sqrt{35}-\sqrt7)^2=42-14\sqrt5
>106946/10000>106929/10000=(327/100)^2.
$$

故全区间有 $0<e<2c/5$。$v,z$ 严格递增，$\sqrt{7/5}>29/25$、$\sqrt{7/20}<3/5$ 又给

$$
v\ge v(7/50)>3/10,\qquad z\le z(7/40)<43/80<11/20,\qquad v<z.
\tag{4.5}
$$

取 $G=\log g$，则

$$
G'(s)=\frac1{2s(1-\sqrt s)}\ge27/8\quad(0<s<1).
$$

因为分母最大值为 $8/27$，在 $s=4/9$ 取到。分母先增后减；在 $[3/10,11/20]$ 的两个端点均大于 $1/4$：分别使用 $\sqrt{3/10}<11/20$ 和 $\sqrt{11/20}<3/4$，得下界 $27/100$、$11/40$。因而该区间上 $G'<4$。积分比较遂给

$$
\begin{aligned}
G(5c/2)+G(v)-G(2c)-G(z)
&=[G(5c/2)-G(2c)]-[G(z)-G(v)]\\
&>27c/16-4(2c/5)=7c/80>0,
\end{aligned}
$$

这与（4.4）的对数等式矛盾。所有根号比较均在正数上，故平方保持方向。$\square$

**定理 4.3（每个有限均值 iid 间隙律严格非达到）。** 对每个（2.1）的 $w$，有 $d(P_w)<c_\star$。若所有 $w_n>0$ 且 $d(P_w)\ge1/7$，则存在一个有限平衡方向及其一个符号，使该方向所有充分小的非零悬挂参数严格提高密度。

证明。若某个 $w_n=0$，引理 2.2 使合法柱 $10^n1$ 为零；[普适缺陷卷][P4] 定理 3.1 说每个精确达到者的所有合法柱为正，故结合 $d\le c_\star$ 得严格性。现在设全正，记 $c=d(P_w)$。若 $c<1/7$，供应下界 $c_\star>1/7$ 即给结论。若 $c\ge1/7$，式（1.1）给 $c\le3-2\sqrt2$。假如每个有限方向的一阶项都零，引理 4.1、4.2 矛盾。因此某个 $L_\Delta\ne0$；引理 3.3 给实际平稳提高律，其密度仍至多 $c_\star$，故 $c<c_\star$。这也证明附带提高结论。$\square$

“六间隙”是 $w_6$ 的两个相容表达发生冲突；它不提供提高方向的统一支撑大小，也不提供后文有限见证的长度六上界。

## 5. 事件条件独立族的完整分类

**定义 5.1（可观察事件独立）。** 对全部有限二进制词 $u,v$，允许空词，令

$$
\Gamma_{uv}(P)=P([u1v])P([1])-P([u1])P([1v]),\qquad
\mathcal R=\{P\in\mathcal S:\forall u,v, \Gamma_{uv}(P)=0\}.
\tag{5.1}
$$

各柱在显示的中央 $1$ 处对齐，平稳性使上述起点简写合法。正事件强度时它表示条件于 $X_0=1$ 的过去与未来独立，不要求条件于 $X_0=0$ 独立。用柱等式而不除以事件强度，使零强度边界也在定义中。

**定理 5.2（全零边界与唯一事件分解）。** 恰有

$$
\mathcal R=\{\delta_{0^{\mathbb Z}}\}\ \cup\
\{aP_w+(1-a)\delta_{0^{\mathbb Z}}:0<a\le1, w\text{ 满足（2.1）}\}.
\tag{5.2}
$$

若 $\rho=P([1])>0$，则 $w_n=P([10^n1])/\rho$，$a=P(\exists i:X_i=1)=\rho\mu$，从而 $a,w$ 唯一。无限均值的间隙不能形成正事件强度的归一化成员。每个成员满足

$$
d(aP_w+(1-a)\delta_{0^{\mathbb Z}})=a\,d(P_w).
\tag{5.3}
$$

证明。$\rho=0$ 时，平稳性使每个 $P(X_i=1)=0$，可数并给全零律。若 $\rho>0$，指定“最后一个 $1$ 在 $j$”的事件是两两不交的平移，平稳质量相等，故每个为零；首个事件同理。因此非全零轨道几乎必然在两侧都有无限事件。给定中央事件，下一事件距离有限，所列 $w_n$ 非负且和一。

事件独立等式在每个内部事件处切开给出

$$
P([10^{n_1}1\cdots0^{n_k}1])=\rho\prod_{i=1}^kw_{n_i}\qquad(k\ge1).
\tag{5.4}
$$

具体地，$k=1$ 是定义；在最后一个内部事件用 $P(u1v)\rho=P(u1)P(1v)$，然后归纳。不需任何 $w_n$ 正。把锚移到串内任意事件，（5.4）给中央事件两侧任意有限个完整间隙的联合概率为其乘积，故完整两侧 Palm 间隙律为 $w^{\mathbb Z}$。有限柱生成其 sigma 字段，概率唯一性完成这一识别。

非全零集合 $E$ 分为下列可数不交部分：包含坐标零的屋顶间隙为 $n$，最近不晚于零的事件在 $-j$，下一事件在 $n+1-j$，$0\le j\le n$。每部分是 $10^n1$ 的一个平移，质量 $\rho w_n$，所以

$$
a=P(E)=\rho\sum_n(n+1)w_n\le1.
\tag{5.5}
$$

于是 $\mu=a/\rho<\infty$，是推得的结论。对任意 Borel 位事件 $C$，按这些屋顶相位分解；在相位 $j$ 把屋顶起点移回零，平稳性及（5.4）的完整 Palm 律给

$$
P(C\cap E)=\rho\int\sum_{j=0}^{g_0}\mathbf1_C(x(g,j))\,d(w^{\mathbb Z})(g)
=aP_w(C).
$$

该式先对有限位柱从有限间隙柱及递增截断得到，再由测度唯一性推广；非负相位和用单调收敛。因此得到实际律等式（5.2）。其具体含事件柱概率为 $\rho\overline w_r\overline w_s\prod_iw_{n_i}$，全零柱为 $1-a+\rho\sum_{n\ge m}(n-m+1)w_n$，保留端点与零纤维。

反向，在 iid 悬挂的中央事件条件下，过去由负指标间隙、未来由非负指标间隙确定；两者独立，故所有（5.1）成立。加入全零成分使每个含事件柱乘以 $a$，各残差乘以 $a^2$，仍为零。$a=0$ 也直接成立。

最后，$E$ 几乎处处等于负坐标中有无限事件的集合 $E^-$，后者属于 $\mathcal E_0$。在混合律下取 $q=\mathbf1_{E^-}q_{P_w}$，在其余部分取零。对任意外部事件检验条件期望，事件部分按实际 $aP_w$ 积分，全零部分 $X_0=0$，所以它确为混合律后验。风险分解即（5.3），未声称有限窗口风险仿射。唯一性由 $w_n$ 的公式和 $a=\rho\mu$ 得到；全零时 $w$ 无须指定。$\square$

## 6. 全支撑纯更新律的精确弱闭包

**定理 6.1（最小闭包）。** 令 $\mathcal R_+=\{P_w:w\text{ 满足（2.1），且 }w_n>0\ \forall n\}$。在 $\mathcal S$ 的弱拓扑中

$$
\overline{\mathcal R_+}=\mathcal R.
\tag{6.1}
$$

因此全零混合边界是纯更新律弱极限的真实组成部分，不需要隐藏维数上界或统一矩界。

证明。每个 $\Gamma_{uv}$ 是有限柱概率的连续多项式，故 $\mathcal R$ 闭；引理 2.2 和定理 5.2 给 $\mathcal R_+\subseteq\mathcal R$，从而闭包包含于右侧。

固定目标 $aP_w+(1-a)\delta_{0^{\mathbb Z}}$，先设 $a>0$，并固定全正有限均值参考 $v_n=2^{-n}$。置 $b=\mu(1/a-1)\ge0$。对整数 $m>\max(b,1)$，令

$$
w^{(m)}=(1-b/m)\bigl((1-1/m)w+(1/m)v\bigr)+(b/m)\delta_m.
\tag{6.2}
$$

这里 $\delta_m$ 是间隙值 $m$ 的点质量。每个 $w^{(m)}$ 全正、归一化且有限均值，且

$$
\|w^{(m)}-w\|_1\longrightarrow0,\qquad
\mu_m=(1-b/m)((1-1/m)\mu+(1/m)\mu_v)+(b/m)(m+1)
\longrightarrow\mu+b=\mu/a.
$$

因此每个固定间隙质量与尾概率都收敛。式（2.2）对每个含事件的固定词给出柱概率极限 $aP_w([z])$。固定长度全部合法词的质量和一，唯一不含事件的词是全零词，其质量由其余有限项的补数收敛到 $1-a+aP_w([0^q])$。故所有位柱收敛；紧有限字母空间上的连续函数可被有限柱函数一致逼近，遂为弱收敛。

对全零目标，取 $w^{(m)}=(v+\delta_m)/2$，则 $\mu_m\to\infty$。任意长 $q$ 窗口内至少一个事件的概率至多 $qP_{w^{(m)}}([1])=q/\mu_m\to0$，所以弱收敛到全零律。定理 5.2 的全部成员都已逼近，得到反向包含。$\square$

## 7. 统一最优性差距及共有有限依赖见证

**定理 7.1（闭族统一分离）。** 存在 $\varepsilon_{\mathcal R}>0$，使每个 $P\in\mathcal R$ 都满足

$$
d(P)\le C_{\mathcal R}:=\max_{Q\in\mathcal R}d(Q)
=c_\star-\varepsilon_{\mathcal R}<c_\star.
\tag{7.1}
$$

证明。由定理 5.2、4.3，每个 $a>0$ 成员的风险为 $a\,d(P_w)<c_\star$，因为 $0\le d(P_w)<c_\star$；全零风险零也严格次优。$\mathcal R$ 是紧 $\mathcal S$ 的非空闭子集，而 $d$ 上半连续，所以最大值在某个成员取到；该成员的严格性给正差距。紧性是在实际律空间中使用，不能用未闭的有限均值参数域替代。$\square$

**定理 7.2（近最优律必有有限跨事件依赖）。** 存在 $\delta,\eta>0$、一个固定有限非空词对集合 $W$ 和整数 $L\ge1$，其中所有 $u,v$ 非空、$u1v$ 合法、$|u|,|v|\le L$，使

$$
\forall P\in\mathcal S,\qquad
d(P)\ge c_\star-\delta\ \Longrightarrow\
\max_{(u,v)\in W}|\Gamma_{uv}(P)|\ge\eta.
\tag{7.2}
$$

可取 $\delta=\varepsilon_{\mathcal R}/2$；见证词对可随 $P$ 改变。

证明。上半连续性使 $K=\{P\in\mathcal S:d(P)\ge c_\star-\varepsilon_{\mathcal R}/2\}$ 紧。供应达到律使其非空，定理 7.1 使 $K\cap\mathcal R=\varnothing$。因此开集 $\{|\Gamma_{uv}|>0\}$ 覆盖 $K$，有一个有限子覆盖。空词任一侧使残差恒零；若 $u1v$ 非法，则 $u1$ 或 $1v$ 非法，使两项皆零。故子覆盖可取所述合法非空词对。连续函数 $f=\max_W|\Gamma_{uv}|$ 在紧 $K$ 上处处为正，取到正最小值 $\eta$；取最大词长为 $L$，即得结论。$\square$

该结果直接涉及实际柱概率；它没有给出 $W,L,\eta,\delta$ 的数值或取得效率，也没有给出有限样本误差保证。依赖是近最优的必要条件，非达到的充分条件。一般平稳律仍可以有相关间隙。

## 8. 完整非负隐藏域、零质量裁剪与三状态排除

**定义 8.1（原完整边发射域；[普适缺陷卷][P4] 定义 4.1）。** 对每个整数 $N\ge1$，$\Theta_N$ 是全部实参数 $\theta=(\lambda,M_0,M_1)$，满足

$$
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\quad
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\quad
\lambda M_1^2\mathbf1=0.
\tag{8.1}
$$

$\lambda$ 为行向量，$M_w=M_{w_1}\cdots M_{w_q}$，$M_\epsilon=I$。没有严格正条目、不可约或非周期假设。供应命题 4.2 的一个实际联合律为

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\quad
P_\theta([w])=\lambda M_w\mathbf1.
\tag{8.2}
$$

左右相容分别用 $A\mathbf1=\mathbf1$ 和 $\lambda A=\lambda$；合法性用每位置 $11$ 零质量的可数并。故原接缝仍是 $\lambda M_uM_v\mathbf1$，不是两个边缘乘积。置 $C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$。

**引理 8.2（先裁剪零平稳质量）。** 对每个 $\theta\in\Theta_N$，令 $I_+=\{i:\lambda_i>0\}$，$N_+=|I_+|$。限制到 $I_+$ 的参数 $\widetilde\theta$ 属于 $\Theta_{N_+}$，保留所有可见柱概率，且

$$
\widetilde\lambda>0,\qquad\widetilde M_1^2=0,\qquad
2\operatorname{rank}(\widetilde M_1)\le N_+.
\tag{8.3}
$$

证明。若 $j\notin I_+$，$0=\lambda_j=\sum_{i\in I_+}\lambda_iA_{ij}$，非负性和 $\lambda_i>0$ 使所有保留到删去状态的 $A_{ij}$ 为零；同样 $M_x(i,j)=0$。保留集合闭，限制矩阵行和仍一，限制 $\lambda$ 归一化且平稳。任意从正初始质量开始的乘积路径始终在此集合，所以（8.2）的全部柱质量保留。

限制后 $0=\widetilde\lambda\widetilde M_1^2\mathbf1$，$\widetilde\lambda$ 每项正且矩阵非负，强制 $\widetilde M_1^2$ 每项零。其像包含于核，秩零度公式给 $\operatorname{rank}\widetilde M_1\le N_+-\operatorname{rank}\widetilde M_1$。这一步在裁剪后成立。$\square$

未裁剪矩阵的平方零不是（8.1）的结论。例如 $\lambda=(1,0,0)$、$M_0=\operatorname{diag}(1,0,0)$、$M_1=\operatorname{diag}(0,1,1)$ 满足（8.1），输出全零，但原 $M_1$ 秩二且平方非零；裁剪留下一个状态、事件矩阵零。

**定理 8.3（事件或事件乘积的秩一重置排除）。** 对任意 $N\ge1$、$\theta\in\Theta_N$，若 $\operatorname{rank}(M_1)\le1$ 或 $\operatorname{rank}(M_0M_1)\le1$，则 $P_\theta\in\mathcal R$，从而 $d(P_\theta)\le c_\star-\varepsilon_{\mathcal R}$。若这两条件之一仅在裁剪后的表示上成立，同一结论也成立。

证明。非负秩一矩阵可写成非负列、行的乘积 $fg$：选一个非零列作为 $f$，其他列按非负比例取其倍数。若 $M_1=fg$，则对每个 $u$，$\lambda M_uM_1=(\lambda M_uf)g$；空词的事件行亦是同一 $g$ 的倍数。因此（8.2）的四个柱概率直接给

$$
(\lambda M_uf)(gM_v\mathbf1)(\lambda f)(g\mathbf1)
-(\lambda M_uf)(g\mathbf1)(\lambda f)(gM_v\mathbf1)=0.
$$

若矩阵秩零，事件概率零，所有残差也零。

再令 $B=M_0M_1$ 的秩至多一。由合法性与非负性，$\lambda M_1^2=0$ 为行等式；平稳性因而给 $\lambda M_1=\lambda B$。非空词 $u$ 若末位零，写 $u=s0$，则 $\lambda M_uM_1=\lambda M_sB$。若末位一，写 $u=s1$，整个词 $s11$ 非法，所以 $\lambda M_sM_1^2\mathbf1=0$；非负性使该行本身零。空词用 $\lambda B$。于是秩一 $B=fg$ 时每个事件行都是同一个 $g$ 的倍数，按上一计算残差全零；秩零时 $\lambda M_1=0$。这也覆盖内部非法词。裁剪表示保留同一律，故可对它应用相同证明。$\square$

**推论 8.4（整个有效三状态域）。** 对任意 $N\ge1$、$\theta\in\Theta_N$，若 $N_+\le3$，则

$$
P_\theta\in\mathcal R,\qquad d(P_\theta)\le c_\star-\varepsilon_{\mathcal R}.
$$

特别地对 $N=1,2,3$，$C_N\le C_{\mathcal R}<c_\star$。每个有限隐藏精确达到者的每个裁剪边发射表示都必须有至少四个状态，并且两个事件算子 $\widetilde M_1$、$\widetilde M_0\widetilde M_1$ 都有秩至少二。

证明。引理 8.2 给 $2\operatorname{rank}(\widetilde M_1)\le N_+\le3$，整数秩至多一；定理 8.3 应用到限制表示。取上确界得固定维数界；达到者所需条件为两个排除定理的逆否命题。$\square$

按照 [普适缺陷卷][P4] 定理 6.2，对 $N\le3$ 还存在有限 $r,m\ge1$ 使 $U_{N,r}:=\max_{\theta\in\Theta_N}D_r(P_\theta)<\kappa_m/(m+1)$。这复用其固定维数紧分离等价，没有指定数值分离对。

**命题 8.5（同律映射与表示敏感的资源计数）。** 上述下界计数正平稳质量的边发射生产者状态。一个 $N$ 状态模型先按概率 $e_s(x)$ 发射再按随机矩阵 $A$ 转移，若隐藏初始律 $\lambda$ 平稳，则 $M_x=\operatorname{diag}(e_s(x))A$ 给同一可见律和同样 $N$ 个状态。反向，任意 $\Theta_N$ 表示有一个至多 $2N^2$ 状态的确定性状态发射表示，保留同一可见律。

证明。正向逐路径的发射、转移联合因子为 $e_{h_i}(x_i)A_{h_i h_{i+1}}=M_{x_i}(h_i,h_{i+1})$，所以全部词概率恰为（8.2），合法性保持。反向先按引理 8.2 裁剪，再取状态集合 $Q=\{(i,x,j):\lambda_iM_x(i,j)>0\}$；其大小至多 $2N^2$。在状态 $(i,x,j)$ 确定性发射 $x$，置

$$
\pi_{(i,x,j)}=\lambda_iM_x(i,j),\qquad
K((i,x,j),(k,y,l))=\mathbf1_{\{j=k\}}M_y(k,l).
$$

保留状态间的行和为 $\sum_{y,l}M_y(j,l)=1$，$\sum_Q\pi=1$；到 $(k,y,l)$ 的平稳流为 $(\sum_{i,x}\lambda_iM_x(i,k))M_y(k,l)=\lambda_kM_y(k,l)$，故 $\pi K=\pi$。发射词的路径概率乘积求和为 $\lambda M_{x_1}\cdots M_{x_q}\mathbf1$，证明同律。$\square$

[普适缺陷卷][P4] 命题 4.2 以隐藏初始律的 Cesàro 平均处理可见平稳而隐藏初始未平稳的情形，保留各柱概率及状态数。因此至多三状态的通常随机状态发射表示也被排除。两个方向的上界不同，不能认定各约定的最小维数相等；观察器行数、树地址数不在这一生产者计数中。定理 8.3 只使用 $M_1$ 与 $M_0M_1$ 的条件；不把 $\operatorname{rank}(M_0)$ 与 $\operatorname{rank}(M_0M_1)$ 说成等价，也不把秩一说成 $\mathcal R$ 的表示无关必要条件。

## 9. 四状态非更新反例与原有限隐藏问题

**命题 9.1（同一合法律的四状态依赖反例）。** 存在 $\theta\in\Theta_4$，四个状态都有正平稳质量，$M_1^2=0$，两个事件算子秩均为二，而 $\Gamma_{10,01}(P_\theta)=1/360>0$。该律全支撑、非更新，且没有有限可见 Markov 阶。

证明。复用 [完备卷][P3] 命题 6.2 的实际混合。对 $0<a<1$，取

$$
M_0^a=\begin{pmatrix}1-a&a\\0&0\end{pmatrix},\qquad
M_1^a=\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad
\lambda^a=(1/(1+a),a/(1+a)).
$$

这是合法一阶律 $R^a$；矩阵和随机，直接乘得平稳，$M_1^2=0$，每个合法词概率正。令 $M_x=M_x^{1/3}\oplus M_x^{2/3}$，$\lambda=(\lambda^{1/3},\lambda^{2/3})/2$。这是一份实际联合律：一次选定参数并保持，输出 $P=(R^{1/3}+R^{2/3})/2$，全部（8.1）成立，四个质量正。每块事件矩阵秩一，每块 $M_0^aM_1^a=\left(\begin{smallmatrix}a&0\\0&0\end{smallmatrix}\right)$ 秩一，所以直和秩二。

由 $R^a(1)=a/(1+a)$、$R^a(101)=a^2/(1+a)$、$R^a(10101)=a^3/(1+a)$，

$$
P(1)=13/40,\quad P(101)=7/40,\quad P(10101)=37/360,\quad
\Gamma_{10,01}(P)=\frac{37}{360}\frac{13}{40}-\left(\frac7{40}\right)^2=\frac1{360}.
$$

故不属于 $\mathcal R$。给定长度 $q\ge1$ 的全零过去，下一位为一的实际概率是

$$
\frac{aA_q+bB_q}{A_q+B_q},\quad
A_q=(1-a)^{q-1}/(1+a),\quad B_q=(1-b)^{q-1}/(1+b),\quad
a=1/3, b=2/3.
$$

$B_q/A_q=(4/5)2^{-(q-1)}$ 严格递减，所以该概率严格变化。若可见阶至多 $m$，塔性质会使所有 $q\ge m$ 的条件都等于同一后缀 $0^m$ 的行，矛盾。$\square$

这个反例说明有限隐藏可以保留跨事件依赖，也说明 $\mathcal R$ 一般不凸：两个 $R^a$ 都在其中而其上述混合不在。它不是最优达到者；供应 [普适缺陷卷][P4] 定理 5.1 的实际分量公式及式（7.4）给 $d(P)=(1/7+2/35)/2=1/10<c_\star$。

**开放问题 9.2（完整任意有限隐藏达到）。** 对未改动的全部 $\Theta_N$，是否存在有限 $N\ge4$ 和 $\theta\in\Theta_N$ 使 $d(P_\theta)=c_\star$，还是每个有限 $N$ 都有 $C_N<c_\star$？后一项按供应定理 6.2 等价于

$$
\forall N\ge1\ \exists r,m\ge1:\quad U_{N,r}<\kappa_m/(m+1).
$$

本卷只给事件独立族、两个秩一重置条件和 $N_+\le3$ 的排除。一般 $M_0^nM_1$ 传播隐藏过滤上下文；插入比不能未经证明换成标量 $w_kw_l/w_{k+l+1}$。有限非零 $\Gamma$ 与有限非负实现相容，命题 9.1 已展示这一点。缺少非重置矩阵上下文的变分障碍或一个精确达到构造。供应推论 7.3 的 $\sup_NC_N=c_\star$ 既不证明也不否定有限维达到；不存在对全部有限维数的统一正差距这一推论。原任意有限隐藏问题和更广研究目标未由本卷完成。

## 10. 成熟机制、DEV 对应与归属边界

**约定 10.1（文献与方法归属）。** [Marzen–Crutchfield][MC] *Informational and Causal Architecture of Discrete-Time Renewal Processes*，arXiv:1408.6876v2，§II.1、§V、附录 A，使用平稳持久二元更新过程、归一化 iid 零计数 $F(n)$（$n\ge0$）和有限计数均值。此处对应是 $F(0)=0$、$F(n)=w_n$，其计数均值加一等于本卷屋顶均值 $\mu$。更新归一化、年龄／剩余时间及有限生成与无限预测记忆的区别是已有机制。其信息量目标不供应原调和最优性；其遍历设置不直接给出本卷的全零混合闭包。

[Dawid–Lauritzen–Parry][DLP] *Proper Local Scoring Rules on Discrete Sample Spaces*，arXiv:1104.2224v2，§4.2、例 4.4、式（14），给出条件 Brier 损失与后验平方差的 ratio matching 机制。其全乘积空间严格 proper 论证假定概率处处正；硬 no11 不满足该前提。这里复用供应的合法双点、强制单点、零总质量身份，并在引理 3.3 直接证明所需正交式。没有把其估计结论移到本目标。

悬挂、事件条件概率、可数相容概率扩张、条件正交、上半连续紧极值、有限开覆盖及秩零度公式均是成熟工具。相对于 §1 的供应，定理 4.3、5.2、6.1、7.1–7.2 和有效三状态推论是本卷的 `repo-derived` 综合；通用工具不单列为新知识。所需新增承重证明均在正文给出，候选提议不作为定理前提。

**边界 10.2（三个 DEV 来源的关系合同）。** 对应只消费以下三个独立正文的明确载体与操作定义；其引用链不充当本卷新增概率定理的前提。

| 来源 | 已有关系与本卷的准确边界 |
| --- | --- |
| [异质教师几何][D1] 定义 1.1–1.3、定理 2.1、命题 3.1 | 一个有限全窗口乘积律，字母 $\Sigma=\{000,100,010,101,001\}$，每窗每字母质量至少 $\rho>0$，给 ANOVA／Gram 系数下界。相邻窗口 $001\mid100$ 质量至少 $\rho^2$，拼接含接缝 $11$；因而原律不是平稳 no11 位律。条件化去除接缝会改变乘积假设，插入保护零会改变长度及边对应。六个原生窗口位置不是六个间隙长度；没有概率、目标、资源都保持的映射。 |
| [实际 no11 运输续卷][D7] 第 70–74 章，尤其定理 71.1、71.3、71.5 | 对固定计数和面积的整个有限词纤维，内部间隙加一的双射、共同矩剪切及纤维重数运输；全零与端点分支也在其域中。这不指定 iid 间隙概率或两侧平稳悬挂。原 Hamming 翻转改变一计数，不能留在固定计数纤维中；映射长度也随计数变化，故矩运输不证明调和边运输。 |
| [全叶词原生续读][D8] 第 67–69 章 | 固定完整叶词、任意有序括号、字面 branch／absent 掩码、实际前缀、命中集最优和观察器可达行容量；行是读取者记录，非随机生产者状态。按上一卷 $a=0,b=1$ 的实际标签，$T_4$ 的 $babba$ 是 $10110$，含 $11$。换标签没有自动提供平稳律或状态数映射；其三叶 absent 边界也不能删除。 |

**边界 10.3（检索范围及结论范围）。** 仓内目录与所读供应的对应只支持此处明确的增量比较；词项搜索、未读正文及未核对引用不证明全库或世界范围无先例。文献仅按上述版本、章节和假设作方法归属。统一差距与有限见证都是存在性结果，没有数值缺口、有效求取、有限样本、最优律唯一性或混合速率结论；也没有跨表示最小状态数相等结论。没有物理、神经结构或实际机器学习收益的转移结论。普通证明不冒充内核证明。

[P0]: FIB_LEGAL_EDGE_LOAD_ERGODIC_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[P1]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[P2]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[P3]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[P4]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[P5]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[P6]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[D1]: FIB_ATOM_WHITEBOX_HETEROGENEOUS_TEACHER_GEOMETRY.md
[D7]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS_ACTUAL_NO11_CONTINUATION.md
[D8]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS_WHOLE_WORD_NATIVE_CONTINUATION.md
[MC]: https://arxiv.org/html/1408.6876v2
[DLP]: https://arxiv.org/html/1104.2224v2

## 追加锚（本行以下为增补区）
