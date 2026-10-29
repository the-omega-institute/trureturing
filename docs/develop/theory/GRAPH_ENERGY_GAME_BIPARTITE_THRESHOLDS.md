# 完全二部图能量博弈的 Shapley 核阈值

## 1. 图、联盟与分配

**定义 1.1（普通图能量博弈）。** 设 $G=(V,E)$ 为有限简单无向图，$A_G$ 为其邻接矩阵，邻接特征值按重数记为 $\lambda_1,\ldots,\lambda_{|V|}$。普通能量及诱导联盟价值定义为

$$
\mathcal E(G)=\sum_{\ell=1}^{|V|}|\lambda_\ell|,
\qquad w_G(C)=\mathcal E(G[C])\quad(C\subseteq V).
$$

空图的能量为零，因而 $w_G(\varnothing)=0$。这里固定采用 Arizmendi–Arizmendi，[*The graph energy game*, arXiv:2012.14114v2](https://arxiv.org/pdf/2012.14114v2)，Definition 3.1，第 5 页的普通邻接能量定义。

**定义 1.2（Shapley 分配、收益核与阻塞赤字）。** 对有限玩家集 $V$、$n=|V|\ge1$ 和满足 $w(\varnothing)=0$ 的价值函数，定义

$$
\phi_v(w)=\sum_{S\subseteq V\setminus\{v\}}
\frac{|S|!(n-|S|-1)!}{n!}
\bigl(w(S\cup\{v\})-w(S)\bigr).
$$

分配 $p\in\mathbb R^V$ 的收益核条件为

$$
\sum_{v\in V}p_v=w(V),
\qquad
\sum_{v\in C}p_v\ge w(C)\quad\text{对每个 }C\subseteq V.
$$

第一式称为效率。记满足全部条件的集合为 $\operatorname{Core}(w)$。联盟 $C$ 相对于 $p$ 的赤字为

$$
\Delta(C;p)=w(C)-\sum_{v\in C}p_v.
$$

称 $C$ 严格阻塞 $p$，是指 $\Delta(C;p)>0$。这些定义分别对应上述文献 §2.4 的阶乘公式及 Definition 2.7，第 4 页。普通 Shapley 分配是此阶乘公式；另一个分配 $e_v=(|A_G|)_{vv}$，其中 $|A_G|=(A_G^2)^{1/2}$，是该文 Theorems 3.5–3.6，第 6–7 页的 vertex-energy 分配。

**定义 1.3（完全二部图的标号）。** 对正整数 $a,b$，令

$$
A=\{A_1,\ldots,A_a\},\qquad
B=\{B_1,\ldots,B_b\},\qquad V=A\sqcup B.
$$

$K_{a,b}$ 恰含全部连接 $A$ 与 $B$ 的边。对联盟 $C$ 记 $i=|C\cap A|$、$j=|C\cap B|$，并记 $E_{a,b}=2\sqrt{ab}$。以下 $x_{a,b}$、$y_{a,b}$ 分别记 $\phi_{A_1}(w_{K_{a,b}})$、$\phi_{B_1}(w_{K_{a,b}})$；同侧分配相等将在证明中给出。对 $a=2,b=m$，简记 $x_m=x_{2,m}$、$y_m=y_{2,m}$。

## 2. 二顶点侧的精确阈值与统一赤字

**定理 2.1（$K_{2,m}$ 的完整正整数阈值）。** 对每个正整数 $m$，定义 1.1–1.3 的 Shapley 分配满足

$$
\phi(w_{K_{2,m}})\in\operatorname{Core}(w_{K_{2,m}})
\quad\Longleftrightarrow\quad 1\le m\le4.
$$

当 $m\ge5$ 时，令

$$
j_m=\left\lfloor\frac m2\right\rfloor+1,
\qquad \delta_m=2j_m-m\in\{1,2\},
\qquad R_m=\sqrt{\frac{m}{2j_m}},
\qquad T_m=\frac{\sqrt{2m}}{1+R_m}.
$$

任取一名 $A$ 侧顶点及任意 $j_m$ 名 $B$ 侧顶点形成联盟 $C_m$，都有精确恒等式与严格下界

$$
\Delta_m:=\Delta(C_m;\phi)
=\frac{\delta_m}{m}(x_m-T_m)
>\frac{\delta_m}{100\sqrt m}>0.
$$

**证明。** 先把谱值、排列平均及核条件接到同一个联盟计数上。完全二部图的能量与二顶点侧分配式亦见仓内的[完全二部图能量及 Shapley 分配](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.md)中的数学计算；这里写出所需的谱与组合对应。

（一）联盟若有 $i,j>0$ 名两侧顶点，其邻接矩阵在两侧常值向量张成的二维子空间上具有矩阵

$$
\begin{pmatrix}0&j\\ i&0\end{pmatrix},
$$

在两侧分别坐标和为零的向量空间上为零。因此非零特征值为 $\sqrt{ij},-\sqrt{ij}$，其余为零；若 $ij=0$ 则没有边。于是所有联盟统一满足

$$
w_{K_{a,b}}(C)=2\sqrt{ij}.
\tag{2.1}
$$

对任一玩家 $v$，在均匀随机排列中令 $P_v$ 为它的前驱集合。固定 $S\subseteq V\setminus\{v\}$，恰有 $|S|!(n-|S|-1)!$ 个排列以 $S$ 为前驱集合。因此定义 1.2 等于

$$
\phi_v=\mathbb E\bigl[w(P_v\cup\{v\})-w(P_v)\bigr].
\tag{2.2}
$$

沿每个排列相加的边际贡献望远镜求和为 $w(V)-w(\varnothing)$，再取平均即得效率。任一同侧置换保持价值函数及排列分布，所以同侧玩家的分配相等。由 (2.1)，每项边际均非负；固定一个仅含一名异侧玩家的前驱集合，其概率严格为正，而相应边际为 $2$。故对所有正整数 $a,b$，

$$
x_{a,b}>0,\qquad y_{a,b}>0,\qquad
ax_{a,b}+by_{a,b}=E_{a,b}.
\tag{2.3}
$$

（二）在本证明及定理 3.1 中，使用如下核不等式的因式分解。令 $x=x_{a,b}$、$y=y_{a,b}$，并置

$$
u=\frac{ax}{E_{a,b}}\in(0,1),\qquad
\tau=\frac{1-u}{u}>0.
$$

纯侧联盟的价值为零，由 (2.3) 满足核不等式。对 $1\le i\le a$、$1\le j\le b$，置

$$
r=\sqrt{\frac{ib}{ja}}.
$$

因为 $i/a=(j/b)r^2$，效率给出

$$
\begin{aligned}
\frac{ix+jy-2\sqrt{ij}}{E_{a,b}}
&=\frac iau+\frac jb(1-u)-\sqrt{\frac ia\frac jb}\\
&=\frac jb\bigl(ur^2-r+1-u\bigr)\\
&=\frac jb\,u(r-1)(r-\tau).
\end{aligned}
\tag{2.4}
$$

因此 $r=1$ 时取等，$r<1$ 时该联盟要求 $\tau\ge r$，$r>1$ 时要求 $\tau\le r$。这三种情形及纯侧联盟覆盖所有联盟。

对 $a=2,b=m$，有

$$
u=\frac{x_m}{\sqrt{2m}},\qquad
\tau=\frac{\sqrt{2m}-x_m}{x_m}.
\tag{2.5}
$$

此时 $r<1$ 当且仅当 $i=1$ 且 $j>m/2$，其最大值为 $R_m$，在且仅在计数 $(i,j)=(1,j_m)$ 取得。由 (2.4)，这些联盟中最强的 $\tau$ 下约束为

$$
\tau\ge R_m
\quad\Longleftrightarrow\quad x_m\le T_m.
\tag{2.6}
$$

这里比较的是对 $\tau$ 的约束；它不比较不同联盟的绝对赤字。对相同计数，标签可以任意选择。若另有 $\tau\le1$，则所有 $r>1$ 的核约束也自动成立。

（三）计算 $x_m$。写

$$
q=\sqrt2,\qquad H=(m+1)(m+2),\qquad
S_1=\sum_{k=0}^{m}\sqrt k,\qquad
S_3=\sum_{k=0}^{m}k\sqrt k.
$$

对目标 $A_1$，按另一名 $A$ 顶点是否属于前驱集合分类。含 $k$ 名 $B$ 顶点且不含 $A_2$ 的全部前驱集合总权重为

$$
\binom mk\frac{k!(m+1-k)!}{(m+2)!}=\frac{m+1-k}{H},
$$

相应边际为 $2\sqrt k$。含 $A_2$ 的总权重为

$$
\binom mk\frac{(k+1)!(m-k)!}{(m+2)!}=\frac{k+1}{H},
$$

边际为 $2(q-1)\sqrt k$。这对 $0\le k\le m$，包括零边际端点，均成立。相加得到

$$
x_m=\frac{2\bigl((m+q)S_1+(q-2)S_3\bigr)}{H},
\qquad
y_m=\frac{2\sqrt{2m}-2x_m}{m}.
\tag{2.7}
$$

（四）先处理 $m\le4$ 的全部核约束。$m=1$ 时，(2.7) 给出

$$
x_1=\frac{2q-1}{3},\qquad y_1=\frac{2+2q}{3}.
$$

除纯侧、空联盟及全体外，唯一混合联盟计数为 $(1,1)$，其分配和为 $(1+4q)/3>2$，其中 $q>5/4$ 由 $2>25/16$ 得到。纯侧由严格正性满足，全体由效率取等。这也处理了 $\tau_1>1$ 的情形：事实上 $x_1<q/2$ 等价于 $q<2$。$m=2$ 时，(2.7) 给出 $x_2=y_2=1$，所以 $u=1/2$、$\tau=1$，(2.4) 对所有混合联盟均非负。

$m=3,4$ 时，(2.7) 化为

$$
\begin{aligned}
x_3&=\frac{7+q-3\sqrt3+4\sqrt6}{10},
&T_3&=4\sqrt6-6q,\\
x_4&=\frac{12q-2\sqrt3+4\sqrt6}{15},
&T_4&=6q-4\sqrt3.
\end{aligned}
\tag{2.8}
$$

为同时比较 (2.5) 与 (2.6)，取明确的正有理端点

$$
\begin{aligned}
L_2&=\frac{14142}{10000},&U_2&=\frac{14143}{10000},\\
L_3&=\frac{17320}{10000},&U_3&=\frac{17321}{10000},\\
L_6&=\frac{24494}{10000},&U_6&=\frac{24495}{10000}.
\end{aligned}
$$

严格平方比较分别是

$$
\begin{aligned}
199996164&<200000000<200024449,\\
299982400&<300000000<300017041,\\
599956036&<600000000<600005025.
\end{aligned}
$$

故 $L_d<\sqrt d<U_d$ 对 $d=2,3,6$ 成立。按 (2.8) 各系数符号代入这些夹逼，得到

$$
\begin{aligned}
\frac{\sqrt6}{2}
&<\frac{13}{10}
<\frac{26031}{20000}
<x_3
<\frac{130163}{100000}
<\frac{13017}{10000}
<\frac{6559}{5000}
<T_3,\\
q
&<\frac32
<\frac{116519}{75000}
<x_4
<\frac{14566}{9375}
<\frac{7769}{5000}
<\frac{973}{625}
<T_4.
\end{aligned}
\tag{2.9}
$$

例如 $T_3>4L_6-6U_2=6559/5000$，$T_4>6L_2-4U_3=973/625$；$x_3$、$x_4$ 的端点依次为

$$
\begin{aligned}
\frac{7+L_2-3U_3+4L_6}{10}&=\frac{26031}{20000},
&\frac{7+U_2-3L_3+4U_6}{10}&=\frac{130163}{100000},\\
\frac{12L_2-2U_3+4L_6}{15}&=\frac{116519}{75000},
&\frac{12U_2-2L_3+4U_6}{15}&=\frac{14566}{9375}.
\end{aligned}
$$

式 (2.9) 的左端证明 $x_m>\sqrt{2m}/2$，即 $\tau<1$；右端证明 $x_m<T_m$，即 $\tau>R_m$。所以 $r<1$ 与 $r>1$ 的两方向约束同时成立，$r=1$、纯侧及空联盟也均已涵盖，得到 $m=3,4$ 的核归属。

（五）现设 $m\ge5$。对 $k=1,\ldots,m$，在每个区间 $[k-1/2,k+1/2]$，$\sqrt t$ 凹而 $t^{3/2}$ 凸，区间长度为 $1$、中点为 $k$。中点的凹凸积分不等式给出

$$
\begin{aligned}
S_1&\ge\int_{1/2}^{m+1/2}\sqrt t\,dt
=\frac23\bigl((m+1/2)^{3/2}-2^{-3/2}\bigr),\\
S_3&\le\int_{1/2}^{m+1/2}t^{3/2}\,dt
=\frac25\bigl((m+1/2)^{5/2}-2^{-5/2}\bigr).
\end{aligned}
\tag{2.10}
$$

令 $h=1/(2m)$，则 $0<h\le1/10$。凸函数的切线界给 $(1+h)^{3/2}\ge1+3h/2$。另一方面，对 $0\le s\le1/10$，

$$
\frac52(1+s)^{3/2}
\le\frac52\left(\frac{11}{10}\right)^{3/2}<3,
$$

因为 $(11/10)^3=1331/1000<36/25$。积分此导数界，得 $(1+h)^{5/2}\le1+3h$。代回 (2.10)，第二式舍去其负的常数项，得到

$$
S_1\ge\frac23m^{3/2}+\frac12\sqrt m-\frac1{3q},
\qquad
S_3\le\frac25m^{5/2}+\frac35m^{3/2}.
\tag{2.11}
$$

由于 $q-2<0$，在 (2.7) 中对 $S_3$ 代入上界，方向为下估计 $x_m$。令

$$
z=m^{-1/2}\in(0,1/\sqrt5],\quad
Q(z)=1+3z^2+2z^4>0,
$$

并记

$$
c=\frac{2(3q-1)}{15},\qquad d=\frac{19q}{15}-\frac7{10}.
$$

将 (2.11) 完整代入并除以 $\sqrt m$，得到

$$
\frac{x_m}{\sqrt m}\ge\frac{N(z)}{Q(z)},
\qquad
N(z)=2\left(c+dz^2-\frac{z^3}{3q}+\frac q2z^4-\frac13z^5\right).
\tag{2.12}
$$

为给出统一严格界，展开

$$
\begin{aligned}
P(z)&=N(z)-\frac{77}{100}Q(z)\\
&=\frac{240q-311}{300}
+\left(\frac{38q}{15}-\frac{371}{100}\right)z^2
-\frac{2}{3q}z^3
+\left(q-\frac{77}{50}\right)z^4
-\frac23z^5.
\end{aligned}
\tag{2.13}
$$

这里常数系数严格为正，因为 $q>707/500$；一次项系数为零。二次、四次系数由 $q<10/7$ 分别满足

$$
\frac{38q}{15}-\frac{371}{100}<-\frac{191}{2100}<0,
\qquad
q-\frac{77}{50}<-\frac{39}{350}<0.
$$

三次、五次系数也严格为负。所用 $707/500<q<10/7$ 由 $499849<500000$ 和 $98<100$ 的平方比较得到。因此 $0\le z\le1/\sqrt5$ 时，每个非常数非零项在右端点最小，故

$$
\begin{aligned}
P(z)&\ge P(1/\sqrt5)=D,\\
D&=\frac{101q}{75}-\frac{6901}{3750}
-\frac2{15\sqrt{10}}-\frac2{75\sqrt5}.
\end{aligned}
\tag{2.14}
$$

正有理数 $1581/500$、$559/250$ 分别严格小于 $\sqrt{10}$、$\sqrt5$，其平方比较为 $2499561<2500000$、$312481<312500$。连同 $q>707/500$，(2.14) 给出完全有理的严格下界

$$
\begin{aligned}
D
&>\frac{101}{75}\frac{707}{500}-\frac{6901}{3750}
-\frac2{15}\frac{500}{1581}-\frac2{75}\frac{250}{559}\\
&=\frac{325668263}{33141712500}
>\frac9{1000}>0.
\end{aligned}
\tag{2.15}
$$

最后一个严格比较也可写为 $325668263000>298275412500$。由 $Q(z)>0$、(2.12) 与 (2.13)，对全部 $m\ge5$，

$$
x_m>\frac{77}{100}\sqrt m.
\tag{2.16}
$$

（六）估计真正阻塞联盟的门槛。若 $m=2k\ge6$，则

$$
R_m^2=\frac{k}{k+1}\ge\frac34.
$$

若 $m=2k+1\ge5$，则

$$
R_m^2=\frac{2k+1}{2k+2}\ge\frac56>\frac34.
$$

所以两种奇偶情形都有

$$
\frac{T_m}{\sqrt m}
\le\frac{q}{1+\sqrt3/2}<\frac{19}{25}.
\tag{2.17}
$$

后一比较的两边为正，平方后等价于 $5000<361(7+4\sqrt3)$。由 $\sqrt3>173/100$，其右端减左端严格大于 $628/25>0$，而 $173^2<3\cdot100^2$ 证明所用根式下界。因此 (2.16)–(2.17) 推出

$$
x_m-T_m>\frac1{100}\sqrt m.
\tag{2.18}
$$

任意上述 $C_m$ 的两侧计数恰为 $(1,j_m)$。为核对赤字的常数，记 $R=R_m$，由 $2j_m/m=R^{-2}$ 及 (2.7)，

$$
\begin{aligned}
\Delta_m
&=2\sqrt{j_m}-x_m-j_my_m\\
&=(R^{-2}-1)x_m-\sqrt{2m}(R^{-2}-R^{-1})\\
&=(R^{-2}-1)\left(x_m-\frac{\sqrt{2m}}{1+R}\right)\\
&=\frac{2j_m-m}{m}(x_m-T_m).
\end{aligned}
$$

$j_m\le m$，所以联盟合法；奇数 $m$ 时 $\delta_m=1$，偶数 $m$ 时 $\delta_m=2$。乘 (2.18) 即得所述严格赤字界，故所有 $m\ge5$ 的分配均不在核内。结合（四）完成正整数全范围的充要结论。∎

## 3. 固定一侧规模时的最终失效

**定理 3.1（固定 $a$ 的显式充分阈值）。** 固定整数 $a\ge2$，令 $\alpha=(a-1)/a$，并定义

$$
\begin{aligned}
h_a(t)&=\sum_{k=0}^{a-1}\binom{a-1}{k}
t^k(1-t)^{a-1-k}\bigl(\sqrt{k+1}-\sqrt k\bigr),\\
u_a&=\sqrt a\int_0^1\sqrt t\,h_a(t)\,dt,
\qquad \eta_a=u_a-\frac12.
\end{aligned}
$$

则 $0<\eta_a<1/2$。对每个满足

$$
b>\max\left\{\frac{4a^2}{\eta_a^4},
\frac{1+\eta_a}{4\alpha\eta_a}\right\}
\tag{3.1}
$$

的正整数 $b$，$K_{a,b}$ 的普通能量博弈 Shapley 分配不在收益核内。具体地，令

$$
j_b=\lfloor\alpha b\rfloor+1,\qquad
u_{a,b}=\frac{ax_{a,b}}{2\sqrt{ab}},\qquad
\tau_{a,b}=\frac{1-u_{a,b}}{u_{a,b}},\qquad
r_b=\sqrt{\frac{\alpha b}{j_b}}.
$$

任意包含 $a-1$ 名 $A$ 侧玩家和 $j_b$ 名 $B$ 侧玩家的联盟 $C_b$ 都满足

$$
\Delta(C_b;\phi)
=2\sqrt{ab}\,\frac{j_b}{b}\,u_{a,b}
(1-r_b)(r_b-\tau_{a,b})>0.
\tag{3.2}
$$

边界 $a=1$ 时，对每个正整数 $b$，星图 $K_{1,b}$ 的 Shapley 分配均在核内。式 (3.1) 仅为充分阈值，不要求该阈值最优，也不假定 $a\ge3$ 时核归属对 $b$ 单调。

**证明。** 对每个玩家赋予相互独立、服从 $[0,1]$ 均匀分布的优先级。相等优先级的事件概率为零，按从小到大排序给出均匀排列，所以定理 2.1 的 (2.2) 与定义 1.2 的原始阶乘公式仍完全一致。

条件于目标玩家 $A_1$ 的优先级 $U_{A_1}=t$，其他每名玩家成为前驱的事件都是其自身独立优先级小于 $t$。因此，其他 $A$ 侧前驱数 $J_t$ 与 $B$ 侧前驱数 $S_{b,t}$ 的条件分布为

$$
J_t\sim\operatorname{Bin}(a-1,t),\qquad
S_{b,t}\sim\operatorname{Bin}(b,t),
$$

且在此条件下相互独立。两者由互不相交的独立优先级组生成；无条件独立性并非这里的假设。由 (2.1)，该玩家的边际贡献为

$$
2\sqrt{S_{b,t}}\bigl(\sqrt{J_t+1}-\sqrt{J_t}\bigr).
$$

记

$$
\mu_b(t)=\mathbb E\sqrt{S_{b,t}/b}.
$$

条件独立性及对 $t$ 积分给出

$$
x_{a,b}=2\sqrt b\int_0^1h_a(t)\mu_b(t)\,dt,
\qquad
u_{a,b}=\sqrt a\int_0^1h_a(t)\mu_b(t)\,dt.
\tag{3.3}
$$

对非负实数 $s,t$，$|\sqrt s-\sqrt t|\le\sqrt{|s-t|}$。对条件随机变量 $X=S_{b,t}/b$，两次使用二次矩不等式得到

$$
\begin{aligned}
|\mu_b(t)-\sqrt t|
&\le\mathbb E\sqrt{|X-t|}\\
&\le\bigl(\mathbb E|X-t|\bigr)^{1/2}\\
&\le\bigl(\mathbb E(X-t)^2\bigr)^{1/4}\\
&=\left(\frac{t(1-t)}b\right)^{1/4}
\le(4b)^{-1/4}.
\end{aligned}
\tag{3.4}
$$

这里 $\mathbb EX=t$，方差为 $t(1-t)/b$。又有 $0<h_a(t)\le1$、$0\le\mu_b(t)\le1$，且凹性给出 $\mu_b(t)\le\sqrt t$。所以积分中有与 $b$ 无关的可积支配函数 $1$，并且 (3.4) 直接给出更强的统一误差控制

$$
|u_{a,b}-u_a|\le\sqrt a\,(4b)^{-1/4},
\qquad u_{a,b}\longrightarrow u_a.
\tag{3.5}
$$

这个极限只使用各个条件二项分布的矩，不要求跨 $b$ 的随机变量属于同一耦合。

为确定极限相对于 $1/2$ 的严格位置，定义有限二项和

$$
f_a(t)=\sum_{k=0}^a\binom ak t^k(1-t)^{a-k}\sqrt k
=\mathbb E\sqrt{\operatorname{Bin}(a,t)}.
$$

对 $0<t<1$ 逐项求导，用
$k\binom ak=a\binom{a-1}{k-1}$ 和
$(a-k)\binom ak=a\binom{a-1}{k}$，移位并相减得到

$$
\begin{aligned}
f_a'(t)
&=a\sum_{k=0}^{a-1}\binom{a-1}{k}t^k(1-t)^{a-1-k}
\bigl(\sqrt{k+1}-\sqrt k\bigr)\\
&=a h_a(t).
\end{aligned}
\tag{3.6}
$$

因此，对 $0<\varepsilon<1$，在 $[\varepsilon,1]$ 分部积分给出

$$
\frac1{\sqrt a}\int_\varepsilon^1\sqrt t\,f_a'(t)\,dt
=1-\frac{\sqrt\varepsilon f_a(\varepsilon)}{\sqrt a}
-\frac1{2\sqrt a}\int_\varepsilon^1\frac{f_a(t)}{\sqrt t}\,dt.
$$

Jensen 不等式给 $0\le f_a(t)\le\sqrt{at}$，故
$\sqrt\varepsilon f_a(\varepsilon)\le\sqrt a\,\varepsilon\to0$，且
$f_a(t)/\sqrt t\le\sqrt a$ 是可积控制；左边的被积函数由 (3.6) 也可积。令 $\varepsilon\downarrow0$，得到

$$
u_a=1-\frac1{2\sqrt a}\int_0^1\frac{f_a(t)}{\sqrt t}\,dt.
\tag{3.7}
$$

当 $0<t<1$ 时，$\operatorname{Bin}(a,t)$ 非退化，严格凹的平方根函数给出严格 Jensen 界

$$
0<f_a(t)<\sqrt{at}.
$$

这些函数在 $(0,1)$ 连续，故积分也严格满足

$$
0<\int_0^1\frac{f_a(t)}{\sqrt t}\,dt<\sqrt a.
$$

由 (3.7)，$1/2<u_a<1$，即 $0<\eta_a<1/2$。

现在设 $b$ 满足 (3.1)。第一个阈值使 $\sqrt a(4b)^{-1/4}<\eta_a/2$，所以 (3.5) 给出

$$
u_{a,b}>\frac12+\frac{\eta_a}{2},
\qquad
\tau_{a,b}<\frac{1-\eta_a}{1+\eta_a}.
\tag{3.8}
$$

由 $0<\alpha<1$ 和整数 $b$，

$$
\alpha b<j_b\le\alpha b+1,\qquad 1\le j_b\le b,
$$

因此指定联盟确实存在，且 $0<r_b<1$。函数 $(1+s)^{-1/2}$ 在 $s\ge0$ 严格凸，其在零点的切线给出对 $s>0$ 的严格下界 $(1+s)^{-1/2}>1-s/2$。于是

$$
\begin{aligned}
r_b
&\ge\left(1+\frac1{\alpha b}\right)^{-1/2}\\
&>1-\frac1{2\alpha b}\\
&>\frac{1-\eta_a}{1+\eta_a}
>\tau_{a,b}.
\end{aligned}
\tag{3.9}
$$

倒数第二步恰由 (3.1) 的第二个阈值保证。对计数 $(a-1,j_b)$，(2.4) 中的交叉比正是 $r_b$；取其负数即得到 (3.2)。所有因子均严格为正，证明最终失效。

最后在同一判据内处理边界 $a=1$。对唯一中心玩家，前驱中有 $k$ 名叶子的总概率为 $1/(b+1)$，其边际为 $2\sqrt k$，故

$$
x_{1,b}=\frac2{b+1}\sum_{k=0}^b\sqrt k.
$$

逐项使用 $\sqrt k\ge k/\sqrt b$（$0\le k\le b$）给出 $x_{1,b}\ge\sqrt b$。因此 $u=x_{1,b}/(2\sqrt b)\ge1/2$，且由 (2.3) 仍有 $u<1$，所以 $0<\tau\le1$。每个混合联盟有 $i=1$、$1\le j\le b$，于是 $r=\sqrt{b/j}\ge1$；(2.4) 给出非负余量。纯侧由 (2.3) 的正性满足，全体由效率取等，得到所有正整数 $b$ 的星图核归属。∎

## 追加锚（本行以下为增补区）

## 4. 固定一侧规模的最大阻塞赤字

**定义 4.1（最大赤字与极限轮廓）。** 对整数 $a\ge2$、$b\ge1$，在定义 1.1–1.3 的同一个图 $K_{a,b}$ 及其普通能量博弈上，记

$$
D_{a,b}=\max_{C\subseteq A\sqcup B}\Delta(C;\phi)
=\max_{C\subseteq A\sqcup B}
\left(w_{K_{a,b}}(C)-\sum_{v\in C}\phi_v(w_{K_{a,b}})\right).
\tag{4.1}
$$

这里最大化有符号的阻塞赤字；空联盟给出 $D_{a,b}\ge0$。价值函数与阶乘 Shapley 分配采用 Arizmendi–Arizmendi，[*The graph energy game*, arXiv:2012.14114v2](https://arxiv.org/pdf/2012.14114v2)，Definition 3.1、§2.4 的约定。沿用定理 3.1 的 $h_a$、$u_a$ 以及 (3.3) 的 $u_{a,b}$，并置

$$
v_a=1-u_a,\qquad
\varepsilon_{a,b}=\sqrt a\,(4b)^{-1/4}.
$$

由 (3.5)–(3.7)，$1/2<u_a<1$、$0<v_a<1/2$，且
$|u_{a,b}-u_a|\le\varepsilon_{a,b}$。对 $z\in[0,1]$ 定义

$$
M_a(z)=
\begin{cases}
\displaystyle\frac{z(2u_a-1)^2}{4v_a},&0\le z\le4v_a^2,\\[6pt]
\sqrt z-u_a z-v_a,&4v_a^2<z\le1.
\end{cases}
\tag{4.2}
$$

另记

$$
\rho_a=\frac{a}{4u_a^2},\qquad
I_a=\{\lfloor\rho_a\rfloor,\lceil\rho_a\rceil\}
\cap\{0,1,\ldots,a\},\qquad
L_a=\max_{i\in I_a}M_a(i/a).
\tag{4.3}
$$

**定理 4.2（最大赤字系数、两计数约化与实现联盟）。** 对每个整数 $a\ge2$，有

$$
L_a=\max_{0\le i\le a,\ i\in\mathbb Z}M_a(i/a)>0,
\qquad
\operatorname*{arg\,max}_{0\le i\le a,\ i\in\mathbb Z}M_a(i/a)
\subseteq I_a.
\tag{4.4}
$$

对每个整数 $b\ge1$，有显式比较

$$
\left|\frac{D_{a,b}}{2\sqrt{ab}}-L_a\right|
\le\sqrt a\,(4b)^{-1/4}+b^{-1/2}+b^{-1}.
\tag{4.5}
$$

因此固定 $a$、令 $b$ 沿正整数趋于无穷时，

$$
\frac{D_{a,b}}{\sqrt b}\longrightarrow2\sqrt a\,L_a>0.
\tag{4.6}
$$

具体地，对任一使 $M_a(i/a)$ 最大的整数 $i$，置

$$
s_i=\min\left\{1,\frac{i/a}{4v_a^2}\right\},\qquad
j_b=\lfloor bs_i\rfloor.
\tag{4.7}
$$

任取 $i$ 名 $A$ 侧玩家与 $j_b$ 名 $B$ 侧玩家组成联盟 $C_b$，均有

$$
\frac{\Delta(C_b;\phi)}{2\sqrt{ab}}\longrightarrow L_a.
\tag{4.8}
$$

式 (4.4) 保留 $I_a$ 中两计数并列的可能；若 $\rho_a$ 为整数，$I_a$ 只有一个计数。式 (4.5) 对所有 $a\ge2,b\ge1$ 成立，不要求 $b\ge a$；(4.6)、(4.8) 的极限均固定 $a$。

**证明。** 首先把所有联盟的赤字写在同一个图的两个计数上。设

$$
z=i/a,\qquad s=j/b,\qquad U=u_{a,b}.
$$

由 (2.1)–(2.3) 的联盟能量、同侧对称性和效率，

$$
\begin{aligned}
\frac{\Delta(C;\phi)}{2\sqrt{ab}}
&=\frac{2\sqrt{ij}-ix_{a,b}-jy_{a,b}}{2\sqrt{ab}}\\
&=\sqrt{zs}-Uz-(1-U)s.
\end{aligned}
\tag{4.9}
$$

每个整数计数对 $0\le i\le a$、$0\le j\le b$ 都由实际联盟实现；计数相同的联盟赤字相同。式 (4.9) 同时包含空联盟、纯侧联盟和全体联盟。

对任意 $z,s\in[0,1]$ 记

$$
F_a(z,s)=\sqrt{zs}-u_a z-v_a s.
$$

式 (4.9) 与此函数的差恰为 $(U-u_a)(s-z)$。由 (3.5)，统一有

$$
\left|\sqrt{zs}-Uz-(1-U)s-F_a(z,s)\right|
\le\varepsilon_{a,b}.
\tag{4.10}
$$

现对固定的 $z$ 在 $s\in[0,1]$ 上最大化 $F_a$。用通常的一元二次配方法，令 $q=\sqrt s\in[0,1]$，则

$$
F_a(z,q^2)
=-v_a\left(q-\frac{\sqrt z}{2v_a}\right)^2
+\frac{z}{4v_a}-u_a z.
$$

因 $v_a>0$，唯一最大点为
$q=\min\{1,\sqrt z/(2v_a)\}$，亦即
$s=\min\{1,z/(4v_a^2)\}$，包括 $z=0$ 时的 $s=0$。利用
$1-4u_av_a=(2u_a-1)^2$，得到

$$
\max_{0\le s\le1}F_a(z,s)=M_a(z).
\tag{4.11}
$$

在分支连接点 $z_0=4v_a^2\in(0,1)$，(4.2) 两式都等于
$v_a(2u_a-1)^2$，左右导数也都等于

$$
c_a=\frac{(2u_a-1)^2}{4v_a}>0.
$$

在 $0<z<z_0$，导数为 $c_a$；在 $z_0<z<1$，导数为
$1/(2\sqrt z)-u_a$。后者只在

$$
z_*=(4u_a^2)^{-1}
$$

为零。因为 $4u_av_a=1-(2u_a-1)^2<1$，有
$z_0<z_*<1$；同时 $z_*>1/4$。所以 $M_a$ 在 $[0,z_*]$ 上严格递增，在 $[z_*,1]$ 上严格递减。其两端为
$M_a(0)=M_a(1)=0$，从而对每个 $0<z<1$ 都有 $M_a(z)>0$。

现在只在 $z=i/a$ 上取值。因 $az_*=\rho_a\in(0,a)$，若 $i<\lfloor\rho_a\rfloor$，则向右移一个整数计数使 $M_a(i/a)$ 严格增大；若 $i>\lceil\rho_a\rceil$，则向左移一个整数计数使其严格增大。因此所有最大计数均在 $I_a$ 中。若两邻点的值相等，两者都保留；若 $\rho_a$ 为整数，严格单调性排除其它计数。又因 $a\ge2$，$1/a\in(0,1)$，故
$L_a\ge M_a(1/a)>0$，证得 (4.4)。

最后比较连续最大值与合法的 $B$ 侧网格。对任意 $z,s,t\in[0,1]$，平方根的基本不等式给出

$$
\begin{aligned}
|F_a(z,s)-F_a(z,t)|
&\le\sqrt z\,|\sqrt s-\sqrt t|+v_a|s-t|\\
&\le\sqrt{|s-t|}+|s-t|.
\end{aligned}
\tag{4.12}
$$

对每个 $i\in\{0,\ldots,a\}$，令 $s_i$ 如 (4.7)，即使 $i$ 不是最大计数也采用同一公式。由 (4.11)，
$F_a(i/a,s_i)=M_a(i/a)$。置 $t_{i,b}=\lfloor bs_i\rfloor/b$，则

$$
0\le\lfloor bs_i\rfloor\le b,\qquad
0\le s_i-t_{i,b}<b^{-1}.
$$

所以该取整始终给出实际联盟，包括 $s_i=0,1$ 时精确落在端点的情形。由 (4.10)–(4.12)，任一对应联盟 $C_{i,b}$ 满足

$$
\left|\frac{\Delta(C_{i,b};\phi)}{2\sqrt{ab}}-M_a(i/a)\right|
\le\varepsilon_{a,b}+b^{-1/2}+b^{-1}.
\tag{4.13}
$$

另一方面，对任意合法计数 $(i,j)$，(4.10)、(4.11)、(4.4) 依次给出

$$
\frac{\Delta(C;\phi)}{2\sqrt{ab}}
\le F_a(i/a,j/b)+\varepsilon_{a,b}
\le M_a(i/a)+\varepsilon_{a,b}
\le L_a+\varepsilon_{a,b}.
$$

在全部联盟上取最大值即得同一上界。取任一最大计数 $i$，(4.13) 给出下界

$$
\frac{D_{a,b}}{2\sqrt{ab}}
\ge L_a-\varepsilon_{a,b}-b^{-1/2}-b^{-1}.
$$

合并上下界得到 (4.5)。对固定 $a$，右侧误差趋于零，乘以 $2\sqrt a$ 即得 (4.6)。对每个最大计数直接应用 (4.13)，即得任意标签选择的 (4.8)。这里确定的是极限最大赤字系数及实现其极限的联盟，未给出有限 $b$ 的精确最大联盟或核归属分类，也未推出核归属随 $b$ 的单调性。∎

**命题 4.3（$a=2$ 的精确最大系数）。** 当 $a=2$ 时，定义 4.1 的常数满足

$$
\begin{aligned}
u_2&=\frac{12-2\sqrt2}{15},&
v_2&=\frac{3+2\sqrt2}{15},& I_2&=\{1,2\},\\
L_2&=\frac{627-442\sqrt2}{120},&
s_1&=\frac{225}{8(17+12\sqrt2)}.
\end{aligned}
\tag{4.14}
$$

在全部 $i\in\{0,1,2\}$ 中，唯一最大计数是 $i=1$。于是

$$
\frac{D_{2,b}}{\sqrt b}
\longrightarrow\frac{627\sqrt2-884}{60},
\tag{4.15}
$$

且任取一名 $A$ 侧玩家及 $\lfloor bs_1\rfloor$ 名 $B$ 侧玩家得到的联盟实现 (4.8)。

**证明。** 定理 3.1 的有限二项式在此为
$h_2(t)=1+(\sqrt2-2)t$。直接代入其中的收益积分得到

$$
u_2=\sqrt2\left(\frac23+\frac25(\sqrt2-2)\right)
=\frac{12-2\sqrt2}{15},
$$

相减即得 $v_2$。这里使用的是 (3.3)–(3.7) 的收益极限。由
$1<\sqrt2$ 可知 $u_2<2/3$，而 $4/9<1/2$ 给出
$2/3<1/\sqrt2$；结合 $u_2>1/2$，得到

$$
1<\rho_2=\frac1{2u_2^2}<2.
$$

所以 $I_2=\{1,2\}$。又有

$$
4v_2^2=\frac{4(17+12\sqrt2)}{225}>\frac12,
$$

因为 $8(17+12\sqrt2)>136+96>225$。故 $z=1/2$ 位于 (4.2) 的第一分支，且 $0<s_1<1$。于是

$$
\begin{aligned}
M_2(1/2)
&=\frac{(2u_2-1)^2}{8v_2}
=\frac{113-72\sqrt2}{120(3+2\sqrt2)}\\
&=\frac{(113-72\sqrt2)(3-2\sqrt2)}{120}
=\frac{627-442\sqrt2}{120},\\
s_1&=\frac1{8v_2^2}
=\frac{225}{8(17+12\sqrt2)}.
\end{aligned}
$$

定理 4.2 给 $M_2(1/2)>0$，而 $M_2(0)=M_2(1)=0$，所以唯一最大计数为 $1$，且 $L_2=M_2(1/2)$。将其乘以 $2\sqrt2$ 得到 (4.15)，实现联盟由 (4.7)–(4.8) 给出。

作为比较，补集联盟 $(A\sqcup B)\setminus\{A_1\}$ 的计数为 $(1,b)$，由 (4.9)、(3.5) 得到其赤字除以 $\sqrt b$ 的系数

$$
2\sqrt2\,F_2(1/2,1)=\frac{26-18\sqrt2}{15}.
$$

此补集联盟正是[完全二部图能量及 Shapley 分配](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.md)中使用的阻塞联盟；它的渐近系数亦见 [aa2012 的相应计算](../../../Problems/aa2012.md#triage)。由于二次配方中的最大点 $\sqrt{s_1}<1$，严格有

$$
L_2-F_2(1/2,1)=v_2(1-\sqrt{s_1})^2>0.
$$

因此 (4.15) 给出的最大赤字系数严格大于该补集联盟的系数。两者均涉及定义 1.2 的同一个普通 Shapley 分配。∎

## 追加锚（本行以下为增补区）

## 5. 三顶点侧的有限核分类

**定理 5.1（$K_{3,b}$ 的唯一零赤字端点）。** 对每个整数 $b\ge3$ 及每对不交的有限标号集 $A,B$，若 $|A|=3$、$|B|=b$，令 $G$ 为恰含全部 $A$–$B$ 边的简单图。采用定义 1.1–1.2 的普通邻接能量价值与阶乘 Shapley 分配，以及定义 4.1 在全部联盟上的有符号最大赤字，则

$$
D_{3,b}=0\quad\Longleftrightarrow\quad b=3.
\tag{5.1}
$$

具体地，$b=3$ 时每名玩家的 Shapley 分配均为 $1$；每个整数 $b\ge4$ 时，置

$$
j_b=\left\lfloor\frac{2b}{3}\right\rfloor+1.
\tag{5.2}
$$

任取两名 $A$ 侧玩家和 $j_b$ 名 $B$ 侧玩家组成的联盟 $C_b$，均有
$\Delta(C_b;\phi)>0$，从而 $D_{3,b}>0$。这里的价值与分配是 Arizmendi–Arizmendi，[*The graph energy game*, arXiv:2012.14114v2](https://arxiv.org/pdf/2012.14114v2)，§2.2、§2.4、Definition 3.1 的同一普通能量博弈；Theorem 3.6 的 vertex-energy 分配与 Proposition 4.13 的 $2$-energy Shapley 分配分别是不同的分配与不同的价值函数。

**证明。** 只用保持两侧各自不变的顶点置换，同侧玩家的分配分别记为 $x_{3,b}$、$y_{3,b}$。任意标号集可经两侧各自的双射与定义 1.3 的标号对应；这样的双射逐项运输阶乘和中的前驱集合，保持其大小和边际价值。由 (2.1)–(2.3)，对每个联盟 $C$，包括某侧计数为零的情形，

$$
w_G(C)=2\sqrt{ij},\qquad
x_{3,b}>0,\quad y_{3,b}>0,\quad
3x_{3,b}+by_{3,b}=2\sqrt{3b},
\qquad i=|C\cap A|,\quad j=|C\cap B|.
\tag{5.3}
$$

因而 $u_{3,b}=3x_{3,b}/(2\sqrt{3b})$ 属于 $(0,1)$。证明先确定平衡端点的实际分配，再把其余全部整数归约到两个有限分配计算。

（一）沿用 (3.3)、(3.6) 的有限二项式积分与导数恒等式。记

$$
f_n(t)=\sum_{k=0}^n\binom nk t^k(1-t)^{n-k}\sqrt k,
\qquad \mu_n(t)=\frac{f_n(t)}{\sqrt n}
\quad(n\ge1),
$$

则 $f_3'(t)=3h_3(t)$，且

$$
u_{3,b}=\sqrt3\int_0^1h_3(t)\mu_b(t)\,dt.
\tag{5.4}
$$

这些恒等式来自同一阶乘分配：给目标玩家和其他玩家独立均匀优先级，条件于目标优先级 $t$ 时，其余两名 $A$ 侧玩家的前驱数为 $\operatorname{Bin}(2,t)$，$B$ 侧前驱数为 $\operatorname{Bin}(b,t)$，且在这个条件下独立。固定前驱集合 $S$ 的排列数仍为 $|S|!(b+2-|S|)!$，总排列数为 $(b+3)!$，故没有遗漏任何前驱集合。

在 $b=3$ 时，直接代入 (5.4) 而不预设两侧分配相等，得到

$$
\begin{aligned}
u_{3,3}
&=\int_0^1h_3(t)f_3(t)\,dt
=\frac13\int_0^1f_3'(t)f_3(t)\,dt\\
&=\frac{f_3(1)^2-f_3(0)^2}{6}
=\frac12,
\end{aligned}
\tag{5.5}
$$

因为 $f_3(1)=\sqrt3$、$f_3(0)=0$。所以 $x_{3,3}=1$，再由 (5.3) 得 $y_{3,3}=1$。对所有整数计数 $0\le i,j\le3$，

$$
\Delta(C;\phi)=2\sqrt{ij}-i-j
=-(\sqrt i-\sqrt j)^2\le0.
$$

空联盟与全体联盟都取零，故在所有联盟上的有符号最大值恰为 $D_{3,3}=0$。

（二）为比较 (5.4) 中不同样本大小的二项式平均，固定 $t\in[0,1]$ 和正整数 $n$，在同一个概率空间取 $n+1$ 个独立 $\operatorname{Bernoulli}(t)$ 变量 $X_1,\ldots,X_{n+1}$。令

$$
T=\sum_{\ell=1}^{n+1}X_\ell,\qquad
Y_\ell=\frac{T-X_\ell}{n}.
$$

同一次实现内有

$$
\frac1{n+1}\sum_{\ell=1}^{n+1}Y_\ell
=\frac{T}{n+1}.
$$

平方根的凹性逐次实现给出

$$
\sqrt{\frac{T}{n+1}}
\ge\frac1{n+1}\sum_{\ell=1}^{n+1}\sqrt{Y_\ell}.
$$

每个 $nY_\ell$ 都服从 $\operatorname{Bin}(n,t)$；这些删去一个变量的和之间不要求独立。取期望便得 $\mu_{n+1}(t)\ge\mu_n(t)$，包含 $t=0,1$。这是经典的删去一个样本的 Jensen 比较，见 Lamkin–Tkocz，[*Log-concavity and log-convexity of moments of averages of i.i.d. random variables*, arXiv:2001.06439v3](https://arxiv.org/pdf/2001.06439v3)，§1，第 1 页，式 (1) 后的平均恒等式；期刊为 *Canadian Mathematical Bulletin* **65**(2)，271–278，[DOI:10.4153/S0008439521000254](https://doi.org/10.4153/S0008439521000254)。这里直接使用非负 Bernoulli 变量和有限 Jensen 不等式，零值处也在定义域中。

由于 $h_3(t)>0$，把这个比较代入 (5.4)，所需的结论为

$$
u_{3,b}\ge u_{3,5}\qquad(b\ge5).
\tag{5.6}
$$

（三）计算 $u_{3,4}$、$u_{3,5}$。对目标 $A$ 侧玩家，将其前驱集按其中另外两名 $A$ 侧玩家的数量 $r\in\{0,1,2\}$ 和 $B$ 侧玩家数量 $k\in\{0,\ldots,b\}$ 分类。该类前驱集的阶乘总权重恰为

$$
W_{r,k}=\binom2r\binom bk
\frac{(k+r)!(b+2-k-r)!}{(b+3)!}.
$$

令 $H_b=(b+1)(b+2)(b+3)$。用 $\binom bk k!(b-k)!=b!$ 约去阶乘，三类分别为

$$
\begin{aligned}
W_{0,k}&=\frac{(b+2-k)(b+1-k)}{H_b},\\
W_{1,k}&=\frac{2(k+1)(b+1-k)}{H_b},\\
W_{2,k}&=\frac{(k+1)(k+2)}{H_b}.
\end{aligned}
$$

其边际价值为 $2\sqrt k(\sqrt{r+1}-\sqrt r)$。包括 $k=0$ 的零边际端点，完整相加得到

$$
\begin{aligned}
x_{3,b}&=\frac2{H_b}\sum_{k=0}^b\sqrt k\,P_b(k),\\
P_b(k)&=(b+2-k)(b+1-k)
+2(\sqrt2-1)(k+1)(b+1-k)\\
&\hspace{2em}+(\sqrt3-\sqrt2)(k+1)(k+2).
\end{aligned}
\tag{5.7}
$$

代入 $b=4,5$，分别先将和式合并为

$$
\begin{aligned}
\sum_{k=0}^4\sqrt k\,P_4(k)
&=60-36\sqrt2+56\sqrt3+8\sqrt6,\\
\sum_{k=0}^5\sqrt k\,P_5(k)
&=66-10\sqrt2+54\sqrt3+16\sqrt6
-10\sqrt5-30\sqrt{10}+42\sqrt{15}.
\end{aligned}
$$

由 (5.7) 先乘以 $2/H_b$ 得到 $x_{3,b}$，再乘以 $3/(2\sqrt{3b})$，即得

$$
\begin{aligned}
u_{3,4}&=\frac{42+6\sqrt2+15\sqrt3-9\sqrt6}{105},\\
u_{3,5}&=\frac{315+81\sqrt5+24\sqrt{10}+33\sqrt{15}
-5\sqrt{30}-25\sqrt3-75\sqrt6}{840}.
\end{aligned}
\tag{5.8}
$$

为作严格有理比较，沿用定理 2.1 证明中的
$L_2=14142/10000$、$L_3=17320/10000$、$U_3=17321/10000$、$U_6=24495/10000$，其中 $L_d<\sqrt d<U_d$。另取

$$
L_5=\frac{22360}{10000},\quad
L_{10}=\frac{31622}{10000},\quad
L_{15}=\frac{38729}{10000},\quad
U_{30}=\frac{54773}{10000}.
$$

这些新端点所需的严格平方比较是

$$
\begin{aligned}
22360^2&=499969600<500000000,\\
31622^2&=999950884<1000000000,\\
38729^2&=1499935441<1500000000,\\
54773^2&=3000081529>3000000000.
\end{aligned}
$$

所有端点均为正，故 $L_d<\sqrt d$ 对 $d=5,10,15$ 成立，而 $\sqrt{30}<U_{30}$。按 (5.8) 中每项系数的符号代入，得到

$$
\begin{aligned}
u_{3,4}
&>\frac{42+6L_2+15L_3-9U_6}{105}
=\frac{181399}{350000}
>\frac{1287}{2500}
=9-6L_2
>9-6\sqrt2,\\
u_{3,5}
&>\frac{315+81L_5+24L_{10}+33L_{15}
-5U_{30}-25U_3-75U_6}{840}\\
&=\frac{148471}{280000}
=\frac{53}{100}+\frac{71}{280000}
>\frac{53}{100}.
\end{aligned}
\tag{5.9}
$$

第一行中间的有理严格差为 $1219/350000$。

（四）验证指定联盟对全部 $b\ge4$ 都严格阻塞。由 (5.2) 与 $b\ge3$，

$$
\frac{2b}{3}<j_b\le\frac{2b}{3}+1\le b.
$$

因此所需的两侧玩家数量均可取得，并且

$$
r_b=\sqrt{\frac{2b}{3j_b}}\in(0,1),\qquad
\tau_{3,b}=\frac{1-u_{3,b}}{u_{3,b}}.
$$

当 $b=4$ 时，$j_4=3$，所以

$$
\frac1{1+r_4}
=\frac1{1+2\sqrt2/3}=9-6\sqrt2<u_{3,4}
\tag{5.10}
$$

由 (5.9) 得到。若 $b=5$，则 $j_5=4\le5b/6$；若 $b\ge6$，则
$j_b\le2b/3+1\le5b/6$。故全部 $b\ge5$ 同时满足

$$
r_b\ge\frac2{\sqrt5},\qquad
\frac1{1+r_b}\le\frac1{1+2/\sqrt5}
=5-2\sqrt5
<5-2L_5=\frac{66}{125}<\frac{53}{100}
<u_{3,5}\le u_{3,b}.
\tag{5.11}
$$

式 (5.10)–(5.11) 给出每个整数 $b\ge4$ 的严格不等式
$u_{3,b}>1/(1+r_b)$。因为 $u_{3,b}>0$，这等价于
$r_b>\tau_{3,b}$。对计数 $(i,j)=(2,j_b)$，(2.4) 的因式分解于是给出精确赤字

$$
\Delta(C_b;\phi)
=2\sqrt{3b}\,\frac{j_b}{b}\,u_{3,b}
(1-r_b)(r_b-\tau_{3,b})>0.
\tag{5.12}
$$

这里每个因子都严格为正，且任意指定标签的 $C_b$ 都是实际联盟。全部联盟组成有限非空集合，所以定义 4.1 的最大值确实取得，并有 $D_{3,b}\ge\Delta(C_b;\phi)>0$。结合（一）的 $D_{3,3}=0$，得到 (5.1)。式 (5.12) 只给出严格阻塞联盟，不将其指定为有限 $b$ 的最大赤字联盟。∎

**定义 5.2（其余固定侧规模的有限分类域）。** 对整数 $a\ge4$，沿用定理 3.1 的 $\alpha=(a-1)/a$、$\eta_a$，记

$$
B_a=\max\left\{\frac{4a^2}{\eta_a^4},
\frac{1+\eta_a}{4\alpha\eta_a}\right\},\qquad
Z_a=\{b\in\mathbb Z:\ b\ge a,\ D_{a,b}=0\}.
$$

由定理 3.1 与效率，$Z_a\subseteq\{b\in\mathbb Z:a\le b\le B_a\}$；确定这个有限集合的成员是 $a\ge4$ 的有限核分类问题。定理 5.1 的充要式只量化 $a=3$、$b\ge3$，不确定 $Z_a$，也不要求 $D_{3,b}$ 的单调性或正赤字的精确最大值。

## 追加锚（本行以下为增补区）

## 6. 四顶点侧的有限核分类

**定理 6.1（$K_{4,b}$ 的唯一零赤字端点）。** 对每个整数 $b\ge4$ 及每对不交的有限标号集 $A,B$，设 $|A|=4$、$|B|=b$，且 $G$ 恰含全部 $A$–$B$ 边。采用定义 1.1–1.2 的普通邻接能量价值与原始阶乘 Shapley 分配，以及定义 4.1 在全部联盟上的有符号最大赤字，则

$$
D_{4,b}=0\quad\Longleftrightarrow\quad b=4.
\tag{6.1}
$$

$b=4$ 时每名玩家的分配均为 $1$，且每个联盟 $C$，记 $i=|C\cap A|$、$j=|C\cap B|$，均满足

$$
\Delta(C;\phi)=-(\sqrt i-\sqrt j)^2.
\tag{6.2}
$$

每个整数 $b\ge5$ 时，令

$$
j_b=\left\lfloor\frac{3b}{4}\right\rfloor+1.
\tag{6.3}
$$

任取三名 $A$ 侧玩家和 $j_b$ 名 $B$ 侧玩家组成的联盟 $C_b$ 都合法，并且

$$
\Delta(C_b;\phi)>0,\qquad D_{4,b}>0.
\tag{6.4}
$$

这里的价值与分配对应 Arizmendi–Arizmendi，[*The graph energy game*, arXiv:2012.14114v2](https://arxiv.org/pdf/2012.14114v2)，§2.2、§2.4、Definition 3.1。该文 Theorems 3.5–3.6 的 vertex-energy 分配 $e_v=(|A_G|)_{vv}$ 与本定理的阶乘分配不同；Proposition 4.13 的 $2$-energy 博弈采用 $\operatorname{tr}(|A_G|^2)$，也不同于此处的普通能量 $\operatorname{tr}|A_G|$。

**证明。** 对两个标号集分别取双射，会在阶乘和中双射地运输全部前驱集合，保持其大小、边际价值及权重。因此可沿用定义 1.3 的 $K_{4,b}$ 标号。由 (2.1)–(2.3) 的谱计算、排列平均、同侧对称性和效率，记 $x_b=x_{4,b}$、$y_b=y_{4,b}$，则

$$
w_G(C)=2\sqrt{ij},\qquad x_b>0,\quad y_b>0,\quad
4x_b+by_b=4\sqrt b.
\tag{6.5}
$$

置

$$
u_b=u_{4,b}=\frac{x_b}{\sqrt b}\in(0,1),\qquad
\tau_b=\frac{1-u_b}{u_b}.
$$

式 (4.9) 在这里给出全部联盟的同一个公式

$$
\frac{\Delta(C;\phi)}{4\sqrt b}
=\sqrt{\frac i4\frac jb}-u_b\frac i4-(1-u_b)\frac jb,
\quad 0\le i\le4,\quad 0\le j\le b.
\tag{6.6}
$$

每个整数计数对均由实际联盟实现，纯侧与空联盟也包含在内。下面先计算平衡端点，再给出其余整数的统一严格阻塞界。

（一）沿用定理 3.1 与定理 5.1 证明中的有限二项式

$$
f_n(t)=\sum_{k=0}^n\binom nk t^k(1-t)^{n-k}\sqrt k,
\qquad \mu_n(t)=\frac{f_n(t)}{\sqrt n}\quad(n\ge1).
$$

由 (3.3)、(3.6)，

$$
f_4'(t)=4h_4(t),\qquad
u_b=2\int_0^1h_4(t)\mu_b(t)\,dt.
\tag{6.7}
$$

参数对应为 $a=4$：条件于目标 $A$ 侧玩家的优先级为 $t$，其余三名同侧玩家的前驱数服从 $\operatorname{Bin}(3,t)$，异侧前驱数服从 $\operatorname{Bin}(b,t)$，且在此条件下独立。此时边际贡献为 $2\sqrt k(\sqrt{r+1}-\sqrt r)$。固定前驱集的排列数为 $(k+r)!(b+3-k-r)!$，总排列数为 $(b+4)!$，与定义 1.2 完全相同。式 (6.7) 是这个有限阶乘和的优先级积分，不取 $b\to\infty$ 的极限。

当 $b=4$ 时，$\mu_4=f_4/2$，$f_4(0)=0$、$f_4(1)=2$，故

$$
\begin{aligned}
u_4
&=\int_0^1h_4(t)f_4(t)\,dt
=\frac14\int_0^1f_4'(t)f_4(t)\,dt\\
&=\frac{f_4(1)^2-f_4(0)^2}{8}=\frac12.
\end{aligned}
$$

所以 $x_4=1$，由 (6.5) 得 $y_4=1$。对每个 $0\le i,j\le4$，直接有
$\Delta(C;\phi)=2\sqrt{ij}-i-j=-(\sqrt i-\sqrt j)^2\le0$。等号恰在 $i=j$ 时成立；空联盟与全体联盟都取零，故全部联盟上的最大值恰为 $D_{4,4}=0$。

（二）复用定理 5.1 证明（二）的删去一个样本的 Jensen 比较：对每个 $t\in[0,1]$ 与正整数 $n$，$\mu_{n+1}(t)\ge\mu_n(t)$。其经典中间步骤见 Lamkin–Tkocz，[*Log-concavity and log-convexity of moments of averages of i.i.d. random variables*, arXiv:2001.06439v3](https://arxiv.org/pdf/2001.06439v3)，§1，第 1 页，式 (1) 后的平均恒等式。此处取独立 $\operatorname{Bernoulli}(t)$ 变量、函数 $s\mapsto\sqrt s$ 及样本数 $n$；平方根在零处连续，故 $t=0,1$ 与样本均值为零的实现均包括在内。仅使用该 Jensen 比较，不使用该文更强的矩对数凹性结论。因为 $h_4(t)>0$，(6.7) 立即给出所需比较

$$
u_b\ge u_6\qquad(b\ge6).
\tag{6.8}
$$

（三）从四顶点侧的全部前驱集合计算 $u_5,u_6$。对目标 $A$ 侧玩家，令 $r\in\{0,1,2,3\}$、$k\in\{0,\ldots,b\}$ 分别为同侧及异侧前驱数。该类集合的阶乘总权重为

$$
W_{r,k}=\binom3r\binom bk
\frac{(k+r)!(b+3-k-r)!}{(b+4)!}.
$$

令 $H_b=(b+1)(b+2)(b+3)(b+4)$，用
$\binom bk k!(b-k)!=b!$ 约去阶乘，得到包含全部端点的四式

$$
\begin{aligned}
H_bW_{0,k}&=(b+3-k)(b+2-k)(b+1-k),\\
H_bW_{1,k}&=3(k+1)(b+2-k)(b+1-k),\\
H_bW_{2,k}&=3(k+1)(k+2)(b+1-k),\\
H_bW_{3,k}&=(k+1)(k+2)(k+3).
\end{aligned}
\tag{6.9}
$$

乘以边际贡献并相加，可写为

$$
\begin{aligned}
P_b(k)&=(b+3-k)(b+2-k)(b+1-k)\\
&\quad+3(\sqrt2-1)(k+1)(b+2-k)(b+1-k)\\
&\quad+3(\sqrt3-\sqrt2)(k+1)(k+2)(b+1-k)\\
&\quad+(2-\sqrt3)(k+1)(k+2)(k+3),\\
x_b&=\frac2{H_b}\sum_{k=0}^b\sqrt k\,P_b(k),\qquad
u_b=\frac2{bH_b}\sum_{k=0}^b\sqrt{bk}\,P_b(k).
\end{aligned}
\tag{6.10}
$$

这里 $k=0$ 的边际为零，其余前驱集合没有删减。代入 $b=5,6$，分别使用 $H_5=3024$、$H_6=5040$ 并合并根式，得

$$
\begin{aligned}
u_5&=\frac{535-75\sqrt2-175\sqrt3+173\sqrt5
-5\sqrt{10}+27\sqrt{15}+8\sqrt{30}}{1260},\\
u_6&=\frac{546+18\sqrt2-164\sqrt3+106\sqrt6
-21\sqrt{10}-24\sqrt{15}+49\sqrt{30}}{1260}.
\end{aligned}
\tag{6.11}
$$

为对这两个有限和给出严格有理界，沿用定理 2.1 和定理 5.1 证明中的端点

$$
\begin{gathered}
L_2=\frac{14142}{10000},\quad U_2=\frac{14143}{10000},\quad
U_3=\frac{17321}{10000},\quad L_5=\frac{22360}{10000},\\
L_6=\frac{24494}{10000},\qquad L_{15}=\frac{38729}{10000}.
\end{gathered}
$$

它们各自满足 $L_d<\sqrt d$ 或 $\sqrt d<U_d$。另取

$$
U_{10}=\frac{31623}{10000},\qquad
U_{15}=\frac{38730}{10000},\qquad
L_{30}=\frac{54772}{10000}.
$$

正性及下列整数平方比较给出新增的三个严格端点：

$$
\begin{aligned}
31623^2&=1000014129>1000000000,\\
38730^2&=1500012900>1500000000,\\
54772^2&=2999971984<3000000000.
\end{aligned}
$$

在 (6.11) 中，正系数的根式代入下端点，负系数的根式代入上端点，得到

$$
\begin{aligned}
u_5
&>\frac{535-75U_2-175U_3+173L_5-5U_{10}
+27L_{15}+8L_{30}}{1260}\\
&=\frac{76811}{150000}
=\frac{51}{100}+\frac{311}{150000}>\frac{51}{100},\\
u_6
&>\frac{546+18L_2-164U_3+106L_6-21U_{10}
-24U_{15}+49L_{30}}{1260}\\
&=\frac{6560501}{12600000}
=\frac{13}{25}+\frac{8501}{12600000}>\frac{13}{25}.
\end{aligned}
\tag{6.12}
$$

（四）现验证 (6.3) 的实际联盟。对 $b\ge5$，

$$
\frac{3b}{4}<j_b\le\frac{3b}{4}+1\le b.
$$

因此三名同侧玩家与 $j_b$ 名异侧玩家均可取得。记

$$
r_b=\sqrt{\frac{3b}{4j_b}}\in(0,1).
$$

$b=5$ 时 $j_5=4$，所以 $r_5=\sqrt{15}/4$。由
$196^2=38416<39015=15\cdot51^2$，有 $\sqrt{15}>196/51$，故 (6.12) 给出

$$
\frac1{1+r_5}=\frac4{4+\sqrt{15}}<\frac{51}{100}<u_5.
\tag{6.13}
$$

$b=6,7$ 时分别有 $j_6=5\le7\cdot6/8$、$j_7=6\le7\cdot7/8$；$b\ge8$ 时则有
$j_b\le3b/4+1\le7b/8$。故所有 $b\ge6$ 均满足 $r_b\ge\sqrt{6/7}$。又因
$6\cdot169=1014>1008=7\cdot144$，有 $\sqrt{6/7}>12/13$。结合 (6.8)、(6.12)，

$$
\frac1{1+r_b}\le\frac1{1+\sqrt{6/7}}
<\frac{13}{25}<u_6\le u_b\qquad(b\ge6).
\tag{6.14}
$$

式 (6.13)–(6.14) 覆盖全部整数 $b\ge5$。因 $u_b>0$，所得
$u_b>1/(1+r_b)$ 等价于 $r_b>\tau_b$。对于计数 $(i,j)=(3,j_b)$，取 (2.4) 的负数即得精确恒等式

$$
\Delta(C_b;\phi)
=4\sqrt b\,\frac{j_b}{b}\,u_b(1-r_b)(r_b-\tau_b)>0.
\tag{6.15}
$$

各因子均严格为正，且任意具有该计数的联盟都具有同一赤字。全部联盟构成有限非空集合，所以定义 4.1 的最大值取得，并满足
$D_{4,b}\ge\Delta(C_b;\phi)>0$。结合（一）的 $D_{4,4}=0$，完成 (6.1) 的两个方向。∎

本定理确定定义 5.2 中的 $Z_4=\{4\}$。对每个整数 $a\ge5$，后续有限分类仍是确定
$Z_a\subseteq\{b\in\mathbb Z:a\le b\le B_a\}$ 的全部成员，其中 $B_a$ 沿用定义 5.2、有限上界沿用定理 3.1。对 $a=4$、$b\ge5$，(6.15) 只给出严格阻塞联盟；正最大值 $D_{4,b}$ 的精确值及其全部最大联盟未由本定理确定，亦不推出 $D_{4,b}$ 关于 $b$ 的单调性。

## 追加锚（本行以下为增补区）

## 7. 两侧规模同时变化时的平衡核分类

**定义 7.1（归一化侧份额与二项式多项式）。** 对整数 $b\ge a\ge5$，取不交的有限标号集 $A,B$，满足 $|A|=a$、$|B|=b$，令 $G=K_{a,b}$ 恰含全部 $A$–$B$ 边。沿用定义 1.1–1.3 与定义 4.1：若 $C\subseteq A\sqcup B$、$i=|C\cap A|$、$j=|C\cap B|$，则

$$
\begin{aligned}
w(C)&=\mathcal E(G[C])=2\sqrt{ij},\qquad n=a+b,\\
\phi_v&=\sum_{S\subseteq(A\sqcup B)\setminus\{v\}}
\frac{|S|!(n-|S|-1)!}{n!}\bigl(w(S\cup\{v\})-w(S)\bigr),\\
\Delta(C;\phi)&=w(C)-\sum_{v\in C}\phi_v,\qquad
D_{a,b}=\max_{C\subseteq A\sqcup B}\Delta(C;\phi).
\end{aligned}
\tag{7.1}
$$

其中能量是邻接特征值绝对值之和。最大值取遍所有实际联盟，保留赤字的符号。由 (2.1)–(2.3)，同侧玩家分别取得 $x_{a,b}$、$y_{a,b}$，且

$$
ax_{a,b}+by_{a,b}=2\sqrt{ab},\qquad
U_{a,b}=\frac{ax_{a,b}}{2\sqrt{ab}},\qquad
H(a,b)=U_{a,b}-\frac12.
\tag{7.2}
$$

对任意正整数 $m$ 与 $0\le t\le1$，记

$$
\begin{aligned}
\mu_m(t)&=\sum_{k=0}^m\binom mk t^k(1-t)^{m-k}\sqrt{k/m},\\
d_r&=\sqrt{r+1}-\sqrt r\quad(r\ge0).
\end{aligned}
\tag{7.3}
$$

式 (7.1) 的普通能量、阶乘分配和核约定对应 Arizmendi–Arizmendi，[*The graph energy game*, arXiv:2012.14114v2](https://arxiv.org/pdf/2012.14114v2)，§2.2、§2.4、Definition 3.1。此处的参数对应为该文的玩家集 $V=A\sqcup B$、总人数 $n=a+b$、诱导联盟 $G[C]$ 及其普通能量；同一文献 Theorem 3.6 的 vertex-energy 分配与 Proposition 4.13 的 $2$-energy 博弈不用于定义 $\phi$。式 (7.3) 是 (3.3)、(3.6) 中 $f_m/\sqrt m$ 的同一个有限多项式。

**引理 7.2（一个有理多项式的积分界）。** 置

$$
\begin{aligned}
P(z)&=1+\frac{82}{125}z+\frac{279}{625}z^2
+\frac{624}{3125}z^3+\frac{138}{3125}z^4,\\
F(u)&=\frac{u^{-1/2}}{(1+u)^2}P\!\left(\frac1{1+u}\right)
\quad(u\ge1).
\end{aligned}
\tag{7.4}
$$

则对每个实数 $T>1$，

$$
\int_1^T F(u)\,du>
\frac{75}{208}\left(1-\frac1T\right).
\tag{7.5}
$$

**证明。** 令 $c=75/208$、$R(u)=u^2F(u)$、$z=(1+u)^{-1}$。因 $u\ge1$，有 $0<z\le1/2$。直接求导表明 $R'(u)$ 与下列多项式同号：

$$
\begin{aligned}
Q(z)&=(4z-1)P(z)-2z(1-z)P'(z)\\
&=-1+\frac{254}{125}z+\frac{213}{125}z^2
+\frac{6792}{3125}z^3+\frac{4998}{3125}z^4
+\frac{1656}{3125}z^5.
\end{aligned}
\tag{7.6}
$$

$Q$ 在 $[0,1/2]$ 上严格递增，$Q(0)=-1$ 而 $Q(1/2)=4151/5000>0$。因此 $R$ 在 $[1,\infty)$ 上先严格递增、再严格递减，且趋于零。又有

$$
R(1)=\frac{36683}{100000},\qquad
R(1)-c=\frac{8129}{1300000}>0.
\tag{7.7}
$$

所以 $R-c$ 在 $[1,\infty)$ 上恰有一个零点，在此点前为正、之后为负。

现计算总积分。对整数 $m\ge2$，令

$$
I_m=\int_1^\infty\frac{dy}{(1+y^2)^m}.
$$

分部积分给出

$$
I_m=\frac{2m-3}{2m-2}I_{m-1}
-\frac1{(2m-2)2^{m-1}},\qquad I_1=\frac\pi4.
$$

代换 $u=y^2$，再逐项使用此递推，得到

$$
\begin{aligned}
\int_1^\infty\frac{u^{-1/2}}{(1+u)^2}\,du
&=\frac\pi4-\frac12,\\
\int_1^\infty\frac{u^{-1/2}}{(1+u)^3}\,du
&=\frac{3\pi}{16}-\frac12,\\
\int_1^\infty\frac{u^{-1/2}}{(1+u)^4}\,du
&=\frac{5\pi}{32}-\frac{11}{24},\\
\int_1^\infty\frac{u^{-1/2}}{(1+u)^5}\,du
&=\frac{35\pi}{256}-\frac5{12},\\
\int_1^\infty\frac{u^{-1/2}}{(1+u)^6}\,du
&=\frac{63\pi}{512}-\frac{61}{160}.
\end{aligned}
$$

故

$$
\int_1^\infty F(u)\,du
=\frac{380387}{800000}\pi-\frac{283159}{250000}.
\tag{7.8}
$$

为完全给出所需的严格常数比较，对 $x>0$，恒等式

$$
\frac1{1+x^2}=1-x^2+x^4-x^6+\frac{x^8}{1+x^2}
$$

积分后给出
$\arctan x>x-x^3/3+x^5/5-x^7/7$。由于
$\arctan(1/2)+\arctan(1/3)=\pi/4$，有

$$
\pi>4\sum_{k=0}^3\frac{(-1)^k}{2k+1}
\left(2^{-(2k+1)}+3^{-(2k+1)}\right)
=\frac{1538665}{489888}
=\frac{223}{71}+\frac{191}{34782048}
>\frac{223}{71}.
$$

式 (7.8) 因而满足

$$
\int_1^\infty F(u)\,du-c
>\frac{380387}{800000}\frac{223}{71}
-\frac{283159}{250000}-\frac{75}{208}
=\frac{767453}{3692000000}>0.
\tag{7.9}
$$

最后令

$$
J(T)=\int_1^T\frac{R(u)-c}{u^2}\,du.
$$

由 (7.7) 及 $R-c$ 的唯一变号，$J$ 从零开始先严格增加、再严格减少；由 (7.9)，其无穷远极限仍严格为正。因此对每个 $T>1$ 都有 $J(T)>0$，这正是 (7.5)。∎

**引理 7.3（二项式积分的联合定量差）。** 对所有整数 $b>a\ge5$，式 (7.3) 满足

$$
\int_0^1\mu_a'(t)\bigl(\mu_b(t)-\mu_a(t)\bigr)\,dt
>\frac5{32}\left(\frac1a-\frac1b\right).
\tag{7.10}
$$

**证明。** 对任意正整数 $n$ 和 $t\in[0,1]$，取 $n+1$ 个独立 $\operatorname{Bernoulli}(t)$ 变量 $X_1,\ldots,X_{n+1}$，记

$$
K=\sum_{\ell=1}^{n+1}X_\ell,\qquad
Y_\ell=\frac{K-X_\ell}{n}.
$$

同一实现中 $\frac1{n+1}\sum_\ell Y_\ell=K/(n+1)$。这与定理 5.1 证明（二）的删去一个样本恒等式相同；经典中间步骤的出处为 Lamkin–Tkocz，[*Log-concavity and log-convexity of moments of averages of i.i.d. random variables*, arXiv:2001.06439v3](https://arxiv.org/pdf/2001.06439v3)，§1，第 1 页，式 (1) 后的平均恒等式。此处以非负 Bernoulli 样本和平方根的有限 Jensen 不等式使用该恒等式。

条件于 $K=k$，在 $n+1$ 个删去一个变量的均值中，有 $n+1-k$ 个等于 $k/n$，有 $k$ 个等于 $(k-1)/n$。因此相应的 Jensen 差

$$
q_{n,k}=\sqrt{\frac{k}{n+1}}
-\frac{n+1-k}{n+1}\sqrt{\frac{k}{n}}
-\frac{k}{n+1}\sqrt{\frac{k-1}{n}}
\quad(1\le k\le n+1)
$$

非负，且 $k=0$ 时差为零。取期望便是
$\mu_{n+1}(t)-\mu_n(t)$。特别在 $k=1$ 时，

$$
q_{n,1}=\frac{\sqrt{n+1}-\sqrt n}{n+1}.
$$

只保留这一非负项及其概率 $(n+1)t(1-t)^n$，即得

$$
\mu_{n+1}(t)-\mu_n(t)
\ge(\sqrt{n+1}-\sqrt n)t(1-t)^n.
\tag{7.11}
$$

这里其余条件差均非负，不要求删去样本之间独立；$t=0,1$ 也包含在式中。式 (7.11) 是从上述 Jensen 分解取得的定量项，而非仅用样本量单调性。

由 (3.6) 的有限和导数恒等式，

$$
\mu_a'(t)=\sqrt a\sum_{r=0}^{a-1}
\binom{a-1}{r}d_r t^r(1-t)^{a-1-r}.
\tag{7.12}
$$

每一项非负。对 $n\ge a\ge5$，将 (7.11) 乘以 (7.12)，保留 $r=0,1,2,3,4$ 的项并积分。有限次分部积分给出

$$
\int_0^1t^{r+1}(1-t)^{a+n-r-1}\,dt
=\frac{(r+1)!(a+n-r-1)!}{(a+n+1)!}.
$$

记 $(a-1)_{\underline r}=\prod_{j=1}^r(a-j)$，空乘积为 $1$，得到

$$
\begin{aligned}
L_{a,n}&:=\int_0^1\mu_a'(t)
\bigl(\mu_{n+1}(t)-\mu_n(t)\bigr)\,dt\\
&\ge\frac{\sqrt a}{\sqrt{n+1}+\sqrt n}
\sum_{r=0}^4
\frac{(r+1)d_r(a-1)_{\underline r}}
{(a+n+1)(a+n)\prod_{j=1}^r(a+n-j)}.
\end{aligned}
\tag{7.13}
$$

下面所有比较都在 $n\ge a\ge5$ 的同一范围内。令 $s=a+n$、$z=a/s$。因为 $s\ge2a$，

$$
\begin{aligned}
\sqrt{n+1}+\sqrt n
&\le\sqrt n\bigl(1+\sqrt{1+1/a}\bigr),\\
(s+1)s\prod_{j=1}^r(s-j)
&\le\left(1+\frac1{2a}\right)s^{r+2},\\
\frac{(a-1)_{\underline r}}{a^r}
&=\prod_{j=1}^r\left(1-\frac ja\right)
\ge\prod_{j=1}^r\left(1-\frac j5\right).
\end{aligned}
\tag{7.14}
$$

此外

$$
\frac1{(1+\sqrt{1+1/a})(1+1/(2a))}
\ge\frac{10}{11(1+\sqrt{6/5})}>
\frac{13}{30}.
\tag{7.15}
$$

最后一个严格比较等价于 $\sqrt{6/5}<157/143$，由正数平方比较
$6\cdot143^2=122694<123245=5\cdot157^2$ 得到。

对所保留的四个正指标，使用
$\sqrt2<10/7$、$\sqrt3<7/4$、$\sqrt5<9/4$，以及
$d_r=(\sqrt{r+1}+\sqrt r)^{-1}$，可得

$$
\begin{aligned}
d_1&>\frac7{17}>\frac{41}{100},&
d_2&>\frac{28}{89}>\frac{31}{100},\\
d_3&>\frac4{15}>\frac{26}{100},&
d_4&>\frac4{17}>\frac{23}{100}.
\end{aligned}
\tag{7.16}
$$

三个根式上界的平方比较分别为 $98<100$、$48<49$、$80<81$。将 (7.14)–(7.16) 代入 (7.13)，$r=0$ 的系数为 $1$，其余四个系数的有理下界依次为

$$
\begin{aligned}
2\frac{41}{100}\frac45&=\frac{82}{125},&
3\frac{31}{100}\frac{4\cdot3}{5^2}&=\frac{279}{625},\\
4\frac{26}{100}\frac{4\cdot3\cdot2}{5^3}&=\frac{624}{3125},&
5\frac{23}{100}\frac{4\cdot3\cdot2\cdot1}{5^4}&=\frac{138}{3125}.
\end{aligned}
$$

它们正是引理 7.2 的 $P$。于是

$$
L_{a,n}>\frac{13}{30}
\frac{\sqrt a}{\sqrt n(a+n)^2}
P\!\left(\frac a{a+n}\right).
\tag{7.17}
$$

对固定 $a$，函数

$$
x\longmapsto\frac{\sqrt a}{\sqrt x(a+x)^2}
P\!\left(\frac a{a+x}\right)
$$

在 $x\ge a$ 上为正且严格递减，因为每个单项式都是正常数乘以
$x^{-1/2}(a+x)^{-r-2}$。有限求和望远镜及左端点积分比较给出

$$
\begin{aligned}
\int_0^1\mu_a'(t)(\mu_b(t)-\mu_a(t))\,dt
&=\sum_{n=a}^{b-1}L_{a,n}\\
&>\frac{13}{30}\int_a^b
\frac{\sqrt a}{\sqrt x(a+x)^2}
P\!\left(\frac a{a+x}\right)\,dx\\
&=\frac{13}{30a}\int_1^{b/a}F(u)\,du\\
&>\frac{13}{30a}\frac{75}{208}
\left(1-\frac ab\right)
=\frac5{32}\left(\frac1a-\frac1b\right).
\end{aligned}
$$

其中最后一步用引理 7.2，且 $b/a>1$。全部求和有限；没有对 $a$ 或 $b$ 取极限，也没有更换两者的量词。∎

**定理 7.4（所有 $b\ge a\ge5$ 的唯一零赤字情形）。** 对定义 7.1 的每个整数对 $b\ge a\ge5$ 及每对相应的不交有限标号集 $A,B$，有

$$
D_{a,b}=0\quad\Longleftrightarrow\quad a=b.
\tag{7.18}
$$

更具体地，当 $b>a\ge5$ 时，实际稀缺侧总 Shapley 份额的偏移满足

$$
H(a,b)>\frac{5(b-a)}{32ab},
\tag{7.19}
$$

且对每一对玩家 $v\in A$、$w\in B$，实际联盟
$C=(A\sqcup B)\setminus\{v,w\}$ 都严格阻塞 $\phi$。当 $a=b$ 时，每个联盟都满足

$$
\Delta(C;\phi)=-(\sqrt i-\sqrt j)^2,
\qquad 0\le i,j\le a,
\tag{7.20}
$$

其中包含空联盟、纯侧联盟和全体联盟。

**证明。** 首先把引理 7.3 与 (7.1) 的字面阶乘和连接。任意保持两侧的标号双射，将每个前驱集合双射地运输到同样大小的前驱集合，保留边际价值与阶乘权重。因此以下计算适用于所有所述标号集。

复用 (2.1)–(2.3) 的谱计算、排列平均、同侧对称性与效率。给全部玩家赋独立均匀优先级，条件于目标 $A$ 侧玩家的优先级为 $t$，其余同侧前驱数 $R$ 与异侧前驱数 $K$ 条件独立，分别为

$$
R\sim\operatorname{Bin}(a-1,t),\qquad
K\sim\operatorname{Bin}(b,t).
$$

边际价值是 $2\sqrt K\,d_R$。这里 $R$ 的范围为 $0,\ldots,a-1$，$K$ 的范围为 $0,\ldots,b$，均包括零端点。固定一个大小为 $k$ 的前驱集合，其优先级概率为

$$
\int_0^1t^k(1-t)^{a+b-1-k}\,dt
=\frac{k!(a+b-1-k)!}{(a+b)!}.
$$

因此优先级积分就是 (7.1) 的全部阶乘和，与 (3.3)、(3.6) 的参数对应为样本量 $a-1$ 与 $b$。用 (7.12) 得

$$
x_{a,b}=2\sqrt{\frac ba}\int_0^1\mu_a'(t)\mu_b(t)\,dt,
\qquad
U_{a,b}=\int_0^1\mu_a'(t)\mu_b(t)\,dt.
\tag{7.21}
$$

因 $\mu_a(0)=0$、$\mu_a(1)=1$，

$$
\int_0^1\mu_a'(t)\mu_a(t)\,dt=\frac12,
\qquad
H(a,b)=\int_0^1\mu_a'(t)(\mu_b(t)-\mu_a(t))\,dt.
\tag{7.22}
$$

当 $b>a\ge5$ 时，引理 7.3 直接给出 (7.19)。这一步将前述谱与阶乘公式、经典删去一个样本的 Jensen 恒等式，同引理 7.2–7.3 的定量推导组合起来；所需的联合下界不是固定 $a$ 的极限结论。

现令

$$
z=1-\frac1a,\qquad s=1-\frac1b,\qquad
\delta=s-z=\frac{b-a}{ab}>0.
$$

任取 $v\in A$、$w\in B$，其补联盟的计数为 $(a-1,b-1)$。由 (4.9) 的同一联盟恒等式和 $U_{a,b}=1/2+H(a,b)$，

$$
\begin{aligned}
\frac{\Delta(C;\phi)}{2\sqrt{ab}}
&=\sqrt{zs}-\left(\frac12+H(a,b)\right)z
-\left(\frac12-H(a,b)\right)s\\
&=\delta H(a,b)-\frac12(\sqrt s-\sqrt z)^2\\
&=\delta\left(H(a,b)
-\frac{\delta}{2(\sqrt s+\sqrt z)^2}\right).
\end{aligned}
\tag{7.23}
$$

因为 $s>z\ge4/5$，有 $(\sqrt s+\sqrt z)^2>16/5$，所以

$$
\frac{\delta}{2(\sqrt s+\sqrt z)^2}
<\frac5{32}\delta<H(a,b).
$$

式 (7.23) 严格为正。计数 $(a-1,b-1)$ 对所有指定标签都合法；故每个这样的联盟严格阻塞，并有 $D_{a,b}>0$。

当 $b=a$ 时，(7.21) 给出 $U_{a,a}=1/2$，由 (7.2) 及效率得到 $x_{a,a}=y_{a,a}=1$。对任一联盟，(7.1) 遂给出

$$
\Delta(C;\phi)=2\sqrt{ij}-i-j=-(\sqrt i-\sqrt j)^2\le0.
$$

这在 $i=0$ 或 $j=0$ 时仍成立；空联盟与全体联盟均取得零。因此所有联盟上的有符号最大值恰为 $D_{a,a}=0$。结合非平衡情形完成 (7.18)。

本定理确定定义 5.2 的全部 $Z_a=\{a\}$（$a\ge5$）。其量词不改变定理 2.1 中 $a=2$ 的额外零赤字情形，也不改变定理 3.1 的星图边界；定理 5.1 与定理 6.1 分别处理 $a=3,4$。式 (7.23) 仅断言所述联盟严格阻塞，未确定 $b>a$ 时 $D_{a,b}$ 的精确值或全部最大联盟。∎

## 追加锚（本行以下为增补区）
