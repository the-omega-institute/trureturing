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
