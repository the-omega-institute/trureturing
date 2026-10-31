# 共同活动度 hard-core 占据的高活动度稳定性与精确缺陷分解

## 1. Gibbs 律与度序列目标

**定义 1.1（图与共同活动度）。** 设 $G=(V,E)$ 为任意有限简单图，$n=|V|$，$N(v)=\{u:\{u,v\}\in E\}$，$N[v]=N(v)\cup\{v\}$，$d_v=|N(v)|$。独立集族记为 $\mathcal I(G)$，包括空集；$\alpha(G)=\max_{J\in\mathcal I(G)}|J|$。空图取 $\alpha(G)=0$、最大度为 $0$。对每一个共同参数 $\lambda>0$，定义

$$
Z_G(\lambda)=\sum_{J\in\mathcal I(G)}\lambda^{|J|},\qquad
\mathbb P_{G,\lambda}(I=J)=\frac{\lambda^{|J|}}{Z_G(\lambda)},\qquad
M_G(\lambda)=\mathbb E_{G,\lambda}|I|.
$$

下文全部占据概率与期望均取此实际 Gibbs 律，图的不同顶点使用同一个 $\lambda$。对空图，$Z_G=1$、$M_G=0$；所有空和均取 $0$。记 $\log$ 为自然对数。

**定义 1.2（度序列缺陷）。** 定义

$$
A_v=1+(d_v+1)\lambda,\qquad
B_G(\lambda)=\sum_{v\in V}\frac{\lambda}{A_v},\qquad
D_G(\lambda)=M_G(\lambda)-B_G(\lambda).
$$

Davies–Kang 的共同活动度目标是对每个有限简单图和每个 $\lambda>0$ 均有 $D_G(\lambda)\ge0$，见 [Davies–Kang，arXiv:2501.03379v2，§8，Conjecture A](https://arxiv.org/html/2501.03379v2#S8)。该目标的已知小活动度范围包括：若最大度为 $\Delta\ge1$，则 $0<\lambda\le3/(\Delta+1)^2$，见 [Davies–Sandhu–Tan，arXiv:2505.13396v2，Theorem 1.3](https://arxiv.org/html/2505.13396v2)；以及 $0<\lambda<1/\Delta$，后者是 [Davies–Sandhu–Seo–Tan，arXiv:2605.05149v1，Theorem 1](https://arxiv.org/html/2605.05149v1) 的共同活动度特例。这些文献结果仅作为目标的已知范围。

## 2. 不依赖图阶的高活动度范围

**定义 2.1（完全分量的剥离）。** 给定整数 $\Delta\ge2$，令

$$
T_\Delta=(\Delta+1)\max\{\Delta^2,2\Delta+1\},\qquad
\varepsilon_\Delta=T_\Delta^{-1}.
$$

对最大度至多 $\Delta$ 的图 $G$，令 $\mathcal K(G)$ 为其所有完全连通分量的集合，包括孤立点 $K_1$。令 $H$ 为删去这些分量后得到的诱导子图，$m=|V(H)|$，并置

$$
C(H)=\sum_{v\in V(H)}\frac1{d_H(v)+1}.
$$

$H$ 没有完全连通分量，而且 $d_H(v)=d_G(v)$ 对每个 $v\in V(H)$ 成立。

**定理 2.2（稳定性增益与高活动度占据）。** 对定义 2.1 中的每个 $G,\Delta,H$，有

$$
\alpha(H)\ge C(H)+m\varepsilon_\Delta.
\tag{2.2a}
$$

在所有没有完全连通分量、最大度至多 $\Delta$ 的有限简单图上，$\varepsilon_\Delta$ 是使（2.2a）统一成立的最大系数。对每个 $\lambda>1$，还有

$$
M_G(\lambda)\ge
\sum_{K_k\in\mathcal K(G)}\frac{k\lambda}{1+k\lambda}
+C(H)+m\varepsilon_\Delta-\frac{m\log2}{\log\lambda}.
\tag{2.2b}
$$

因此，对每个 $\lambda\ge2^{T_\Delta}$，

$$
M_G(\lambda)\ge B_G(\lambda).
\tag{2.2c}
$$

在（2.2c）的范围内，等号成立当且仅当 $G$ 的每个连通分量均完全。另对最大度至多 $1$ 的任意有限简单图，每个 $\lambda>0$ 均有 $M_G(\lambda)=B_G(\lambda)$。阈值 $2^{T_\Delta}$ 是充分条件；（2.2a）的最优系数不蕴含此活动度阈值最优。

**证明 2.2。** 先证明（2.2a）。采用 [Kelly–Postle，*Improving the Caro-Wei bound and applications to Turán stability*，arXiv:2407.17363v1，Theorem 1.4](https://arxiv.org/html/2407.17363v1) 作为中间输入：若图 $F$ 上的函数 $f$ 满足

$$
f(v)\le\frac1{d_F(v)+1/2},\qquad
\sum_{v\in K}f(v)\le1\quad\text{对每个团 }K,
$$

则 $\alpha(F)\ge\sum_v f(v)$。在 $H$ 上取

$$
f(v)=\frac1{d_H(v)+1}+\varepsilon_\Delta.
$$

对 $d=d_H(v)\le\Delta$，

$$
\frac1{d+1/2}-\frac1{d+1}
=\frac1{(2d+1)(d+1)}
\ge\frac1{(2\Delta+1)(\Delta+1)}
\ge\varepsilon_\Delta.
$$

故满足逐点条件。若 $K$ 是 $H$ 的非空团，令 $k=|K|$。因为 $H$ 没有完全分量，$K$ 至少有一个顶点在 $K$ 外有邻点；否则 $K$ 本身就是一个完全连通分量。该顶点的度至少为 $k$，其余 $k-1$ 个顶点的度至少为 $k-1$。同时 $k\le\Delta$：一个 $\Delta+1$ 阶团的每个顶点都已达到最大度，必自成完全分量。因此

$$
\sum_{v\in K}\frac1{d_H(v)+1}
\le\frac{k-1}{k}+\frac1{k+1}
=1-\frac1{k(k+1)},
$$

而

$$
k\varepsilon_\Delta
\le\frac{k}{\Delta^2(\Delta+1)}
\le\frac1{k(k+1)}.
$$

最后一步等价于 $k^2(k+1)\le\Delta^2(\Delta+1)$。空团的条件自动成立，故 Kelly–Postle 的全部假设满足，得到（2.2a）。若 $H$ 为空，所有条件与结论均按空和成立。

系数的上界由两个图给出。$\Delta=2$ 时，$H=C_5$ 满足 $\alpha(H)=2$、$C(H)=5/3$、$m=5$，所以

$$
\frac{\alpha(H)-C(H)}m=\frac1{15}=\varepsilon_2.
$$

$\Delta\ge3$ 时，取两个互不相交的 $K_\Delta$，分别选一个顶点并在这两个顶点之间加一条边。所得 $H$ 连通且不完全，最大度为 $\Delta$；任何独立集在每个原团中至多取一个顶点，而在两个团中各取一个非桥端点给出大小为 $2$ 的独立集。因此

$$
\alpha(H)=2,\qquad m=2\Delta,\qquad
C(H)=2\left(\frac{\Delta-1}{\Delta}+\frac1{\Delta+1}\right),
$$

从而

$$
\frac{\alpha(H)-C(H)}m
=\frac1{\Delta^2(\Delta+1)}=\varepsilon_\Delta,
$$

这里用了 $\Delta^2\ge2\Delta+1$。结合下界，系数确为最大值。

再转回实际 Gibbs 律。令其在 $H$ 上的 Shannon 熵为

$$
\mathsf H_H=-\sum_{J\in\mathcal I(H)}
\mathbb P_{H,\lambda}(J)\log\mathbb P_{H,\lambda}(J).
$$

展开定义得到 Gibbs 熵恒等式

$$
\log Z_H=M_H\log\lambda+\mathsf H_H;
$$

这也是 [Davies，*Random independent sets and local sparsity*，arXiv:2609.04654v1，引言（1.1）](https://arxiv.org/html/2609.04654v1) 在 $\mu=\pi_{H,\lambda}$ 时的情形。熵满足

$$
\mathsf H_H\le\log|\mathcal I(H)|\le m\log2.
$$

第一步可直接由对数的凹性推出：所有独立集概率均正，故 $\mathbb E\log(1/\mathbb P(I))\le\log\mathbb E(1/\mathbb P(I))=\log|\mathcal I(H)|$。最大独立集的一项权重给出 $Z_H\ge\lambda^{\alpha(H)}$。因为 $\log\lambda>0$，上述关系与（2.2a）合并为

$$
M_H\ge\alpha(H)-\frac{m\log2}{\log\lambda}
\ge C(H)+m\varepsilon_\Delta-\frac{m\log2}{\log\lambda}.
$$

不同连通分量的独立集构成笛卡尔积，权重相乘，故分区函数相乘、$M_G$ 按分量相加。一个完全分量 $K_k$ 的分区函数为 $1+k\lambda$，占据期望为 $k\lambda/(1+k\lambda)$；这证明（2.2b）。

若 $\lambda\ge2^{T_\Delta}$，则 $\log2/\log\lambda\le\varepsilon_\Delta$，于是 $M_H\ge C(H)$。对每个 $v\in V(H)$ 和有限的 $\lambda>0$，

$$
\frac{\lambda}{1+(d_H(v)+1)\lambda}<\frac1{d_H(v)+1}.
$$

因此 $m>0$ 时 $M_G>B_G$，而 $m=0$ 时各完全分量给出精确等号。空图亦为等号。最大度至多 $1$ 的图只由 $K_1$ 和 $K_2$ 构成，故全部正活动度下均为等号。$\square$

## 3. 精确缺陷与诱导三点路

**定义 3.1（邻域超额与边余项）。** 对定义 1.1 的每个 $G,\lambda$，令

$$
\beta=1+\frac1\lambda,\qquad
q_v=\frac1{\beta+d_v}=\frac\lambda{A_v},\qquad
p_v=\mathbb P_{G,\lambda}(v\in I),
$$

$$
Y_v=|I\cap N(v)|,\qquad
s_v=\mathbb E_{G,\lambda}(Y_v-1)_+,
\qquad (t)_+=\max\{t,0\},
$$

以及

$$
R_G(\lambda)=\sum_{\{u,v\}\in E}(q_u-q_v)(p_u-p_v).
$$

这里每条无序边只计一次；交换其两个端点不改变被加项。另令

$$
w_v=\bigl|\{\{a,b\}\subseteq N(v):a\ne b,\ \{a,b\}\notin E\}\bigr|,
\qquad W(G)=\sum_{v\in V}w_v.
$$

即 $W(G)$ 是无序诱导三点路的数目：以 $v$ 为中心，两个端点 $\{a,b\}$ 无序，每一条诱导三点路只在其唯一中心计一次。

**定理 3.2（实际 Gibbs 缺陷的精确分解）。** 对每个有限简单图 $G$ 和每个 $\lambda>0$，

$$
D_G(\lambda)=\sum_{v\in V}q_v s_v+R_G(\lambda).
\tag{3.2}
$$

此外，$s_v=0$ 当且仅当 $N(v)$ 是团，允许空团与单点团；而 $D_G$、$R_G$ 和 $W(G)$ 均按连通分量相加。

**证明 3.2。** 条件于 $I\cap N(v)=\varnothing$，加入或删去 $v$ 的两类配置权重之比为 $\lambda$，故

$$
p_v=\frac{\lambda}{1+\lambda}\mathbb P(Y_v=0),
\qquad \mathbb P(Y_v=0)=\beta p_v.
$$

这个局部占据关系是 [Davies–Sandhu–Seo–Tan，arXiv:2605.05149v1，Proposition 5 及其证明](https://arxiv.org/html/2605.05149v1) 的共同活动度情形。对非负整数 $Y_v$，逐点恒等式

$$
Y_v=\mathbf1_{\{Y_v\ge1\}}+(Y_v-1)_+
$$

给出保留超额项的精确平衡

$$
\beta p_v+\sum_{u\in N(v)}p_u=1+s_v.
\tag{3.2a}
$$

将（3.2a）乘以 $q_v$ 并对 $v$ 求和，利用 $\beta q_v=1-d_vq_v$，得到

$$
\begin{aligned}
\sum_v q_vs_v
&=\sum_vp_v-\sum_vq_v-\sum_vd_vq_vp_v
  +\sum_{\{u,v\}\in E}(q_up_v+q_vp_u)\\
&=D_G-\sum_{\{u,v\}\in E}(q_u-q_v)(p_u-p_v).
\end{aligned}
$$

这证明（3.2）。若 $N(v)$ 是团，独立性保证 $Y_v\le1$，于是 $s_v=0$。若 $N(v)$ 有不相邻的两个点 $a,b$，配置 $I=\{a,b\}$ 的 Gibbs 概率严格为正，故 $\mathbb P(Y_v\ge2)>0$，$s_v>0$。

连通分量的乘积律使各点的边缘律等于其所属分量上的 Gibbs 边缘律，且顶点度不变。三个量的加性随即由其定义得到，空图亦成立。与只保留（3.2a）左侧大于等于 $1$ 的平衡不等式相比，（3.2）同时保留非负的邻域超额和可能带符号的边余项；两项都来自同一个实际 Gibbs 律。$\square$

**定理 3.3（非负边余项下的定量缺陷）。** 设 $\Delta\ge2$ 为整数，$G$ 为最大度至多 $\Delta$ 的任意有限简单图。对任意 $\lambda>0$，若 $R_G(\lambda)\ge0$，则

$$
D_G(\lambda)\ge
\frac{2W(G)\lambda^3}
{\Delta\bigl(1+(\Delta+1)\lambda\bigr)(1+\lambda)^{2\Delta+1}}.
\tag{3.3}
$$

在此假设下，$D_G(\lambda)=0$ 当且仅当 $G$ 的每个连通分量均完全。

**证明 3.3。** 对 $0\le y\le d_v\le\Delta$ 的整数 $y$，

$$
(y-1)_+\ge\frac2\Delta\binom y2.
$$

因为 $y=0,1$ 时两边为 $0$，而 $y\ge2$ 时此式等价于 $y\le\Delta$。因此

$$
s_v\ge\frac2\Delta\mathbb E\binom{Y_v}2
=\frac2\Delta\sum_{\substack{\{a,b\}\subseteq N(v)\\\{a,b\}\notin E}}
\mathbb P(a,b\in I).
\tag{3.3a}
$$

固定其中一个端点对，令 $U=N[a]\cup N[b]$，$F=G[V\setminus U]$。由于 $a,b$ 不相邻，包含两者的独立集与 $F$ 的独立集一一对应，故

$$
\mathbb P(a,b\in I)=\frac{\lambda^2Z_F}{Z_G}.
$$

对每个固定的 $J\in\mathcal I(F)$，向 $U$ 中扩展的允许配置，其权重和至多为全部子集的权重和 $(1+\lambda)^{|U|}$。逐个 $J$ 求和得

$$
Z_G\le (1+\lambda)^{|U|}Z_F.
$$

两个闭邻域都含中心 $v$，所以 $|U|\le2(\Delta+1)-1=2\Delta+1$，进而

$$
\mathbb P(a,b\in I)\ge\frac{\lambda^2}{(1+\lambda)^{2\Delta+1}}.
\tag{3.3b}
$$

（3.2）、（3.3a）、（3.3b）和 $q_v\ge\lambda/(1+(\Delta+1)\lambda)$ 给出（3.3）。

若 $W(G)>0$，右侧严格为正。若某个连通分量不完全，在其中取两个不相邻顶点间的一条最短路，该路的前三点构成诱导三点路，故 $W(G)>0$。反之，完全分量没有诱导三点路，且每个完全分量的 $D$ 为 $0$。这也包含没有顶点或最大度至多 $1$ 的边界情形。$\square$

## 4. 分裂图的全部正活动度

**定义 4.1（分裂图与逐分量条件）。** 若有限简单图的顶点集存在分拆 $V=C\sqcup S$，使 $G[C]$ 为团、$G[S]$ 为独立集，则称其为分裂图；两部分允许为空，$C,S$ 间的邻接任意。称 $G$ 满足逐分量分裂条件，是指每个连通分量均为分裂图，各分量可以各自选择分拆。此条件并不要求整个 $G$ 具有同一个分裂分拆。

**定理 4.2（分裂分量上的精确排序与占据界）。** 若 $G$ 满足逐分量分裂条件，则对每个 $\lambda>0$ 和每条边 $\{u,v\}$，

$$
(q_u-q_v)(p_u-p_v)\ge0.
\tag{4.2a}
$$

因此 $D_G(\lambda)\ge0$，等号成立当且仅当每个连通分量均完全。若另有整数 $\Delta\ge2$ 使最大度至多 $\Delta$，则（3.3）的定量界成立。

**证明 4.2。** 由分量乘积律，只需考察一个具有分拆 $C\sqcup S$ 的分量。置

$$
c=|C|,\qquad b=|S|,\qquad
r_a=|N(a)\cap S|\quad(a\in C),
$$

$$
t=\frac\lambda{1+\lambda},\qquad
h_a=(1+\lambda)^{-r_a},\qquad
F=1+\lambda\sum_{a\in C}h_a.
$$

独立集在 $C$ 中至多取一个顶点。分别按不取 $C$ 和取某个 $a\in C$ 求和，得到

$$
Z_G=(1+\lambda)^bF,\qquad
p_a=\frac{\lambda h_a}{F}\quad(a\in C).
\tag{4.2b}
$$

对 $z\in S$，不取 $C$ 时其条件占据概率为 $t$；取 $a\in C$ 时，若 $a\notin N(z)$ 则仍为 $t$，否则为 $0$。于是

$$
p_z=\frac tF\left(1+\lambda
\sum_{a\in C\setminus N(z)}h_a\right).
\tag{4.2c}
$$

这些式子也覆盖 $C=\varnothing$ 或 $S=\varnothing$。

若 $a,a'\in C$，其度分别为 $c-1+r_a,c-1+r_{a'}$。$q_a$ 与 $p_a$ 均随 $r_a$ 单调递减，所以这类边的（4.2a）成立，$r_a=r_{a'}$ 时乘积为 $0$。

若 $\{a,z\}\in E$，$a\in C,z\in S$，则 $r_a\ge1$，且

$$
d_a=c-1+r_a\ge c\ge d_z,\qquad
p_a=\frac{\lambda(1+\lambda)^{-r_a}}F
\le\frac tF\le p_z.
$$

故 $q_a\le q_z$ 且 $p_a\le p_z$，乘积仍非负。$S$ 内没有边，所有边类型已经穷尽。这证明（4.2a）并给出 $R_G\ge0$，从（3.2）得到 $D_G\ge0$。

若图含诱导三点路，其中心的 $s_v>0$，又 $q_v>0$，所以 $D_G>0$。不含诱导三点路的图只由完全分量构成，反向等号由完全分量的精确期望得到。最后在最大度有界时直接应用定理 3.3；其 $W(G)$ 仍按中心和无序端点计数。$\square$

## 5. 独立数至多二的精确有理式

**定义 5.1（非边计数与独立数条件）。** 对满足 $\alpha(G)\le2$ 的有限简单图，记

$$
m_2=\bigl|\{\{u,v\}\subseteq V:u\ne v,\ \{u,v\}\notin E\}\bigr|.
$$

$m_2$ 计无序非边，每对只计一次。另称图满足逐分量二独立数条件，是指每个非空连通分量 $J$ 均有 $\alpha(J)\le2$；这允许整个图的 $\alpha(G)>2$。下文对一个分量 $J$ 使用的 $n_J,m_{2,J},Z_J,d_{J,v},A_{J,v},w_{J,v}$ 均按该分量自身定义。

**定理 5.2（二独立数图的缺陷平方分解）。** 若 $\alpha(G)\le2$，则对每个 $\lambda>0$，

$$
Z_G=1+n\lambda+m_2\lambda^2,
$$

且有精确恒等式

$$
D_G(\lambda)=
\frac{\lambda^3}{Z_G}\sum_{v\in V}\frac{w_v}{A_v}
+\frac{\lambda^4}{Z_G}
\sum_{\{u,v\}\in E}\frac{(d_u-d_v)^2}{A_uA_v}.
\tag{5.2a}
$$

故 $D_G(\lambda)\ge0$，等号成立当且仅当 $G$ 的每个连通分量均完全。

更一般地，若 $G$ 满足逐分量二独立数条件，则

$$
\begin{aligned}
D_G(\lambda)=\sum_{J\text{ 为连通分量}}\Biggl[
&\frac{\lambda^3}{Z_J}\sum_{v\in V(J)}\frac{w_{J,v}}{A_{J,v}}\\
&+\frac{\lambda^4}{Z_J}
\sum_{\{u,v\}\in E(J)}
\frac{(d_{J,u}-d_{J,v})^2}{A_{J,u}A_{J,v}}
\Biggr]\ge0.
\end{aligned}
\tag{5.2b}
$$

此时等号仍等价于所有连通分量完全。若最大度至多某个整数 $\Delta\ge2$，则定理 3.3 的定量界亦成立。

**证明 5.2。** 在 $\alpha(G)\le2$ 的假设下，所有独立集只有大小 $0,1,2$，所以分区函数正是所述二次多项式。固定 $v$，包含 $v$ 的配置仅为 $\{v\}$ 和与其不相邻的另一顶点组成的点对，故

$$
p_v=\frac{\lambda\bigl(1+(n-1-d_v)\lambda\bigr)}{Z_G}.
$$

于是对每条边，

$$
p_u-p_v=-\frac{\lambda^2(d_u-d_v)}{Z_G},\qquad
q_u-q_v=-\frac{\lambda^2(d_u-d_v)}{A_uA_v},
$$

其乘积为（5.2a）中对应的平方项。

又因 $Y_v\le2$，$s_v=\mathbb P(Y_v=2)$。每一对不相邻的邻点 $\{a,b\}\subseteq N(v)$ 出现时，$I$ 必恰为 $\{a,b\}$，不能还有第三个点；不同点对对应的事件互斥。因此

$$
s_v=\frac{w_v\lambda^2}{Z_G},\qquad
q_vs_v=\frac{w_v\lambda^3}{Z_GA_v}.
$$

代入（3.2）即得（5.2a）。所有项均非负；若 $D_G=0$，第一项强迫全部 $w_v=0$，从而没有诱导三点路，每个连通分量均完全。反向等号仍由完全分量的精确期望得到。

在逐分量条件下，分别对每个分量使用（5.2a），再用加性，即得（5.2b）。此时一般不能把全图的分区函数替换为一个二次式；（5.2b）使用的是各分量不同的 $Z_J$。每条边的乘积在其分量内非负，故全图的 $R_G\ge0$，可应用定理 3.3。

空图的（5.2a）两边为 $0$，$Z_G=1$；单点图以及 $K_2$ 均有 $w_v=0$，边的度差也为 $0$，与全部正活动度下的等号一致。$\square$

## 6. 负边余项与仍待证的补偿

**定理 6.1（较高度端点可有较大占据率）。** 设 $G$ 的顶点为六个互异的点 $u,v,a,b,x,y$，边集恰为

$$
E=\{\{u,v\},\{u,a\},\{u,b\},\{a,b\},
\{v,x\},\{a,y\},\{b,y\}\}.
$$

对每个 $\lambda>0$，

$$
Z_G=1+6\lambda+8\lambda^2+\lambda^3,\qquad
p_u-p_v=\frac{\lambda^2(\lambda-1)}{Z_G}.
\tag{6.1a}
$$

特别地，当 $\lambda>1$ 时，$d_u=3>d_v=2$ 而 $p_u>p_v$，并且边 $\{u,v\}$ 对 $R_G$ 的贡献严格为负：

$$
(q_u-q_v)(p_u-p_v)
=-\frac{\lambda^4(\lambda-1)}
{Z_G(1+4\lambda)(1+3\lambda)}<0.
\tag{6.1b}
$$

**证明 6.1。** 八个独立点对恰为

$$
\{u,x\},\{u,y\},\{v,a\},\{v,b\},\{v,y\},
\{a,x\},\{b,x\},\{x,y\}.
$$

包含 $u$ 的独立集大小至多为 $3$，唯一的三点集是 $\{u,x,y\}$。不含 $u$ 的诱导子图由团 $\{a,b,y\}$ 和边 $\{v,x\}$ 构成，故其独立集大小至多为 $2$。所以全部独立集按大小计数为 $1,6,8,1$，再无更大独立集，得到 $Z_G$。

包含 $u$ 的配置是 $\{u\},\{u,x\},\{u,y\},\{u,x,y\}$；包含 $v$ 的配置是 $\{v\},\{v,a\},\{v,b\},\{v,y\}$。因此

$$
p_u=\frac{\lambda+2\lambda^2+\lambda^3}{Z_G},\qquad
p_v=\frac{\lambda+3\lambda^2}{Z_G},
$$

相减得（6.1a）。由度数和 $q$ 的定义得到（6.1b）。$\lambda=1$ 时两边缘率相等；$0<\lambda<1$ 时大小关系反转。此例否定的是对所有图、所有正活动度都成立的边上度反向排序 $d_u>d_v\Rightarrow p_u\le p_v$，并未由单条边的符号决定 $D_G$ 的符号。$\square$

**假设 6.2（无结构限制的共同活动度目标，待证）。** 对每个有限简单图 $G$ 与每个 $\lambda>0$，是否总有

$$
M_G(\lambda)\ge\sum_{v\in V(G)}
\frac{\lambda}{1+(d_v+1)\lambda}?
\tag{6.2a}
$$

这是定义 1.2 的 Davies–Kang 目标，量词仍覆盖所有有限简单图及所有正的共同活动度。由定理 3.2，它等价于

$$
R_G(\lambda)\ge-\sum_v q_vs_v.
\tag{6.2b}
$$

定理 6.1 表明不能在一般图上逐条删去边余项。仍需对同一实际 Gibbs 律中的负边项与邻域超额建立统一补偿，而非另选一个独立集分布或只要求非负向量满足局部平衡不等式。局部占据 LP 的一般活动度障碍见 [Davies–Sandhu–Seo–Tan，arXiv:2605.05149v1，§6](https://arxiv.org/html/2605.05149v1#S6)；该 LP 的可行向量与实际 Gibbs 边缘律是不同的数学对象。

对于每个固定整数 $\Delta\ge2$，定理 2.2 覆盖最大度至多 $\Delta$ 时 $\lambda\ge2^{T_\Delta}$ 的全部图；定理 4.2 和 5.2 覆盖其各自结构类的全部 $\lambda>0$。结合定义 1.2 的已知小活动度结果，在这些结构类之外、最大度为 $\Delta$ 的一般图上，中间活动度范围的统一补偿仍待证。最大度至多 $1$、空图与完全分量均已有精确等号，不构成此缺口。

积分形式的分区函数界不提供（6.2b）所需的逐点补偿。[Lee–Seo，arXiv:2602.02450v2，Theorem 1.1、§5（5.1）与（5.2）](https://arxiv.org/html/2602.02450v2) 中，Theorem 1.1 的结论是 $Z_G$ 的下界，§5 则另述占据率目标；[Lee–Seo，arXiv:2608.17920v1，Theorems 1.1–1.2](https://arxiv.org/html/2608.17920v1) 的结论也是配分量下界。对所有 $\lambda$ 的函数下界不能直接逐点微分为导数下界。类似地，[Zhang–Xu，*On the Variance Fraction of the Hard-Core Model on Graphs with Bounded Maximum Degree*，arXiv:2604.01717v3，Theorem 1.3](https://arxiv.org/html/2604.01717v3) 的方差界按最大度给出，而非（6.2a）的逐顶点度序列之和；它不替代此处的补偿问题。

## 追加锚（本行以下为增补区）
