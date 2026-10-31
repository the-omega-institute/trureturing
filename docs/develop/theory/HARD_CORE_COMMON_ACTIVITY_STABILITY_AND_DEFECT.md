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

## 7. 单邻点交换与配置电荷恒等式

**定义 7.1（超额配置电荷）。** 沿用定义 1.1、1.2、3.1 的实际共同活动度 Gibbs 律、$\beta,q_v,p_v,Y_v,s_v,D_G,R_G$。置

$$
Q_G(\lambda)=\sum_{v\in V}q_vs_v,
$$

并对每个独立集 $J\in\mathcal I(G)$ 定义

$$
C_{G,\lambda}(J)=
\sum_{\substack{v\in V\\|J\cap N(v)|\ge2}}
\left(\sum_{u\in J\cap N(v)}q_u-q_v\right).
\tag{7.1}
$$

当 $G,\lambda$ 固定时简记 $C_G(J)$。此电荷使用同一个 $\lambda$ 决定的全部 $q_v$，不是另选独立集分布。

**定理 7.2（实际 Gibbs 缺陷的配置期望）。** 对每个有限简单图 $G$ 和每个 $\lambda>0$，有精确恒等式

$$
D_G(\lambda)=\mathbb E_{G,\lambda}C_G(I).
\tag{7.2a}
$$

**证明 7.2。** 对有向邻接对 $(u,v)$ 定义

$$
\mathcal S_{u\to v}=
\{J\in\mathcal I(G):J\cap N(v)=\{u\}\}.
$$

若 $J\in\mathcal S_{u\to v}$，则 $u\in J$、$v\notin J$。映射

$$
T_{uv}(J)=(J\setminus\{u\})\cup\{v\}
\tag{7.2b}
$$

的像是独立集，因为 $v$ 在 $J$ 中唯一的邻点为 $u$。又因原来的 $J$ 不含 $N(u)$ 中任何点，交换后的配置与 $N(u)$ 的交恰为 $\{v\}$，故 $T_{uv}(J)\in\mathcal S_{v\to u}$。反向交换是其逆，且大小不变。因此共同活动度权重 $\lambda^{|J|}$ 不变，得到

$$
\mathbb P(I\in\mathcal S_{u\to v})
=\mathbb P(I\in\mathcal S_{v\to u}).
\tag{7.2c}
$$

独立集间的保权交换与消去是既有组合方法；例如 [Bencs，*Christoffel-Darboux type identities for independence polynomial*，arXiv:1409.2527v1，Theorems 1.3–1.4、§2](https://arxiv.org/html/1409.2527v1) 对独立集对的二分连通分量作交换。这里使用的是（7.2b）的单配置双射，不以该文的多项式乘积恒等式替代（7.2a）的推导。

对每个固定配置 $J$，先对所有 $v$ 求 $\sum_{u\in J\cap N(v)}q_u-q_v$，再删去邻点数为 $0$ 和 $1$ 的部分，恰得

$$
\begin{aligned}
C_G(J)
={}&\sum_{u\in J}d_uq_u-\sum_vq_v
+\sum_vq_v\mathbf1_{\{J\cap N(v)=\varnothing\}}\\
&-\sum_{\substack{(u,v)\\\{u,v\}\in E}}
(q_u-q_v)\mathbf1_{\{J\in\mathcal S_{u\to v}\}}.
\end{aligned}
\tag{7.2d}
$$

最后一和遍历每条边的两个方向。取期望后，其相反方向的两项由（7.2c）抵消。证明 3.2 中已给出的实际 Gibbs 关系 $\mathbb P(Y_v=0)=\beta p_v$，亦见 [Davies–Sandhu–Seo–Tan，arXiv:2605.05149v1，Proposition 5 的证明](https://arxiv.org/html/2605.05149v1)，于是给出

$$
\mathbb EC_G(I)
=\sum_v(d_v+\beta)q_vp_v-\sum_vq_v
=\sum_vp_v-\sum_vq_v=D_G.
$$

所有和均有限；空图时恒等式两边均为 $0$。$\square$

## 8. 诱导三点路的充分条件与度数范围

**定理 8.1（端点权重充分条件）。** 固定有限简单图 $G$ 与 $\lambda>0$。若每条诱导三点路 $a-v-b$，即 $a,b\in N(v)$ 且 $a,b$ 不相邻，均满足

$$
q_a+q_b\ge q_v,
\tag{8.1a}
$$

则每个 $J\in\mathcal I(G)$ 均有 $C_G(J)\ge0$，从而 $D_G(\lambda)\ge0$。对每一条这样的三点路，（8.1a）等价于显式度数条件

$$
(d_a-d_v)(d_b-d_v)\le(\beta+d_v)^2.
\tag{8.1b}
$$

这里仅断言充分性，不断言该条件对缺陷非负为必要条件，也不给出非严格条件下的一般等号刻画。

**证明 8.1。** 若 $|J\cap N(v)|\ge2$，从中取两个不同点 $a,b$。独立性保证其不相邻，故

$$
\sum_{u\in J\cap N(v)}q_u-q_v
\ge q_a+q_b-q_v\ge0.
$$

逐项相加，再用（7.2a），得到两个非负性结论。由于所有分母为正，（8.1a）等价于

$$
(2\beta+d_a+d_b)(\beta+d_v)
\ge(\beta+d_a)(\beta+d_b).
$$

两边相减等于 $(\beta+d_v)^2-(d_a-d_v)(d_b-d_v)$，这证明等价性。$\square$

**推论 8.2（不含活动度的局部度数条件）。** 若有限简单图 $G$ 的每条诱导三点路 $a-v-b$ 均满足

$$
(d_a-d_v)(d_b-d_v)\le(1+d_v)^2,
\tag{8.2}
$$

则 $D_G(\lambda)\ge0$ 对全部 $\lambda>0$ 成立。

**证明 8.2。** 每个有限的正活动度均有 $\beta>1$，故 $(1+d_v)^2<(\beta+d_v)^2$。（8.2）蕴含（8.1b），可直接应用定理 8.1。这里把 $\beta=1$ 仅作为度数判据的代入值，并没有取无限活动度的 Gibbs 律充当有限活动度的证明。$\square$

**推论 8.3（最大度五与小活动度范围）。** 对每个最大度至多 $5$ 的有限简单图 $G$ 和每个 $\lambda>0$，

$$
M_G(\lambda)\ge\sum_v\frac{\lambda}{1+(d_v+1)\lambda},
\tag{8.3a}
$$

等号成立当且仅当每个连通分量均完全。另对任意整数 $\Delta\ge6$，每个最大度至多 $\Delta$ 的有限简单图在

$$
0<\lambda\le\frac1{\Delta-5}
\tag{8.3b}
$$

时满足（8.3a）；（8.3b）只是一条充分活动度界。

**证明 8.3。** 诱导三点路的中心度数至少为 $2$。在最大度至多 $5$ 时，对任意 $\beta>1$，

$$
q_a+q_b\ge\frac2{\beta+5}
>\frac1{\beta+2}\ge q_v,
\tag{8.3c}
$$

其中严格不等式等价于 $\beta>1$。于是定理 8.1 适用。若某个分量不完全，两个不相邻点之间的最短路含一条诱导三点路 $a-v-b$。配置 $J=\{a,b\}$ 在实际 Gibbs 律下有严格正概率，且其电荷在中心 $v$ 处由（8.3c）严格为正，其余被计入的项均非负。因此 $D_G=\mathbb EC_G(I)>0$。反之，各完全分量的精确等号已由定理 2.2 的证明给出；分量加性包含孤立点和空图。

在（8.3b）下，$\beta=1+1/\lambda\ge\Delta-4$，所以

$$
q_a+q_b\ge\frac2{\beta+\Delta}
\ge\frac1{\beta+2}\ge q_v.
$$

中间不等式恰为 $\beta+4\ge\Delta$，故仍由定理 8.1 得到结论。$\square$

**推论 8.4（最小度与最大度的比值范围）。** 若非空有限简单图 $G$ 的最小度为 $\delta$、最大度为 $\Delta$，且 $\Delta\le2\delta+1$，则 $D_G(\lambda)\ge0$ 对每个 $\lambda>0$ 成立。

**证明 8.4。** 对每条诱导三点路及每个 $\beta>1$，有

$$
q_a+q_b\ge\frac2{\beta+\Delta}
>\frac1{\beta+\delta}\ge q_v,
$$

因为 $\beta+2\delta>2\delta+1\ge\Delta$。应用定理 8.1 即可。无诱导三点路时该定理的条件为空条件，仍然适用。$\square$

## 9. 总边余项为负的共同活动度实例

**命题 9.1（负总余项与正缺陷并存）。** 令 $G$ 由独立三点集 $S$ 与不交并 $K_2\sqcup K_3$ 作完全连接得到：$S$ 的每点与两个团的每点相邻，两个团之间没有边。全部八个顶点使用同一个 $\lambda>0$。记

$$
A=1+6\lambda,\qquad B=1+5\lambda,\qquad
Z=1+8\lambda+9\lambda^2+\lambda^3.
$$

则 $Z_G=Z$，且精确地有

$$
\begin{aligned}
R_G(\lambda)&=-\frac{6\lambda^4(\lambda-1)}{ZAB},\\
D_G(\lambda)&=\frac{\lambda^3(33+187\lambda+48\lambda^2)}{ZAB}>0,\\
Q_G(\lambda)&=\frac{\lambda^3(33+181\lambda+54\lambda^2)}{ZAB}>0.
\end{aligned}
\tag{9.1a}
$$

特别地，$\lambda>1$ 时总和 $R_G<0$，而原占据目标仍严格成立。此命题不包含图阶最小性断言。

**证明 9.1。** 一个独立集不能同时在 $S$ 和团侧取点。团侧在 $K_2,K_3$ 中各至多取一点，故

$$
Z_G=(1+\lambda)^3+(1+2\lambda)(1+3\lambda)-1=Z.
\tag{9.1b}
$$

$S$ 与 $K_3$ 中的点度数均为 $5$，而 $K_2$ 中的点度数为 $4$。分别用下标 $S,2,3$ 表示这三类顶点，对每一个单独顶点有

$$
\begin{aligned}
&q_S=q_3=\frac\lambda A,\qquad q_2=\frac\lambda B,\\
&p_S=\frac{\lambda(1+\lambda)^2}{Z},\qquad
p_2=\frac{\lambda(1+3\lambda)}{Z},\qquad
p_3=\frac{\lambda(1+2\lambda)}{Z}.
\end{aligned}
\tag{9.1c}
$$

边余项中，两个团内部的边与 $S$ 到 $K_3$ 的边都因 $q$ 相等而贡献 $0$。剩下的六条 $S$ 到 $K_2$ 的边各贡献

$$
(q_2-q_S)(p_2-p_S)
=\frac{\lambda^2}{AB}\frac{\lambda^2(1-\lambda)}Z,
$$

这直接给出 $R_G$。

对 $S$ 中的点，邻域超额只在两个团各取一点时为 $1$，所以 $s_S=6\lambda^2/Z$。对任一团中的点，邻域里同团的其他顶点至多占据一个；超额只可能来自 $S$ 中的二点集或三点集。因此

$$
s_2=s_3=\frac{3\lambda^2+2\lambda^3}Z.
$$

于是独立地算得

$$
\begin{aligned}
Q_G
&=\frac{3\lambda}A\frac{6\lambda^2}Z
+\left(\frac{2\lambda}B+\frac{3\lambda}A\right)
\frac{3\lambda^2+2\lambda^3}Z\\
&=\frac{\lambda^3}{ZAB}
\bigl((27+6\lambda)B+(6+4\lambda)A\bigr),
\end{aligned}
$$

展开括号即（9.1a）的 $Q_G$。最后由配置大小计数而非余项符号得到

$$
M_G=\frac{8\lambda+18\lambda^2+3\lambda^3}Z,
\qquad
\sum_vq_v=\frac{6\lambda}A+\frac{2\lambda}B.
$$

相减、通分，其分子为 $\lambda^3(33+187\lambda+48\lambda^2)$，这证明 $D_G$ 的表达式和严格正性。三个表达式也满足定理 3.2 的 $D_G=Q_G+R_G$。$\square$

## 10. 固定活动度下系数一之前的一致余量障碍

**定义 10.1（不平衡连接族与等大团替换）。** 对整数 $r\ge2,m\ge3$，令 $F_{r,m}$ 是独立集 $S$（$|S|=r+1$）与 $r$ 个互不相交的 $m$ 阶团的完全连接。团侧顶点总数为 $rm$。另对任意有限简单图 $F$ 和正整数 $k$，定义 $F[K_k]$：以 $k$ 阶团 $\{(v,i):1\le i\le k\}$ 替换每个 $v\in V(F)$；当且仅当 $uv\in E(F)$ 时，在对应两个团间加入全部 $k^2$ 条边。新图仍为有限简单图。

**命题 10.2（连接族的正极限缺陷与超额）。** 对 $F=F_{r,m}$，有

$$
Z_F(\lambda)=(1+\lambda)^{r+1}+(1+m\lambda)^r-1,
\tag{10.2a}
$$

且当 $\lambda\to\infty$ 时，

$$
\begin{aligned}
Q_F(\lambda)&\longrightarrow Q_\infty
=\frac{r^2m}{m+r+1}>0,\\
D_F(\lambda)&\longrightarrow D_\infty
=\frac{rm(m+r^2+2r)}{(rm+1)(m+r+1)}>0,\\
\frac{D_F(\lambda)}{Q_F(\lambda)}
&\longrightarrow\frac{D_\infty}{Q_\infty}
=\frac{m+r^2+2r}{r(rm+1)}.
\end{aligned}
\tag{10.2b}
$$

其中比值在充分大的有限活动度有定义。

**证明 10.2。** 与（9.1b）相同，配置只能取自 $S$ 或团侧；$r$ 个团的选择独立相乘，空集只计一次，得到（10.2a）。$S$ 中的点度数为 $rm$，团侧的点度数为 $m+r$。$S$ 自身是唯一大小为 $r+1$ 的独立集，而团侧的独立集大小至多为 $r$。因此将 $Z_F$ 与配置权重同时除以 $\lambda^{r+1}$ 可知，实际 Gibbs 律趋向集中于配置 $S$；并且 $M_F\to r+1$。

在配置 $S$ 上，$S$ 中每点的 $Y_v=0$；团侧每点的 $Y_v=r+1$，所以邻域超额为 $r$。图固定且配置数有限，逐项取极限合法，$\beta\to1$ 给出

$$
Q_\infty=rm\frac r{m+r+1},
\qquad
D_\infty=r+1-\frac{r+1}{rm+1}-\frac{rm}{m+r+1}.
$$

第二式通分后的分子为 $rm(m+r^2+2r)$，均严格为正。由于 $Q_\infty>0$，比值极限成立并化为（10.2b）。$\square$

**定理 10.3（每个固定共同活动度的严格障碍）。** 对每个预先指定的 $\lambda_0>0$ 和每个 $0\le c<1$，存在有限简单图 $G$，其全部顶点均使用同一个活动度 $\lambda_0$，且

$$
Q_G(\lambda_0)>0,\qquad D_G(\lambda_0)>0,
\qquad R_G(\lambda_0)<-cQ_G(\lambda_0).
\tag{10.3a}
$$

因而不存在仅依赖活动度的函数 $c:(0,\infty)\to[0,1)$，使得所有有限简单图均满足 $R_G(\lambda)\ge-c(\lambda)Q_G(\lambda)$；即使将此要求限制到 $D_G(\lambda)>0$ 的图也不成立。此障碍不证明系数恰为一的补偿界，不排除依赖度数的余量，也不结算原猜想。

**证明 10.3。** 置 $\varepsilon=1-c>0$。先选有限整数 $r\ge2$ 使 $1/r^2<\varepsilon/2$，再选有限整数 $m\ge3$ 使 $(1+2/r)/m<\varepsilon/2$。命题 10.2 给出

$$
0<\frac{D_\infty}{Q_\infty}
=\frac{m+r^2+2r}{r(rm+1)}
\le\frac1{r^2}+\frac{1+2/r}{m}<\varepsilon.
\tag{10.3b}
$$

固定所选的有限图 $F=F_{r,m}$。由两个严格正极限及比值极限，存在有限 $L>0$，使对所有 $t\ge L$ 均有

$$
Q_F(t)>0,\qquad D_F(t)>0,\qquad
D_F(t)<\varepsilon Q_F(t).
\tag{10.3c}
$$

定理 3.2 随即给出 $R_F(t)=D_F(t)-Q_F(t)<-cQ_F(t)$。下面把此高活动度事实传回预先固定的 $\lambda_0$，并保持实际 Gibbs 律与三个量完全对应。

选正整数 $k$ 使 $t=k\lambda_0\ge L$，取 $G=F[K_k]$。对 $G$ 的一个独立集 $I'$，令 $J\subseteq V(F)$ 为被占据的替换团的集合。每团至多占据一个点，故 $J\in\mathcal I(F)$。每个固定 $J$ 恰有 $k^{|J|}$ 个提升，且每个提升在共同活动度 $\lambda_0$ 的未归一化权重均为 $\lambda_0^{|J|}$。因此

$$
Z_G(\lambda_0)=Z_F(k\lambda_0)=Z_F(t),\qquad
\mathbb P(J=J_0)=\frac{t^{|J_0|}}{Z_F(t)}.
\tag{10.3d}
$$

这正是 $F$ 在共同活动度 $t$ 的 Gibbs 律；条件于 $J$，每个被占据团的标签在 $\{1,\ldots,k\}$ 上独立均匀。以下未加撇的 $q_v,p_v,s_v,Y_v$ 都在 $F,t$ 上计算，加撇的量在 $G,\lambda_0$ 上计算。替换团中每点的度数为

$$
d'_{(v,i)}=k(d_v+1)-1,
$$

从而精确地有

$$
\begin{aligned}
q'_{(v,i)}
&=\frac1{1+1/\lambda_0+k(d_v+1)-1}
=\frac{q_v}{k},\\
p'_{(v,i)}&=\frac{p_v}{k},\qquad
M_G(\lambda_0)=M_F(t),\qquad
\sum_{v,i}q'_{(v,i)}=\sum_vq_v.
\end{aligned}
\tag{10.3e}
$$

特别地 $D_G(\lambda_0)=D_F(t)$。为核对 $Q$，若 $v\notin J$，则 $Y'_{(v,i)}=Y_v(J)$；若 $v\in J$，独立性保证 $Y_v(J)=0$，而 $Y'_{(v,i)}$ 只是本团所选标签是否不等于 $i$ 的指示量，取值至多为 $1$。两种情形均给出逐配置等式

$$
(Y'_{(v,i)}-1)_+=(Y_v(J)-1)_+.
$$

所以 $s'_{(v,i)}=s_v$，结合 $q'_{(v,i)}=q_v/k$ 得到 $Q_G(\lambda_0)=Q_F(t)$。最后，本团内部的边因 $q'$ 相同而对 $R_G$ 贡献 $0$；每条原边 $uv$ 的 $k^2$ 条提升边的总贡献为

$$
k^2\left(\frac{q_u-q_v}k\right)
\left(\frac{p_u-p_v}k\right)
=(q_u-q_v)(p_u-p_v).
$$

故全部实际量满足

$$
(D_G,Q_G,R_G)(\lambda_0)=(D_F,Q_F,R_F)(t).
\tag{10.3f}
$$

把（10.3c）传入（10.3f）即得（10.3a）。$r,m,k$ 均先后选为有限整数；构造没有更改 $\lambda_0$，也未给不同顶点指定不同活动度。若存在结论中排除的函数，在任意 $\lambda_0$ 取 $c=c(\lambda_0)$，即被（10.3a）矛盾。$\square$

## 11. 配置逐点非负的边界与剩余补偿目标

**命题 11.1（负配置电荷不等于负期望缺陷）。** 在完全二分图 $G=K_{2,6}$ 中，令 $J$ 为含两个度六顶点的独立集。则

$$
C_G(J)=6\left(\frac2{\beta+6}-\frac1{\beta+2}\right)
=\frac{6(\beta-2)}{(\beta+6)(\beta+2)}<0
\quad(\lambda>1).
\tag{11.1a}
$$

但对这个图的每个 $\lambda>0$，$D_G(\lambda)>0$。所以（7.2a）不能在一般图上以逐配置非负直接证明占据目标；定理 8.1 的逐点充分条件与期望层面的补偿须分别处理。

**证明 11.1。** 两个度六点在 $J$ 中，它们的邻域占据数均为 $0$；其余六个度二点各有两个占据邻点。因此定义 7.1 直接给出（11.1a）。$\lambda>1$ 等价于 $1<\beta<2$，故该值严格为负。

为独立核对实际缺陷，图的分区函数和两类单点边缘率为

$$
\begin{aligned}
Z_G&=(1+\lambda)^2+(1+\lambda)^6-1,\\
p_{d=6}&=\frac{\lambda(1+\lambda)}{Z_G},\qquad
p_{d=2}=\frac{\lambda(1+\lambda)^5}{Z_G}.
\end{aligned}
$$

每个正活动度均有 $p_{d=6}<p_{d=2}$，且 $q_{d=6}<q_{d=2}$，故十二条边在 $R_G$ 中的贡献均严格为正。$Q_G\ge0$ 和定理 3.2 给出 $D_G=Q_G+R_G>0$。负电荷配置本身有正 Gibbs 概率，但其负值被其他配置的贡献补偿。$\square$

**假设 11.2（配置期望的一般非负性，待证）。** 对所有有限简单图 $G$ 和全部共同活动度 $\lambda>0$，待证的原目标仍为

$$
\mathbb E_{G,\lambda}C_G(I)\ge0,
\quad\text{等价地}\quad R_G(\lambda)\ge-Q_G(\lambda).
\tag{11.2}
$$

等价性由定理 7.2 与定理 3.2 给出；原始量词来自 [Davies–Kang，arXiv:2501.03379v2，§8，Conjecture A](https://arxiv.org/html/2501.03379v2#S8)。定理 8.1 覆盖满足相应活动度下局部度数条件的图，推论 8.2–8.4 因而缩小假设 6.2 所述的未覆盖范围：最大度至多五已覆盖全部正活动度；给定最大度上界 $\Delta\ge6$ 时，新的充分小活动度区间为（8.3b），而定理 2.2 仍覆盖其高活动度区间。分裂分量、逐分量独立数至多二等既有结构范围继续由定理 4.2、5.2 给出。对本卷这些充分条件以外的图与活动度，本卷尚未证明（11.2）。

命题 9.1 排除了把总边余项一律取非负的加强；定理 10.3 排除了在系数一之前保留仅依赖活动度的一致比例余量；命题 11.1 排除了把所有配置电荷都取非负的加强。这三个否定均不否定（11.2）。对固定活动度下的实际 Gibbs 联合律，仍需建立允许负配置或负边项的期望补偿。仅要求非负向量满足局部占据不等式，不能代替这条实际联合律；相关松弛的限制见 [Davies–Sandhu–Seo–Tan，arXiv:2605.05149v1，§6](https://arxiv.org/html/2605.05149v1#S6)。

## 追加锚（本行以下为增补区）
