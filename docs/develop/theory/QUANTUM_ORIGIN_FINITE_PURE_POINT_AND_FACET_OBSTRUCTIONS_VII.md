# QUANTUM ORIGIN: FINITE PURE POINT AND FACET OBSTRUCTIONS VII

本卷的章节引用采用如下约定：第88章及88.x条目指[第五卷](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)；第89—95章及其子条目指[第六卷](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)；第96章及96.x条目指本卷。式号同属其章号指定的卷，未另注卷名的跨章引用均按此约定。

## 96. 有限纯点的facet注入与高关系零度障碍

### 96.1 整个原基的顶点与facet

**定义 96.1（有限纯点的面数）。** 完整保留89.1的原 $V,C,u,K,P,[0,u]$，并且只在本章的有限分支假设整个 $P$ 有限。记

$$
m=\dim\operatorname{aff}K=\dim V-1,\qquad
n=|P|,\qquad \nu=n-m-1.
\tag{96.1}
$$

这里 $\nu$ 就是92.1的整个关系空间零度。$m\ge1$ 时，$\mathcal A(K)$ 为原多面体 $K=\operatorname{conv}P$ 的全部facet，即维数 $m-1$ 的面，记 $f=|\mathcal A(K)|$。这些是整个基的面，不是某个抽取配置的面。$m=0$ 时 $K$ 为单点，单独处理，不选择facet。$D_p$、$\perp$、$\mathrm B$、$\mathrm{Z0}$、$\mathrm A$、$\mathrm H$ 和 $S$ 仍取88—89章的全域定义，尤其 $\mathrm{Z0}$ 的两个被排除端点仍遍历全部原混态。

### 96.2 零拼合给出的非入射facet注入

**定理 96.2（全效应facet注入）。** 在定义96.1及 $m\ge1$ 下，单独 $\mathrm{Z0}$ 已使每个facet $F$ 都有一个原纯点 $p_F$，满足

$$
D_{p_F}=F,\qquad p_F\notin F.
\tag{96.2}
$$

任意逐facet作出的这种选择都是单射 $F\mapsto p_F$，因此

$$
f\le n.
\tag{96.3}
$$

所选顶点与facet还满足对称的交叉入射律

$$
p_G\in F\quad\Longleftrightarrow\quad p_F\in G
\qquad(F,G\in\mathcal A(K)).
\tag{96.4}
$$

这里不预设 $\mathrm B$、自对偶配对或顶点到facet的满射。

证明。固定整个facet $F$。多面体的支撑表示给实仿射函数 $\ell_F$，在整个 $K$ 上非负，且零集恰为 $F$。它非恒定，故 $M_F=\max_K\ell_F>0$；线性优化在某个原顶点 $p_F\in P$ 达到这个最大值。把 $\ell_F/M_F$ 从归一超平面齐次延伸到 $V$，记作 $h_F$。具体地，任选 $x_0\in K$，用 $V=\mathbb Rx_0\oplus\ker u$ 将其仿射表达唯一线性延伸。由于每个非零 $c\in C$ 均为 $u(c)k$、$k\in K$，整个基上的零一界给

$$
0\le h_F\le u\text{ 于整个 }C,\qquad
h_F(p_F)=1,\qquad K\cap\ker h_F=F.
\tag{96.5}
$$

所以这是一张原全效应，$F\subseteq D_{p_F}$，并没有留下从子配置向整个载体延拓的义务。88.3由全称混态 $\mathrm{Z0}$ 给 $D_{p_F}$ 为暴露面；它是非空真面，因为 $p_F\notin D_{p_F}$。facet是极大真面，故 $F\subseteq D_{p_F}\subsetneq K$ 迫使 $D_{p_F}=F$。若两个facet选到同一个纯点，它们都等于该点的 $D_p$，故相等，得到单射及(96.3)。

最后，两个纯端点的原零排除对称，因为同一proper效应的补交换零和一。因此

$$
p_G\in F=D_{p_F}
\ \Longleftrightarrow\ p_F\perp p_G
\ \Longleftrightarrow\ p_G\perp p_F
\ \Longleftrightarrow\ p_F\in D_{p_G}=G.
$$

这证明(96.4)，并未把该有限非入射匹配提升为整个面格的极性。证毕。

### 96.3 关系零度至多八的原载体

**定理 96.3（有限低零度的单纯形结论）。** 在定义96.1下，若 $\nu\le8$，则

$$
\boxed{\mathrm B+\mathrm{Z0}
\quad\Longleftrightarrow\quad K\text{ 是单纯形}.}
\tag{96.6}
$$

因此，89.12的任何有限纯点真反例必须满足

$$
|P|-\dim V\ge9.
\tag{96.7}
$$

这里的附加条件是整个原纯点集有限且有给定关系零度，不把一般原载体替换成有限子配置。

证明。先设 $\mathrm B+\mathrm{Z0}$。由于 $P$ 有限，整个 $K$ 及它的每个面都是多面体。维数至少二的欧氏球有无限多个极点，故 $\mathrm B$ 中每个整个二态最小面只能是 $B^1$，即其两个端点之间的整条边。因此原 $K$ 是2-neighborly多面体：每两个不同原顶点组成一条边。这一步只用整个最小面和全部原纯点，没有采用抽样球面。

$m=0,1$ 时分别是单点和线段。$m=2$ 时多边形的边图是圈，完全边图迫使它为三角形；$m=3$ 时边图平面性给 $n(n-1)/2\le3n-6$，而 $n\ge4$，所以 $n=4$。这些分支均为单纯形。以下设 $m\ge4$。

由96.2及 $\nu\le8$，

$$
f\le n=m+1+\nu\le m+9.
\tag{96.8}
$$

在这个精确范围，直接引用 A. N. Maksimenko、D. V. Gribanov、D. S. Malyshev，*All 2-neighborly d-polytopes with at most d + 9 facets*，[arXiv:1912.03900v1，§1图1及§§2—4](https://arxiv.org/pdf/1912.03900v1) 的完整分类。除单纯形外，其基本类型的三元组 $(\text{维数},\text{顶点数},\text{facet数})$ 为

$$
\begin{gathered}
(4,6,9),\ (5,7,12),\ (6,8,15),\ (5,8,12),\ (5,8,14),\\
(6,9,15),\ (9,12,18),\ (6,10,14),\ (6,10,15),\ (7,14,16),
\end{gathered}
\tag{96.9}
$$

其余非单纯形类型均为这些类型的有限次棱锥。每个列出的类型都有 $f>n$；一次棱锥同时把维数、顶点数和facet数各增加一，故仍严格有 $f>n$。所以所有非单纯形类型都与(96.8)矛盾。这里引用的是对全部实凸2-neighborly多面体的分类；其部分类型有零一坐标实现，不是额外的坐标前件。于是 $K$ 必为单纯形。

反向，原单纯形的全部不同纯对最小面为边，故有 $\mathrm B$。各纯点的重心坐标是原全proper区间中的确认效应，且其零集为对面单纯形；原排除集恰为这个零面，故有对全部原混态的 $\mathrm{Z0}$。单点取 $e_p=u$、$D_p=\varnothing$。这些既有单纯形事实按92.2复用。

最后，任一单纯形都满足 $\mathrm A$ 和 $\mathrm H$，所以若有限原载体满足 $\mathrm B+\mathrm{Z0}+\neg\mathrm A$，便不是单纯形，(96.6)的逆否命题给 $\nu\ge9$，即(96.7)。这仅加强有限分支的必要界，不证明 $\nu\ge9$ 时存在反例。证毕。

### 96.4 低维原基的进一步排除

**推论 96.4（基维数至多六的有限分支）。** 在定义96.1及 $\mathrm B+\mathrm{Z0}$ 下，若 $m\le5$，则 $K$ 为单纯形，不要求 $\nu\le8$。若 $m=6$ 且 $K$ 非单纯形，则必有

$$
f=n\ge27,\qquad \nu\ge20,
\tag{96.10}
$$

并且对偶多面体也是2-neighborly；96.2的单射此时为双射，每个原纯点的 $D_p$ 都是一张facet，(96.4)遍及这个完整顶点—facet配对。

证明。原 $K$ 的2-neighborly性及 $f\le n$ 已在96.2—96.3中给出。$m\le3$ 的证明同96.3且不使用顶点数上限。$m=4$ 时2-neighborly多面体的facet数为 $n(n-3)/2$，故 $f\le n$ 和 $n\ge5$ 迫使 $n=5$。$m=5$ 时，引用 A. Maksimenko，*On the minimum number of facets of a 2-neighborly polytope*，[arXiv:1808.09672v2 Theorem 2，取 $k=2,d=5$](https://arxiv.org/pdf/1808.09672v2)：$f\ge n$ 且等号只在单纯形成立。与 $f\le n$ 合用即得结论。

$m=6$ 时，同文 Theorem 5 给 $f\ge n$，且非单纯形的等号情形必须是对偶亦2-neighborly、并有 $n\ge27$ 的多面体。因此 $f=n\ge27$、$\nu=n-7\ge20$。有限等基数使96.2的注入为双射，从而每个纯点都恰是某个 $p_F$，其 $D_p=F$ 和交叉入射对称律随即覆盖全部顶点。这里只得到可能反例的必要结构，不断言该结构存在或足以满足原 $\mathrm{Z0}$。证毕。

### 96.5 同数据消费者与剩余的接触义务

**推论 96.5（有限表示域的几何替换）。** 完整保留89.7的同一个原装饰元组 $\mathcal O$ 及其全部非几何前件。若每个原 $X=A,D,E$ 都有有限的整个纯点集，且分别满足 $\nu_X\le8$ 或 $\dim\operatorname{aff}K_X\le5$，则把各原几何项 $\mathrm B+\mathrm{Boundary}$ 换成同一载体的 $\mathrm B+\mathrm{Z0}$，仍是89.8的完整同数据等价；每个满足该几何项的原基必为单纯形。

证明。正向由96.3或96.4给原 $K_X$ 为单纯形，其原重心坐标效应给完整 $S$，89.4给 $\mathrm B+\mathrm{Boundary}$。反向，89.4的完整 $S$ 给 $\mathrm B$，其least零集论证按90.6给 $\mathrm{Z0}$。其余原数据没有改变，故89.8直接适用，89.9的消费者仍按各自完整前件复用。这个有限表示域只供应经典单纯形几何，不由它生成非经典复块、指定复合、CP、更新、时间或原source-adoption map；同一个PRE、原source、全部菜单、参考、资源、记录和全部合法未来仍保留原类型与条件。

一般89.12仍有两类未解原载体：有限纯点而不满足上述排除范围者，以及整个纯点集无限者。后者包括通常非经典量子基，不能用有限抽取、闭包或受限效应代替。在这些原载体上，尚须从 $\mathrm B+\mathrm{Z0}$ 证明90.10的全部接触 $D_p\cap H(p,q)\ne\varnothing$，或构造同时满足全称 $\mathrm B$、全称混态 $\mathrm{Z0}$ 而违反 $\mathrm A/\mathrm H$ 的整个载体。facet注入、(96.7)及(96.10)均为必要条件，不是这项接触的证明或反例。

96.2的全效应facet注入与对称交叉入射，以及它和所引面数定理结合得到的原载体排除及同数据应用，采用 `repo-derived` 归属；(96.9)的完整多面体分类和96.4使用的面数界归所引原文，作为证明的成熟中间步骤。96.3并未重做92章的单关系优化，亦未推广91章的团表示到任意原锥。上述有限来源对应不支持全球原创或历史优先权结论；原89.4与89.7—89.10在各自完整前件下保持原结论。证毕。

## 追加锚（本行以下为增补区）

## 97. 有限全效应零拼合的面格正交补与度量障碍

### 97.1 原载体、卷别与有限参数

**定义 97.1（整个有限基的面格）。** 保留[第六卷定义89.1](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)的整个原 $V,C,u,K,P,[0,u]_{C^*}$，假设全部原纯点集 $P$ 有限，并沿用本卷VII96.1的

$$
m=\dim\operatorname{aff}K=\dim V-1,\qquad n=|P|,\qquad
\nu=n-m-1.
\tag{VII97.1}
$$

本章的VII96.x、VII97.x指本卷；VI89.x、VI90.x、VI97.x指[第六卷](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)；V88.x指[第五卷](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)。特别是，这里的 $n$ 是整个基的顶点数，不是VI97.1的实或复共同支撑维数；这里的 $m$ 也不取其他卷中字长参数的含义。VI97.6的实ROG共同支撑 $n\le4$ 结论按其原参数理解，不是本章有限顶点假设的替代。

记 $\mathcal L(K)$ 为整个多面体 $K=\operatorname{conv}P$ 的全部面，包含空面与 $K$，并约定 $\dim\varnothing=-1$。$F\vee G$ 表示包含 $F\cup G$ 的最小面，$F\wedge G=F\cap G$。$m\ge1$ 时，$\mathcal A(K)$ 是全部维数 $m-1$ 的facet，$f=|\mathcal A(K)|$。$D_p=\{x\in K:p\perp x\}$ 及 $\mathrm{Z0}$ 采用V88.1—88.2的全效应、全混态定义；对纯 $p,q$，补效应给 $p\perp q\Longleftrightarrow q\perp p$，且 $p\notin D_p$。以下不附加 $\mathrm B$，除非命题中明写。

### 97.2 全部顶点与facet的双射

**定理 97.2（有限零拼合的完整facet配对）。** 在定义VII97.1、$m\ge1$ 及 $\mathrm{Z0}$ 下，

$$
D_p\subseteq D_q\quad\Longrightarrow\quad p=q,
\qquad
P\longrightarrow\mathcal A(K),\quad p\longmapsto D_p
\text{ 是双射},\qquad f=n.
\tag{VII97.2}
$$

这个结论适用于任意有限 $m\ge1$，不要求 $\mathrm B$、$m=6$ 或关系零度上界。

证明。V88.3给每个非空 $D_p$ 为暴露真面，空 $D_p$ 也视为真面；VII96.2给每个facet $F$ 一个原纯点 $r$，使 $F=D_r$。先设 $D_p\subseteq D_q$。取任意包含 $p$ 的facet $F=D_r$。纯点排除对称性给

$$
p\in D_r\ \Longrightarrow\ r\in D_p\subseteq D_q
\ \Longrightarrow\ q\in D_r=F.
\tag{VII97.3}
$$

顶点 $\{p\}$ 等于所有包含它的facets之交，故 $q=p$。这里使用的是多面体的面由包含它的全部facets相交表示，未假设 $D_p$ 已是facet。

任取 $p\in P$，将真面 $D_p$ 包含于某个facet $D_r$；空面时也可这样选择。刚证出的蕴含给 $p=r$，所以 $D_p=D_r$ 本身就是facet。VII96.2已经给满射，而 $D_p=D_q$ 蕴含 $p=q$，故得到双射及 $f=n$。这也排除了 $m\ge1$ 时的空 $D_p$。证毕。

### 97.3 整个面格上的组合正交补

**定理 97.3（零关系生成的反序对合）。** 在定理VII97.2的前件下，对每个 $F\in\mathcal L(K)$ 定义

$$
F^\#=\bigcap_{p\in\operatorname{ext}F}D_p,
\qquad \bigcap\varnothing=K.
\tag{VII97.4}
$$

则 $F^\#\in\mathcal L(K)$，且对全部面 $F,G$ 有

$$
\begin{gathered}
F\subseteq G\ \Longrightarrow\ G^\#\subseteq F^\#,
\qquad F^{\#\#}=F,\qquad
\varnothing^\#=K,\quad K^\#=\varnothing,\quad \{p\}^\#=D_p,\\
F\cap F^\#=\varnothing,\qquad F\vee F^\#=K,\\
(F\vee G)^\#=F^\#\cap G^\#,
\qquad (F\cap G)^\#=F^\#\vee G^\#,\\
\dim F+\dim F^\#=m-1.
\end{gathered}
\tag{VII97.5}
$$

这些性质是原有限面格的组合正交补性质，不包含线性映射 $V\to V^*$、正定内积或数值互反性的存在断言。

证明。facets的交是面，且 $\operatorname{ext}F=P\cap F$，所以( VII97.4 )定义了面并反转包含。若 $p\in\operatorname{ext}F$、$r\in\operatorname{ext}F^\#$，则 $r\in D_p$；排除对称性给 $p\in D_r$。遍历这些 $r$ 再取凸包，得到 $F\subseteq F^{\#\#}$。

反向，设原顶点 $q\notin F$。面为facets的交，故有一个包含 $F$ 而不含 $q$ 的facet $G$。VII97.2将它唯一写成 $G=D_r$。每个 $p\in\operatorname{ext}F$ 都在 $D_r$ 中，故 $r\in D_p$，即 $r\in F^\#$。原顶点 $r$ 也就是这个面的顶点，因此

$$
F^{\#\#}\subseteq D_r=G,\qquad q\notin F^{\#\#}.
\tag{VII97.6}
$$

面由顶点决定，故 $F^{\#\#}=F$。空面和整个基的端点情形可直接核对：空交集是 $K$；若 $K^\#$ 非空，它作为面必有某个原顶点 $p$，却因 $K^\#\subseteq D_p$ 得 $p\in D_p$，矛盾。所以 $K^\#=\varnothing$。

若 $F\cap F^\#$ 非空，取该交面的一个顶点 $p$。它是 $F$ 的顶点，又属于 $F^\#\subseteq D_p$，再次矛盾。反序双射将最小上界送到最大下界，给两个De Morgan恒等式，再由 $(F\cap F^\#)^\#=K$ 得 $F\vee F^\#=K$。最后，有限多面体面格的秩是 $\rho(F)=\dim F+1$，最大秩为 $m+1$；反转一条经过 $F$ 的完整面旗给 $\rho(F)+\rho(F^\#)=m+1$，即维数公式。

若 $m=0$，整个基是单点 $K=\{p\}$，唯一确认效应为 $u$，故 $D_p=\varnothing$。此时( VII97.4 )仅交换 $\varnothing$ 与 $K$，( VII97.5 )仍成立，但不在这个分支计facet或主张 $f=n$。

从V88.3、VII96.2及纯点排除对称性到上述完整配对与面格的推导采用 `repo-derived` 归属。面与facets的交表示、面旗的秩以及反序双射的De Morgan律是其中的标准多面体与格论步骤。证毕。

### 97.4 对偶的二邻接性与准确的边接触条件

**推论 97.4（有限球条件的双侧边结构）。** 在定义VII97.1、$m\ge1$ 及 $\mathrm B+\mathrm{Z0}$ 下，原 $K$ 和它的对偶多面体都为2-neighborly。$m\ge2$ 时，任意两个不同facets的交都是维数 $m-2$ 的ridge。对每条原边 $E=[p,q]$ 及端点 $p$，有准确等价

$$
E=\{p\}\vee(E\cap D_p)
\quad\Longleftrightarrow\quad q\in D_p.
\tag{VII97.7}
$$

因而VI90.10的全部接触义务，在本有限分支正是要求( VII97.7 )左边对全部顶点—边区间成立，即这些秩二区间上的正交模律。它是原接触要求的同强改写。

证明。直接复用VII96.3中有限 $\mathrm B$ 的论证：整个二态最小面只能是一维球，故每两个不同原顶点的join都是它们之间的整条边。对不同 $p,q$，VII97.3给

$$
(\{p\}\vee\{q\})^\#=D_p\cap D_q,
\qquad \dim(D_p\cap D_q)=m-2.
\tag{VII97.8}
$$

VII97.2的双射使这覆盖所有不同facet对。对偶的两个顶点之间于是总有一条边；$m=1$ 时原基与对偶都是线段。

由于 $D_p$ 是不含 $p$ 的面，$E\cap D_p$ 只能是 $\varnothing$ 或 $\{q\}$。两种情况下( VII97.7 )左边的右端分别为 $\{p\}$ 或 $E$，得到等价。有限 $\mathrm B$ 又使 $H(p,q)=E$，其局部对径就是 $q$，所以这正是VI90.10的条件，没有另证这些交非空。若该全称条件成立，V88.3的共同零效应消灭每个 $p$ 以外的所有原顶点，V88.4遂给完整 $S$；反序对合本身没有给这项条件。

VII96.4的 $m\le5$ 单纯形结论及 $m=6$ 非单纯形时 $n=f\ge27$、$\nu\ge20$ 的必要界仍按原范围成立；$f=n$、完整facet配对和对偶二邻接性则由本章在任意有限维得到。这些必要结构不证明一般有限 $\mathrm B+\mathrm{Z0}$ 为单纯形，也不提供其非单纯形反例。证毕。

### 97.5 原单位下的实际slack与度量实现条件

**命题 97.5（零模式与数值极性的分界）。** 在定理VII97.2的前件下，每个原纯点 $p$ 有唯一的 $h_p\in[0,u]$ 满足 $h_p(p)=1$ 且 $K\cap\ker h_p=D_p$。令

$$
T_{pq}=h_p(q),\qquad M_{qp}=h_p(q).
\tag{VII97.9}
$$

本处矩阵 $T_{pq}$ 只记规范facet效应的评价，不将它等同于VI89.1的下包络 $T_p(q)$。则 $M=T^{\mathsf T}$ 是同一个原锥 $C$ 的实际slack矩阵，行取原极射线 $\mathbb R_+q$，列取原对偶极射线 $\mathbb R_+h_p$，并且

$$
\operatorname{rank}T=m+1,\qquad T_{pp}=1,\qquad
0\le T_{pq}<1\ (p\ne q),\qquad
T_{pq}=0\ \Longleftrightarrow\ T_{qp}=0.
\tag{VII97.10}
$$

这个对称零模式与原面格正交补均不单独蕴含 $C$ 在某个正定内积下自对偶。

证明。V88.3给所需 $h_p$ 的存在；$D_p$ 为facet，消灭它的正泛函只有一条射线，$h_p(p)=1$ 给唯一归一化。若另一个纯 $q$ 也有 $h_p(q)=1$，则同一个原效应给 $D_p\subseteq D_q$，VII97.2迫使 $q=p$。纯点排除对称性给零模式对称。全部 $p$ 张成 $V$，全部facet法向 $h_p$ 张成 $V^*$，所以该评价矩阵的秩为 $\dim V=m+1$。这里始终用原 $u$ 归一化，没有改换基或效应区间。

将原尖、生成、多面体锥 $C\subset V\simeq\mathbb R^{m+1}$ 代入 Gouveia–Lourenço，*Self-dual polyhedral cones and their slack matrices*，[arXiv:2207.11747v2 Theorem 3.6](https://arxiv.org/html/2207.11747v2)，其成熟判据说明：存在正定自对偶内积，当且仅当这个实际 $M$ 经适当行置换及正列缩放成为PSD矩阵。VII97.2—97.3的配对只满足该文[§5](https://arxiv.org/html/2207.11747v2#S5)的strongly involutive组合条件，还没有供应数值对称化或PSD。以下VII97.6在同一原锥层面给出失败实例。

该文[Theorem 3.7](https://arxiv.org/html/2207.11747v2)使用基的射影等价；它不把换过归一超平面的基自动认作原 $K$。Jensen，*Self-Polar Polytopes*，[arXiv:1902.00784v1 Theorem 3.2](https://arxiv.org/html/1902.00784v1#S3.Thmtheorem2)的实现判据也先给定含原点于内部的全维多面体 $Q$、内积和正交变换 $U$，再要求全部顶点 $v,w$ 满足 $\langle Uv,w\rangle\le1$，并且每个facet的全部顶点同时在某个这样的线性函数上取等号。它不是从组合配对构造这个内积的定理。即使另得全锥自对偶，逐面自对偶、最小确认和正面投影也各有额外义务；VII97.10不将它们加入结论。证毕。

### 97.6 全混态零拼合而无正定自对偶的有理七边形

**命题 97.6（组合正交补不供应原锥的度量极性）。** 取 $V=\mathbb R^3$，坐标为 $(t,x,y)$，$u(t,x,y)=t$，并令

$$
\begin{gathered}
v_0=(10,0),\quad v_1=(6,8),\quad v_2=(-2,10),\quad
v_3=(-9,4),\\
v_4=(-9,-4),\quad v_5=(-2,-10),\quad v_6=(6,-8),\\
p_i=(1,v_i),\qquad C=\operatorname{cone}\{p_0,\ldots,p_6\},\qquad
K=C\cap\{u=1\}=\operatorname{conv}\{p_0,\ldots,p_6\}.
\end{gathered}
\tag{VII97.11}
$$

指标均模七，效应取整个原 $[0,u]_{C^*}$，混态取全部原 $K$。这是定义VI89.1的闭尖生成锥及严格正原单位，其全部纯点恰为所列七点；它满足全混态 $\mathrm{Z0}$，且

$$
D_{p_i}=Q_i:=[p_{i+3},p_{i+4}].
\tag{VII97.12}
$$

但不存在使同一个 $C$ 自对偶的正定内积。这个载体不满足 $\mathrm B$，因而不是VI89.12的反例，也不否定有限 $\mathrm B+\mathrm{Z0}$ 蕴含单纯形。

证明。对每条候选边定义齐次支撑泛函

$$
s_j(t,x,y)=\det\bigl(v_{j+1}-v_j,(x,y)-t v_j\bigr),
\qquad S_{jk}=s_j(p_k).
\tag{VII97.13}
$$

其精确矩阵为

$$
S=\begin{pmatrix}
0&0&56&136&168&136&64\\
56&0&0&62&126&160&128\\
142&62&0&0&56&140&174\\
152&120&56&0&0&56&120\\
142&174&140&56&0&0&62\\
56&128&160&126&62&0&0\\
0&64&136&168&136&56&0
\end{pmatrix}.
\tag{VII97.14}
$$

每一行恰在相邻两点取零，其余严格正，故这些恰是整凸七边形的全部边与顶点。其仿射维数为二，因而 $C$ 生成 $\mathbb R^3$；有限生成性给闭性，所有生成元的 $t=1$ 给尖性和 $u$ 在非零锥上的严格正性。各行最大值唯一出现的列依次为 $4,5,6,0,1,2,3$，所以

$$
h_i=\frac{s_{i+3}}{S_{i+3,i}}\in[0,u],\qquad
h_i(p_i)=1,\qquad K\cap\ker h_i=Q_i.
\tag{VII97.15}
$$

于是 $Q_i\subseteq D_{p_i}$。为证明反向，取任意原 proper 效应 $e$，满足 $e(p_i)=1$，置 $g=u-e$。在归一超平面上，$g$ 是非负且在 $p_i$ 取零的仿射函数。两条相邻支撑 $s_{i-1},s_i$ 是在 $p_i$ 取零的仿射函数空间的一组基；分别在 $p_{i+1}$、$p_{i-1}$ 评价给

$$
g=\alpha s_{i-1}+\beta s_i,\qquad \alpha,\beta\ge0.
\tag{VII97.16}
$$

这是该顶点的整个正法向锥，不是有限张效应的抽样。由( VII97.14 )，对每个 $j\notin\{i+3,i+4\}$，存在 $k\in\{i+3,i+4\}$ 使

$$
S_{i-1,j}<S_{i-1,k},\qquad S_{i,j}<S_{i,k}.
\tag{VII97.17}
$$

下表给出覆盖全部这些严格不等式的选择；表中下标均取 $0,\ldots,6$。

| $i$ | 可取 $k=i+3$ 的 $j$ | 可取 $k=i+4$ 的 $j$ |
| --- | --- | --- |
| $0$ | $0,1,2,6$ | $5$ |
| $1$ | $0,1,2,3$ | $6$ |
| $2$ | $1,2,3,4$ | $0$ |
| $3$ | $2,3,4,5$ | $1$ |
| $4$ | $2,3,4,5,6$ | $\varnothing$ |
| $5$ | $0,3,4,5,6$ | $\varnothing$ |
| $6$ | $0,1,5,6$ | $4$ |

若 $(\alpha,\beta)\ne(0,0)$，每个 $Q_i$ 外的顶点都被某个 $Q_i$ 端点在 $g$ 上严格超过，故 $g$ 的全部最大点均在 $Q_i$。对任意原混态 $x\in K$，若 $e(x)=0$，则 $g(x)=1$，而 $0\le g\le u$，所以 $x$ 是这个非零 $g$ 的最大点，必在 $Q_i$。$(\alpha,\beta)=(0,0)$ 时 $e=u$ 没有零点。因此 $D_{p_i}\subseteq Q_i$，证明( VII97.12 )。每个 $D_{p_i}$ 都是一条凸边，从而全体原混态的中点零拼合成立。

再设存在正定内积 $B$ 使原 $C$ 自对偶。其Riesz映射将原极射线双射到原对偶极射线，诱导一个面格反序同构 $\phi$：将 $p_i$ 送到 $B(p_i,\cdot)$ 的零边。它满足

$$
p_i\notin\phi(p_i),\qquad
p_i\in\phi(p_j)\ \Longleftrightarrow\ p_j\in\phi(p_i).
\tag{VII97.18}
$$

记 $L_j=[p_j,p_{j+1}]$。七边形的顶点邻接圈与对偶边邻接圈都是 $C_7$，所以任何面格反序同构在顶点上必形如

$$
\phi(p_i)=L_{a+\epsilon i},\qquad
a\in\mathbb Z/7\mathbb Z,\quad \epsilon\in\{1,-1\}.
\tag{VII97.19}
$$

若 $\epsilon=-1$，方程 $2i=a$ 在模七有解，使 $p_i\in L_{a-i}$，违反自非入射。若 $\epsilon=1$，交叉入射对称要求
$\{a,a+1\}=\{-a,-a-1\}$，故 $2a+1=0\pmod7$，即 $a=3$。所以唯一可能的配对是 $\phi(p_i)=Q_i$。这排除了通过另一种顶点—边配对取得内积的可能。

facet正法向只有一条射线，故 $B(p_i,\cdot)=\lambda_i h_i$，其中 $\lambda_i=B(p_i,p_i)>0$。写 $T_{ij}=h_i(p_j)$，内积对称性要求

$$
\lambda_iT_{ij}=\lambda_jT_{ji},\qquad
T_{01}T_{12}T_{20}=T_{10}T_{21}T_{02}.
\tag{VII97.20}
$$

但是( VII97.14—VII97.15 )给

$$
\begin{gathered}
(T_{01},T_{12},T_{20})=(15/19,70/87,7/20),\\
(T_{10},T_{21},T_{02})=(71/87,4/5,7/19),\\
T_{01}T_{12}T_{20}=\frac{245}{1102},\qquad
T_{10}T_{21}T_{02}=\frac{1988}{8265},\qquad
\frac{T_{01}T_{12}T_{20}}{T_{10}T_{21}T_{02}}=\frac{525}{568}\ne1.
\end{gathered}
\tag{VII97.21}
$$

故连正行缩放的数值对称化都不成立，更无上述正定内积；结合唯一配对，这也与VII97.5所引实际slack的PSD判据一致。所否定的是这个实际原锥的度量自对偶，不是七边形组合类型存在另一自对偶实现。

最后，$p_0,p_2$ 不相邻，包含它们的最小面是整个七边形 $K$，不是整欧氏球，故 $\mathrm B$ 失败。其边 $[p_0,p_1]$ 又有 $p_1\notin D_{p_0}=Q_0$，所以面格虽有VII97.3的正交补，却不满足VII97.7的秩二正交模律。该实例只证明删去 $\mathrm B$ 时这两条捷径均失败，不给 $\mathrm B+\mathrm{Z0}$ 的接触反例；已有正五边形在其原前件下的边界也不由此改判。这里的原载体、全效应排除集与有理三环障碍的组合采用 `repo-derived` 归属；度量slack与self-polar实现判据归VII97.5所引原文，不主张历史优先权。证毕。

## 追加锚（本行以下为增补区）

## 98. 任意纯点集的失败端点与横向共同纤维维数障碍

### 98.1 原全效应载体与整个二纯面的最小维数

**定义 98.1（原仿射方向及球尺度）。** 本章的VI89.x、VI90.x指[第六卷](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)，V88.x指[第五卷](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)，VII96.x—98.x指本卷。采用VI89.1—89.2的非零有限维实 $V$、闭尖生成凸锥 $C$、严格正原单位 $u$、整个紧基 $K=C\cap\{u=1\}$、全部纯点 $P=\operatorname{ext}K$、整个原效应区间 $[0,u]_{C^*}$ 及全称 $\mathrm B$。不要求 $P$ 有限或闭，不附加ROG、PSD表示、谱性、全局内积或 $\mathrm{Z0}$。记

$$
E=\ker u=\operatorname{lin}(K-K),\qquad m=\dim E=\dim\operatorname{aff}K.
\tag{VII98.1}
$$

生成性与 $K$ 的归一化给 $\operatorname{span}K=V$，故 $\operatorname{aff}K=\{u=1\}$，得到上述方向等式。$m=0$ 时 $K$ 是单点，$\mathrm A$ 的不同纯对量词为空；该分支不定义下列 $\delta$，其单点效应 $\alpha$ 由 $\alpha u$ 延拓。$m\ge1$ 时定义

$$
\delta=\min_{p,q\in P,\ p\ne q}\dim H(p,q),\qquad 1\le\delta\le m.
\tag{VII98.2}
$$

非单点紧凸集至少有两个纯点；这些维数构成 $\{1,\ldots,m\}$ 的非空子集，所以最小值存在且由某一纯对达到。这不是在 $P\times P$ 上对连续函数取极值，不用 $P$ 的紧性。

固定一个整个二纯最小面 $F$。由 $\mathrm B$ 选其内在球坐标

$$
F=c+B_F,\qquad W_F=\operatorname{lin}(F-F),\qquad
B_F=\{v\in W_F:|v|_F\le1\},\qquad d=\dim F\ge\delta.
\tag{VII98.3}
$$

$|\cdot|_F$ 只作用于 $W_F$，不延伸为 $E$ 上的指定内积。$\mathrm A(F)$ 指每个 $|n|_F=1$ 的原纯对径 $c+n,c-n$ 均能由同一张原 proper 效应分别取一和零；全部 $\mathrm A(F)$ 就是原 $\mathrm A$。

本章直接复用VI90.9的原基范数及其达到性。若 $\gamma$ 是 $K-K$ 在 $E$ 上的Minkowski泛函，则原质量归一化给

$$
\gamma(z)=\frac12\|z\|_C
 =\max_{e\in[0,u]}e(z)
 =\min\{t\ge0:z=t(a-b),\ a,b\in K\},\qquad z\in E.
\tag{VII98.4}
$$

$z=0$ 的最后一项按 $t=0$ 理解。系数 $1/2$ 来自 $u(z)=0$：最小正负锥分解的两侧质量相等；对偶式来自VI(90.17)的 $g=2e-u$。在同一个最优实现 $z=t(a-b)$、$t>0$ 上，取同一对偶极大点 $e$，有 $e(z)=t$，故

$$
e(a)=1,\qquad e(b)=0.
\tag{VII98.5}
$$

成熟来源为 Lami–Palazuelos–Winter，*Ultimate data hiding in quantum mechanics and beyond*，[arXiv:1703.03392v2 §II.1 Definition 1—2、Lemma 3](https://arxiv.org/html/1703.03392v2#S2.SS1)。其原假设正是有限维实闭尖生成锥、$u\in\operatorname{int}C^*$ 及全效应；此处严格正性在有限维闭锥上给同一内部条件。这里不采用其双系统或受限测量前提，(VII98.4)—(VII98.5)是VI90.9接口的同单位使用，不另计为新基范数定理。

### 98.2 任意失败对径的两个端点均混且在原面外

**引理 98.2（失败端点不能纯化）。** 在定义VII98.1下，取 $F$ 中任意纯对径 $p,r$。任意实现

$$
p-r=t(a-b),\qquad a,b\in K,\qquad 0<t<1
\tag{VII98.6}
$$

都满足 $a,b\notin F$ 且 $a,b\notin P$。这里不要求该实现最优。

证明。由(VII98.6)有同一个点

$$
z=\frac{p+tb}{1+t}=\frac{r+ta}{1+t}.
\tag{VII98.7}
$$

若 $a\in F$，右式给 $z\in F$，左式是 $p,b$ 的严格凸组合，面的性质遂给 $b\in F$。于是
$2=|p-r|_F=t|a-b|_F\le2t<2$，矛盾。若 $b\in F$，交换两式得到相同矛盾。因此两端都在 $F$ 外；这里没有先假定 $z\in F$。

若 $a$ 纯，则 $a\ne r$，因为 $r\in F$。令 $G=H(r,a)$，$\mathrm B$ 使 $G$ 为整个仿射球。(VII98.7)的右式在 $G$，左式及面性质给 $p,b\in G$。又因 $p,r$ 的中点是 $F$ 的相对内点，$H(p,r)=F$，所以 $F\subseteq G$，且 $F$ 是 $G$ 的面。严格凸球的非空真面只能是单点，而 $F$ 含不同的 $p,r$，故 $F=G$。这又使 $a,b\in F$，矛盾。交换 $p,r$ 与 $a,b$ 同样排除 $b$ 纯。证毕。

这项结论只针对 $t<1$ 的局部对径捷径；任意方向的最优差分端点不受此量词覆盖。后续维数见证还需在同一个 $F$ 中重新选方向，不能把它归给起初指定的每个失败方向或它的全部最优实现。

### 98.3 最大伸长与同差纤维的两层极点

**定理 98.3（B-only横向维数障碍）。** 在定义VII98.1下，若 $\mathrm A(F)$ 失败，则存在同一原球 $F$ 中重新选出的失败对径 $p_*,r_*$、同一对最优原端点 $a,b$、同一张原效应 $e$，以及包含 $a,b$ 的各自最小面 $G_+,G_-$，使

$$
\begin{gathered}
p_*-r_*=t_*(a-b),\qquad 0<t_*<1,\qquad
\gamma(p_*-r_*)=t_*,\qquad e(a)=1,\quad e(b)=0,\\
a\in\operatorname{ri}G_+,\qquad b\in\operatorname{ri}G_-,\qquad
L_\pm=\operatorname{lin}(G_\pm-G_\pm),\\
W_F\oplus L_+\oplus L_-\ \subseteq\ E,\qquad
\delta\le\dim G_\pm,\qquad
\dim G_++\dim G_-\le m-d.
\end{gathered}
\tag{VII98.8}
$$

同一 $e$ 在整个 $G_+$ 恒一、在整个 $G_-$ 恒零。特别是

$$
\mathrm A(F)\text{ 失败}\quad\Longrightarrow\quad m-d\ge2\delta.
\tag{VII98.9}
$$

证明。令

$$
Q=(K-K)\cap W_F,\qquad R=\max_{w\in Q}|w|_F.
\tag{VII98.10}
$$

$Q$ 是紧凸集，且含 $F-F=2B_F$。由VI90.9，原失败对径 $p,r$ 有最优(VII98.6)，故 $(p-r)/t\in Q$ 的长度为 $2/t>2$，于是 $R>2$。选一个达到 $R$ 的 $w$。平方欧氏范数严格凸：若 $w$ 是 $Q$ 中两个不同点的严格凸组合，则 $|w|_F^2$ 严格小于它们平方范数的加权和，后者至多为 $R^2$。所以 $w\in\operatorname{ext}Q$。

取非空紧凸纤维及其一个极点

$$
M_w=\{(x,y)\in K\times K:x-y=w\},\qquad
(a,b)\in\operatorname{ext}M_w.
\tag{VII98.11}
$$

因 $w\in K-K$，有 $\gamma(w)\le1$。若 $\gamma(w)<1$，(VII98.4)的最优实现将给 $w=s(x-y)$、$s<1$；于是 $w/s\in Q$ 且 $|w/s|_F>R$，矛盾。因此 $\gamma(w)=1$，(VII98.11)的这一端点对就是最优实现。定义

$$
p_*=c+\frac wR,\qquad r_*=c-\frac wR,\qquad
 t_*=\frac2R.
\tag{VII98.12}
$$

这两个点是 $F$ 的纯对径，也是整个 $K$ 的纯点，并且
$\gamma(p_*-r_*)=2/R=t_*<1$。由(VII98.4)—(VII98.5)取得同一张原 $e$ 饱和同一对 $a,b$。如果最初方向的最优系数为 $t$，还有 $t_*\le t$；这只说明重新选择的方向至少同样失败。VII98.2给所选 $a,b$ 均混且在 $F$ 外。

现在使用有限维凸集的最小面相对内点性质：每一点处于其最小面的相对内部，故对每个 $v_+\in L_+$、$v_-\in L_-$，存在共同的充分小 $\varepsilon>0$，使

$$
a\pm\varepsilon v_+\in G_+\subseteq K,\qquad
b\pm\varepsilon v_-\in G_-\subseteq K.
\tag{VII98.13}
$$

这是成熟的面与相对内部工具（参见 Rockafellar，*Convex Analysis*，§18）；不要求 $G_\pm$ 暴露或紧。其有限维理由是：在包含给定点的面内，若该点不在相对内部，相对支撑便给一个含该点的更小真面，与最小性矛盾。相对内部正给每个方向所需的双向小扰动。

设 $v_+-v_-\in W_F$。两组同步扰动的差都是 $Q$ 中的点，且

$$
w=\tfrac12\bigl(w+\varepsilon(v_+-v_-)\bigr)
  +\tfrac12\bigl(w-\varepsilon(v_+-v_-)\bigr).
\tag{VII98.14}
$$

第一层 $w\in\operatorname{ext}Q$ 迫使 $v_+-v_-=0$。此时两组端点仍在同一个 $M_w$；第二层 $(a,b)\in\operatorname{ext}M_w$ 又迫使 $v_+=v_-=0$。所以

$$
L_+\times L_-\longrightarrow E/W_F,\qquad
(v_+,v_-)\longmapsto[v_+-v_-]
\quad\text{是单射}.
\tag{VII98.15}
$$

将 $v_-$ 换成 $-v_-$，即得(VII98.8)的直和及维数上界。第一层单独只消去差分移动，仍容许共同平移；第二层在第一层之后才消去共同平移，两层不可互代。这是原 $K\times K$ 上的直接扰动，不借PSD的秩界。

还须得到两端的下界。整个紧凸 $K$ 的有限纯分解（有限维Minkowski定理，亦见 *Convex Analysis* §18）给 $a$ 为有限多个原纯点的正权凸组合，面性质使这些点全部在 $G_+$。因 $a$ 非纯，至少有两个不同的纯点 $s,t$ 出现。于是整个 $H(s,t)\subseteq G_+$，故 $\dim G_+\ge\dim H(s,t)\ge\delta$；$b$ 同理。这一步只用整个 $K$ 的分解，不对可能非闭的 $G_\pm$ 另用紧凸分解。

最后，$K\cap\{e=1\}$ 与 $K\cap\{e=0\}$ 是分别包含 $a,b$ 的暴露面，所以包含它们的最小面 $G_+,G_-$。同一个 $e$ 遂在两面恒一和恒零。所有端点、方向、扰动及效应属于同一实现，证毕。

### 98.4 严格维数域的原接触与全部局部效应延拓

**推论 98.4（严格横向界）。** 在定义VII98.1下，若

$$
m-d<2\delta,
\tag{VII98.16}
$$

则有

$$
(K-K)\cap W_F=F-F,\qquad \mathrm A(F),\qquad
\operatorname{res}_F:[0,u]_{C^*}\twoheadrightarrow[0,1]_{\operatorname{aff}(F)}.
\tag{VII98.17}
$$

特别地，$m\ge1$ 且 $m<3\delta$ 时全部 $\mathrm A$ 成立。不要求 $\mathrm{Z0}$ 或 $P$ 有限。

证明。VII98.3排除失败，故有 $\mathrm A(F)$。为明确整个截面，始终有 $F-F=2B_F\subseteq Q$。若 $Q$ 含长度大于二的 $w$，则 $p=c+w/|w|_F$、$r=c-w/|w|_F$ 满足
$p-r=(2/|w|_F)w$，由VI90.9得到同一 $F$ 中的失败对径，矛盾。因此 $Q=2B_F=F-F$。

事实上该截面等式与 $\mathrm A(F)$ 等价：等式使每个直径差的 $\gamma$ 等于一，VI90.9给全域排除；反向刚由长于二的向量构造失败。这里精确复用原基范数接口，不以局部球距离冒充原基范数。VI90.8再给全部局部 proper 效应逐一延拓。具体地，若球坐标中的 $h(c+s)=\alpha+\ell(s)$ 满足 $0\le h\le1$，令 $r=\|\ell\|_{F,*}\le\min(\alpha,1-\alpha)$。$r>0$ 时写 $\ell(s)=r\langle n,s\rangle_F$，取 $\mathrm A(F)$ 给出的原 $e_n$，其球上限制必为 $(1+\langle n,s\rangle_F)/2$，故

$$
\widetilde h=(\alpha-r)u+2r e_n+(1-\alpha-r)0\in[0,u],
\qquad \widetilde h|_F=h.
\tag{VII98.18}
$$

$r=0$ 时用 $\alpha u$。这是 $\forall F\ \forall h\ \exists\widetilde h$，不供应共同正线性右逆、滤子或实际菜单。

每个整个二纯球维数 $d\ge\delta$，所以 $m<3\delta$ 给 $m-d<2\delta$，逐面应用即得全部 $\mathrm A$。(VII98.16)只是充分条件；其失败不意味着 $\mathrm A(F)$ 失败。这里 $m-d$ 是原基内的仿射余维，与VI96的PSD环境实余维 $c$ 不同，不能互换。证毕。

### 98.5 临界等号只归约为三个原球的接触义务

**命题 98.5（临界三球归约及斜率边界）。** 若定义VII98.1中的 $F$ 失败且 $m-d=2\delta$，则VII98.3所选实现满足

$$
\dim G_+=\dim G_-=\delta,\qquad
G_\pm\text{ 均为整个原二纯球},\qquad
E=W_F\oplus W_{G_+}\oplus W_{G_-},
\tag{VII98.19}
$$

$a,b$ 分别在这两个球的相对内部，同一原 $e$ 在 $G_+,G_-$ 恒一、恒零。这些结论仍只要求 $\mathrm B$；它们没有证明临界接触不等式 $|a-b|_F\le2$。

证明。式(VII98.8)的上下界全取等号。其纯分解给某个整个 $H(s,t)\subseteq G_+$，维数至少 $\delta$，现在只能等于 $\dim G_+$。同维面不能真包含：其相对内部中的一点也是大面的相对内点，面性质遂迫使相等。因此 $G_+=H(s,t)$，是整个 $\delta$ 维球；$G_-$ 同理。直和维数为 $m$，故充满 $E$。相对内点与全脸饱和则来自VII98.3，不是额外的暴露性假设。

写 $e(c+s)=\alpha+L(s)$，$s\in W_F$。球上的零一界给

$$
\sigma:=\|L\|_{F,*}\le\min(\alpha,1-\alpha)\le\tfrac12,
\qquad L(a-b)=1,
\qquad 1\le\sigma|a-b|_F\le\tfrac12|a-b|_F.
\tag{VII98.20}
$$

所以它只给 $|a-b|_F\ge2$，方向恰与待证上界相反。即使 $\sigma=1/2$，也不反推 $|a-b|_F=2$；还须证明 $L(a-b)=\sigma|a-b|_F$ 的径向对齐。例如在欧氏二维空间，$L(x,y)=x/2$、$w=(2,1)$ 满足 $L(w)=1$、$\|L\|_*=1/2$，却有 $|w|=\sqrt5>2$。这个代数例子只否定该一步推理，不是满足整个 $\mathrm B+\mathrm{Z0}$ 的载体反例。

在(VII98.19)下，固定两个仿射空间 $\operatorname{aff}G_\pm$ 后，条件 $a-b\in W_F$ 至多确定一对端点：两对解之差进入(VII98.15)的核。维数相等又使该商映射为线性同构，故仿射空间层面的解恰有一对，但它是否在两个球的相对内部、其差的长度是否不超过二，仍需另证。

因此本章保留的临界问题是：在整个原 $\mathrm B+\mathrm{Z0}$ 载体中，对全部具有(VII98.19)、共同饱和效应以及相对内部横截端点的配置，是否总有 $|a-b|_F\le2$？若这个全称命题成立，才能把局部严格界扩为 $m-d\le2\delta$、全局扩为 $m\le3\delta$；若证明使用 $\mathrm{Z0}$，这两个等号版也必须保留 $\mathrm{Z0}$。相反，整个原 $\mathrm B+\mathrm{Z0}$ 模型中的一个此类 $|a-b|_F>2$ 实现，将由式(VII98.12)及同一 $e$ 给出VI89.12的真反例。仅有有限个纯分解项或三个球的抽取配置，不代付整个原模型的 $\mathrm B$、混态 $\mathrm{Z0}$。证毕。

### 98.6 正维球形facet给整个原基的棱锥及全部A

**定理 98.6（球形facet的全基加强）。** 在定义VII98.1及 $m\ge2$ 下，若 $K$ 有一个正维球形facet $F$，则存在唯一的 $s\in P\setminus F$，使

$$
K=\operatorname{conv}(F\cup\{s\}),\qquad
P=\operatorname{ext}F\cup\{s\},\qquad \mathrm A.
\tag{VII98.21}
$$

这里 $P$ 可无限，不要求 $\mathrm{Z0}$。正维球形面中任意两不同纯点的中点在其相对内部，故该面本身就是它们的整个最小面。VII98.4已由 $m-\dim F=1<2\delta$ 给 $\mathrm A(F)$；本条进一步给全部原基及其他二纯面的结构。

证明。先在推导内使用标准支撑包含事实（有限维相对支撑定理，见 Rockafellar，*Convex Analysis*，§11、§18）：任意非空真面 $G$ 都包含于某个真暴露面，不要求 $G$ 自身暴露。具体地，取 $z\in\operatorname{ri}G$。若 $z\in\operatorname{ri}K$，则对任意 $y\in K$ 可沿 $z-y$ 小幅延长，面性质迫使 $y\in G$，与 $G$ 真矛盾。故 $z\in\operatorname{rbd}K$，相对支撑给在 $K$ 非负、在 $z$ 为零且在 $\operatorname{aff}K$ 非恒定的仿射 $h$。对任意 $y\in G$，相对内点性质给 $z+\varepsilon(z-y)\in G$；非负性和该严格凸组合迫使 $h(y)=0$。所以 $G\subseteq K\cap\{h=0\}\subsetneq K$。此论证也不要求 $G$ 闭。

对facet $F$，包含它的这个真暴露面与 $F$ 同维，故等于 $F$。可取仿射坐标

$$
F=\{(x,0):x\in\mathbb R^{m-1},\ |x|\le1\},\qquad
K\subseteq\{t\ge0\},\qquad K\cap\{t=0\}=F.
\tag{VII98.22}
$$

整个 $K=\operatorname{conv}P$ 的有限纯分解及 $\dim K=m$ 保证存在外部纯点 $s=(a,b)$，$b>0$。对每个单位 $v\in\mathbb R^{m-1}$，$p_v=(v,0)$ 是原纯点。$\mathrm B$ 使 $G=H(p_v,s)$ 为球。若 $G=K$，则 $K$ 是维数 $m\ge2$ 的严格凸球，不可能有正维真面 $F$，故 $G$ 真。用上面的支撑包含事实，取在整个 $G$ 上取等号的真支撑

$$
w\cdot x+\eta t\le c_0\quad\text{于 }K,
\qquad w\cdot v=c_0=w\cdot a+\eta b.
\tag{VII98.23}
$$

$w=0$ 将使 $c_0=\eta=0$，与支撑非恒定矛盾。限制到整个底球得 $c_0=|w|>0$ 且 $w=|w|v$；除以正数 $|w|$，得到

$$
v\cdot x+\frac{1-v\cdot a}{b}\,t\le1.
\tag{VII98.24}
$$

逐个单位 $v$ 取上确界，得

$$
\left|x-\frac tb a\right|\le1-\frac tb.
\tag{VII98.25}
$$

设 $\theta=t/b$。由 $t\ge0$ 和右边非负知 $0\le\theta\le1$。$\theta<1$ 时，$y=(x-\theta a)/(1-\theta)$ 在单位底球，故 $(x,t)=(1-\theta)(y,0)+\theta s$；$\theta=1$ 时只有 $s$。凸性给反向包含，证明整个棱锥等式。中间高度的点均非纯，底部纯点恰为 $\operatorname{ext}F$，所以外部纯点也唯一。

两个不同底球纯点的中点在 $\operatorname{ri}F$，故其整个最小面为 $F$；(VII98.24)在底球上的等号点只有 $p_v$，故在棱锥上的等号集恰为 $[p_v,s]$，其整个最小面正是这条边。这穷尽了全部不同原纯对。

还可显式延拓原效应。对底球上任意 $h(x)=\alpha+q\cdot x\in[0,1]$ 和任意指定顶点值 $\zeta\in[0,1]$，令

$$
\widetilde h(x,t)=\alpha+q\cdot x+
\frac{\zeta-\alpha-q\cdot a}{b}\,t.
\tag{VII98.26}
$$

它在 $(1-\theta)(y,0)+\theta s$ 上等于 $(1-\theta)h(y)+\theta\zeta$，所以在整个 $K$ 上取值于 $[0,1]$。底球对径用 $h(x)=(1+n\cdot x)/2$ 区分，顶点边的两个端点用 $t/b$ 及其补区分，故全部 $\mathrm A$ 成立。这些仿射效应由 $\operatorname{aff}K=\{u=1\}$ 唯一齐次线性延伸到原 $V$；原 $C=\mathbb R_+K$ 上的零一界正给 $0\le\widetilde h\le u$。没有用局部球效应替代原全效应。证毕。

### 98.7 不限制纯点总数的三维以内全分支

**推论 98.7（低仿射维的B-only结论）。** 在VI89.1—89.2的原全效应域内，$m\le3$ 时 $\mathrm B\Rightarrow\mathrm A$，不要求 $P$ 有限或 $\mathrm{Z0}$。

证明。$m=0$ 按VII98.1的单点约定；$m=1$ 时整个基是非退化闭线段，两个原重心坐标效应区分端点。对 $m=2,3$，若某个 $H(p,q)$ 维数为 $m$，它与 $K$ 同维，故等于 $K$；$\mathrm B$ 使整个基为球，标准球效应给全部 $\mathrm A$。若 $m=3$ 且某个 $H(p,q)$ 为二维，它是正维球形facet，应用VII98.6。

剩下情形的每个二纯最小面均为一维球，即 $H(p,q)=[p,q]$；这些整段都是 $K$ 的面。若 $|P|\ge m+2$，从整个 $P$ 中取 $m+2$ 个不同纯点。有限维Radon划分给两个不交非空指标集及同一个点

$$
z=\sum_{i\in I}\lambda_i p_i=\sum_{j\in J}\mu_jp_j,\qquad
\lambda_i,\mu_j>0,\qquad\sum_I\lambda_i=\sum_J\mu_j=1,
\qquad |I|+|J|\le m+2\le5.
\tag{VII98.27}
$$

这里的成熟Radon步骤可直接由这些点的仿射相关式得到：非零相关系数总和为零，正负两侧分别归一，零系数删去。因此较小一侧至多有两点。若只有一点，它被表示为其他不同纯点的凸组合，违反极端性；若有两点 $p,q$，则 $z\in(p,q)$，整段 $[p,q]$ 的面性质迫使另一侧所有正权纯点都在该段内，但 $P\cap[p,q]=\{p,q\}$，与指标不交矛盾。故 $|P|\le m+1$。整个 $K=\operatorname{conv}P$ 及维数又迫使恰有 $m+1$ 个仿射独立顶点，原基为单纯形，其原重心坐标效应给 $\mathrm A$。

以上所有分支先从任意 $P$ 出发，只有最后一支才推出它有限。它不重做VII96的有限 $P$、$m\le5$ 或 $\nu\le8$ 结论，也不把这两个有限范围推广到无限 $P$。若 $\mathrm B+\neg\mathrm A$ 的整个载体存在，则必须 $m\ge4$，且不能有正维球形facet；高维其余载体仍不由本推论判定。证毕。

### 98.8 保留混态Z0的完整旧消费者

**定理 98.8（维数域内的同原数据几何替换）。** 完整保留VI89.7的原装饰元组 $\mathcal O$、共同合同 $\mathfrak S(\mathcal O)$ 及VI89.8—89.10的所有非几何条件。对选定的任意子集 $J\subseteq\{A,D,E\}$，只要求其中每个原载体 $X$ 满足下列已限定适用域之一：单点；$m_X\ge1$ 且 $m_X<3\delta_X$；$1\le m_X\le3$；或具有正维球形facet。则可把这些 $X$ 上的原 $\mathrm B_X+\mathrm{Boundary}_X$ 等价替换为

$$
\mathrm B_X+\mathrm{Z0}_X,
\tag{VII98.28}
$$

其余 $X$ 的原几何条件不动。每个 $\mathrm{Z0}_X$ 的两被排除端点仍遍历全部原混态；不以纯纯零条件替代。所得完整包与VI(89.14)的全部既有完整包在这一固定适用域内同数据等价。

证明。VII98.4、98.6、98.7及单点约定在所列域内由 $\mathrm B_X$ 给全部 $\mathrm A_X$。下一步准确使用的旧桥是

$$
\boxed{\mathrm{Z0}+\mathrm B+\mathrm A
\quad\Longleftrightarrow\quad\mathrm B+\mathrm H
\quad\Longleftrightarrow\quad S.}
\tag{VII98.29}
$$

具体地，V88.3的完整混态 $\mathrm{Z0}$ 给每个原纯 $p$ 一个共同 proper 效应，其零集恰为 $D_p$。$\mathrm A$ 使所有经过 $p$ 的原球对径都在这个同一零集中，故有 $\mathrm H$；V88.4、V88.10及VI89.4再给完整 $S$、$\mathrm{Boundary}$ 和 $\mathrm Q$。反向，$S$ 给 $\mathrm B+\mathrm H$ 与全部 $\mathrm A$，其least效应又使 $D_p$ 是同一非负效应的零面，从而给全混态 $\mathrm{Z0}$。不能把(VII98.29)缩成裸 $\mathrm B+\mathrm A\Rightarrow S$。

替换仅供应几何项；VI89.7的下列原数据与量词全部保留。原概率像 $K_X=\{k_\sigma\}$ 自身紧、非空、有限仿射维，单位为一，所有中点在原标签中实现，不先补闭包或凸包；原测试像自身闭、含零和单位、闭于中点、补及有界倍增，且每张表由同一个原测试对全部原准备实现。正带质量输出保留每个原中点实现（含重复标签），所有非负输入质量的原缩放仍含零、次归一及不等质量；其他过程和参考的下降仅在原已供应的全部联合输入域及闭尖输出锥上使用，不能以边缘或乘积输入代付全部相关联合。

原实双线性 $L:D\times A\to E$、原实线性读回 $p:E\to D$、$\omega=1_D/m$ 及派生 $K,M,J,H,B_1,U,G,Q$ 仍按VI89.7和87.12的原定义，特别是 $K(a)=pL(\omega,a)$、$M(a,b)=pL(K(a),b)$ 使用同一个原 $p$ 两次。两实张成、全部实 $a,b$ 上的 $Z:B_1M(a,b)=\tau_A(a)Jb$、含秩一分支的完整(83.8)、原迹／伴随／二次表示／单位、VI(89.13)的全部两尺度等式、C2及整个 $G=1_E$ 逐项保留；总迹或一个标量锚不能代替整个输出条件。精确 PRE 之后的原 H13 仍消费同一原资格态、原 $I^{\rm raw}$ 和整个输出，保留所有活跃块、严格负方向、共享总迹一、零质量和空活跃集，不逐块换态或由输出反选资格。

共同 $\mathfrak S$ 仍含准备和测试的设备／事件／来源绑定出现、全部菜单、过程和分支、实际参考、副本及相关联合、记录、权限、控制、钟及单位、ready／flags、失败／拒绝／停止／销毁／返回、所有质量、全部合法未来、旧固定支撑和每个中间切口，以及原实际混合服务。数学上的逐效应延拓不生成实际准备、测试、服务、资源或有限认证。于是VI89.8可直接按同一 $\mathcal O$ 应用，得到完整等价，证毕。

**推论 98.9（逐消费者与原生来源的范围）。** 在VII98.8和每个旧消费者自身的完整前件下，VI89.9的消费者保持如下准确范围。

| 旧消费者 | 仍需的原条件与所得范围 |
| --- | --- |
| 复型及Born | 一般EJA忠实桥与同一原精确两接口66.3；之后才得有限复Hermitian直和、整个密度基和全效应及 $\sum_i\operatorname{Tr}(f_i\rho_i)$，保留跨块零和不等中心质量。新维数条件不选择复型。 |
| 指定二份／三份及读回 | 同一 $L,p$、两次原读回、两实张成、全实 $Z$、完整(83.8)、C2、整个 $G=1_E$ 与PRE后的同一原H13；才得原指定 $M,L,p,p_{13}$ 的张量／偏迹形式，覆盖全部相关及纠缠锥，不扩到另一括号、更高份数或无限维。 |
| 指定CP事件及分支 | 同事件原实线性 $\Phi_e$、唯一复HP延拓及原 $P_{E,e}$，全实(87.21)、原非负腿权和全部复矩阵核包含条件，以及每输入块实际指定纯探针 $\psi_i$；保留零腿权、不等维、记录、ready、参考、副本、控制、钟和未来。HP提升全锥正性仍是被认证结论，不能预先假定。已有82.5完整递归参考路线按原类型直接复用。 |
| Kraus及实际仪器 | 逐块CP后才有成熟矩形Kraus表示；实际分支、typed输入输出、真实参考、旁观者、全部菜单、记录、顺序接线、同族真粗粒化、共同重置输入行一致及87.23两预算均保留。完整实际菜单总TP才给完备和，次单位仅给TNI，不由矩阵表示生成环境或独立调用。 |
| 条件态与Lüders | 原输入／分支质量、零分支和全部未来保持原域，只在正质量时归一；Lüders另需同一CP分支的锐投影效应、全部确定接受态逐点中性和原输出校准。同效应和同概率不决定更新。 |
| 物理时间 | 原物理时间上的连续、齐次、可逆 $*$ 自同构群、实际逆、原钟、单位及动态来源；有限块Hamiltonian形式按该域取得，无限维正常性、生成元域和收敛仍须另付。 |

证明。VII98.8只把几何输入还原为VI89.8的原完整包，表中结论逐项直接调用VI89.9，未删去任何消费者前件。对VI89.10的原生路线，也完整保留同一 $89$ 路径、$26+63$ 嵌入、原射影几何与密度、唯一ready、全部十一地址原有限字及terminal futures、原矩阵次序和资源合同。旧有限秩入口、无独立容量的全未来 $\mathrm R_{10}+\mathrm{UR}$ 与四前缀行关系入口、完整联合菜单入口，以及非恒定粗Born加全有符号关系／同秩的细化入口，均按各自原条件复用；数学完成点、full proper和共同POVM不自动有实际来源或仪器。

[原生来源续卷VII](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md)第33—34章在其指定完整双列类上供应的 $\mathrm H_8,\mathrm H_3$ 联合闭包及支撑／十维压缩必要界亦直接复用，不重列为缺失。该卷第35章对(32.3)指定正候选的当前ready／代码校准与固定future破坏全未来ready回返同时成立；它不判定(32.4)的原全字精确细零蕴涵，也不否定整个指定双列类。新维数域没有供应这些来源律或把该必要界改成充分条件。

若把完成行对象用于原 $A,D,E$，仍需该续卷VII20.2的 source-adoption map、87章全部原像和效应及共同来源合同。原1024细标签（含零、失败等原类型）、原粗归组、旧校准与支撑、全部历史和未来、实际参考与资源均按VI89.10保留；记录插入后的原七地址条件未来仍消费其完整原合同。同秩入口中已经导出的联合下降和回返无需重付，但不能把仅当前ready或固定future的后果替代全未来条件。本章不从几何增量生成复结构、原source、细Born、指定复合、CP、仪器、更新或时间。证毕。

### 98.9 组合归属与尚存的原接触域

**命题 98.10（严格障碍的适用边界）。** VII98.2—98.4的新增组合，是原 $\mathrm B$ 的失败端点限制与差集截面／共同纤维两层极点共同给出 $W_F\oplus L_+\oplus L_-$，再用整个 $K$ 的有限纯分解把两端维数各压到至少 $\delta$。VII98.5保留临界接触缺口；VII98.6—98.7是标准支撑、球严格凸性与Radon方法在相同原全效应问题中的几何加强；VII98.8—98.9仅在保留完整混态 $\mathrm{Z0}$ 和全部原数据后回接旧消费者。

证明与归属。基范数、同一饱和效应和逐效应延拓归VI90.8—90.9及所引LPW；最小面、相对内部、紧凸分解、支撑与Radon划分是上述推导内明用的成熟凸几何步骤。新增资格不归一般维数计数本身，也不借PSD的Pataki秩定理。VI93—94的ROG分类、VI96—97的环境低余维／实低支撑结果、VII96的 $\nu\le8$ 与有限 $m\le5$ 排除及 $m=6$ 的 $n=f\ge27$、$\nu\ge20$ 必要界、VII97的有限面格与度量障碍均按原域复用，不重报为新增。上述原问题内的组合采用 `repo-derived` 归属，不主张全球原创、文献穷尽或一般开放状态认证。

本章没有证明VII98.5的临界接触上界，因而没有给 $\mathrm B$ 下的 $m\le3\delta$ 一般等号版，也没有给整个 $P$ 任意有限时的单纯形结论。无限 $P$ 或高维剩余域中，若未落入本章充分条件，仍须证明全部VI90.10接触，或构造同时满足全称 $\mathrm B$、全混态 $\mathrm{Z0}$ 而失败 $\mathrm A/\mathrm H$ 的整个原载体。一般VI89.12及完整量子起源问题不由这些局部增量解决；有限纯分解见证也不把整个 $P$ 变成有限集。证毕。

## 追加锚（本行以下为增补区）

## 99. 四维共同排除面覆盖、圆盘联结与精确零拼合缺口

### 99.1 同一个原凸体与四维问题

**定义 99.1（全效应的四维域）。** 使用VI89.1的同一个非零有限维实空间 $V$、闭尖生成锥 $C$、严格正原单位 $u$、整个紧基 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$ 和全部原 proper 效应。记

$$
\begin{gathered}
E=\operatorname{lin}(K-K),\qquad m=\dim E,\qquad
F_p=\{f\in[0,u]_{C^*}:f(p)=1\},\\
T_p(x)=\min_{f\in F_p}f(x),\qquad
p\perp x\ \Longleftrightarrow\ T_p(x)=0,\qquad
D_p=\{x\in K:p\perp x\}.
\end{gathered}
\tag{VII99.1}
$$

$\mathrm B,\mathrm{Z0},\mathrm A,\mathrm H,S$ 准确取V88.1—88.4、VI89.1—89.4的原定义。特别是，$\mathrm B$ 管每个不同原纯对的整个最小面 $H(p,q)$；$\mathrm{Z0}$ 管每个原纯 $p$ 和全部原混态 $x,y$ 的零排除中点，不只管纯端点。除99.2的通维引理外，本章分类取 $m=4$；此 $m$ 不是ROG矩阵环境的余维 $c$。不对 $P$ 加有限、闭、可数或光滑前件，不给 $C$ 预付矩阵表示、ROG、谱性、自对偶或内积。

$\mathbb B^d$ 表示闭欧氏单位球的仿射类型，$\Delta_j$ 表示 $j$ 维单纯形，$*$ 表示仿射联结：两因子置于仿射独立的位置，其凸包为联结，维数为两因子维数之和再加一。二维球形真面称为圆盘面，包含其整个内部；其圆周才是纯点集。球坐标中的长度只在对应的球面方向空间使用，不成为原 $V$ 上的额外结构。

### 99.2 零面与共同排除面的覆盖

**引理 99.2（原纯点指标的共同排除覆盖）。** 在任意有限 $m\ge1$ 下，$\mathrm{Z0}$ 使每个非空 $D_p$ 为一张原效应的整个零面。若另有 $\mathrm B$ 且整个 $K$ 不是球，则对每个 $p\in P$，

$$
D_p\ne\varnothing,\qquad
P\subseteq\bigcup_{r\in\operatorname{ext}D_p}D_r.
\tag{VII99.2}
$$

每个指标 $r$ 都是原 $K$ 的纯点；每张 $D_r$ 都取在整个原 $K$ 上。

证明。先复用V88.3的紧性与相对内点论证。原全效应区间在从 $K$ 选出的线性基上取值有界，且为闭集，故紧；$F_p$ 非空紧，最小值达到。$D_p$ 是紧集 $\{(f,x)\in F_p\times K:f(x)=0\}$ 的投影。$\mathrm{Z0}$ 给中点凸，紧性给凸。非空时取 $z\in\operatorname{ri}D_p$ 及一张 $f\in F_p$，使 $f(z)=0$。对任意 $x\in D_p$，相对内点性把 $z$ 写成 $x$ 与另一个 $D_p$ 中点的严格凸组合；$f\ge0$ 迫使 $f(x)=0$。反向包含直接来自定义，所以

$$
D_p=K\cap\{f=0\},\qquad p\notin D_p.
\tag{VII99.3}
$$

这只给共同零面，尚未宣布 $f$ 为least确认。

给定 $q\in P\setminus\{p\}$，$\mathrm B$ 使 $H(p,q)$ 为球；因 $K$ 本身不是球，此面为真面。VII98.6证明内的支撑包含事实给一张非恒定仿射支撑，使整个 $H(p,q)$ 包含于其最大值面。将该函数按其在整个 $K$ 上的最小、最大值归一化，得到原效应 $h$，满足

$$
h(p)=h(q)=1,\qquad \min_Kh=0.
\tag{VII99.4}
$$

在非空紧零面 $K\cap\{h=0\}$ 取一个极点 $r$。零面是 $K$ 的面，故 $r\in P$；同一张 $h$ 给 $r\in D_p$。又因 $D_p$ 是面，$r\in\operatorname{ext}D_p$。补效应 $u-h$ 同时确认 $r$ 并排除 $p,q$，故 $p,q\in D_r$。这里的纯排除对称性只用同一 proper 效应取补，没有借用非零 $T$ 值互反。

$q=p$ 时，不调用不同纯对的 $\mathrm B$：在原边界点 $p$ 取任一非恒定支撑，归一化后仍有 $h(p)=1$、$\min_Kh=0$，按同样方式取零面中的原纯点 $r$。这同时证明 $D_p$ 非空并覆盖 $p$。所以(VII99.2)成立。证毕。

**推论 99.3（整个零球面与极大真球面的原A）。** 在 $\mathrm B+\mathrm{Z0}$ 下，若一个整个二纯球 $F$ 满足 $F=D_s$、$s\in P$，则 $\mathrm A(F)$ 成立。特别是，每个同时为极大真面的整个二纯球都满足原 $\mathrm A(F)$。

证明。若整个 $K$ 是球，标准球效应已给 $\mathrm A$。否则对任意 $p\in\operatorname{ext}F$，将(VII99.2)用于 $s$ 和被覆盖点 $p$，取得 $r\in\operatorname{ext}D_s=\operatorname{ext}F$，使 $p\in D_r$。补效应给一张原 $f\in F_p$，满足 $f(r)=0$。球上的非恒定仿射效应在纯点取一和零时，这两个点必为对径：在单位球坐标中，若 $f(x)=a+b\cdot x$，则 $\|b\|\le a\le1-\|b\|$，两端取一、零迫使 $a=\|b\|=1/2$，取等点相反。因此 $r$ 正是 $p$ 在 $F$ 内的对径，见证效应已在整个原 $K$ 上。

若 $F$ 为极大真面，先用支撑包含事实取得 $F$ 的真暴露包；极大性使这个包等于 $F$。将其支撑效应取成在 $F$ 恒零、在某个原纯点 $s$ 取一，得到 $F\subseteq D_s\subsetneq K$。由(VII99.3)及极大性，$D_s=F$，归入前一情形。证毕。

### 99.3 排除球与球facet后的全部真面

**引理 99.4（四维剩余分支的真面类型）。** 设 $m=4$ 且有 $\mathrm B$。先分出整个 $K$ 为球的分支；若 $K$ 有三维球形facet，VII98.6给 $K=\mathbb B^3*\Delta_0$。在余下分支，每个非空真面都是下列类型之一：单纯形、圆盘、圆盘上的三维棱锥。因此每个真面至多含一张圆盘面；不含圆盘面的真面只有有限多个原纯点。任意两个原纯点都包含于某个真支撑面，同点也有非恒定支撑。

证明。一个面中的纯点也是原纯点，面中的二纯最小面等于原二纯最小面，故继承 $\mathrm B$。为准确使用VII98.7的紧凸前件，先把任意非空真面 $Q$ 放入VII98.6证明所给的真暴露面 $M$。$M$ 紧，维数至多三，并继承 $\mathrm B$。直接消费VII98.7的各分类分支：$M$ 是单纯形、整球，或三维圆盘棱锥。不再重证其低维Radon／边图步骤。三维整球就是已分出的球facet；二维整球是圆盘；低于二维的球为单点或线段，已在单纯形中。

这些紧模型的面分别是子单纯形；球自身与单点；以及底圆盘、以一个底部纯点和外顶点组成的边、单点和整个棱锥。由于 $Q$ 是 $M$ 的面，$Q$ 自身亦在所列类型内，特别也为紧面。这避免了对一般真面的闭性作未经证明的假定。圆盘棱锥恰有一张圆盘面，其余真面不含圆盘；其盘外只有一个纯顶点。最后，非球的 $K$ 中每个 $H(p,q)$ 都是真面，支撑包含事实给公共真支撑面；$p=q$ 时直接在该边界点取支撑。证毕。

### 99.4 两圆盘的互补方向、唯一交点与零拼合矛盾

**引理 99.5（B下两圆盘的四维支撑锥）。** 在引理99.4的剩余分支中，若有两张不同圆盘面 $F,G$，记其方向平面为 $W_F,W_G$，则

$$
E=W_F\oplus W_G,\qquad F\cap G=\{z\},\qquad z\in P.
\tag{VII99.5}
$$

存在非恒定仿射支撑 $h_F,h_G\ge0$ 于整个 $K$，分别在整个 $F,G$ 恒零，且

$$
\{h\in\operatorname{Aff}(K):h\ge0,\ h(z)=0\}
=\mathbb R_+h_F+\mathbb R_+h_G.
\tag{VII99.6}
$$

这两个原面之外不存在第三张圆盘面。以上结论尚未使用 $\mathrm{Z0}$，也没有断言仅靠 $\mathrm B$ 已排除两盘。

证明。假设有 $0\ne d\in W_F\cap W_G$。在 $F$ 上选沿 $+d$ 的半径端点 $p$，在 $G$ 上选沿 $-d$ 的半径端点 $q$。这两个端点都是原纯点。若 $p\ne q$，引理99.4给在两点为零、于整个 $K$ 非负的非恒定支撑 $h$；若 $p=q$，直接在这个原边界点取这样的非恒定支撑，不使用不同纯对的 $\mathrm B$。

在圆盘上，一个非负仿射函数于圆周点为零，要么恒零，要么为该点切向函数的严格正倍数。写 $p=c_F+ad$、$q=c_G-bd$，$a,b>0$。$h$ 在 $F$ 的限制给沿 $d$ 的导数非正，且非零限制时严格负；在 $G$ 的限制给该导数非负，且非零限制时严格正。导数是同一全局线性部分在同一 $d$ 上的值，故两限制只能都恒零。于是非恒定 $h$ 的整个零面同时含两盘，违反引理99.4。故方向交为零，维数之和为四，得到 $E=W_F\oplus W_G$。

两仿射平面因而交于唯一点 $z$。若 $z\notin F$，在 $F$ 的单位球图中选圆周点 $p_v$，使其非负切向函数

$$
\tau_F(w)=1-v\cdot w
\quad\text{满足}\quad \tau_F(z)<0.
\tag{VII99.7}
$$

此处把 $\tau_F$ 仿射延伸到 $\operatorname{aff}F$，因为 $z$ 在盘外，这样的 $v$ 存在。在 $G$ 的单位球图中，另选圆周点 $q_w$，使其切向函数 $\tau_G$ 满足 $\tau_G(z)>0$；例如令 $w$ 与 $z$ 相对该盘球心的坐标内积非正即可。两点不同，否则它们必须等于仿射平面的交点 $z$，而 $p_v\in F$。

取两点的公共非恒定非负支撑 $h$。其盘上限制分别为 $a\tau_F,b\tau_G$，$a,b\ge0$，包括零限制。由于在同一个仿射交点取值相同，

$$
a\tau_F(z)=h(z)=b\tau_G(z)
\tag{VII99.8}
$$

的两侧一非正、一非负，且相应切向值严格异号，只能 $a=b=0$。又产生含两盘的真零面，矛盾。故 $z\in F$；交换两盘得 $z\in G$。两面的单点交集是原面，所以 $z\in P$，并且在两盘的圆周上。

取包含 $F$ 的真支撑零面，记支撑为 $h_F\ge0$；同理取 $h_G\ge0$。若 $h_F$ 在 $G$ 也恒零，就有含两盘的真面，故其 $G$ 上限制非零，是 $z$ 处切向函数的正倍数；$h_G$ 在 $F$ 的限制同理。任取 $h\ge0$、$h(z)=0$，其 $F,G$ 上限制分别为对应切向函数的非负倍数。因此有 $a,b\ge0$，使 $h$ 与 $ah_F+bh_G$ 在两张完整仿射平面上的限制相同。两平面在 $z$ 相交且方向互补，故这些限制唯一确定 $\operatorname{aff}K$ 上的仿射函数，得到(VII99.6)。反向包含由两支撑的非负性直接成立。这一步准确使用四维方向互补，不能外推到更高维。

令

$$
M_F=K\cap\{h_F=0\},\qquad M_G=K\cap\{h_G=0\}.
\tag{VII99.9}
$$

对任意 $q\in P\setminus\{z\}$，取过 $q,z$ 的非恒定非负支撑。由(VII99.6)，它是两生成元的非负组合，至少一个系数为正；在 $q$ 取零迫使对应生成元也取零。$z$ 则属于两个零面。因此

$$
P\subseteq M_F\cup M_G.
\tag{VII99.10}
$$

若有第三张圆盘 $J$，$M_F$ 不能包含 $J$，否则它同时包含 $F,J$，违反引理99.4；$M_G$ 同理。非负仿射函数限制到圆盘，若不恒零，零集至多含一个圆周纯点。于是 $M_F\cup M_G$ 至多覆盖 $J$ 的两个圆周点，不能满足(VII99.10)。不存在第三张圆盘。证毕。

**定理 99.6（全混态零拼合排除两圆盘共存）。** 在引理99.4的剩余分支及完整 $\mathrm{Z0}$ 下，圆盘面至多有一张。

证明。若有不同圆盘 $F,G$，引理99.5给唯一原纯交点 $z$，并排除第三盘。在 $F$ 的圆周上选 $p$，避开 $z$ 以及 $z$ 的盘内对径点。限制任一原效应到整个 $F$，推论99.3证明中的球效应计算表明：$f(p)=1,f(z)=0$ 只能在两点对径时成立。因此 $z\notin D_p$。

$D_p$ 是真面，既不含 $F$（因为不含 $p$），也不含 $G$（因为不含 $z$）。又没有第三张圆盘，故由引理99.4，$D_p$ 只有有限多个纯点。将(VII99.2)用于整个 $G$ 的圆周。对每个 $r\in\operatorname{ext}D_p$，补效应给 $p\in D_r$。若 $G\subseteq D_r$，则 $z,p\in D_r$。两点是 $F$ 内不同的原纯点，其整个最小面为 $F$，故 $F\subseteq D_r$，又产生含两盘的真面。因而 $D_r$ 不包含 $G$；其与 $G$ 的交作为圆盘的真面，至多含一个圆周纯点。有限多个 $D_r$ 无法覆盖整条圆周，与(VII99.2)矛盾。

指标有限性来自 $D_p$ 的原真面分类，而非先验的 $P$ 有限；每个覆盖集合也都是原全效应的整个零面。证毕。

### 99.5 唯一圆盘强迫与原真边的全联结

**引理 99.7（唯一盘的两个外顶点）。** 在引理99.4的剩余分支及 $\mathrm{Z0}$ 下，若没有圆盘，则 $P$ 有限。若恰有一张圆盘 $F$，则恰有两个外部原纯点 $s,t$，并且

$$
[s,t]\text{ 是原真边},\qquad
K=F*[s,t],\qquad P=\operatorname{ext}F\cup\{s,t\}.
\tag{VII99.11}
$$

证明。无圆盘时，任取 $p\in P$，引理99.4使 $\operatorname{ext}D_p$ 有限，且(VII99.2)中的每个 $D_r$ 也只有有限个原纯点。该有限覆盖推出整个 $P$ 有限。

现设 $F$ 是唯一圆盘。选 $p\in\operatorname{ext}F$。$D_p$ 不包含 $F$，故其原纯点集有限。(VII99.2)中的每个真面 $D_r$ 若不含 $F$，就只有有限个纯点；若含 $F$，按引理99.4，它只能是 $F$ 或以 $F$ 为底的三维棱锥，盘外纯点至多一个。因此先得到

$$
P\setminus F\text{ 有限}.
\tag{VII99.12}
$$

沿 $W_F$ 作二维商投影 $\pi$，以盘心为仿射原点，使 $\pi(F)=0$。面性质给

$$
K\cap\operatorname{aff}F=F.
\tag{VII99.13}
$$

确实，若 $a\in K\cap\operatorname{aff}F$，取 $c\in\operatorname{ri}F$，可在 $F$ 内选 $b$ 使 $c$ 位于 $(a,b)$；$F$ 的面性质迫使 $a\in F$。(VII99.12)和 $K=\operatorname{conv}P$ 这时才使 $\pi(K)$ 成为二维多边形。若 $0$ 是 $\pi(K)$ 中两点的严格凸组合，选原像 $a,b\in K$；其相应组合属于 $\pi^{-1}(0)\cap K=F$，面性质迫使 $a,b\in F$，故两商点都为零。因此 $0$ 是该多边形的顶点。

$0$ 的两条邻边各有一个在 $\pi(K)$ 上非负且以该边为整个零集的线性支撑。拉回后得到两个包含 $F$ 的原真面。每个拉回面含 $F$ 和一个盘外点，维数至少三；又是真支撑面，维数至多三。因此它们都是三维facet，按引理99.4各为一个底盘恰是 $F$ 的棱锥，记唯一外纯顶点为 $s,t$。两邻边方向独立，选原仿射坐标使

$$
F=\{(x,0,0):x\in\mathbb R^2,\ \|x\|\le1\},\qquad
s=(0,1,0),\qquad t=(0,0,1).
\tag{VII99.14}
$$

商多边形在 $0$ 处的切锥是两邻边生成的尖角，所以全部原点的最后两坐标均非负；两个拉回facet分别在其中一个坐标为零的超平面内。

$H(s,t)$ 是原二纯球。它不能为整个 $K$，因为已排除整球；不能为三维球，因为已排除球facet；不能为二维球，因为唯一圆盘是 $F$，而 $s,t\notin F$。故

$$
H(s,t)=[s,t]
\tag{VII99.15}
$$

是原真边。

若还有盘外原纯点 $r=(x,\lambda,\mu)$，则 $r\ne s,t$。若 $\lambda=0$ 或 $\mu=0$，它落在上述一个棱锥facet上，而该facet的盘外纯点唯一，矛盾。因此 $\lambda,\mu>0$。

对每个单位向量 $v\in\mathbb R^2$，$p_v=(v,0,0)$ 与 $r$ 是不同原纯点。取两点的公共非恒定非负支撑 $h_v$。它不能在整个 $F$ 恒零：若如此，它只依赖商坐标，写为 $a y_1+b y_2$；在 $s,t$ 非负给 $a,b\ge0$，在 $r$ 为零与 $\lambda,\mu>0$ 给 $a=b=0$，违反非恒定性。故限制到 $F$ 是 $p_v$ 处非零切向函数的正倍数，归一化后可写

$$
h_v(x',y_1,y_2)=1-v\cdot x'+\alpha_v y_1+\beta_v y_2.
\tag{VII99.16}
$$

在原 $s,t$ 的非负性给 $\alpha_v,\beta_v\ge-1$；在同一个原 $r$ 取零给

$$
1-v\cdot x=-\alpha_v\lambda-\beta_v\mu\le\lambda+\mu.
\tag{VII99.17}
$$

遍历全部单位 $v$，得到

$$
L:=\lambda+\mu\ge1+\|x\|.
\tag{VII99.18}
$$

若 $L=1$，则 $x=0$，$r$ 是原边 $[s,t]$ 的严格内点，违反纯性。若 $L>1$，则

$$
\frac{\lambda s+\mu t}{L}
=\frac1Lr+\frac{L-1}{L}
  \left(-\frac{x}{L-1},0,0\right).
\tag{VII99.19}
$$

由(VII99.18)，右端第二点属于 $F$。左端是原边 $[s,t]$ 的严格内点，右端是两个原状态的严格凸组合。原边的面性迫使右端两点均属于 $[s,t]$，但 $F\cap[s,t]=\varnothing$，矛盾。因此没有额外 $r$。由整个 $K$ 的有限纯分解，得到(VII99.11)；两商方向独立保证它是全联结，不只是一个凸包记号。这里排除额外点靠原真边的面性，没有把共线关系当作效应存在。证毕。

### 99.6 四维全部类型、整个proper区间与least确认

**定理 99.8（任意原纯点集的四维分类）。** 在定义99.1及 $m=4$ 下，严格同原载体地有

$$
\boxed{\mathrm B+\mathrm{Z0}
\quad\Longleftrightarrow\quad
K\cong_{\rm aff}\Delta_4,\ \mathbb B^4,\
\mathbb B^3*\Delta_0\ \text{或}\ \mathbb B^2*\Delta_1.}
\tag{VII99.20}
$$

四类均满足全部原 $\mathrm A,\mathrm H,S$；每个整个二纯球上的任意 proper 仿射效应都有原全域延拓。仿射同构同时运输原 $C,u$、全部状态及全部效应，没有替换原单位或缩小效应集。

证明。正向先分出整球 $\mathbb B^4$；有三维球facet时直接消费VII98.6，得到 $\mathbb B^3*\Delta_0$。其余分支由99.6至多有一盘。有一盘时99.7给 $\mathbb B^2*\Delta_1$。无盘时99.7先推出整个 $P$ 有限，再直接消费VII96.4的有限 $m\le5$ 结论，给 $\Delta_4$。此处没有用有限抽取替代原纯点集。

为核对反向及所有原效应，统一写后三个含球类型的规范齐次坐标为

$$
\begin{gathered}
C_{d,j}=\{(t,x,y):t\ge\|x\|,\ y\in\mathbb R_+^j\},\qquad
u_{d,j}(t,x,y)=t+\sum_{i=1}^j y_i,\\
(d,j)=(4,0),(3,1),(2,2),\qquad
K_{d,j}=C_{d,j}\cap\{u_{d,j}=1\}.
\end{gathered}
\tag{VII99.21}
$$

其纯点是球因子的 $p_v=(1,v,0)$、$\|v\|=1$，以及标量因子的 $s_i=(0,0,e_i)$。任一线性效应必唯一写成

$$
f(t,x,y)=a t+b\cdot x+\sum_i\eta_i y_i.
\tag{VII99.22}
$$

直接在整个锥上检验 $f\ge0$ 和 $u_{d,j}-f\ge0$，准确得到全部 proper 区间

$$
\|b\|\le a\le1-\|b\|,\qquad 0\le\eta_i\le1.
\tag{VII99.23}
$$

必要性由球因子 $x=\pm tv$ 及每个标量射线给出；充分性由 $|b\cdot x|\le\|b\|t$ 及 $y_i\ge0$ 给出。因此这不是另选的效应子族。

同一球因子内任意不同纯对的最小面是整个底球；球纯点与标量顶点的最小面是两点之间的原边。例如非负泛函

$$
t-v\cdot x+\sum_{k\ne i}y_k
\tag{VII99.24}
$$

的整个归一零面恰为 $[p_v,s_i]$。两标量顶点的边由 $t+\sum_{k\ne i,j}y_k$ 的零面暴露。因此全部不同纯对满足 $\mathrm B$。$j=0$ 时只有整个球一类二纯面。

原least确认可显式写为

$$
e_{p_v}(t,x,y)=\frac{t+v\cdot x}{2},\qquad
e_{s_i}(t,x,y)=y_i.
\tag{VII99.25}
$$

若(VII99.22)确认 $p_v$，则 $a+b\cdot v=1$，与(VII99.23)合用迫使 $b=\beta v$、$a=1-\beta$、$0\le\beta\le1/2$。因而在整个原规范锥上

$$
f-e_{p_v}=(1/2-\beta)(t-v\cdot x)+\sum_i\eta_i y_i\ge0.
\tag{VII99.26}
$$

若 $f$ 确认 $s_i$，则 $\eta_i=1$，其余项仍为正泛函，所以 $f-e_{s_i}\ge0$。这些 $e$ 自身都是 proper 确认效应，故它们是全锥序least，而非仅极小；对全部原混态均有 $T_p(x)=e_p(x)$。纯点间的值为

$$
e_{p_v}(p_w)=\frac{1+v\cdot w}{2},\qquad
e_{p_v}(s_i)=e_{s_i}(p_v)=0,\qquad
e_{s_i}(s_k)=\delta_{ik}.
\tag{VII99.27}
$$

所以互反性成立，得到完整 $S$。而 $D_p=K_{d,j}\cap\ker e_p$ 是一个原效应的整个零面，直接给全部混态的 $\mathrm{Z0}$；这里没有使用裸 $\mathrm B+\mathrm A\Rightarrow\mathrm{Z0}$。这些零面具体为

$$
D_{p_v}=\operatorname{conv}(\{p_{-v}\}\cup\{s_i\}_{i=1}^j),\qquad
D_{s_i}=\operatorname{conv}(\{p_w:\|w\|=1\}\cup\{s_k:k\ne i\}).
\tag{VII99.28}
$$

球内对径由 $e_{p_v}$ 排除，原边两端由(VII99.23)独立指定，故全部 $\mathrm A$ 成立；所有经过同一纯点的球对径又由同一个 $e_p$ 同时排除，给 $\mathrm H$。

全部局部 proper 效应也有明确全域公式。球面上任取 $g(x)=a+b\cdot x\in[0,1]$，并任给所有外顶点值 $\eta_i\in[0,1]$，(VII99.22)—(VII99.23)就是它的整个基上延拓。在99.7的仿射坐标中，特别有

$$
\widetilde g(x,y_1,y_2)
=a+b\cdot x+(\eta_1-a)y_1+(\eta_2-a)y_2.
\tag{VII99.29}
$$

这在生成整个 $K$ 的 $F,s,t$ 上取值于 $[0,1]$，故在整个 $K$ 上亦如此。对跨因子的原边，可任意指定两个端点读数：球端值用球上的常数效应取得，标量端值独立指定；两标量边同理。由仿射性得到边上的任意 proper 效应。整球类型的延拓是恒等操作。

对 $\Delta_4$，取 $C=\mathbb R_+^5$、$u(z)=\sum_i z_i$。全部效应为 $\sum_i\eta_i z_i$、$0\le\eta_i\le1$，原least确认为重心坐标 $e_i=z_i$。它们的整个零面给全混态 $\mathrm{Z0}$，互反值为 $\delta_{ik}$；全部二纯面是边，任意边效应也可独立指定端点后延拓。这完成四类的反向和全部效应陈述。

最后，若 $\phi:K\to K'$ 是上述仿射同构，它唯一齐次延伸为线性同构 $\widehat\phi:V\to V'$，满足 $\widehat\phi(tk)=t\phi(k)$、$\widehat\phi(C)=C'$、$u'\widehat\phi=u$。仿射性与 $K$ 张成 $V$ 保证此延伸线性且唯一。原效应通过 $f'\mapsto f'\widehat\phi$ 与规范全部效应区间双射，所有零面、整个最小面、least序和混态量词均随同运输。因此上述公式确实回到同一个原单位与原效应域。证毕。

规范表示只描述结论，不是前提。$\mathbb B^4$ 的锥是五维Lorentz锥，属于spin-factor分支；它既不是三维Bloch球的复qubit，也不是仿射维十五的完整复四能级态空间。$\mathbb B^3*\Delta_0$ 可表示为 $\operatorname{Herm}_2(\mathbb C)_+\oplus\mathbb R_+$ 的迹一基，$\mathbb B^2*\Delta_1$ 可表示为 $\operatorname{Sym}_2(\mathbb R)_+\oplus\mathbb R_+^2$ 的迹一基；这些是保单位序坐标，未给原模型增加矩阵假设。

### 99.7 三角矩曲线中的原全效应精确缺口

**命题 99.9（B-only的四维阈值与十分之一零拼合缺口）。** 在相同完整原效应范畴内，$m\le3$ 的 $\mathrm B\Rightarrow\mathrm A$ 不能扩至 $m=4$。成熟的二阶三角矩曲线凸体

$$
c_\theta=(\cos\theta,\sin\theta,\cos2\theta,\sin2\theta),\qquad
K_2=\operatorname{conv}\{c_\theta:\theta\in\mathbb R\}
\tag{VII99.30}
$$

给一个 $\mathrm B$ 成立、$\mathrm A$ 失败的完整四维模型。在此同一模型中，令

$$
p=c_0,\qquad
x=\frac{c_{\pi/2}+c_{-\pi/2}}2,\qquad y=c_\pi,\qquad
m_0=\frac{x+y}{2}.
\tag{VII99.31}
$$

则 $x,y\in D_p$，但在整个确认区间下准确有

$$
\boxed{T_p(m_0)=\frac1{10}.}
\tag{VII99.32}
$$

因而全混态 $\mathrm{Z0}$ 在这一原模型上失败。

证明。这里消费的是Carathéodory三角矩曲线凸体的成熟构造，不把模型或neighborly性质重新归为新增结果。其原始条件与一般化见 Sanyal—Sottile—Sturmfels，*Orbitopes*，arXiv:0911.5436v4，§5.1、Theorem 5.2、Corollary 5.4。为落实当前原效应与阈值计算，直接核对所需接口如下。

五个函数 $1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta$ 线性无关，故 $\dim\operatorname{aff}K_2=4$。曲线紧，凸包紧。取 $V=\mathbb R\oplus\mathbb R^4$、$C=\{t(1,z):t\ge0,z\in K_2\}$、$u(t,w)=t$，即得闭尖生成锥与严格正单位，归一基就是整个 $K_2$。每个 $c_a$ 由第一谐波 $\cos(\theta-a)$ 唯一暴露；反向，紧曲线凸包中的极点只能来自曲线，因为有限凸组合中的非平凡多项组合不可能极端。因此全部原纯点恰是整条曲线。

对任意 $a\ne b\pmod {2\pi}$，三角多项式

$$
h_{a,b}(\theta)=(1-\cos(\theta-a))(1-\cos(\theta-b))
\tag{VII99.33}
$$

非负、阶数至多二，且零点恰为 $a,b$。它是原仿射泛函在曲线上的限制，所以其整个原零面恰为 $[c_a,c_b]$，是一条暴露真边。故所有不同原纯对的整个最小面均为线段，$\mathrm B$ 成立。这是上述成熟面结构在本模型中的具体使用。

这个原全效应区间恰对应全部满足 $0\le g(\theta)\le1$ 的实二阶三角多项式；没有只保留平方效应。它不可能使所有不同纯对完全可区分。否则对 $q_n=c_{1/n}\to p$，$\mathrm A$ 在原边 $[p,q_n]$ 上给 $f_n\in F_p$、$f_n(q_n)=0$。原 $F_p$ 紧，取收敛子列 $f_n\to f\in F_p$；评价联合连续给 $f(p)=\lim_n f_n(q_n)=0$，而 $f\in F_p$ 又给 $f(p)=1$，矛盾。因此 $\mathrm A$ 失败。VII98.7已给全部 $m\le3$ 的正结论，所以四维是B-only失败的准确最低仿射维。此论证只用原全效应紧性，不需要额外的纯态区分阈值公式。

现在计算(VII99.32)。原效应 $g_1(\theta)=\cos^2\theta$ 在 $p$ 取一、在组成 $x$ 的两个纯点取零，故 $p\perp x$；原效应 $g_2(\theta)=(1+\cos\theta)/2$ 在 $p$ 取一、在 $y$ 取零，故 $p\perp y$。两者都是阶数至多二且在整圆取值于 $[0,1]$ 的原效应。

取 $u_0\in(0,\pi)$，使 $\cos u_0=-2/3$。逐一比较原四坐标，得到

$$
\begin{gathered}
x=(0,0,-1,0),\qquad y=(-1,0,1,0),\qquad
m_0=(-1/2,0,0,0),\\
z_0:=\frac{c_{u_0}+c_{-u_0}}2=(-2/3,0,-1/9,0),\\
m_0=\frac1{10}p+\frac9{10}z_0.
\end{gathered}
\tag{VII99.34}
$$

因此对每一张原 $f\in F_p$，正性和仿射性都给

$$
f(m_0)=\frac1{10}+\frac9{10}f(z_0)\ge\frac1{10}.
\tag{VII99.35}
$$

这个下界遍历整个确认区间，不来自局部候选效应的失败。另一方面，取

$$
g_*(\theta)=\left(\frac{3\cos\theta+2}{5}\right)^2,
\qquad
f_*(X)=\frac{17}{50}+\frac{12}{25}X_1+\frac9{50}X_3.
\tag{VII99.36}
$$

$g_*=f_*\circ c$；由于 $-1\le3\cos\theta+2\le5$，它在整圆满足 $0\le g_*\le1$，因而 $f_*$ 是整个 $K_2$ 的原 proper 效应。它在 $p$ 取一，在 $c_{\pm u_0}$ 取零，故 $f_*(m_0)=1/10$。与(VII99.35)合用，得精确最小值。该模型只有 $\mathrm B$ 而没有全混态 $\mathrm{Z0}$，所以不是一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 的反例。证毕。

### 99.8 同一完整装饰元组上的四维候选

**定理 99.10（m至多四的完整同数据几何替换）。** 固定VI89.7、VII98.8—98.9的同一个完整原装饰元组 $\mathcal O$、共同来源合同 $\mathfrak S(\mathcal O)$ 和全部非几何前件。对选定的任意 $J\subseteq\{A,D,E\}$，在VII98.8的固定适用域中把分支 $1\le m_X\le3$ 扩为 $1\le m_X\le4$，其他分支按原条件保留。定义 $\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)$：只把 $X\in J$ 的原几何项替换为同一载体上的 $\mathrm B_X+\mathrm{Z0}_X$；其余几何项和全部非几何包不变。则在这个共同适用域内

$$
\boxed{\begin{aligned}
\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)
&\Longleftrightarrow\mathsf R_{\rm polar}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm zero\text{-}ball}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{\rm mid}(\mathcal O)
\Longleftrightarrow\mathsf R_{86}^{\rm ev}(\mathcal O)
\Longleftrightarrow[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O).
\end{aligned}}
\tag{VII99.37}
$$

每个 $\mathrm{Z0}_X$ 仍量化全部原混态；四维类型分类不替换原数据或实际来源。

证明。对新增的 $m_X=4$ 分支，99.8在同一个原 $K_X$、全部纯点、全部效应和原 $u_X$ 上给 $\mathrm A_X$ 与完整 $S_X$。对VII98.8的其余原适用分支，直接复用其证明。准确的桥仍是VII(98.29)的

$$
\mathrm B+\mathrm{Z0}+\mathrm A
\Longleftrightarrow\mathrm B+\mathrm H
\Longleftrightarrow S,
\tag{VII99.38}
$$

不是裸 $\mathrm B+\mathrm A\Rightarrow S$。反向由旧完整 $S$ 的least零面取得全混态 $\mathrm{Z0}$。VI89.4再给同一原 $\mathrm{Boundary}$ 与 $\mathrm Q$，然后逐项调用VI89.8的完整同数据等价，得到(VII99.37)。VI89.3中只涉及至多三个原纯标签的关系生成元、内在商及有限仿射基仍按原定义运输；它们不把这里的混态量词改成纯纯三点检验。

非几何部分准确采用VI89.7与VII98.8的整个合同：原概率像自身紧、非空、有限仿射维及全部原中点实现；原测试像自身闭、零、单位、中点、补、有界倍增及同一原测试对全部准备实现；原带质量输出、重复标签、全部非负质量缩放和零／次归一／不等质量；每个过程与参考自身的全部相关联合输入域；同一个原 $L,p,\omega$ 与两次同 $p$、两实张成、全实 $Z$、含秩一分支的完整(83.8)、原迹／伴随／二次表示／单位、全部两尺度等式、C2、整个 $G=1_E$，以及精确PRE后同一原资格态的整个H13。共同 $\mathfrak S$ 中的设备／事件／来源绑定、全部菜单与分支、实际参考与副本、记录／权限／控制／钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、实际混合服务、全部合法未来、旧支撑与每个中间切口均不删减。

每个QM消费者完整消费VII98.9及VI89.9自己的前件：复型与Born仍需原忠实EJA桥及精确两接口66.3；指定二份／三份及读回仍需同一原 $L,p$ 和全部联合条件；指定CP仍需同事件原实线性映射、唯一复HP延拓、全实提升律、腿权／核条件与实际纯探针，或既有完整递归参考路线；Kraus与实际仪器仍需逐块CP及真实完整菜单、接线、粗粒化、重置和两预算；Lüders仍需同一分支的锐效应、确定接受态中性与原输出校准；物理时间仍需原连续齐次可逆群、实际逆、原钟与动态来源。四维球的spin-factor分支不能直接供应复型。

原生来源方面，VII98.9及VI89.10的完整 $89$ 路径、$26+63$ 嵌入、射影群与密度、唯一ready、原十一地址全部有限字及terminal futures、各旧入口自己的有限秩或全未来关系、全部细标签与原粗归组、记录后原七地址条件未来、source-adoption map及全部资源条件仍完整保留。已有同秩入口的联合下降／回返和已取得的Born／联合POVM结论按其原域复用，不列作新的缺口；当前ready或固定future仍不能代付全未来条件。于是这里供应的只是几何入口在新增维数域内的等价替换，各非几何消费者没有被单独生成。证毕。

### 99.9 文献归属、剩余范围与几何白话

本章使用的三角矩曲线是 *Orbitopes* 的universal Carathéodory orbitope $C_2$，不是只取奇频的对称矩曲线 $C_{(1,3)}$。该文[arXiv:0911.5436v4，§5.1、Theorem 5.2、Corollary 5.4](https://arxiv.org/pdf/0911.5436v4)分别给其三角坐标、对角线为一的Hermitian Toeplitz半正定表示和至多两个圆周点对应的真面。正文只把这些成熟构件用在99.9的具体反例内；该模型的矩阵表示不成为99.8的一般凸体前件。

Naszódi—Szilágyi—Weiner，[*Higher rank antipodality*，arXiv:2307.16857v3，§2及Proposition 4](https://arxiv.org/pdf/2307.16857v3)，把完整仿射测量 $K\to\Delta_k$ 与联合对踵性联系起来。这里纯点的 $p\perp q$ 正是 $k=1$ 的整个 $K\to[0,1]$ 区分；仅知道二点最小面是一条边并不给这个全域映射，99.9恰区分二者。

Alfsen—Shultz，[*State spaces of Jordan algebras*，Acta Mathematica 140，155—190，§3、Theorems 3.11与7.2](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf)，其Hilbert ball property要求每个二极点最小面仿射同构Hilbert球并为norm-exposed面，且包括两点相同的单点情形。Theorem 3.11从JBW代数的正常态空间推出这一性质；Theorem 7.2的逆向JB态空间刻画还要求极点的 $\sigma$ 凸包为split face、每个norm-exposed面为projective，以及每个连续仿射函数有正交正负分解。这些是该文的实际前件，不能由本题裸 $\mathrm B$ 自动补入。99.2—99.8通过原零面覆盖证明所需接触，不从球面名称相似推出原 $\mathrm A$，也不预设任意局部效应延拓。

99.2的整个零面部分复用V88.3；99.3的球支持计算、99.4的低维分类、球facet的全基棱锥及99.8的有限分支分别消费VII98.6—98.7、VII96.4。支撑包含、紧凸有限纯分解、球的严格凸性和联结效应计算是推导内明用的成熟凸几何构件。原问题中的新增综合为共同排除面覆盖与四维双盘支撑锥的连接、全混态零拼合的有限圆周覆盖矛盾、唯一盘的商多边形与原边面性闭合，以及99.9针对原整个确认区间的精确 $1/10$ 缺口；采用 `repo-derived` 归属，不主张全球原创或文献穷尽。

一般高维 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 仍须处理VI90.10的全部原接触，除非落在已有充分域。四维关键的“两盘限制唯一确定全局支撑”使用了 $\dim W_F+\dim W_G=m$；更高维的额外方向不能由这一步控制。VII98.5的一般临界三球接触上界、全部有限纯点的无维数限制结论，以及不预设表示的一般域，都没有从四维分类取得证明。实际复型、复合、CP、仪器、更新、时间与来源分别保留99.10所列原义务；这些纸面定理不宣称kernel核验或完整物理来源。

白话说，这个完整候选仍在同一批原准备、测试、过程和未来上，只把几何入口写成两条：任意两个纯点所在的最小面是整球；固定一个纯点后，各自能被排除的任意混态，其混合仍能被排除。第二条把所有零读数拼成同一张原零面。四维中，两张圆盘的方向刚好用满空间，零面覆盖便会要求有限多个点盖住整条圆周，因而两盘不能共存；只剩一盘时，商平面的两条邻边挑出两个外顶点，原边的面性又排除其他顶点，整个形状只能是圆盘与线段的全联结。连同无盘、整球和球棱锥，恰是99.8的四类。反事实也可精确量出：若删掉混态零拼合，三角矩曲线让每一纯对仍有整条原边，两种目标也各自能读零，但它们等量混合后的最低读数却是 $1/10$。这些几何结论恢复的是原全域效应与最小确认；复数、实际复合、操作和时间仍由完整候选中各自的原合同承担。

## 追加锚（本行以下为增补区）

## 100. 原有限全效应的边四边形、指定投影与facet延拓障碍

### 100.1 整个原载体、两种比较与实际边

**定义 100.1（有限全混态零拼合域）。** 本章的VII97.x—100.x指本卷，VI89.x、VI90.x指[第六卷](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)，V88.x指[第五卷](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)。取非零有限维实空间 $V$、闭尖生成凸锥 $C$、在 $C\setminus\{0\}$ 上严格正的原线性单位 $u$，并使用

$$
\begin{gathered}
C^*=\{f\in V^*:f(C)\subseteq\mathbb R_+\},\qquad
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad |P|<\infty,\\
[0,u]=\{f\in V^*:f\in C^*,\ u-f\in C^*\},\qquad
F_p=\{f\in[0,u]:f(p)=1\},\\
T_p(x)=\min_{f\in F_p}f(x),\qquad
p\perp x\ \Longleftrightarrow\ T_p(x)=0,\qquad
D_p=\{x\in K:p\perp x\},\\
\mathrm{Z0}:\quad
\forall p\in P\ \forall x,y\in K,\quad
p\perp x\ \land\ p\perp y\ \Longrightarrow\ p\perp(x+y)/2,\qquad
m=\dim\operatorname{aff}K=\dim V-1.
\end{gathered}
\tag{VII100.1}
$$

$P$ 是整个原基的全部纯点，$x,y$ 遍历全部原混态，$[0,u]$ 是整个原区间。紧基张成 $V$，故 $[0,u]$ 及非空 $F_p$ 紧，上式最小值达到；零排除等价于存在同一张 $f\in[0,u]$ 在 $p$ 取一、在 $x$ 取零。本章假设这个完整 $\mathrm{Z0}$，不假设 $\mathrm B$、least确认、自对偶、正定配对、正交模律、Jordan乘积、ROG表示或正滤子，也不加入标签归一化或实际装置前提。

$m\ge1$ 时直接复用VII97.2—97.5：$p\mapsto D_p$ 是顶点到facet的双射，$h_p\in[0,u]$ 是零面为 $D_p$ 且 $h_p(p)=1$ 的唯一规范facet效应，且 $h_p$ 只在 $p$ 达到一。记

$$
T_{pq}:=h_p(q),\qquad
0\le T_{pq}<1\ (p\ne q),\qquad
T_{pq}=0\ \Longleftrightarrow\ T_{qp}=0.
\tag{VII100.2}
$$

这里 $T_{pq}$ 是已指定的规范facet读数，$T_p(q)$ 则仍是遍历全部原确认效应的下包络；不将二者认同。对面 $F$ 沿用 $F^\#=\bigcap_{r\in\operatorname{ext}F}D_r$、$\varnothing^\#=K$，以及VII97.3的反序对合和 $\dim F+\dim F^\#=m-1$。$\operatorname{span}\varnothing=\{0\}$。本章的实际边是 $K$ 的一维面 $E=[p,q]$，$p,q\in P$ 不同；$m=1$ 时允许 $E=K$。取定这样一条边后置

$$
a=T_{qp}=h_q(p),\qquad b=T_{pq}=h_p(q),\qquad
d=1-ab>0,\qquad E^\#=D_p\cap D_q.
\tag{VII100.3}
$$

### 100.2 两张facet效应给整个边效应面和严格外部余量

**定理 100.2（实际边的原效应四边形）。** 在定义VII100.1的前件下，对每条实际边 $E=[p,q]$，令

$$
\begin{gathered}
Q_E=\{f\in C^*:f|_{E^\#}=0\},\qquad
\mathcal I_E=\{f\in[0,u]:f|_{E^\#}=0\},\\
e_E=\frac{(1-a)h_p+(1-b)h_q}{d}.
\end{gathered}
\tag{VII100.4}
$$

则 $Q_E=\mathbb R_+h_p+\mathbb R_+h_q$，且 $\mathcal I_E$ 是整个原 $[0,u]$ 的二维面，准确为

$$
\begin{aligned}
\mathcal I_E
&=\{\alpha h_p+\beta h_q:\alpha,\beta\ge0,
\ \alpha+a\beta\le1,\ b\alpha+\beta\le1\}\\
&=\operatorname{conv}\{0,h_p,e_E,h_q\}.
\end{aligned}
\tag{VII100.5}
$$

$e_E$ 是唯一在 $E^\#$ 恒零、在 $p,q$ 都取一的原效应；其整个零面和一面分别为 $E^\#$ 和 $E$。特别是，对每个原顶点 $r\in P\setminus\{p,q\}$，有严格余量

$$
\Delta_{pqr}:=d-(1-a)T_{pr}-(1-b)T_{qr}
=d\bigl(1-e_E(r)\bigr)>0.
\tag{VII100.6}
$$

若 $m\ge2$，还存在对每个 $s\in\operatorname{ext}E^\#$ 都严格正的系数 $\lambda_s$，使

$$
u=e_E+\sum_{s\in\operatorname{ext}E^\#}\lambda_sh_s.
\tag{VII100.7}
$$

若 $m=1$，则 $E=K$、$E^\#=\varnothing$、$a=b=0$、$e_E=u$，式(VII100.7)的和为空和零，不要求存在任何系数。$m=0$ 没有实际边，因而本定理的边量词为空。

证明。先设 $m\ge2$。VII97.3给 $\dim E^\#=m-2$，所以 $\dim\operatorname{span}E^\#=m-1$，其在 $V^*$ 中的消灭子为二维。$h_p,h_q$ 都消灭这个空间；它们在 $p,q$ 上的评价矩阵为

$$
\begin{pmatrix}1&b\\a&1\end{pmatrix},\qquad \det=d>0,
\tag{VII100.8}
$$

故它们是一组基。不同facets $D_q,D_p$ 互不包含，存在原顶点 $r\in D_q\setminus D_p$ 和 $s\in D_p\setminus D_q$。若 $f=\alpha h_p+\beta h_q\in C^*$，分别在 $r,s$ 评价便给 $\alpha,\beta\ge0$。反向由 $h_p,h_q\in C^*$ 直接成立。因此得到 $Q_E$ 的准确表达。$m=1$ 时 $K=[p,q]$，两张规范facet效应是端点重心坐标，$D_p=\{q\}$、$D_q=\{p\}$，同一矩阵为单位矩阵，且整个 $V^*=\operatorname{span}\{h_p,h_q\}$；上述非负锥表达也成立。

以下对所有 $m\ge1$ 同时论证。对任意 $0\ne f\in Q_E$，令 $M_f=\max_K f>0$。若原顶点 $v$ 达到 $M_f$，则 $f/M_f$ 是原 proper 效应，确认 $v$ 并消灭 $E^\#$，故 $E^\#\subseteq D_v$。反序对合给 $v\in E^{\#\#}=E$。由于 $K$ 是整个有限顶点凸包，$f$ 的极大集也是由其极大顶点生成的面，故

$$
\operatorname{argmax}_K f\subseteq E,\qquad
\max_K f=\max\{f(p),f(q)\}.
\tag{VII100.9}
$$

这对任意非零 $f\in Q_E$ 只给极大集包含于 $E$，没有声称每个这样的 $f$ 都在整条边恒定。零泛函的零一界直接成立。因此 $\alpha h_p+\beta h_q$ 为proper，当且仅当两系数非负且端点值 $\alpha+a\beta,b\alpha+\beta$ 都不超过一，得到(VII100.5)第一行。

该平面区域在坐标轴上的顶点为 $(0,0),(1,0),(0,1)$；另外两条上界直线的交点为

$$
(\alpha_*,\beta_*)=
\left(\frac{1-a}{d},\frac{1-b}{d}\right),\qquad
\alpha_*,\beta_*>0.
\tag{VII100.10}
$$

每条上界在线段轴端的另一约束均严格，交点两坐标为正，故这四点正是全部顶点，按 $0,h_p,e_E,h_q$ 循环排列。$e_E(p)=e_E(q)=1$，由(VII100.9)其一面恰为 $E$；两个严格正系数又使其零面恰为 $D_p\cap D_q=E^\#$。同一可逆矩阵给唯一性，并立即给(VII100.6)。由于所有原效应在 $E^\#$ 非负，若一个严格凸组合在其上恒零，两个分量也都恒零，故 $\mathcal I_E$ 是原区间的面；它含仿射独立的 $0,h_p,h_q$ 且在上述二维消灭子内，维数恰为二。空 $E^\#$ 时它就是整个二维原区间。

为证(VII100.7)，只需标准多面体的facet—对偶极射线对应：VII97.2已列出全部facets，因而 $C^*=\operatorname{cone}\{h_s:s\in P\}$。其有限维分离证明是：这些半空间 $h_s\ge0$ 的交正是 $C$；若某个原正泛函不在这些法向的有限生成闭锥中，分离就给一个在所有 $h_s$ 上非负、在该泛函上为负的向量，与它属于 $C$ 矛盾。这是成熟凸锥对偶步骤，不是额外自对偶前提。

$m\ge2$ 时令 $R=\operatorname{ext}E^\#\ne\varnothing$、$g=u-e_E$、$S_R=\sum_{s\in R}h_s$。$g,S_R$ 都在 $p,q$ 取零；对其他原顶点 $v$，$g(v)>0$。有限性允许取 $\varepsilon>0$，使 $g(v)-\varepsilon S_R(v)\ge0$ 对全部 $v\in P$ 成立，于是 $g-\varepsilon S_R\in C^*$。将它写成上述 $h_s$ 的非负组合。在 $p,q$ 评价为零，迫使每个有非零系数的 $h_s$ 同时消灭 $p,q$，亦即 $s\in D_p\cap D_q=E^\#$，其中用了纯点零排除对称性。因此加回 $\varepsilon S_R$ 后每个 $s\in R$ 的系数都严格正。$m=1$ 时端点重心坐标之和就是 $u$，单独给所述空和分支。证毕。

### 100.3 沿原补面张成的指定分裂及其正性

**定理 100.3（proper质量不代付正投影）。** 在定义VII100.1下，每条实际边都有准确线性直和

$$
V=\operatorname{span}\{p,q\}\oplus\operatorname{span}E^\#.
\tag{VII100.11}
$$

沿这里的原补面张成投到边张成的唯一线性投影为

$$
\begin{gathered}
\Pi_E(x)=\xi_p(x)p+\xi_q(x)q,\\
\xi_p=\frac{h_p-bh_q}{d},\qquad
\xi_q=\frac{h_q-ah_p}{d},\qquad
u\circ\Pi_E=\xi_p+\xi_q=e_E\in[0,u].
\end{gathered}
\tag{VII100.12}
$$

下列条件等价：

$$
\begin{gathered}
\Pi_E(C)\subseteq C;\qquad
q\in D_p;\qquad a=b=0;\\
e_E-h_p\in C^*;\qquad e_E-h_q\in C^*;\qquad
\mathcal I_E\text{ 是平行四边形}.
\end{gathered}
\tag{VII100.13}
$$

这些条件成立时 $\Pi_E$ 的像锥为 $\operatorname{cone}\{p,q\}$；失败时(VII100.12)的总质量效应仍为proper。若 $m=1$，$\Pi_E=1_V$，这些条件全成立；$m=0$ 无边，不构造 $\Pi_E$。

证明。$p,q$ 线性独立，因为它们不同且 $u(p)=u(q)=1$。若 $\eta p+\theta q$ 属于 $\operatorname{span}E^\#$，分别作用 $h_p,h_q$ 并用(VII100.8)可得 $\eta=\theta=0$。当 $m\ge2$ 时两个子空间维数为 $2,m-1$，和为 $\dim V=m+1$；$m=1$ 时第二个为零，也得到(VII100.11)。两个 $\xi$ 消灭补面张成，在 $p,q$ 上分别给 $(1,0),(0,1)$，所以(VII100.12)确是所指定的投影，满足 $\Pi_E^2=\Pi_E$，其质量式由直接相加得到。

还需核对像锥：

$$
C\cap\operatorname{span}\{p,q\}=\operatorname{cone}\{p,q\}.
\tag{VII100.14}
$$

若 $0\ne z$ 属于左边，则 $u(z)>0$，且 $u-e_E$ 消灭 $p,q$，故 $(u-e_E)(z)=0$。于是 $z/u(z)\in K$ 位于 $e_E$ 的整个一面 $E=[p,q]$，给出右边的非负分解；零向量及反向包含直接成立。因此 $\Pi_E$ 正，当且仅当其两个唯一坐标 $\xi_p,\xi_q$ 都属于 $C^*$。

若 $a=b=0$，两坐标就是 $h_p,h_q$，故正；它又固定 $p,q$，所以像锥恰为(VII100.14)。若 $a>0$，取VII100.2证明中的原顶点 $r\in D_q\setminus D_p$，则

$$
\xi_q(r)=-\frac{a h_p(r)}d<0,
\tag{VII100.15}
$$

故 $\Pi_E(r)\notin C$。由(VII100.2)，$a=0$ 当且仅当 $b=0$，且等价于 $q\in D_p$；这排除了只有一个非零交叉值的分支。

另一方面，

$$
e_E-h_p=\frac{1-b}{d}(h_q-ah_p),\qquad
e_E-h_q=\frac{1-a}{d}(h_p-bh_q).
\tag{VII100.16}
$$

当 $a>0$ 时，第一式在同一个 $r$ 为负；交换 $p,q$ 得第二式在某个 $s\in D_p\setminus D_q$ 为负。当 $a=b=0$ 时两式分别为 $h_q,h_p$，故得到两项锥序等价。特别是非接触边上的 $e_E\in F_p$ 不支配 $h_p$，不能把规范facet确认当作least确认。

最后，四边形的循环顶点已为 $0,h_p,e_E,h_q$，所以它是平行四边形当且仅当 $e_E=h_p+h_q$。在 $p,q$ 评价这一等式给 $a=b=0$，反向由公式立即成立，完成全部等价。这里的质量proper只给 $0\le u(\Pi_Ex)\le u(x)$（$x\in C$），没有给 $\Pi_Ex\in C$。它因而不产生正滤子、事件更新或可调用量子操作。证毕。

只有在另行加入有限整个纯集的原全称 $\mathrm B$ 时，VII97.4才保证每个不同纯对都是实际边，且每条边就是该对的整个二态球，局部对径为另一端点。按这个已证对应，VI90.10的全部接触准确成为(VII100.13)对每条边成立，亦即这些指定投影全正；VI90.8的整个二态球逐效应延拓仍按它自己的量词消费。本章未从有限 $\mathrm B+\mathrm{Z0}$ 推出所有 $a=b=0$，因而未证明其一般接触或单纯形结论。

### 100.4 每个非接触纯对的一张局部facet尺排除全部延拓

**定理 100.4（指定局部proper效应的全延拓障碍）。** 在定义VII100.1下，任取有序不同原纯对 $p,q\in P$ 满足 $q\notin D_p$；不要求 $[p,q]$ 是边。令

$$
F=D_p,\qquad M=\max_{x\in F}h_q(x),\qquad
\ell_{p,q}=\frac{h_q|_F}{M}.
\tag{VII100.17}
$$

这里 $[0,1]_{\operatorname{aff}(F)}$ 指 $F$ 上全部实仿射函数中满足 $0\le\ell(x)\le1$ 对每个 $x\in F$ 成立者；零一界只在 $F$ 上要求。则 $0<M<1$，$\ell_{p,q}\in[0,1]_{\operatorname{aff}(F)}$ 是指定的局部proper效应，而

$$
\nexists f\in[0,u]:\quad f|_F=\ell_{p,q}.
\tag{VII100.18}
$$

更准确地，其全部实线性延拓恰为

$$
f=\frac{h_q}{M}+\mu h_p,\qquad \mu\in\mathbb R,
\tag{VII100.19}
$$

而没有任何一个同时满足原 $f\ge0$ 及 $f\le u$。全局仿射延拓到 $K$ 也同样被排除，因为 $\operatorname{aff}K=\{u=1\}$，其仿射函数唯一齐次线性延伸到 $V$。

证明。固定 $k_0\in K$，有 $V=\mathbb Rk_0\oplus\ker u$。$\operatorname{aff}K$ 上的仿射式 $c+L(x-k_0)$ 唯一对应 $V$ 上的线性式 $f(tk_0+w)=tc+L(w)$，所以全局仿射延拓与线性延拓的上述对应保持同一原单位。

不同的 $p,q$ 对应不同facets，所以 $F\not\subseteq D_q$，$h_q$ 在 $F$ 上不恒零，得到 $M>0$。$h_q$ 在整个 $K$ 只在 $q$ 达到一，且 $q\notin F$；由 $F$ 紧知 $M<1$。非负性与最大值定义给局部零一界，并在某个 $F$ 的顶点达到一。

$F$ 为facet，$\dim\operatorname{span}F=m$，故其消灭子是一维且由 $h_p$ 张成。两个延拓的差消灭 $F$，因此(VII100.19)穷尽全部实线性延拓。不同facets又给一个原顶点 $r\in D_q\setminus D_p$。若这样的 $f$ 在整个原锥非负，则

$$
f(r)=\mu h_p(r)\ge0,\qquad h_p(r)>0,
\quad\Longrightarrow\quad\mu\ge0.
\tag{VII100.20}
$$

但在同一个原纯点 $q$ 上随即有

$$
f(q)=\frac1M+\mu T_{pq}>1=u(q),
\tag{VII100.21}
$$

矛盾。这排除了全部延拓，不只是自然猜测 $h_q/M$ 的失败。$m=0$ 没有不同纯对，$m=1$ 的两个不同纯点互相接触，所以这两支都没有符合前件的非接触对；$p=q$ 从未在本定理量词内。

这是 $F=D_p$ 上的一张局部facet效应障碍。除非另有对应证明 $F$ 是VI90.8所量化的某个整个二态球，否则不能把(VII100.18)认作该球的延拓反例，更不能由它断言一般 $\mathrm B+\mathrm{Z0}$ 已失败。即使 $[p,q]$ 本身是边，这个 $F=D_p$ 也不是自动等于 $[p,q]$。证毕。

### 100.5 同一个有理七边形中的非正分裂和不可延拓尺

**命题 100.5（原载体上的非空障碍实例）。** 使用VII97.6的整个七点 $p_i=(1,v_i)$、原锥 $C$、单位 $u(t,x,y)=t$ 及整个原效应区间。该载体已满足全混态 $\mathrm{Z0}$。对实际边 $E=[p_0,p_1]$，有

$$
\begin{gathered}
E^\#=\{p_4\},\qquad
h_0(t,x,y)=\frac{9t+x}{19},\qquad
h_1(t,x,y)=\frac{82t+6x+7y}{174},\\
a=\frac{71}{87},\qquad b=\frac{15}{19},\qquad
 d=\frac{196}{551},\qquad
 e_E=\frac{76}{147}h_0+\frac{29}{49}h_1
     =\frac{22t+2x+y}{42}=u-h_4.
\end{gathered}
\tag{VII100.22}
$$

它在全部原顶点上的读数和严格外部余量为

| 原顶点 | $p_0$ | $p_1$ | $p_2$ | $p_3$ | $p_4$ | $p_5$ | $p_6$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $e_E$ | $1$ | $1$ | $2/3$ | $4/21$ | $0$ | $4/21$ | $13/21$ |
| $1-e_E$ | $0$ | $0$ | $1/3$ | $17/21$ | $1$ | $17/21$ | $8/21$ |

因此五个外部顶点都有 $\Delta_{p_0p_1r}=(196/551)(1-e_E(r))>0$。然而

$$
\Pi_E(p_5)=\frac{29}{28}p_0-\frac{71}{84}p_1\notin C,
\qquad u(\Pi_E(p_5))=\frac4{21}>0.
\tag{VII100.23}
$$

同一个有序非接触对 $p=p_0,q=p_1$ 的facet为 $F=D_{p_0}=[p_3,p_4]$，其(VII100.17)效应满足

$$
M=\frac{28}{87},\qquad
\ell_{p_0,p_1}(p_3)=1,\quad \ell_{p_0,p_1}(p_4)=0,
\tag{VII100.24}
$$

且没有原 proper 延拓。此处 $F$ 的确是 $p_3,p_4$ 的整个最小面，是一维整球；故这一特定facet障碍也给出该整个线段上的局部端点尺不可延拓，但该载体没有全称 $\mathrm B$。

证明。VII97.14—97.15的第 $3,4$ 行分别给 $h_0=s_3/152$、$h_1=s_4/174$，正是(VII100.22)的齐次式。$D_{p_0}=[p_3,p_4]$、$D_{p_1}=[p_4,p_5]$ 给 $E^\#=\{p_4\}$。代入(VII100.4)并合并系数得到 $e_E$，而第 $0$ 行给 $h_4=(20t-2x-y)/42$，所以补效应也符合(VII100.7)。逐个代入VII97.11的七个坐标得到表中全部值，未更换基或归一超平面。$h_0(p_5)=7/19$、$h_1(p_5)=0$，代入(VII100.12)给(VII100.23)。两个坐标中第二个为负，(VII100.14)即排除其属于原锥，尽管总质量为正且由proper效应读出。

这也实际区分了两种比较：$e_E\in F_{p_0}$，从而

$$
T_{p_0}(p_5)\le\frac4{21}<\frac7{19}=T_{p_0p_5}.
\tag{VII100.25}
$$

本式只使用下包络的定义，没有将该上界冒称其精确值。

在 $F$ 的两端，$h_1(p_3)=56/174=28/87$、$h_1(p_4)=0$，所以最大值和局部效应为(VII100.24)。任意全局线性延拓为 $f=(87/28)h_1+\mu h_0$。在同一个 $p_5\in D_{p_1}\setminus D_{p_0}$，非负性迫使 $\mu\ge0$；但 $f(p_1)=87/28+(15/19)\mu>1$，证明全部proper延拓不存在。因为 $[p_3,p_4]$ 是实际边，包含它两端的整个最小面恰是该边；局部 $\ell$ 是它唯一的端点零一仿射尺，故上述球对应在这一实例中明确成立。

另一方面，VII97.6已给 $H(p_0,p_2)=K$，整个七边形不是整欧氏球，故全称 $\mathrm B$ 失败。因此这个实例同时实现本章一般有限 $\mathrm{Z0}$ 域内的严格外部slack、proper总质量、指定分裂非正及局部尺全延拓失败，仍不是VI89.12的 $\mathrm B+\mathrm{Z0}$ 反例。证毕。

### 100.6 数学归属和原消费者的条件边界

**约定 100.6（复用与尚存的桥）。** VII100.2—100.4的边四边形及 $\Delta$ 公式、沿原补面张成的指定投影正性充要条件、以及 $\ell_{p,q}$ 的全部延拓障碍采用 `repo-derived` 归属。它们由VII97.2—97.5的既有完整facet配对、反序对合及规范slack推导；VII100.5直接使用VII97.6的原七边形，不另主张新载体。证明内的有限维支撑／分离、facet法向生成对偶锥、面上极值及二维线性代数是成熟步骤（凸分析来源沿用VII98.6所引 Rockafellar，*Convex Analysis*，§11、§18），不将它们分别计作新定理。

[FinitePureSimplex](../../../Blueprint/D5/S3/Quantum/Foundation/FinitePureSimplex.md)的 `zero_gluing_iff_simplex` 要求整个纯点坐标核维数至多一，`zero_kernel_least_confirmation` 要求该核为零；[WeightedRelationConfirmation](../../../Blueprint/D5/S3/Quantum/Foundation/WeightedRelationConfirmation.md)的加权精确确认值也在完整一关系域内。它们不供应本章任意关系零度的边、投影及facet延拓公式；本章亦不重证这些既有支路。VI90.8—90.10的原全效应限制／接触接口是本章的既有消费者，只有已证的整个面对应才能接入。

Dobbins，*Antiprismless, or: Reducing Combinatorial Equivalence to Projective Equivalence in Realizability Problems for Polytopes*，[arXiv:1307.0071v3 §3 Theorem 3.2、Lemma 3.3、Theorem 3.9](https://arxiv.org/html/1307.0071v3)讨论balanced pair、antiprism和interval polytope的组合实现及存在性边界；这些结果不是(VII100.4)—(VII100.24)在此原锥和原单位上的数值公式或正性、延拓判据。本章只确定每条实际边的上述二维效应面，不主张原 $[0,u]$ 的全部面或全部极端效应分类。该有限来源对应不主张全球原创、文献穷尽或一般开放状态认证。

VI99.7的全实ROG、任意共同支撑维数及余维的 $\mathrm G_2\Longleftrightarrow\mathrm{Z0}\Longleftrightarrow S$ 闭合按其完整ROG表示前件复用；裸有限 $\mathrm{Z0}$ 没有在本章取得该表示。有限 $\mathrm B+\mathrm{Z0}$ 一般域仍须证明每条原边的 $a=b=0$，才能沿VII97.4及VI90.10完成全部接触；VII98.5的临界等号、一般VI89.12和一般有限 $\mathrm B+\mathrm{Z0}$ 的单纯形问题均未由本章解决。指定 $\Pi_E$ 的正性也不是VI90.8所要求的任意整球逐效应延拓的无条件替代。

复型与Born、指定复合、同事件CP和仪器、更新、实际来源及物理时间仍保留VI89.7—89.10及VII98.8—98.9的全部原合同。[原生来源续卷VII](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md)第33—34章的指定 $\mathrm H_8,\mathrm H_3$ 联合供应和第35章的特定候选障碍按既有范围复用；它们不是本章待补缺口。原全字精确细零关系、细Born、实际操作与时间则仍未由这些几何效应供应。以上是明确模型条件内的纸面推导，不声明Lean核验或经验实现。

## 追加锚（本行以下为增补区）

## 101. 最小共同零障碍的仿射独立、纯目标元数与四维精确替换

### 101.1 原确认面与纯目标的共同零要求

**定义 101.1（固定确认点的 $\mathrm G_k$）。** 使用VI89.1、VII99.1的同一个有限维原 $V,C,u,K,P$ 和全部原 proper 仿射效应，保留严格正单位及整个原混态域。记

$$
\begin{gathered}
m=\dim\operatorname{aff}K=\dim V-1,\qquad
F_p=\{f\in[0,u]_{C^*}:f(p)=1\},\\
T_p(x)=\min_{f\in F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\},\qquad E_p=P\cap D_p.
\end{gathered}
\tag{VII101.1}
$$

这里 $p\in P$；$m$ 始终是仿射维数，不是矩阵环境余维。除构造101.6外，不限制整个 $P$ 的基数、闭性、光滑性或可数性，不预设ROG、PSD表示、内积、谱性或局部效应延拓。$\mathrm B$、$\mathrm A$、$S$ 仍取VI89.1—89.4的定义；只在明写 $\mathrm B$ 的结论中使用球形二纯面。

对整数 $k\ge0$，定义

$$
\mathrm G_k:\quad
\forall p\in P\ \forall Q\subseteq E_p,\ |Q|\le k,
\quad\exists f\in F_p\quad\forall q\in Q,\ f(q)=0.
\tag{VII101.2}
$$

$Q$ 是至多 $k$ 个不同原纯目标组成的有限集；允许空集，空集由 $u$ 确认。$p\notin D_p$，所以固定确认的纯点 $p$ 是额外一个标签：$\mathrm G_2$ 最多涉及三个纯标签，$\mathrm G_3$ 最多涉及四个。$\mathrm G_1$ 在本定义下自动成立，因为 $E_p$ 中每个点本来就可由某张 $F_p$ 效应排除；$\mathrm G_0$ 也为空要求。

区别在于

$$
\forall q\in Q\ \exists f_q\in F_p:\ f_q(q)=0
\quad\text{与}\quad
\exists f\in F_p\ \forall q\in Q:\ f(q)=0.
\tag{VII101.3}
$$

前者是分别排除，后者是同一效应共同排除，不能交换量词。目标之间不要求能被一张多结果测量彼此区分。原混态条件仍准确为

$$
\mathrm{Z0}:\quad
\forall p\in P\ \forall x,y\in D_p,\quad (x+y)/2\in D_p.
\tag{VII101.4}
$$

本章不把(VII101.4)预放入 $\mathrm G_k$ 的前提。

### 101.2 混态零拼合与全部有限纯目标

**引理 101.2（全域共同零的等价）。** 在定义101.1下，下列三项等价：原 $\mathrm{Z0}$；对每个 $p$，任意有限 $Q\subseteq E_p$ 可由同一原确认效应共同排除；对每个 $p$，存在 $g_p\in F_p$ 满足

$$
D_p=K\cap\{g_p=0\}.
\tag{VII101.5}
$$

这里即使 $P$ 不闭，所用分解也只是原 $K=\operatorname{conv}P$ 中的有限纯分解；共同零效应尚不被称为least确认。

证明。先核对紧性。原 $K$ 张成 $V$，从中取一个线性基；全部原效应在这个基上取值于 $[0,1]$，故效应区间有界，且由定义为闭集。因此它紧，$F_p$ 非空紧，$T_p$ 的最小值达到。$D_p$ 是紧集

$$
\{(f,x)\in F_p\times K:f(x)=0\}
$$

的投影，因而紧。这没有使用 $P$ 的紧性。

若有 $\mathrm{Z0}$，$D_p$ 中点凸且闭，故凸。非空时取 $z\in\operatorname{ri}D_p$ 及 $g_p\in F_p$，使 $g_p(z)=0$。对任意 $x\in D_p$，相对内点性给 $y\in D_p$、$0<t<1$，使 $z=tx+(1-t)y$；非负性迫使 $g_p(x)=0$。反向，$g_p(x)=0$ 本身就见证 $x\in D_p$，得到(VII101.5)。空 $D_p$ 取 $g_p=u$。这是V88.3共同零面论证在同一全效应域内的复用。于是任意有限纯目标当然可共同排除。

反过来，只设所有有限纯目标可共同排除。给 $x\in D_p$，选一张原 $h_x\in F_p$ 使 $h_x(x)=0$，再取原有限纯分解

$$
x=\sum_{a=1}^{s}\lambda_a q_a,\qquad
\lambda_a>0,\quad\sum_a\lambda_a=1,\quad q_a\in P.
\tag{VII101.6}
$$

$0=\sum_a\lambda_a h_x(q_a)$ 与逐项非负给每个 $q_a\in E_p$。对任意 $x,y\in D_p$ 都这样分解，将两分解中的纯目标合并成有限集。其共同确认效应同时零于 $x,y$，也零于它们的中点，故有原 $\mathrm{Z0}$。

同一论证还能直接接回共同零面：各闭集 $\{f\in F_p:f(q)=0\}$、$q\in E_p$ 具有有限交性质，$F_p$ 紧给一个同时零于全部 $E_p$ 的效应。由(VII101.6)，它也零于整个 $D_p$；反向包含仍由定义给出。因而这里从有限纯检验回到整个原混态域，没有把无限纯点集替换成抽样或闭包。证毕。

### 101.3 实际最小不相容组必与确认点仿射独立

**引理 101.3（对角见证与维数界）。** 若原 $\mathrm{Z0}$ 失败，则存在原纯 $p$ 和有限的不同目标 $q_1,\ldots,q_k\in E_p$，整组不能共同排除，但删掉任一目标后可以。必有

$$
2\le k\le m,
\qquad p,q_1,\ldots,q_k\text{ 仿射独立}.
\tag{VII101.7}
$$

证明。取实际失败的 $x,y\in D_p$，使 $(x+y)/2\notin D_p$。按(VII101.6)取两者的原有限纯分解。每个正权分量都在 $E_p$；若这些分量的有限并集可共同排除，中点也可排除，矛盾。从这个实际有限集选包含意义下最小的不相容子集 $\{q_1,\ldots,q_k\}$。空集与单点集都相容，所以 $k\ge2$。

逐一删掉 $q_i$，得到同一个原域中的效应 $f_i$，满足

$$
f_i\in F_p,\qquad f_i(q_j)=0\ (j\ne i),\qquad
 a_i:=f_i(q_i)\in(0,1].
\tag{VII101.8}
$$

$a_i>0$ 来自整组不相容：若为零，$f_i$ 就排除了整组；$a_i\le1$ 来自它在整个原 $K$ 上的proper上界。

先设 $\sum_i d_iq_i=0$ 且 $\sum_i d_i=0$。对这个仿射关系应用 $f_j$，得到 $d_ja_j=0$，因而全部 $d_j=0$。所以目标本身仿射独立。再假定 $p\in\operatorname{aff}\{q_1,\ldots,q_k\}$，写

$$
p=\sum_i c_iq_i,\qquad\sum_i c_i=1.
$$

每张 $f_i$ 都给 $1=c_i a_i$，故 $c_i=1/a_i\ge1$，与 $k\ge2$ 及 $\sum_i c_i=1$ 矛盾。于是 $p$ 不在目标的仿射包中，$p,q_1,\ldots,q_k$ 仿射独立，直接得 $k\le m$。这里既不只检查某个效应字典，也不需要Helly的额外有限化机制。证毕。

**推论 101.4（一般仿射维数的纯元数界）。** 对任意有限 $m\ge1$，

$$
\boxed{\mathrm G_m\quad\Longleftrightarrow\quad\mathrm{Z0}.}
\tag{VII101.9}
$$

证明。$\mathrm{Z0}$ 的方向由101.2给出。若有 $\mathrm G_m$ 而 $\mathrm{Z0}$ 失败，101.3给一个元数至多 $m$ 的不相容纯目标组，直接违反 $\mathrm G_m$。

$m=0$ 时整个 $K$ 为单点，$F_p=\{u\}$、$D_p=\varnothing$，$\mathrm{Z0}$ 与所有 $\mathrm G_k$ 都成立，不需不相容组。$m=1$ 时原紧凸体为线段，只有两端为纯点；对每个端点，确认它的原重心坐标使 $D_p$ 恰为另一端点，故 $\mathrm{Z0}$ 成立。这也说明(VII101.9)在 $m=1$ 与自动成立的 $\mathrm G_1$ 一致。证毕。

### 101.4 球形二纯面排除满维障碍

**定理 101.5（$\mathrm B$ 下少一个纯目标）。** 在定义101.1、$\mathrm B$ 及 $m\ge2$ 下，每个最小不相容纯目标组的元数至多 $m-1$，并且

$$
\boxed{\mathrm G_{m-1}\quad\Longleftrightarrow\quad\mathrm{Z0}.}
\tag{VII101.10}
$$

证明。任意有限最小不相容组都适用101.3证明中从(VII101.8)开始的论证，故只需排除 $k=m$。设有这样的组，沿用其原 $p,q_i,f_i,a_i$。此时 $p,q_1,\ldots,q_m$ 是原 $\operatorname{aff}K$ 的仿射基。定义

$$
\begin{gathered}
F=(f_1,\ldots,f_m),\qquad
F(p)=\boldsymbol 1,\qquad F(q_i)=a_i e_i,\\
S_0=\sum_{i=1}^{m}\frac1{a_i}>1,\qquad
L(y)=\sum_{i=1}^{m}\frac{y_i}{a_i},\qquad
h=\frac{L\circ F-1}{S_0-1}.
\end{gathered}
\tag{VII101.11}
$$

这里 $S_0$ 只是正数，区别于完整最小确认条件 $S$。像点 $a_i e_i$ 仿射独立并张成超平面 $L=1$，而 $L(\boldsymbol1)=S_0\ne1$，所以这些像点连同 $\boldsymbol1$ 也是仿射基。因此 $F:\operatorname{aff}K\to\mathbb R^m$ 是仿射同构，不是丢失信息的投影。每个 $f_i$ 在整个原 $K$ 上属于 $[0,1]$，故

$$
F(K)\subseteq[0,1]^m,\qquad
h(p)=1,\qquad h(q_i)=0,\qquad h\le1\text{ 于整个 }K.
\tag{VII101.12}
$$

最后一项来自 $L(F(x))\le S_0$。若再有 $h\ge0$ 于整个 $K$，它就是一张原proper确认效应并共同排除所有 $q_i$，违反不相容性。因此失败只能发生在下界：$\min_Kh<0$。这个仿射最小值的紧暴露面有一个极点，它也是原 $K$ 的极点，故可取原纯 $r$ 满足 $h(r)<0$。特别是 $r\ne p$。

置 $v=F(r)$、$t=L(v)<1$。由(VII101.12)，$v_i\ge0$。在同一条原线段上取

$$
\theta=\frac{S_0-1}{S_0-t}\in(0,1),\qquad
z=(1-\theta)p+\theta r.
\tag{VII101.13}
$$

于是 $L(F(z))=1$，且每个坐标 $F(z)_i=(1-\theta)+\theta v_i>0$。令 $\gamma_i=F(z)_i/a_i$，便有 $\gamma_i>0$、$\sum_i\gamma_i=1$，以及

$$
F(z)=\sum_i\gamma_iF(q_i).
$$

现在才用 $F$ 的可逆性，得到原空间中的真实等式

$$
z=\sum_i\gamma_iq_i
\in (p,r)\cap\operatorname{ri}\operatorname{conv}\{q_1,\ldots,q_m\}.
\tag{VII101.14}
$$

这不是把两个商像相等当成两个原点相等。原最小面 $H(p,r)$ 含 $z$，面的性质及全部 $\gamma_i>0$ 使它含每个 $q_i$。它又含 $p$，而这些点张成 $\operatorname{aff}K$，故该面含有 $K$ 的相对内点，只能等于 $K$。$p,r$ 是不同原纯点，所以 $\mathrm B$ 使整个原 $K$ 为一个仿射欧氏球。

在这个整球中，固定 $p$ 的对径唯一。任意原proper效应若在 $p$ 取一、在另一纯点取零，该纯点必为此对径：在单位球坐标写成 $a+b\cdot x$，proper界给 $\|b\|\le a\le1-\|b\|$，同时取一和零迫使 $a=\|b\|=1/2$，两个取等方向相反。对每个 $q_j$，因为 $m\ge2$，可选 $i\ne j$，由 $f_i(p)=1$、$f_i(q_j)=0$ 得 $q_j$ 是同一个 $p$ 的唯一对径。于是至少两个不同的 $q_j$ 被迫相等，矛盾。这覆盖 $m=2$，没有遗漏同点或退化球分支。

故 $k=m$ 不可能。若 $\mathrm G_{m-1}$ 成立而 $\mathrm{Z0}$ 失败，101.3的实际不相容组就给矛盾；反向由101.2。定理只给通用充分元数上界，未声称它在所有较高维数都最优。证毕。

### 101.5 等重心单纯形自由和的原全效应模型

**构造 101.6（成熟自由和与全部纯点）。** 取整数 $N\ge3$，在互补实方向空间 $U,V$ 中各放一个以原点 $o$ 为重心的 $(N-1)$ 维单纯形，顶点分别为 $a_1,\ldots,a_N$ 和 $b_1,\ldots,b_N$。例如各自在 $\{s\in\mathbb R^N:\sum s_i=0\}$ 中取 $e_i-\boldsymbol1/N$，再放入 $U\oplus V$ 的两因子。定义整个原模型

$$
\begin{gathered}
K_N=\operatorname{conv}\{a_1,\ldots,a_N,b_1,\ldots,b_N\},\qquad
\frac1N\sum_i a_i=\frac1N\sum_j b_j=o,\\
V_N=\mathbb R\oplus U\oplus V,\qquad
C_N=\{t(1,x):t\ge0,\ x\in K_N\},\qquad
u_N(t,w)=t.
\end{gathered}
\tag{VII101.15}
$$

$u_N$ 是严格正原单位；$C_N$ 闭、尖、生成，$K_N$ 与其整个归一基 $\{(1,x):x\in K_N\}$ 作保单位识别。以下省去首坐标一。使用这个原模型的全部proper效应，不为它预付任何矩阵表示。它是共享一个重心的自由和，仿射维数为 $m=2N-2$；不是仿射联结，也不是两个有序锥的直和。

任意原仿射函数 $f$ 的顶点值记为 $\alpha_i=f(a_i)$、$\beta_j=f(b_j)$。完整效应条件准确为

$$
0\le\alpha_i,\beta_j\le1,\qquad
\sum_i\alpha_i=\sum_j\beta_j.
\tag{VII101.16}
$$

证明其充分性而不只用必要性：等式两边除以 $N$ 得共同常数 $c=f(o)$；各组 $\alpha_i-c$、$\beta_j-c$ 都是零和数列。单纯形的顶点只满足各自的和为零关系，所以这些值分别唯一给出 $U,V$ 上的线性泛函；加共同常数 $c$ 就得到整个 $U\oplus V$ 上唯一仿射函数。顶点上的零一界再由凸性给整个 $K_N$ 上的零一界。反向由共同重心和proper性直接得到(VII101.16)。因此这里确实描述了原全部效应。

全部原纯点恰为这 $2N$ 个顶点。极点只可能来自给定有限生成集；而在 $A$ 侧给某个顶点值一、其他同侧顶点值 $-1/(N-1)$，在 $B$ 侧全取零，所得零和线性函数唯一暴露这个顶点。另一侧同理。

每对不同纯点也都暴露一条原真边。同侧一对可取该侧两点值一、其余点值 $-2/(N-2)$，另一侧全零；两侧各自零和，所以存在原线性函数，最大值一恰在这两个顶点达到。跨侧一对则在每侧所选顶点取一，该侧其余顶点取 $-1/(N-1)$，同样给最大面恰为这两点之间的线段。因此每个 $H(p,q)=[p,q]$，$\mathrm B$ 成立。这里的暴露线性函数只用于识别原面，不把它们直接称为proper效应。

定义原proper效应 $e_{ij}$：它在 $a_i,b_j$ 取一，在全部其他顶点取零。这满足(VII101.16)。对固定 $p=a_i$，所有其他同侧纯点都被每张 $e_{ij}$ 排除；任一 $b_\ell$ 可选 $j\ne\ell$ 排除。另一侧对称。因此每个不同纯对可由原全效应二元区分，原边上的对径端点满足 $\mathrm A$。

给任意至多 $N-1$ 个属于 $E_{a_i}$ 的目标，总有某个 $b_j$ 未被选中；同一张 $e_{ij}$ 排除这些全部目标。同理处理确认点位于另一侧的情形，故

$$
\mathrm B+\mathrm A+\mathrm G_{N-1}\text{ 在 }K_N\text{ 上成立}.
\tag{VII101.17}
$$

但固定 $p=a_i$ 后，全部 $N$ 个 $b_j$ 不可能共同排除：若 $\beta_j=0$ 对全部 $j$ 成立，(VII101.16)及非负性给全部 $\alpha_i=0$，与 $\alpha_i=1$ 矛盾。这个组的每个真子集可排除，所以它是实际最小不相容组，$\mathrm G_N$ 失败。

### 101.6 全原效应的精确转移、零facet并集与无least

**定理 101.7（完整确认区间的下包络）。** 在构造101.6中，任取一个原非负顶点分解

$$
x=\sum_{k=1}^N\lambda_k a_k+\sum_{\ell=1}^N\mu_\ell b_\ell,
\qquad\lambda_k,\mu_\ell\ge0,\qquad
\sum_k\lambda_k+\sum_\ell\mu_\ell=1.
\tag{VII101.18}
$$

则在全部原确认效应上精确有

$$
\boxed{\begin{aligned}
T_{a_i}(x)&=\min_{1\le j\le N}(\lambda_i+\mu_j),\\
T_{b_j}(x)&=\min_{1\le i\le N}(\lambda_i+\mu_j).
\end{aligned}}
\tag{VII101.19}
$$

这些值与分解的选择无关。原排除集为原暴露facet的并集，具体为

$$
\begin{gathered}
Q_{ij}=\operatorname{conv}\bigl(\{a_k:k\ne i\}\cup\{b_\ell:\ell\ne j\}\bigr)
       =K_N\cap\{e_{ij}=0\},\\
D_{a_i}=\bigcup_jQ_{ij},\qquad D_{b_j}=\bigcup_iQ_{ij}.
\end{gathered}
\tag{VII101.20}
$$

每个纯点均无全锥序least确认，但原纯转移数值仍互反。

证明。先固定 $p=a_i$。任意 $f\in F_{a_i}$ 的顶点值满足 $\alpha_i=1$，故

$$
s:=\sum_k\alpha_k=\sum_\ell\beta_\ell\ge1.
$$

取 $w_j=\beta_j/s$，则 $w_j\ge0$、$\sum_jw_j=1$ 且 $w_j\le\beta_j$。原确认效应 $e_w=\sum_jw_je_{ij}$ 在 $a_i$ 取一、其余 $A$ 顶点取零、在 $b_j$ 取 $w_j$。所以 $f-e_w$ 在每个原顶点非负，从而在整个 $K_N$ 及其齐次锥上非负。对每个原混态 $x$，

$$
f(x)\ge e_w(x)=\sum_jw_je_{ij}(x)
             \ge\min_j e_{ij}(x).
\tag{VII101.21}
$$

每张 $e_{ij}$ 自己又属于 $F_{a_i}$，故下界可由其中某张达到。由(VII101.18)，$e_{ij}(x)=\lambda_i+\mu_j$，得到第一式；交换两侧得到第二式。这是对每一张原确认效应的支配论证，没有用受限字典的最小值冒充全效应最小值。

良定义性也可直接看出。若另一归一顶点系数 $\lambda',\mu'$ 表示同一个 $x$，互补方向及各单纯形的唯一线性关系给

$$
\lambda'_k-\lambda_k=t\quad(\forall k),\qquad
\mu'_\ell-\mu_\ell=-t\quad(\forall\ell).
\tag{VII101.22}
$$

后一个常数为 $-t$ 来自总权重仍为一。因此每个 $\lambda_i+\mu_j$ 都不变，不只是它们的最小值不变。此结论适用于任意原非负分解，包括零权与重复顶点合并后的分解。

$e_{ij}\ge0$，其顶点零集恰为(VII101.20)列出的 $2N-2$ 个点，故整个零面就是它们的凸包。全部顶点唯一的仿射依赖由 $\sum a_i=\sum b_j$ 给出，并有全支撑；删掉任何顶点后剩余配置仿射独立。因此 $Q_{ij}$ 中的这些点仿射独立，其维数为 $2N-3=m-1$，确为原暴露facet。有限个非负数的最小值为零，当且仅当其中一个为零，给出两条并集公式。

每个不同原纯对的转移值为零，同点为一，所以

$$
T_p(q)=T_q(p)=\begin{cases}1,&p=q,\\0,&p\ne q.\end{cases}
\tag{VII101.23}
$$

这只有纯数值互反，尚不使 $T_p$ 成为仿射函数。若 $a_i$ 有least确认 $e$，对每个其他纯点 $q$，取一张排除 $q$ 的确认效应 $f_q$。$0\le e(q)\le f_q(q)=0$ 迫使 $e$ 在除 $a_i$ 外的全部顶点为零，却在 $a_i$ 为一，违反(VII101.16)。因此least不存在；另一侧同理。具体地，同一确认面中的 $e_{ij},e_{i\ell}$ 在 $b_j,b_\ell$ 的值相反，$j\ne\ell$ 时互不可比。后面的重心读数还将直接见证(VII101.20)的并集不是凸集。证毕。

### 101.7 双三角形与任意固定纯元数的反事实

**命题 101.8（四维的两个目标确实不足）。** 对 $N=3$，$m=4$ 的同一个原 $K_3$ 满足

$$
\mathrm B+\mathrm G_2+\mathrm A
\quad\text{及全部原纯数值互反},\qquad
\neg\mathrm G_3,\quad\neg\mathrm{Z0},\quad\neg S.
\tag{VII101.24}
$$

证明。前半和 $\neg\mathrm G_3$ 已由101.6—101.7在全部原效应上证明。固定 $p=a_1$，取两个原混态

$$
x=\frac{2b_1+b_2}{3},\qquad
y=\frac{b_2+2b_3}{3},\qquad
\frac{x+y}{2}=\frac{b_1+b_2+b_3}{3}=o.
\tag{VII101.25}
$$

$e_{13}$ 排除 $x$，$e_{11}$ 排除 $y$，二者都确认同一个 $p$。但对任意原 $f\in F_p$，重心关系给

$$
f(o)=\frac{\sum_i\alpha_i}{3}\ge\frac13;
\qquad T_p(o)=\frac13,
\tag{VII101.26}
$$

等号由任一 $e_{1j}$ 达到。因此 $x,y\in D_p$，它们的原中点却不在 $D_p$，直接违反完整混态 $\mathrm{Z0}$。无least已由101.7证明，所以完整 $S$ 也失败。所有二纯最小面仍是原暴露边，每两个被排除纯目标仍可由同一确认效应读零；缺失恰发生在三个目标的共同要求。这个反例否定 $\mathrm B+\mathrm G_2\Rightarrow\mathrm{Z0}$ 及其推出 $S$ 的版本，不否定 $\mathrm B+\mathrm G_2\Rightarrow\mathrm A$，因为它自己的 $\mathrm A$ 成立；也不否定 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$。证毕。

**推论 101.9（不存在跨所有有限维的固定纯元数替代）。** 对每个 $N\ge3$，构造101.6满足 $\mathrm G_{N-1}$、不满足 $\mathrm G_N$ 和 $\mathrm{Z0}$，且仍有 $\mathrm B+\mathrm A$ 与纯数值互反。一般 $N$ 的两个原混态反例可以统一取为

$$
x=b_1,\qquad y=\frac1{N-1}\sum_{j=2}^{N}b_j,\qquad
w=\frac{x+y}{2}.
\tag{VII101.27}
$$

证明。固定 $p=a_1$，$e_{12}(x)=0$、$e_{11}(y)=0$。$w$ 的同一原分解中 $\lambda_i=0$、$\mu_1=1/2$，其余 $\mu_j=1/[2(N-1)]$，故101.7准确给

$$
T_p(w)=\frac1{2(N-1)}>0.
\tag{VII101.28}
$$

全部 $B$ 顶点在这个分解中都有正权，不能留下额外的零权 $B$ 顶点供另一张 $e_{1j}$ 排除整个中点。共同重心仍有

$$
o=\frac1N x+\frac{N-1}{N}y,
\qquad T_p(o)=\frac1N,
\tag{VII101.29}
$$

后式或由(VII101.19)，或由任意确认效应的共同顶点和至少为一得到。$N=3$ 的对称中点(VII101.25)是专门的三点实现；将它照搬到 $N>3$ 会漏掉其余 $b_j$，不能作为一般反例。式(VII101.27)才覆盖全部 $N$。

任给固定 $k\ge1$，选择 $N\ge\max\{3,k+1\}$，则这个有限维原模型满足 $\mathrm G_k$ 却失败 $\mathrm{Z0}$，即使另给 $\mathrm B+\mathrm A$ 和纯数值互反也不改变结论。因此不存在独立于维数的固定纯目标元数替代原 $\mathrm{Z0}$。在这个自由和族中最小不相容组元数为 $N=m/2+1$；除四维情形外，这并不证明通用上界 $m-1$ sharp。证毕。

### 101.8 四维的三个纯目标与原四类几何

**定理 101.10（四维纯元数三的精确替换）。** 在定义101.1的同一个原载体及 $m=4$ 下，

$$
\boxed{\begin{aligned}
\mathrm B+\mathrm G_3
&\Longleftrightarrow\mathrm B+\mathrm{Z0}\\
&\Longleftrightarrow
K\cong_{\rm aff}\Delta_4,\ \mathbb B^4,\
\mathbb B^3*\Delta_0\ \text{或}\ \mathbb B^2*\Delta_1\\
&\Longleftrightarrow S.
\end{aligned}}
\tag{VII101.30}
$$

四类的全部原效应、least确认和局部proper效应的原全域延拓仍准确取定理99.8的公式；这些结论不是本定理的额外前件。在这一固定维数和 $\mathrm B$ 下，以至多几个原纯目标作统一替代，充分且最小的元数为三；固定确认纯点另算，合计至多四个纯标签。

证明。第一步直接应用101.5的 $m-1=3$，不预设 $\mathrm{Z0}$。第二步及四类的完整 $S$ 直接消费VII99.8，不重复四类证明。反向从 $S$ 复用VI89.4及least零面得到原 $\mathrm B+\mathrm{Z0}$，再由101.2得到 $\mathrm G_3$。101.8的同维 $K_3$ 满足 $\mathrm B+\mathrm G_2$ 却失败 $\mathrm{Z0}$，故元数二不足。这里的最小性只比较(VII101.2)这一族原纯目标检验；不声称整个物理包具有最少独立公理。证毕。

### 101.9 同一完整原数据上的几何替换候选

**定义与定理 101.11（$\mathsf R_{\mathrm{BG3},\le4}^{(4)}$）。** 固定定理99.10的同一个完整原装饰元组 $\mathcal O$、选定集合 $J\subseteq\{A,D,E\}$、共同适用域及全部非几何条件，并记

$$
J_4=\{X\in J:m_X=4\}.
$$

以99.10的完整 $\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)$ 为定义起点，仅对 $X\in J_4$ 把原几何项 $\mathrm B_X+\mathrm{Z0}_X$ 换为同一原载体的 $\mathrm B_X+\mathrm G_{3,X}$，所得完整谓词记为 $\mathsf R_{\mathrm{BG3},\le4}^{(4)}(\mathcal O)$。$J\setminus J_4$ 的几何项仍按99.10及VII98.8的原分支取 $\mathrm B_X+\mathrm{Z0}_X$；未选中的载体仍取其原几何项。这是精确局部替换定义，原 $\mathcal O$ 的其余每一条件逐项继承，不是只保留几何条件的摘要。于是同数据有

$$
\boxed{\begin{aligned}
\mathsf R_{\mathrm{BG3},\le4}^{(4)}(\mathcal O)
&\Longleftrightarrow\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm polar}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{\rm zero\text{-}ball}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm mid}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{86}^{\rm ev}(\mathcal O)
\Longleftrightarrow[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O).
\end{aligned}}
\tag{VII101.31}
$$

证明。逐 $X\in J_4$ 应用101.10，便恢复99.10的完整谓词；其余项按定义相同，再直接调用VII(99.37)。所有 $\mathrm G_{3,X}$ 都使用原 $P_X$ 和原整个 $F_{p,X}$，没有另造确认字典或把某个归一支撑子族当成整个确认面。

准确保留的非几何合同就是VI89.7—89.10、VII98.8—98.9和定理99.10的完整合同。特别是，原概率像自身的紧性、有限仿射维与每个原中点实现，原测试像自身的闭性、零、单位、中点、补、有界倍增及同一原测试对全部准备实现，原带质量输出和重复标签、全部非负缩放及零／次归一／不等质量，以及各过程与参考自身的全部相关联合输入域，均保留原量词。原全效应域和这些实际实现条件不能相互代付。

同一个原 $L,p,\omega$、两次使用同一读回、两实张成、全实 $Z$、含秩一分支的完整(83.8)、原迹／伴随／二次表示／单位、VI(89.13)全部两尺度等式、C2与整个 $G=1_E$，以及精确PRE后同一个原资格态的整个H13输出，均保持原定义；全部活跃块、严格负方向、共享总迹一、零质量及空活跃集仍在原域内。共同 $\mathfrak S(\mathcal O)$ 的设备／事件／来源绑定、全部菜单与分支、实际参考／副本／相关联合、记录／权限／控制／钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、实际混合服务、全部合法未来、旧支撑及每个中间切口也全部保留。

VI89.9与VII98.9中复型、Born、指定复合和读回、CP事件、Kraus与实际仪器、条件更新／Lüders、物理时间各自的完整前件继续原义；VI89.10的原生来源各入口、原射影结构与密度、全部字和terminal futures、联合行与菜单、原细标签及粗归组、记录后的条件未来、source-adoption map和资源合同也继续原义。已有入口已经导出的结论无需重付，但 $\mathrm G_3$ 不生成这些非几何对象或来源。故该完整候选压缩的是四维几何入口的目标域，不宣称减少整个包的独立前提或完成量子物理来源。证毕。

### 101.10 文献归属、尚存问题与白话

Beck—Jayawant—McAllister，*Lattice-Point Generating Functions for Free Sums of Convex Sets*，[arXiv:1207.0164v2，§1](https://arxiv.org/pdf/1207.0164v2)，将含原点、位于互补坐标子空间的两凸集之并的凸包称为free sum，并说明它与Cartesian product的极性对偶背景。本章的两方向空间可选择为两坐标因子，且共同重心在两单纯形内部，故借用的是这一成熟凸几何构造和名称。原文有关有理／整数格点、reflexive多面体、生成函数与Ehrhart公式的前件和结论都未用于这里的证明；本模型不以格点条件为前提。

Weiner，*Realization of an Arbitrary Structure of Perfect Distinguishability of States in General Probability Theory*，[arXiv:2301.06553v1，§1及§3](https://arxiv.org/pdf/2301.06553v1)，在全部仿射测量的GPT框架下区分两两完美区分与多态联合完美区分，并构造任意独立系统的联合区分结构。本章只借其成熟的一般GPT背景。该文的联合区分需要一张到单纯形的测量，为每个被区分态提供不同的确定结果；这里固定 $p$ 的共同排除只需一张二元效应把 $p$ 送到一、把所有目标一起送到零，并不区分这些目标。前一种测量可经结果合并给后一种二元效应，反方向并未成立。因此不把该文§3的独立系统构造直接认作本章固定确认点模型或反例的既有证明。

有限维紧凸纯分解、效应紧性、面与相对内部、最小不相容组、仿射依赖、球的唯一对径，以及Helly的一般凸交背景均属成熟方法；本章的元数证明直接从实际失败的有限分解取得见证，不另立Helly定理。原问题内的组合增量为：对角取值使确认点与最小共同零目标组仿射独立；以同一个原线段的真实交点和 $\mathrm B$ 排除满维组；由此得到一般的(VII101.9)—(VII101.10)及四维原 $\mathrm G_3$ 等价；再对等重心自由和的全部原效应给出(VII101.19)—(VII101.29)的精确计算和同数据回接。这些采用 `repo-derived` 归属，不将自由和、一般二元／联合区别或单纯形仿射关系本身重报为新理论，不主张全球原创、文献穷尽或kernel核验。

一般较高维 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 仍须在已有充分域之外解决VI90.10的全部原接触；101.5把 $\mathrm{Z0}$ 写成 $\mathrm G_{m-1}$ 后没有补上这一步。更强的通用纯元数上界及各较高维的最优值也未由本章确定。四维的 $\mathrm B+\mathrm G_2\Rightarrow\mathrm{Z0}$ 则已被101.8否定，不能继续列为未决问题。VI99的全实ROG域与本章任意原凸体的假设不同，不与这里的反例冲突。四维分类及纯目标压缩仍不推出复数、Born、指定复合、CP、仪器、更新、时间或实际来源；完整量子起源目标保持原未决边界。

白话说，先固定一个必须被确认的纯状态，再挑出几种各自能读零的纯目标；真正的问题是能否用同一张原测试让它们全读零。若最小的一组做不到，删去每个目标后留下的测试会像对角表一样标出它，因此这组目标连同确认点必须占据独立的仿射方向，有限维就限制了障碍的大小。球形二纯面又排除了占满全部方向的最后一种障碍：同一条原线段穿过目标单纯形内部，会把整个状态空间迫成球，所有目标却只能挤到确认点的唯一对径，产生矛盾。所以在四维，至多三个纯目标的共同零要求已经等价于全部混态零拼合；确认点另算，总共是四个纯标签。两个目标确实不够：两片共享重心、方向互补的三角形中，每两个目标都能一起读零，任意纯对仍有原边、可二元区分且数值互反，但三个对侧顶点无法一起读零，两种分别可排除的混态之中点最低仍读到三分之一。更高维可用更大的两单纯形把障碍推到任意固定元数之后。这一压缩恢复同一原数据上的四维几何与最小确认；完整候选中关于来源、操作、复合和时间的合同继续各负其责。

## 追加锚（本行以下为增补区）

## 102. 合格纯目标与确认面的双秩降阶及全锚点逐维最优性

### 102.1 同一原效应域内的逐源资格与两个秩

**定义 102.1（合格目标秩与确认效应秩）。** 完整采用VII101.1的同一个有限维原 $V,C,u,K,P,[0,u]$ 及 $F_p,T_p,D_p,E_p$。整个 $P=\operatorname{ext}K$ 可无限、不闭；不预设光滑、ROG、PSD、自对偶、谱性或局部效应延拓。固定原纯 $p$，定义

$$
\begin{gathered}
L_p=\operatorname{aff}(\{p\}\cup E_p),\qquad
d_p=\dim L_p,\qquad h_p=\dim\operatorname{aff}F_p,\\
b_p=\max\{1,\min\{h_p,d_p-1\}\},\qquad
m=\dim\operatorname{aff}K.
\end{gathered}
\tag{VII102.1}
$$

这里 $u\in F_p$，所以 $h_p=\dim\operatorname{span}\{f-u:f\in F_p\}$，且 $0\le h_p,d_p\le m$。$h_p$ 在本章专指整数维数，区别于VII100的规范facet效应记号；$m$ 是原仿射维数，绝不与ROG矩阵环境余维 $c$ 混用。$E_p=\varnothing$ 时 $L_p=\{p\}$、$d_p=0$，仍按同一公式取 $b_p=1$。

将VII101.1的全称条件拆为固定锚点的原谓词：

$$
\begin{aligned}
\mathrm G_k(p):\quad&
\forall\text{有限 }Q\subseteq E_p,\ |Q|\le k,
\quad\exists f\in F_p\quad f|_Q=0,\\
\mathrm{Z0}(p):\quad&
\forall x,y\in D_p,\quad (x+y)/2\in D_p,\\
\mathrm G_k&\Longleftrightarrow\forall p\in P,\ \mathrm G_k(p),\qquad
\mathrm{Z0}\Longleftrightarrow\forall p\in P,\ \mathrm{Z0}(p).
\end{aligned}
\tag{VII102.2}
$$

$\mathrm G_{b_p}(p)$ 的锚点先固定，再只取原合格目标 $E_p$；不同锚点可有不同 $b_p$。$\mathrm G_1(p)$ 由资格定义自动成立，空集由 $u$ 处理，不能将它计作额外物理信息。这里的有限性只限制一次共同排除的目标集，不限制整个 $P$。

原纯点零关系已经对称：若 $f(p)=1,f(q)=0$，则原补效应 $u-f$ 在 $q$ 取一、在 $p$ 取零。本章不以额外的纯数值互易 $\mathrm R:T_p(q)=T_q(p)$ 重新获得这一零对称性，也不把它计作新增结论。

### 102.2 最小不相容组同时受两个原秩限制

**定理 102.2（双秩障碍界）。** 固定 $p$。若 $\mathrm{Z0}(p)$ 失败，则有一个实际最小不相容组 $Q=\{q_1,\ldots,q_k\}\subseteq E_p$ 及原效应 $f_i$，满足

$$
\begin{gathered}
k\ge2,\qquad f_i\in F_p,\qquad
f_i(q_j)=a_i\delta_{ij},\qquad 0<a_i\le1,\\
p,q_1,\ldots,q_k\text{ 仿射独立},\qquad
k\le\min\{d_p,h_p\}.
\end{gathered}
\tag{VII102.3}
$$

同样的界适用于任意已经给定的有限最小不相容组，不以事先选定的混态反例为限。

证明。VII101.2的有限纯分解与共同零等价可逐 $p$ 使用；VII101.3从实际失败的有限组删到最小，给这里的 $q_i,f_i,a_i$ 及 $p,q_1,\ldots,q_k$ 的仿射独立。这些是既有结论的直接复用。所有这些点都在 $L_p$，故 $k\le d_p$。

还须核对确认面这一侧，而不能只援引目标空间维数。设

$$
\sum_{i=1}^k t_i(f_i-u)=0,\qquad
T=\sum_i t_i,\qquad S_0=\sum_i\frac1{a_i}>1.
$$

在每个 $q_j$ 评价给 $t_ja_j-T=0$，因而 $t_j=T/a_j$。求和得 $T=TS_0$；由 $S_0>1$，$T=0$，再得全部 $t_j=0$。于是 $f_i-u$ 线性独立，$u,f_1,\ldots,f_k$ 是 $F_p$ 中的 $k+1$ 个仿射独立点，故 $k\le h_p$。这使用原确认效应的实际对角读数，不以抽象Helly数替代此秩计算。证毕。

### 102.3 球形二纯面排除占满合格目标方向的障碍

**定理 102.3（最小点仍在原资格域内）。** 在定义102.1及全称原 $\mathrm B$ 下，任意固定 $p$ 的有限最小不相容组满足

$$
2\le k\le\min\{h_p,d_p-1\}.
\tag{VII102.4}
$$

证明。由102.2只需排除 $k=d_p$。沿用其 $q_i,f_i,a_i$，记 $L=L_p$，并在整个原 $K$ 上定义仿射函数

$$
\begin{gathered}
F=(f_1,\ldots,f_k),\qquad
\ell(y)=\sum_{i=1}^k\frac{y_i}{a_i},\qquad
S_0=\sum_{i=1}^k\frac1{a_i}>1,\\
\eta(x)=\frac{\ell(F(x))-1}{S_0-1}.
\end{gathered}
\tag{VII102.5}
$$

$F(p)=\boldsymbol1$、$F(q_i)=a_ie_i$；后面 $k$ 点张成 $\ell=1$ 的仿射超平面，$\ell(\boldsymbol1)=S_0\ne1$。因为 $p,q_1,\ldots,q_k$ 已是 $k$ 维 $L$ 的仿射基，

$$
F|_L:L\longrightarrow\mathbb R^k
\quad\text{是仿射同构}.
\tag{VII102.6}
$$

每个 $f_i$ 在原整个 $K$ 上满足 $0\le f_i\le1$，故 $\eta\le1$，且 $\eta(p)=1,\eta(q_i)=0$。若 $\eta\ge0$，它就是共同排除整组的原proper效应，矛盾。因此

$$
c_0=\min_K\eta<0.
$$

紧的最小值暴露面有原极点 $r\in P$ 达到 $c_0$。关键不是任取一个负值点后将它投到 $L$，而是使用同一个全局函数的真正最小点。定义

$$
g(x)=\frac{\eta(x)-c_0}{1-c_0}\quad(x\in K).
\tag{VII102.7}
$$

这是原 $K$ 上的仿射函数，满足 $0\le g\le1$、$g(p)=1$、$g(r)=0$；其齐次表达为 $(\eta-c_0u)/(1-c_0)$。于是 $g$ 是原proper确认效应，$r\in E_p\subseteq L$，且 $r\ne p$。这里没有把 $L\cap K$ 换成新状态体，也没有调用 $L$ 上局部效应的延拓。

置 $v=F(r)$、$t_0=\ell(v)<1$。所有 $v_i\ge0$，并且

$$
\theta=\frac{S_0-1}{S_0-t_0}\in(0,1),\qquad
z=(1-\theta)p+\theta r,
\qquad \ell(F(z))=1.
$$

$F(z)_i=(1-\theta)+\theta v_i>0$，故 $\gamma_i=F(z)_i/a_i$ 满足 $\gamma_i>0$、$\sum_i\gamma_i=1$，以及 $F(z)=\sum_i\gamma_iF(q_i)$。现在 $z,q_i$ 都在 $L$，(VII102.6)的可逆性才给原空间中的真实相交：

$$
z=\sum_i\gamma_iq_i
\in(p,r)\cap\operatorname{ri}\operatorname{conv}\{q_1,\ldots,q_k\}.
\tag{VII102.8}
$$

原最小面 $H(p,r)$ 含 $z$；面的性质与全部 $\gamma_i>0$ 使它包含所有 $q_i$。由 $\mathrm B$，这个整个原面是仿射欧氏球。$p,q_i$ 是原纯点，因而也是这个面的极点。对每个 $j$ 选 $i\ne j$，原 $f_i$ 限制到这个球仍有 $0\le f_i\le1$、$f_i(p)=1,f_i(q_j)=0$。球上一个proper仿射函数同时达到一和零时，两取等纯点必须为对径；单位球坐标中的条件为 $\|b\|\le a\le1-\|b\|$，同时取等迫使 $a=\|b\|=1/2$。所以所有不同的 $q_j$ 都必须等于 $p$ 在这个球中的唯一对径，与 $k\ge2$ 矛盾。

这里的球是 $H(p,r)$；不需要 $H(p,r)=K$，也不需要 $L=\operatorname{aff}K$。102.3对VII101.5的加强正是(VII102.7)保证最小点仍在原 $E_p$，从而让原真实交点论证在 $L_p$ 上成立。证毕。

### 102.4 逐源有限准则及低秩分支

**推论 102.4（双秩有限纯目标准则）。** 在同一原有限维载体上，

$$
\boxed{\mathrm B\quad\Longrightarrow\quad
\forall p\in P:\quad
\bigl[\mathrm{Z0}(p)\Longleftrightarrow\mathrm G_{b_p}(p)\bigr].}
\tag{VII102.9}
$$

因此在 $\mathrm B$ 下，原全部混态 $\mathrm{Z0}$ 等价于 $\forall p\in P,\ \mathrm G_{b_p}(p)$。$b_p$ 是从原资格域与原确认面得到的充分检验上界，不声称每个特定 $K,p$ 的实际最小充分元数都等于 $b_p$。

证明。$\mathrm{Z0}(p)$ 到全部有限纯目标共同排除，直接逐源复用VII101.2。若反向失败，102.2给实际最小不相容组，102.3使其元数 $k\ge2$ 且 $k\le\min\{h_p,d_p-1\}\le b_p$，违反 $\mathrm G_{b_p}(p)$。

低秩分支也由此完整包含。$E_p=\varnothing$ 时，VII101.6的非负纯分解表明 $D_p=\varnothing$，两条件均为空真。$h_p\le1$ 或 $d_p\le2$ 时不可能有(VII102.4)的最小组，故 $\mathrm{Z0}(p)$ 自动成立，$b_p=1$，没有增加假设。$m=0$ 时 $K$ 为单点、$F_p=\{u\}$、$h_p=d_p=0$；$m=1$ 时 $K$ 为线段，端点的原重心坐标确认给 $D_p$ 为另一端点，$d_p=h_p=1$。两者均落在 $b_p=1$ 分支。特别地 $m=2$ 的 $\mathrm B$ 域也自动有 $\mathrm{Z0}$。

对 $m\ge2$，$b_p\le m-1$，所以VII101.5的全称 $\mathrm G_{m-1}$ 仍是统一充分条件；(VII102.9)允许每个源按自己实际的两种秩降低检验数。它不把仅一个固定源满足条件写成全部源满足条件。证毕。

### 102.5 加权自由和的原顶点、原面与全部效应字典

**定义 102.5（整个加权单纯形回路）。** 取整数 $r,s\ge2$，正数 $u_i,v_j$ 满足 $\sum_i u_i=\sum_jv_j=1$。在互补方向空间 $U,W$ 中，取维数分别为 $r-1,s-1$ 的单纯形，顶点为 $a_i,b_j$，满足

$$
\sum_{i=1}^r u_i a_i=\sum_{j=1}^s v_jb_j=o=0,
\qquad
K=\operatorname{conv}(\{a_i\}_i\cup\{b_j\}_j),
\qquad m=r+s-2.
\tag{VII102.10}
$$

$u_i,v_j$ 是关系权重，原单位仍是齐次化空间 $\mathbb R\oplus U\oplus W$ 上的 $u(t,w)=t$；原锥是 $\{t(1,x):t\ge0,x\in K\}$。它闭、尖、生成，$u$ 严格正，整个归一基就是此 $K$。两侧的 $o$ 均为相对内点；其正权平均给整个 $K$ 的相对内点。此处取的是成熟的单纯形自由和及全支撑仿射回路，不把它们另立为新多面体分类。

为后面的全锚点证明，先把其原字典核对完整。互补性与每侧单纯形的唯一线性关系表明，全部顶点的仿射关系恰为

$$
(\Delta\lambda_i,\Delta\mu_j)=t(u_i,-v_j).
\tag{VII102.11}
$$

每个非零关系在两侧都有至少两个非零系数，故没有一个所列点是其余点的凸组合。有限凸包不再有其他极点，所以 $P$ 恰为全部这 $r+s$ 个顶点；不是在更大原纯点集中只挑出一条关系。原全效应的精确条件因此是

$$
\alpha_i=f(a_i),\quad\beta_j=f(b_j),\qquad
0\le\alpha_i,\beta_j\le1,\qquad
\sum_i u_i\alpha_i=\sum_jv_j\beta_j.
\tag{VII102.12}
$$

充分性可直接复用VI(92.8)：此关系就是整个仿射关系空间。亦可令共同加权值为 $c$，分别将 $\alpha_i-c$、$\beta_j-c$ 唯一实现为 $U,W$ 上的线性泛函，再加常数 $c$；顶点零一界给整个 $K$ 上的proper界。这是原全部效应，不是一个预选子字典。

原真面的顶点子集恰为两侧各至少遗漏一个点的子集。必要性在于：若一个面含整侧顶点，就含 $o\in\operatorname{ri}K$，只能是 $K$。充分性可沿VI92.3的成熟面证书写出：对这样的子集 $S$，令未选两侧权重分别为

$$
U_S=\sum_{a_i\notin S}u_i>0,\qquad
V_S=\sum_{b_j\notin S}v_j>0.
$$

在 $S$ 上赋零，未选 $A$ 顶点赋 $V_S/(U_S+V_S)$，未选 $B$ 顶点赋 $U_S/(U_S+V_S)$。两侧加权值相等且都在 $[0,1]$，所以这是一张原proper效应，其整个零面正是 $\operatorname{conv}S$。允许空面。特别地，$r,s\ge3$ 时任意两个不同顶点组成的集合都在两侧留下遗漏点，它们的整个最小面就是原真边，故全称 $\mathrm B$ 成立。这里复用的是标准仿射回路面结构，而非从一张局部线段尺假定全域延拓。

### 102.6 原资格阈值与全部混态的加权下包络

**命题 102.6（共同排除的容量条件与全效应比较）。** 在定义102.5的整个原模型中，固定 $p=a_i$，任取 $Q\subseteq P\setminus\{a_i\}$，有精确充要条件

$$
\exists f\in F_{a_i},\ f|_Q=0
\quad\Longleftrightarrow\quad
\sum_{j:b_j\in Q}v_j\le1-u_i.
\tag{VII102.13}
$$

因此同侧所有不同纯点都属于 $E_{a_i}$，而

$$
b_j\in E_{a_i}\quad\Longleftrightarrow\quad u_i+v_j\le1.
\tag{VII102.14}
$$

交换两侧，对源 $b_j$ 的条件准确为 $\sum_{i:a_i\in Q}u_i\le1-v_j$；其同侧不同纯点也全部合格。若在合格目标中取最小不相容组，必全部来自对侧，并且其权重和首次超过这个阈值；其中每个单目标仍须先满足(VII102.14)，不能把不合格点塞入较短障碍。

任取原混态的任一非负归一顶点分解

$$
x=\sum_k\lambda_k a_k+\sum_j\mu_jb_j,
\qquad\lambda_k,\mu_j\ge0,\quad\sum_k\lambda_k+\sum_j\mu_j=1.
$$

原全部确认效应的最小值是

$$
\boxed{\begin{aligned}
T_{a_i}(x)&=\lambda_i+
\min\left\{\sum_j\mu_j\gamma_j:
0\le\gamma_j\le1,\ \sum_jv_j\gamma_j=u_i\right\},\\
T_{b_j}(x)&=\mu_j+
\min\left\{\sum_i\lambda_i\delta_i:
0\le\delta_i\le1,\ \sum_i u_i\delta_i=v_j\right\}.
\end{aligned}}
\tag{VII102.15}
$$

两式均与所用分解无关，最小值均由原proper效应达到。特别地，记 $t_+=\max\{t,0\}$，跨侧纯值准确为

$$
T_{a_i}(b_j)=\frac{(u_i+v_j-1)_+}{v_j},\qquad
T_{b_j}(a_i)=\frac{(u_i+v_j-1)_+}{u_i}.
\tag{VII102.16}
$$

证明。(VII102.13)的必要性来自 $\alpha_i=1$、选中 $B$ 目标的 $\beta_j=0$，以及

$$
u_i\le\sum_k u_k\alpha_k=\sum_{b_j\notin Q}v_j\beta_j
\le1-\sum_{b_j\in Q}v_j.
$$

反向令 $\alpha_i=1$、其他 $\alpha_k=0$，选中 $B$ 目标取零，未选 $B$ 点统一取 $u_i/(1-\sum_{b_j\in Q}v_j)$。前件保证分母至少为 $u_i>0$，且全部赋值在 $[0,1]$，(VII102.12)给所需原效应。同侧目标不增加任何容量，所以最小不相容组不能含同侧点。取单目标得资格式，另一侧完全同理。

为证(VII102.15)确实遍历原全部效应，任取 $f\in F_{a_i}$，记

$$
c_f=\sum_k u_k\alpha_k=\sum_j v_j\beta_j\ge u_i>0.
$$

将它改为顶点赋值

$$
\widetilde\alpha_i=1,\qquad\widetilde\alpha_k=0\ (k\ne i),
\qquad\widetilde\beta_j=\frac{u_i}{c_f}\beta_j.
\tag{VII102.17}
$$

这些值仍在 $[0,1]$ 且两侧加权值恰为 $u_i$，故给一张原 $\widetilde f\in F_{a_i}$；它在每个原顶点都不大于 $f$，于是于整个原 $K$ 乃至原锥上满足 $\widetilde f\le f$。所以原全部确认效应的最小值可在这个精确截片上取得。截片非空（可取全部 $\gamma_j=u_i$）且紧，目标线性，最小值达到；每个截片点又都由(VII102.12)给原proper效应，从而上下界相合。交换两侧得第二式。

两种归一分解之差由(VII102.11)给

$$
\lambda'_k=\lambda_k+t u_k,\qquad
\mu'_j=\mu_j-t v_j.
$$

对截片中的每一个 $\gamma$，表达式变化恰为 $t u_i-t\sum_jv_j\gamma_j=0$；因此不只最小值不变，截片中的每个候选值都不变。这允许零分解系数，没有另换混态模型。

最后，在源 $a_i$ 下最小化单个 $\gamma_j$，其他坐标最多承担 $1-v_j$ 的加权量，故它至少为 $(u_i+v_j-1)_+/v_j$。若 $u_i\le1-v_j$，取 $\gamma_j=0$、其他坐标统一取 $u_i/(1-v_j)$；否则其他坐标全取一并令 $\gamma_j=(u_i+v_j-1)/v_j$。两支都在原截片中达到下界，另一方向交换两侧即得。

VI92.2及既有WeightedRelationConfirmation已经给分组重心中点的精确值；这里不将该既有值再计作新增。式(VII102.15)把计算写到同一一关系载体上的任意混态，并为下面的全锚点元数计算提供直接接口。证毕。

### 102.7 不均匀三角形侧把全称障碍推迟到m减一

**定理 102.7（每个 $m\ge4$ 的全锚点最优族）。** 对每个整数 $n\ge3$，在定义102.5中取

$$
\begin{gathered}
r=3,\qquad s=n,\qquad m=n+1,\\
u_0=1-2\varepsilon,\quad u_1=u_2=\varepsilon,
\qquad v_j=1/n,\qquad 0<2\varepsilon<1/n.
\end{gathered}
\tag{VII102.18}
$$

$A$ 侧记为 $a_0,a_1,a_2$，$B$ 侧为 $b_1,\ldots,b_n$。这个整个原模型满足

$$
\boxed{\mathrm B+\mathrm G_{n-1},\qquad
\neg\mathrm G_n,\qquad\neg\mathrm{Z0}.}
\tag{VII102.19}
$$

因此对每个仿射维数 $m\ge4$，仅在原 $\mathrm B$ 域内，以VII101.1的全称同类纯目标条件替代 $\mathrm{Z0}$，统一充分元数 $m-1$ 已经逐维最小：$\mathrm B+\mathrm G_{m-2}$ 不足。这里的下界量化全部原锚点，不能由只检查一个轻源代替。

证明。两侧顶点数都至少三，102.5已核对每个不同纯对的整个最小面为真边，所以原全称 $\mathrm B$ 成立。接着分别核对全部三类源。

对重源 $a_0$，有 $u_0+1/n>1$，所以

$$
E_{a_0}=\{a_1,a_2\}.
$$

取原赋值 $\alpha_0=1,\alpha_1=\alpha_2=0$、全部 $\beta_j=u_0$，即同时排除全部合格目标。因此这个源满足所有 $\mathrm G_k(a_0)$；其 $d_{a_0}=2$，(VII102.1)也只要求自动成立的 $\mathrm G_1(a_0)$。

对任一轻源 $a_i$、$i=1,2$，有 $\varepsilon+1/n<1$，所以

$$
E_{a_i}=P\setminus\{a_i\}.
$$

任取至多 $n-1$ 个合格目标，总有一个 $b_{j_0}$ 未选。令 $\alpha_i=1$、其他 $\alpha_k=0$，$\beta_{j_0}=n\varepsilon$、其他 $\beta_j=0$。由于 $0<n\varepsilon<1/2$，这给原proper确认效应，且共同排除所选全部目标，包括其中可能出现的重顶点。故两个轻源都满足 $\mathrm G_{n-1}(a_i)$。若要求排除全部 $n$ 个 $b_j$，其总关系权重为一，严格大于 $1-\varepsilon$，由(VII102.13)不可能。每个真子集仍可共同排除，所以它们是实际元数 $n$ 的最小不相容组。

对任一对侧源 $b_j$，资格准确为

$$
E_{b_j}=\{a_1,a_2\}\cup\{b_\ell:\ell\ne j\};
\qquad a_0\notin E_{b_j}.
$$

取 $\beta_j=1$、其余 $\beta_\ell=0$，$\alpha_1=\alpha_2=0$、$\alpha_0=1/(n u_0)$。由 $u_0>1-1/n$ 及 $n\ge3$，$0<1/(nu_0)<1$；两侧加权值均为 $1/n$。所以这也是一张原proper确认效应，且同时排除这个源的全部合格目标，给所有 $\mathrm G_k(b_j)$。

至此全部原源都满足 $\mathrm G_{n-1}$，两个轻源失败 $\mathrm G_n$，VII101.2再给 $\neg\mathrm{Z0}$。较短的反向三目标集合 $\{a_0,a_1,a_2\}$ 不能作为 $b_j$ 的合格不相容组，因为其中 $a_0$ 连单独都不合格；仅数回路两侧的顶点数会漏掉这个条件。

轻源还使双秩上界本身达到一般最大值：$d_{a_i}=m$，且 $h_{a_i}=m$。后者可在 $\alpha_i=1$ 的超平面内，给其他 $\alpha_k$ 统一取小的 $\delta\in(0,1)$，再令全部 $\beta_j=\varepsilon+\delta(1-\varepsilon)\in(0,1)$，取得其余所有坐标严格在零一界内部的点。原赋值空间只有一个关系，确认再去掉一维，所以 $\dim\operatorname{aff}F_{a_i}=r+s-2=m$。于是 $b_{a_i}=m-1=n$；任何声称在仅 $\mathrm B$ 域内一律用 $m-2$ 个目标的替换，都被同维的整个原模型否定。四维的最小元数三已由VII101.8—101.10给出；此族把逐维结论延伸到全部 $m\ge4$，并未将原四维结论重新计作新结果。证毕。

### 102.8 轻源全部混态的值、五维整数实现及互易边界

**命题 102.8（原中点精确缺口及七点实现）。** 在102.7中，对任一轻源 $a_i$、$i=1,2$，任意非负归一顶点分解均给

$$
T_{a_i}(x)=\lambda_i+n\varepsilon\min_j\mu_j.
\tag{VII102.20}
$$

其 $D_{a_i}$ 是原暴露facet

$$
Q_{ij}=\operatorname{conv}(P\setminus\{a_i,b_j\})
$$

的并集。取原态

$$
x=b_1,\qquad y=\frac1{n-1}\sum_{j=2}^n b_j,\qquad w=(x+y)/2,
$$

有

$$
T_{a_i}(x)=T_{a_i}(y)=0,\qquad
T_{a_i}(w)=\frac{n\varepsilon}{2(n-1)}>0,
\qquad T_{a_i}(o)=\varepsilon.
\tag{VII102.21}
$$

在 $m=5$ 可取七个整数坐标顶点

$$
\begin{gathered}
a_0=(-1,-1;0,0,0),\quad a_1=(14,0;0,0,0),\quad a_2=(0,14;0,0,0),\\
b_1=(0,0;1,1,1),\quad b_2=(0,0;1,-1,-1),\\
b_3=(0,0;-1,1,-1),\quad b_4=(0,0;-1,-1,1),\\
14a_0+a_1+a_2=4\sum_{j=1}^4b_j.
\end{gathered}
\tag{VII102.22}
$$

它满足 $\mathrm B+\mathrm G_3$ 而失败 $\mathrm G_4$ 和原混态 $\mathrm{Z0}$；上式轻源中点的最低原确认值为 $1/24$，共同内点值为 $1/16$。但原纯数值互易 $\mathrm R$ 失败。

证明。在(VII102.15)中，轻源的约束为 $\sum_j\gamma_j=n\varepsilon<1/2$。任意可行向量都有

$$
\sum_j\mu_j\gamma_j\ge n\varepsilon\min_j\mu_j,
$$

把全部 $n\varepsilon$ 放在一个最小 $\mu_j$ 坐标即可达到，仍满足各坐标不超过一。这证明任意混态的(VII102.20)。其达到效应在 $a_i$ 取一、在相应 $b_j$ 取 $n\varepsilon$，其他顶点取零，因此整个零面为 $Q_{ij}$。删去这两个点后留下 $m$ 个仿射独立顶点，故它是维数 $m-1$ 的原facet；全部最低值为零当且仅当至少一张这样的效应取零，得到并集式。另一方面，重源及 $b_j$ 源的全部合格目标已有同一张效应排除，VII101.6直接给

$$
D_{a_0}=\operatorname{conv}\{a_1,a_2\},\qquad
D_{b_j}=\operatorname{conv}\bigl(\{a_1,a_2\}\cup\{b_\ell:\ell\ne j\}\bigr).
$$

对(VII102.21)的 $w$，其 $B$ 权重为 $\mu_1=1/2$、$\mu_j=1/[2(n-1)]$（$j\ge2$），且 $\lambda_i=0$；全部 $B$ 顶点都有正权，所以最低值严格为正。$x$ 与 $y$ 各自缺少至少一个 $B$ 顶点，最低值为零。共同内点 $o=\sum_jb_j/n$ 给最低值 $\varepsilon$。这些分组态的中点值也正是VI92.2的已有效果：取 $t=\varepsilon$、分组权 $b=1/n$，其 $t/(2\max\{b,1-b\})$ 等于这里的数值；此特殊精确缺口属于复用。

七点坐标的两方向分别张成 $\mathbb R^2$ 和 $\mathbb R^3$，两侧分别为三角形及四面体，正权重准确为

$$
(u_0,u_1,u_2)=(7/8,1/16,1/16),\qquad v_j=1/4.
$$

故 $\varepsilon=1/16,n=4$，(VII102.21)给 $4/(16\cdot6)=1/24$，共同内点值 $1/16$；102.7已核对全部七个源。

一般族的重源与任一 $b_j$ 有

$$
T_{a_0}(b_j)=1-2n\varepsilon,\qquad
T_{b_j}(a_0)=\frac{1/n-2\varepsilon}{1-2\varepsilon}.
\tag{VII102.23}
$$

两值的共同正分子为 $1/n-2\varepsilon$，分母分别为 $1/n$ 和 $1-2\varepsilon$，二者不等；所以整个族均不满足 $\mathrm R$。七点例中准确为 $1/2$ 和 $1/7$。这些点仍是原边的对径端点，因而此族的 $\mathrm A$ 也失败；它同时失败 $\mathrm{Z0}$，没有反驳一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$。特别地，五维七点例不满足 $\mathrm B+\mathrm R+\mathrm G_3$ 的前件，不能据它否定该附加互易域的待证问题。仅 $\mathrm B$ 域的逐维最优性不能搬到 $\mathrm B+\mathrm R$ 域。证毕。

### 102.9 完整原装饰数据中的精确逐源替换

**定义与定理 102.9（完整 $\mathsf R_{\rm rank,\le4}$ 候选）。** 固定VII99.10的同一个完整原装饰元组 $\mathcal O$、选定 $J\subseteq\{A,D,E\}$、共同适用域及共同来源合同 $\mathfrak S(\mathcal O)$。对每个原载体 $X$，用其自己的原 $P_X,F_{p,X},E_{p,X}$ 定义

$$
\begin{gathered}
d_{p,X}=\dim\operatorname{aff}(\{p\}\cup E_{p,X}),\qquad
h_{p,X}=\dim\operatorname{aff}F_{p,X},\\
b_{p,X}=\max\{1,\min\{h_{p,X},d_{p,X}-1\}\},\qquad
\mathcal G_{{\rm rank},X}:\quad
\forall p\in P_X,\ \mathrm G_{b_{p,X},X}(p).
\end{gathered}
\tag{VII102.24}
$$

从VII99.10定义的完整 $\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)$ 出发，仅将所选 $X\in J$ 的原几何项 $\mathrm B_X+\mathrm{Z0}_X$ 改写为 $\mathrm B_X+\mathcal G_{{\rm rank},X}$，其余每一项完整继承；所得谓词为 $\mathsf R_{\rm rank,\le4}(\mathcal O)$。它与VII101.11的 $\mathsf R_{\mathrm{BG3},\le4}^{(4)}(\mathcal O)$ 使用同一 $J$、同一 $\mathcal O$ 及同一共同域。于是

$$
\boxed{\begin{aligned}
\mathsf R_{\rm rank,\le4}(\mathcal O)
&\Longleftrightarrow\mathsf R_{\mathrm{BG3},\le4}^{(4)}(\mathcal O)
\Longleftrightarrow\mathsf R_{\mathrm{BZ},\le4}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{\rm polar}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm zero\text{-}ball}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{\rm mid}(\mathcal O)
\Longleftrightarrow\mathsf R_{86}^{\rm ev}(\mathcal O)
\Longleftrightarrow[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O).
\end{aligned}}
\tag{VII102.25}
$$

证明。对所选每个 $X$，102.4在同一个原载体上给

$$
\mathrm B_X+\mathcal G_{{\rm rank},X}
\Longleftrightarrow\mathrm B_X+\mathrm{Z0}_X.
\tag{VII102.26}
$$

这条逐源替换对任意有限仿射维都成立；它本身没有低维、有限 $P_X$ 或表示前件。但(VII102.25)再回到完整 $S_X$ 和旧包的那一步，仍准确使用VII99.10、VII98.8的原共同适用域：单点、原 $m_X<3\delta_X$ 分支、$1\le m_X\le4$，或正维球形facet等各自已有充分条件。四维分支与VII101.11的原 $\mathrm G_{3,X}$ 等价直接复用VII101.10。域外的一般高维 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 并未由(VII102.26)得到证明。

完整继承具有逐项含义：VI89.7—89.10、VII98.8—98.9和VII101.11规定的全部原准备、测试、过程、参考、读回、装饰及来源数据、原像自身的紧闭与中点／补／有界倍增条件、同一测试对全部准备实现、重复标签、带质量输出和全部非负缩放、零与次归一及不等质量、原过程自身的全部相关联合输入域均保持原量词。它们不是 $\mathcal G_{\rm rank}$ 的推论。

同一个原 $L,p,\omega$ 与两次同一读回、两实张成、全实 $Z$、含秩一分支的完整(83.8)、原单位／迹／伴随／二次表示、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$，以及精确PRE之后同一资格态的整个H13输出仍完整保留。严格负方向、共享总迹一、活跃及非活跃块、零质量和空活跃集继续在其原域；这里的仿射维数 $m_X$ 不改写VI89.7中其他有类型的尺度参数。共同 $\mathfrak S(\mathcal O)$ 的设备／事件／来源绑定、菜单和分支、参考／副本／相关联合、记录／权限／控制／钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、实际混合服务、合法未来、旧支撑及每个中间切口逐项继承。

复型与Born、指定复合和读回、同事件CP、Kraus及实际仪器、条件更新与Lüders、物理时间继续消费VII98.9和VI89.9各自的完整前件；原生来源及细化继续消费VI89.10的原几何、密度、全字、terminal futures、联合菜单／全部有符号关系、原细标签与粗归组、记录后条件未来、source-adoption map及资源合同。已有入口实际导出的后果直接复用，不重新列为缺口。这里只精化原谓词内部的几何检验，不替换原状态体，也不自动减少整个物理包的独立前件。

若另有VI99.7的完整全实ROG前件，原 $\mathrm G_2\Longleftrightarrow\mathrm{Z0}\Longleftrightarrow S$ 可在交集中直接使用；其他实／复低余维分支亦仅按VI99.8自己的原域消费。反过来，双秩准则及本章有限加权模型都不供应ROG表示。证毕。

### 102.10 数学归属、未决桥梁与完整白话

**约定 102.10（复用范围与理论边界）。** VII101.2—101.3的有限纯闭合、最小不相容组与仿射独立，VII101.5的 $m-1$ 一般充分界，以及VII99.8、VII101.10的四维分类与既有最优值均按原范围复用。双秩部分的新增组合为：由 $f_i-u$ 的独立性读取原确认面维数；由原全域最小点的proper归一化证明 $r\in E_p$；再于 $L_p$ 中保持真实交点和原球唯一对径矛盾。这给(VII102.9)，不要求整个 $H(p,r)=K$。

一关系部分直接引用VI92.1—92.3。[WeightedRelationConfirmation](../../../Blueprint/D5/S3/Quantum/Foundation/WeightedRelationConfirmation.md)及其[原声明源码](../../../D5/S3/Quantum/Foundation/WeightedRelationConfirmation.lean)的 `full_effect_iff`、`relation_effect` 对应全部原纯点、全部关系上的有界平衡赋值下降；`weighted_gap_after_exchange` 在全关系零度一、正权及交换后最小权重源上给任意非空真分组的原混态精确缺口，并允许原零系数顶点保留。[FinitePureSimplex](../../../Blueprint/D5/S3/Quantum/Foundation/FinitePureSimplex.md)及其[原声明源码](../../../D5/S3/Quantum/Foundation/FinitePureSimplex.lean)的 `zero_kernel_least_confirmation` 处理整个关系核为零，`zero_gluing_iff_simplex` 处理整个核维数至多一，均不要求球性。它们的对应Blueprint叙述与VI92保留这些全载体前件；本章不将已有效应下降、一关系失败 $\mathrm{Z0}$ 或分组中点精确值重报为新增。加权部分的组合增量是(VII102.13)—(VII102.17)的资格／全混态接口与不均匀 $3\mid n$ 族的全部锚点核对，从而建立每个 $m\ge4$ 的全称最优性，而非只找到一个固定源的长障碍。

Beck—Jayawant—McAllister，*Lattice-Point Generating Functions for Free Sums of Convex Sets*，[arXiv:1207.0164v2，§1](https://arxiv.org/pdf/1207.0164v2)，以含原点、位于正交坐标子空间的两凸集之并的凸包定义free sum。本章的互补方向可选择为两个坐标因子，且共同原点在各单纯形内部，故借用其成熟构造与名称；不使用该文的格点、reflexive条件、Ehrhart或生成函数结论。全支撑仿射回路、标准面证书及一关系赋值使用VI92的Gale／Radon背景；VII100的任意关系零度facet计算仍按自身完整 $\mathrm{Z0}$ 前件保留，不由这里的一关系族重新证明。上述秩与全锚点最优性组合采用 `repo-derived` 归属，不主张全球首创、文献穷尽或Lean kernel核验。

一般高维原 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 及其完整量子起源仍未由本章解决；双秩条件精确重写的是 $\mathrm{Z0}$，不是到 $\mathrm A$ 的缺失桥。仅 $\mathrm B$ 域内 $m\ge4$ 的统一元数问题由102.7确定，但附加全部纯数值互易 $\mathrm R$ 后的更强高维界未由这一不互易族确定，特别是五维 $\mathrm B+\mathrm R+\mathrm G_3$ 问题仍需独立处理。复型、Born、指定复合、CP、仪器、更新、时间和实际来源的条件仍为102.9所准确继承者；这里的纸面数学不作经验实现或完整物理来源认证。

白话说，先固定一个必须读一的纯状态，只把那些本来就能单独读零的原纯状态列为合格目标，再问能否用同一张原测试让一组选中的目标全读零。一个最小失败组会让删去不同目标后取得的测试形成对角表，所以它既要占据足够多的合格目标方向，也要占据足够多的确认测试方向；这是两种秩。若它恰好占满合格目标的方向，把这些原测试合成的一把尺在全状态空间取最小值，再按真实最小值归一化，就会得到另一个仍合格的原纯点。确认点到这个点的真实线段穿过目标单纯形内部，把所有目标装进同一个原球面；它们却都必须是确认点唯一的对径，于是矛盾，目标方向的上界因此还能减一。最优反例由共享一个内点的三角形和更大单纯形组成：三角形中两个顶点很轻，确认它们时，只需让对面某个尚未被要求读零的顶点承担一点正值，所以删去对面任意一个目标总能成功，全部目标同时出现才暴露冲突。很重的第三个顶点则让反向的短障碍失去资格——对侧源连单独排除它都做不到，不能拿它凑成更短的合格失败组。这样每个原源都通过小一阶的检验，整组却仍失败，证明仅球形二纯面下的通用阶数已经最优。轻源的两种分别可排除状态混合后，最低读数可以精确算成正数；五维七点例是二十四分之一。这个例子同时失去纯数值互易，所以不能用来判断保留互易后的更强候选。完整候选仍在原来的准备、测试、过程和未来上工作，只把几何中的共同零条件精确换成按源计秩的纯目标准则，其他量子结构、操作和来源继续由各自完整合同承担。

## 追加锚（本行以下为增补区）

## 103. 二纯真面与完整排除球内生的三阶状态几何

### 103.1 原载体、完整排除集与两条几何条件

**定义 103.1（Pair、EB与原面链高）。** 严格沿用[VI89.1][Q103VI]：$V\ne0$ 有限维，$C\subset V$ 为原闭尖生成凸锥，$u\in V^*$ 在 $C\setminus\{0\}$ 上严格正，$K=C\cap\{u=1\}$ 是整个原紧基，$P=\operatorname{ext}K$ 是全部原纯点，效应是整个原区间 $[0,u]_{C^*}$。归一基上的仿射效应与这些线性效应一一对应，不另选测试子菜单。记

$$
\begin{gathered}
F_p=\{f\in[0,u]:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\\
p\perp x\ \Longleftrightarrow\ \exists f\in F_p,\ f(x)=0,
\qquad D_p=\{x\in K:p\perp x\}=\{x:T_p(x)=0\},\\
E_p=P\cap D_p,\qquad
H(p,q)=\text{包含 }p,q\text{ 的整个原最小面}.
\end{gathered}
\tag{VII103.1}
$$

最小面亦为两条原纯射线生成的最小锥面的归一基；不取线段、截面或所选子面代替它。$F_p$ 的紧性和最小值达到见103.2；这里尚未假定 $T_p$ 仿射或是同一张效应。两个条件准确为

$$
\begin{aligned}
\mathrm{Pair}:&\quad p,q\in P,\ p\ne q
                 \ \Longrightarrow\ H(p,q)\ne K,\\
\mathrm{EB}_{\ge1}:&\quad
\forall p\in P\ \exists d_p\in\mathbb N,\ d_p\ge1:
                 \ D_p\simeq_{\rm aff} B^{d_p}.
\end{aligned}
\tag{VII103.2}
$$

$B^d$ 指整个闭欧氏单位球；$d=1$ 是线段。$\mathrm{EB}_{\ge1}$ 起初只要求整个原集合 $D_p$ 为这样的仿射球，不预设它是面或暴露面，也不预给各 $d_p$ 相等。定义 $\mathrm{EB}_{\ge2}$ 为同样全称条件中要求 $d_p\ge2$，$\mathrm{EB}_3$ 为要求全部 $d_p=3$。

对非空面使用通常的凸面定义，不先要求闭。原面链高约定为链中面数：

$$
h(K)=\max\{k:\ \varnothing\ne F_1\subsetneq F_2
              \subsetneq\cdots\subsetneq F_k=K,
              \ F_i\text{ 为原面}\}.
\tag{VII103.3}
$$

有限维下每次严格包含都增大仿射维数，故此最大值存在；例如单点高一，线段高二。本章输入只有上述载体与两条(VII103.2)，不要求 $P$ 有限或闭，不预付 $\mathrm B$、PSD、Jordan、自对偶、谱性、projectivity、局部效应延拓或可逆群。完整 $S$ 始终取VI89.1的全部内容：每个纯 $p$ 有一个原 $e_p\in F_p$，满足 $g-e_p\in C^*$ 对全部 $g\in F_p$ 成立，并且 $e_p(q)=e_q(p)$ 对全部纯点成立。

### 103.2 从整个排除球到全部原真面

**定理 103.2（完整暴露与真面穷尽）。** 仅用 $\mathrm{EB}_{\ge1}$，每个 $D_p$ 都是非点紧暴露真面，存在一张原 $e_p\in F_p$ 使

$$
D_p=K\cap\ker e_p.
\tag{VII103.4}
$$

这里 $e_p$ 起初只表示这张共同暴露尺，不预先称为 least。每个非空原真面若非单点，就恰为某个整个 $D_p$；其余非空真面都是原纯单点。加上 $\mathrm{Pair}$ 后，每对不同纯点的整个 $H(p,q)$ 恰为某个 $D_r$，故原 $\mathrm B$ 是后果。

证明。由于 $K$ 张成 $V$，可在 $K$ 内选一组线性基。每个 $f\in[0,u]$ 在这些基向量上的读数都在 $[0,1]$，故该闭区间在有限维对偶中有界而紧。$F_p$ 是其中含 $u$ 的闭集，故非空紧；每个 $T_p(x)$ 的最小值达到。集合

$$
\{(f,x)\in F_p\times K:f(x)=0\}
$$

紧，投影到 $K$ 就是原 $D_p$，因而 $D_p$ 紧。$p\notin D_p$，因为所有 $f\in F_p$ 都在 $p$ 取一。

取球 $D_p$ 的中心 $c_p$。由 $c_p\in D_p$ 选一次 $e_p\in F_p$，使 $e_p(c_p)=0$。对每个 $x\in D_p$，其关于 $c_p$ 的反射 $x'=2c_p-x$ 仍在整个 $D_p$，所以

$$
0=e_p(c_p)=\tfrac12(e_p(x)+e_p(x')),
\qquad e_p(x),e_p(x')\ge0.
$$

于是 $e_p$ 零于整个 $D_p$；反向，$e_p(x)=0$ 本身就是 $p\perp x$ 的原见证，故得到(VII103.4)。这先证明 $D_p$ 是暴露面，没有先把“球形集合”偷换成“球形面”。非退化性给它至少两个点，$p\notin D_p$ 给它真于 $K$。

任取非空原真面 $F$，即使它未先给闭性，有限维凸几何仍允许取 $x\in\operatorname{ri}F$。此 $x$ 不在 $\operatorname{ri}K$：含一个整体相对内点的面只能是 $K$。在 $x$ 取 $K$ 的一个非恒定相对支撑仿射函数，平移并按其全域最大值归一，得到原仿射 $a$，满足

$$
0\le a\le1\text{ 于 }K,\qquad a(x)=0,
\qquad \max_K a=1.
$$

齐次化将它识别为原 $[0,u]$ 中的线性效应。对 $y\in F$，由 $x\in\operatorname{ri}F$，可使 $x$ 位于 $y$ 与某个 $z\in F$ 的开线段内；非负性迫使 $a(y)=0$。全域最大面是非空紧面，具有一个原纯点 $p$ 达到 $a(p)=1$。因此

$$
F\subseteq\{a=0\}\cap K\subseteq D_p.
\tag{VII103.5}
$$

$F$ 也是球 $D_p$ 的面。严格凸欧氏球（包括线段）的非空真面只有极端单点，所以 $F$ 若非单点必等于整个 $D_p$；若为单点，因其本身是 $K$ 的面，该点属于 $P$。特别地，每个 $D_p$ 都是极大的原真面，不会严格包含于另一真面。上述论证不使用“原真面都已闭或暴露”作为前件。

最后，$p\ne q$ 时 $H(p,q)$ 非点；$\mathrm{Pair}$ 使其为真面，故(VII103.5)给 $H(p,q)=D_r$。反过来，一个 $D_r$ 中任意两个不同纯点的原最小面都等于 $D_r$，因为该最小面是 $D_r$ 的非点面。于是所有这些球确实是整个二纯最小面，包含线段情形；VI89.2的 $\mathrm B$ 已成立。证毕。

### 103.3 原零关系给出的点—球极性

**定理 103.3（交点唯一、双射与面双正交）。** 在 $\mathrm{Pair}+\mathrm{EB}_{\ge1}$ 下，任意两个不同非点原真面恰交于一个原纯点。映射

$$
p\longmapsto D_p
\tag{VII103.6}
$$

是全部原纯点与全部非点原真面之间的双射，且 $p\notin D_p$。对归一面的零补定义

$$
F^\perp=\bigcap_{q\in P\cap F}D_q,
\qquad \varnothing^\perp=K,
\tag{VII103.7}
$$

则

$$
\{p\}^\perp=D_p,\qquad (D_p)^\perp=\{p\},
\qquad K^\perp=\varnothing,
\qquad F^{\perp\perp}=F.
\tag{VII103.8}
$$

这些是原全效应零关系的结论。允许线段时不将它们称为厚射影平面；在额外 $\mathrm{EB}_{\ge2}$ 下，纯点与各球的整个纯边界才构成真正的射影平面，并带无绝对点极性。

证明。先复用V88.1的原零对称：对纯 $p,q$，若一张 $f$ 在 $p$ 取一、在 $q$ 取零，则原补效应 $u-f$ 见证反向。因此

$$
q\in D_p\quad\Longleftrightarrow\quad p\in D_q.
\tag{VII103.9}
$$

这只用了零一读数，并未用非零比较值互易或 least。

设 $L=D_p,M=D_q$ 不同，则 $p\ne q$。103.2给 $H(p,q)=D_r$。$p,q\in D_r$ 与(VII103.9)给 $r\in L\cap M$。这个交是两个球的面；若含不止一个点，就等于整个 $L$ 与整个 $M$，与不同矛盾。因此 $L\cap M=\{r\}$，且该单点作为 $K$ 的面是原纯点。

还须证明不同纯点不会对应同一球，不能由上一段擅自假定。若 $p\ne q$ 而 $D_p=D_q=L$，置 $M=H(p,q)$。因 $p\notin L$，有 $M\ne L$。上一段给 $M\cap L=\{r\}$，其中 $r$ 纯。由 $r\in D_p\cap D_q$ 和零对称，$p,q\in D_r$；故 $M\subseteq D_r$。两者都是非点极大真面，必 $M=D_r$。但 $r\in M$ 遂给 $r\in D_r$，矛盾。单射成立，满射由103.2的真面穷尽给出。

由零对称，$p\in(D_p)^\perp$。若另有纯 $s\in(D_p)^\perp$，则 $P\cap D_p\subseteq D_s$；对球的全部极点取凸包得 $D_p\subseteq D_s$，所以两面相等，单射迫使 $s=p$。任意 $x\in(D_p)^\perp$ 都有有限原纯分解。每个 $D_q$ 都是面，故该分解的每个正权纯点亦在所有 $D_q$ 中；它们只能是 $p$，所以 $x=p$。同样，若 $K^\perp$ 非空，它作为面含一个纯 $s$，却须 $s\in D_s$，不可能。结合103.2的全部面类型，逐项得到(VII103.8)，并有包含反序。没有把混态第一端点的另一种排除关系混入(VII103.7)。

最后，以 $P$ 为点、以 $P\cap D_p$ 为线。两不同点唯一确定其整个最小球面；两不同线唯一相交，刚已证明。$\mathrm{EB}_{\ge2}$ 保证每线至少三个点；又 $p\notin D_p$，故并非全部点共线。明确地，从线上的两点 $a,b$ 和线外点 $c$ 出发，在线 $ab$ 取异于 $a,b$ 的 $d$，再在线 $cd$ 取异于 $c,d$ 的 $e$；唯一交点性质保证 $e$ 不在三角形 $abc$ 的任何边上，故 $a,b,c,e$ 构成非退化四边形。这满足射影平面的关联公理；(VII103.6)、零对称及 $p\notin D_p$ 给无绝对点极性。此处未调用任何 Desargues 性、拓扑平面分类或 Veronese 定理。证毕。

### 103.4 原least、全部数值互易与既有一般桥的直接消费

**定理 103.4（原球几何到完整S及面高三）。** 在同一个原载体上，$\mathrm{Pair}+\mathrm{EB}_{\ge1}$ 推出 $\mathrm A$、完整 $S$ 及 $h(K)=3$。103.2构造的 $e_p$ 就是原全锥序 least，满足

$$
\begin{gathered}
T_p=e_p\text{ 于整个 }K,\qquad
\{x\in K:e_p(x)=0\}=D_p,\qquad
\{x\in K:e_p(x)=1\}=\{p\},\\
T_p(q)=T_q(p)\quad(p,q\in P),\\
T_p\!\left(\sum_i\lambda_iq_i\right)
 =\sum_i\lambda_iT_{q_i}(p)
\quad(\lambda_i\ge0,\ \sum_i\lambda_i=1).
\end{gathered}
\tag{VII103.10}
$$

立即消费VI89.4／V88.4、88.10及[Library完整S桥][Q103S]，得到一个有限维 EJA $J$ 和线性双射 $\Phi:J\to V$，使

$$
\Phi(J_+)=C,\qquad u\Phi=\tau_J,
\qquad \Phi\{x\in J_+:\tau_Jx=1\}=K.
\tag{VII103.11}
$$

$\tau_J$ 是每个本原幂等元取一的规范迹，且 $\operatorname{rank}J=3$。这是原整个锥、原单位、原全部效应和原全部纯点的忠实表示，不是换一个完成体。

证明。固定纯 $p$，取任意过 $p$ 的原二纯球 $F$。它与 $D_p$ 不同，103.3给唯一纯交点 $r$。原 $e_p$ 在 $p$ 取一、在 $r$ 取零，且在整个 $F$ 上 proper。取球图 $\chi:F\to B^d$，记 $n=\chi(p)$。一个球上有零一两端的 proper 仿射函数必沿唯一的一对对径达到两端，所以 $\chi(r)=-n$，并且

$$
e_p(\chi^{-1}z)=\frac{1+\langle n,z\rangle}{2}.
\tag{VII103.12}
$$

为核对这一等号条件及 least，任取原 $g\in F_p$，在整个球上写 $g(\chi^{-1}z)=a+\langle b,z\rangle$。有 $\|b\|\le a$、$a+\|b\|\le1$ 及 $a+\langle b,n\rangle=1$。因此

$$
\begin{gathered}
b=\lambda n,\qquad a=1-\lambda,\qquad0\le\lambda\le\tfrac12,\\
g(\chi^{-1}z)-e_p(\chi^{-1}z)
=(\tfrac12-\lambda)(1-\langle n,z\rangle)\ge0.
\end{gathered}
\tag{VII103.13}
$$

对 $e_p$ 再用 $e_p(r)=0$，便迫使 $\lambda=1/2$，得到(VII103.12)及对径唯一。这也见证原 $p\perp r$，遍及全部球与其全部纯点即为 $\mathrm A$。

每个不同纯 $q$ 都与 $p$ 共处一个这样的整个球，故(VII103.13)给 $g(q)\ge e_p(q)$；在 $p$ 两者相等。用原 $K=\operatorname{conv}P$、$C=\operatorname{cone}P$，得 $g-e_p\in C^*$。这才证明全锥序 least，故 $T_p=e_p$；此前未从点态下确界中预选 least。在同一个 $H(p,q)$ 对 $e_q$ 使用(VII103.12)，得到

$$
e_p(q)=\frac{1+\langle\chi(p),\chi(q)\rangle}{2}=e_q(p).
\tag{VII103.14}
$$

这包括所有非零比较值，取值并非仅限零一。同点值为一；不同球内的不同纯点内积严格小于一，所以 $e_p$ 唯一确认 $p$，对任意混态用有限纯分解即得唯一确认面的断言。线性和互易给(VII103.10)末式。至此已精确取得VI89.1定义的完整 $S$，没有遗留一般重构前件。

现在直接应用既有桥。其源空间取本章的 $V$，正锥取同一个 $C$，规范泛函取同一个 $u$，效应取整个 $[0,u]$，纯点取全部 $P$，least 和 reciprocal 分别由(VII103.13)、(VII103.14)供给。Library中的正对偶剥离、共同完整框架、忠实自对偶配对、有符号谱性、正面投影、projectivity 与滤波纯性全部按其既有证明复用；最后消费的是 Barnum–Müller–Ududec 的 Theorem 16，非另需强对称的 Theorem 17。本章不重证这些一般步骤，也不以“$D_p$ 暴露”替代其中 projectivity 的完整接口。其同载体归一给(VII103.11)。

面高由分类前的原几何已可读出。103.2说明全部非空真面只有纯单点和极大的整个 $D_p$；取任一球边界纯点 $q\in D_p$，有严格链

$$
\{q\}\subsetneq D_p\subsetneq K.
\tag{VII103.15}
$$

不可能插入其他非空面，故 $h(K)=3$。有限 EJA 的成熟面字典把非零锥面与非零幂等元的支撑对应，包含对应幂等元序，严格包含严格增加秩；完整本原 Jordan 框架的部分和给长度恰为秩的最大非空链。原线性同构保持整个面格，故 $\operatorname{rank}J=h(K)=3$。此处只将既有 EJA 面格字典应用于(VII103.15)，不新增 Jordan 分类。证毕。

(VII103.12)还精确消费VI90.8的全部局部球效应延拓：若 $h(z)=a+\langle b,z\rangle$ 且 $0\le a-\|b\|\le a+\|b\|\le1$，$b\ne0$ 时取 $s=\chi^{-1}(b/\|b\|)$，原延拓为

$$
\widehat h=(a-\|b\|)u+2\|b\|e_s\in[0,u].
\tag{VII103.16}
$$

$b=0$ 时取 $au$。两端系数界保证其全域 proper，(VII103.12)给其限制恰为 $h$。这是既有逐效应延拓的参数对应，不另计为新一般定理，不供应共同正线性扩张或物理操作。

### 103.5 三个原纯点的共同单位尺

**定理 103.5（唯一非负暴露尺与三元finite lift）。** 在上述原域中，非零 $a\in C^*$ 若零于整个 $D_p$，必有

$$
a=a(p)e_p,\qquad a(p)>0.
\tag{VII103.17}
$$

任取 $p\in P$、$q\in E_p$，令 $H(p,q)=D_r$；则 $p,q,r$ 两两原零相关，$r$ 由 $p,q$ 唯一确定，并且

$$
u=e_p+e_q+e_r,\qquad e_i(j)=\delta_{ij}
\quad(i,j\in\{p,q,r\}).
\tag{VII103.18}
$$

所以每个原纯点都属于一个原三元完备框架。这里给的是本章新几何域的直接三元关系解释，不把既有一般框架完备定理重计为新增。

证明。先证(VII103.17)。令 $M=\max_Ka>0$，在原全域最大面取纯 $s$。$a/M$ 是原 proper 确认效应，故 $D_p\subseteq D_s$。两者都是非点极大真面，必相等；103.3的单射给 $s=p$，所以 $M=a(p)>0$。原 least 给 $b=a/M-e_p\in C^*$。$b$ 同时零于整个 $D_p$ 和 $p$；若 $b\ne0$，其零面是真面，却包含极大真面 $D_p$ 及面外点 $p$，不可能。因此 $b=0$。

因 $q\in D_p$，$p\ne q$。$H(p,q)=D_r$ 和零对称使 $r\in D_p\cap D_q$，故三点两两零相关。$p,q\in D_r$，且 $r\notin D_r$，所以三者不同。由103.3的交点唯一，$r$ 是同时零相关于 $p,q$ 的唯一原纯点。在球 $D_r$ 内，$e_p(p)=1,e_p(q)=0$ 使 $p,q$ 为对径；球公式遂给 $e_p+e_q=1$ 于整个 $D_r$。

在原全空间置 $h=u-e_p-e_q$。它在 $D_r$ 恒零，在 $r$ 取一，且由 $e_p,e_q\ge0$ 有 $h\le u$。尚不能在这一步假定 $h\ge0$。若

$$
c=\min_Kh<0,
$$

取原最小面中的纯点 $x$ 达到 $c$，则

$$
g=\frac{h-cu}{1-c}\in[0,u],\qquad g(r)=1,\quad g(x)=0.
\tag{VII103.19}
$$

上界使用 $h\le u$，下界使用原全域最小值 $c$，故这是一张真正原 proper 效应。它见证 $x\in D_r$，但 $h|_{D_r}=0$ 与 $h(x)=c<0$ 矛盾。因此 $h\ge0$。现在 $h$ 非零、零于整个 $D_r$，(VII103.17)给 $h=h(r)e_r=e_r$，得到(VII103.18)。

每个 $D_p$ 是非退化球，故有原纯点 $q\in E_p$ 可选；于是每个 $p$ 都能进入这个三元框架。共同的一族效应 $(e_p,e_q,e_r)$ 非负且和为 $u$，所以这是 joint 完备，绝非分别给三对各找一张测试。也不能再添第四个不同的两两零纯点，因为它须同时在 $D_p,D_q$ 中，唯一交点已是 $r$。所有读数和单位等式都在原 $V,C,u$ 上成立。证毕。

### 103.6 完整反向与任意原unit的归一对应

**定理 103.6（同载体的精确双向）。** 在定义103.1的有限维全效应域内，以下三项等价：

$$
\boxed{\begin{aligned}
&\mathrm{Pair}+\mathrm{EB}_{\ge1}\\
\Longleftrightarrow\quad &S\ \text{且}\ h(K)=3\\
\Longleftrightarrow\quad &\exists\text{ rank-three有限EJA }J\text{ 及满足(VII103.11)的 }\Phi.
\end{aligned}}
\tag{VII103.20}
$$

这一等价保留原 $C,u,K,P,[0,u]$；不将原 $u$ 默认为某个事先选好的矩阵迹。

证明。第一项到其余两项由103.4。第二项由既有完整 $S$ 桥得到有限 EJA；原面高与成熟幂等元面格对应给秩三，故到第三项。

反向从任意秩三有限 EJA $J$ 出发。记其单位为 $e$，规范迹为 $\tau$，迹配对为 $\langle a,x\rangle=\tau(a\circ x)$，平方锥为 $J_+$。成熟自对偶及谱字典给

$$
K_J=\{x\in J_+:\tau x=1\},\qquad
P_J=\{p:p\text{ 为本原幂等元}\},\qquad
\mathcal E_J=\{x\mapsto\tau(a\circ x):0\le a\le e\}.
\tag{VII103.21}
$$

全部原效应恰为此区间；没有缩成一组投影测试。V88.4的逆向及Library完整桥的反向已证明：若 $0\le a\le e$ 在纯 $p$ 取一，则 $a\ge p$。其参数正是这里的规范迹及本原 $p$，所以直接复用，得到

$$
e_p(x)=\tau(p\circ x),\qquad
D_p=K_J\cap J_0(p),\qquad
J_0(p)=\{x:p\circ x=0\}.
\tag{VII103.22}
$$

$J_0(p)$ 是单位 $e-p$、秩二的 Peirce-zero EJA，$D_p$ 是它的全部迹一态空间。成熟秩二字典给一个非退化欧氏球：简单秩二因子是 spin factor，非简单秩二为 $\mathbb R\oplus\mathbb R$，其态空间是线段。故 $\mathrm{EB}_{\ge1}$ 成立。两个不同本原幂等元的支撑并 $p\vee q$ 秩二；其整个最小面是该秩二支撑面，真于秩三整个 $J$。所以 $\mathrm{Pair}$ 成立。此处用的是成熟 Jordan 面格／秩二面结果，亦即V88.4及Library二态球部分的同一结论，并未重新证明一般重构。

再明确任意原归一泛函的回接。若先只有一个锥线性同构 $T:J\to V$，则原严格正 $u$ 在迹配对下唯一写为

$$
u(Tx)=\tau(b\circ x),\qquad b\in\operatorname{int}J_+.
$$

严格正与自对偶使 $b$ 正可逆，包括每个直和扇区。采用成熟 Jordan 二次表示

$$
\mathsf P_a=2L_a^2-L_{a^2},\qquad L_a(x)=a\circ x,
\qquad \Phi=T\mathsf P_{b^{-1/2}}.
\tag{VII103.23}
$$

其保正、自伴随及正逆 $\mathsf P_{b^{1/2}}$ 直接复用V75.1及其所引文献；$b$ 的谱函数彼此算子交换，给 $\mathsf P_{b^{-1/2}}b=e$。因此

$$
u(\Phi x)=\tau\bigl(b\circ\mathsf P_{b^{-1/2}}x\bigr)
=\tau\bigl((\mathsf P_{b^{-1/2}}b)\circ x\bigr)=\tau x.
\tag{VII103.24}
$$

于是 $\Phi$ 满足(VII103.11)，把上述完整字典搬回同一个原单位切片。原纯点写为 $p=\Phi c$，其中 $c$ 本原，而原 least 及所有原效应精确为

$$
e_p(v)=\tau(c\circ\Phi^{-1}v),\qquad
f_a(v)=\tau(a\circ\Phi^{-1}v),\quad0\le a\le e.
\tag{VII103.25}
$$

面、球、零关系、least 的全锥序及互易随这个同一同构保持。它不改变原 $u$，也没有把未归一的 $Tc$ 误作原纯归一态。最后，秩三面格给 $h(K)=3$，反向全部完成。证毕。

### 103.7 允许线段的全部分支与复三能级选择

**定理 103.7（分类参数是后果，非输入）。** (VII103.20)的全部模型，在忠实同单位坐标中恰为

$$
J=\mathbb R\oplus\operatorname{spin}_d\quad(d\ge1),
\qquad\text{或}\qquad
H_3(\mathbb R),\ H_3(\mathbb C),\ H_3(\mathbb H),\ H_3(\mathbb O).
\tag{VII103.26}
$$

这里 $\operatorname{spin}_d=\mathbb R\oplus\mathbb R^d$ 的积为

$$
(a,x)\circ(b,y)=(ab+x\cdot y,ay+bx),
\qquad \tau(a,x)=2a,
\tag{VII103.27}
$$

其迹一态空间为 $B^d$；$d=1$ 是 split $\mathbb R^2$，所以 $\mathbb R\oplus\operatorname{spin}_1\simeq\mathbb R^3$ 包含经典三角形。非简单分支的态空间是旗标 join $\Delta_0*B^d$，不是另一种简单三能级。

在此域内，全部 $D_p$ 维数至少二当且仅当 $J$ 简单；此时参数恰为

| 简单代数 $J$ | $\operatorname{affdim}K$ | 每个整个 $D_p$ 的球维数 |
| --- | --- | --- |
| $H_3(\mathbb R)$ | $5$ | $2$ |
| $H_3(\mathbb C)$ | $8$ | $3$ |
| $H_3(\mathbb H)$ | $14$ | $5$ |
| $H_3(\mathbb O)$ | $26$ | $9$ |

特别地，无须先给总维数、球维同质性或复结构，

$$
\boxed{\mathrm{Pair}+\mathrm{EB}_3
\ \Longleftrightarrow\
\text{同一原完整载体为复三能级迹态／全效应模型}.}
\tag{VII103.28}
$$

证明及成熟分类的应用。有限 EJA 分解为简单理想的直和，秩相加。秩三非简单分解只能是 $1+2$ 或 $1+1+1$；秩一因子为 $\mathbb R$，简单秩二因子为 spin factor，split 秩二即 $\mathbb R^2$，所以统一为(VII103.26)首项。简单秩三分类给其余四项。此处使用成熟 Jordan 分类，不将它或其参数表当作新分类：秩二球／spin 对应可定位到 Alfsen—Shultz [1978原文][Q103AS] Lemma 3.10（印刷pp164—165）；秩三实、复、四元、Cayley 四类在该文 Proposition 7.6的证明（印刷p189）明确调用其文献[4] Proposition 8.3，即 Alfsen—Shultz—Størmer 的 *A Gelfand–Neumark theorem for Jordan algebras*。本章沿该精确既有归属使用有限分类，不声称已另读其[4]全文。

具体核对首项，令旗标纯点为 $f$，球纯点为 $a_n$、$\|n\|=1$，相反点记 $a_{-n}$。全部原纯点恰为 $\{f\}\cup\{a_n\}$，球与旗标在 join 的独立中央坐标中。完整迹效应字典给

$$
D_f=B^d,\qquad D_{a_n}=[f,a_{-n}].
\tag{VII103.29}
$$

因为确认 $f$ 的 least 是旗标中央坐标，确认 $a_n$ 的 least 在球上为 $(1+n\cdot z)/2$、在旗标为零；一个非负读数的混合为零恰要求其全部正权组分为零。因此球源的完整排除集恰为所示线段，不是遗漏了一些非纯排除态的局部图。两球纯点生成整个球面，两点为同一球的不同极点；旗标与一个球纯点生成一条 join 边。它们都是整个 $K$ 的真面，故 $\mathrm{Pair}$ 直接成立。$d=1$ 时就是经典三角形。$d\ge2$ 时旗标的排除球维数为 $d$，球源的排除球维数为一，说明输入不宜擅加维数同质性。

所有非简单分支都存在这些线段 $D_{a_n}$，所以被 $\mathrm{EB}_{\ge2}$ 排除；四个简单分支的 Peirce-zero 子代数分别为 $H_2(\mathbb R),H_2(\mathbb C),H_2(\mathbb H),H_2(\mathbb O)$，其迹一态都是维数 $2,3,5,9$ 的球。若标量代数实维数为 $k=1,2,4,8$，则三阶 Hermitian 空间实维数为 $3+3k$，其迹切片仿射维为 $2+3k$；二阶对应空间实维为 $2+k$，其迹切片维为 $1+k$。这给表内全部参数，且每个纯点具有同样 Peirce 类型，球维同质性在简单域内成为后果。

若所有 $D_p$ 都是三球，(VII103.29)先排除非简单分支，再由表唯一选择 $H_3(\mathbb C)$；反向该模型所有 Peirce-zero 态空间确为三球。只要求存在一个三球不够，$\Delta_0*B^3$ 就只有旗标的 $D_f$ 为三球而仍有大量线段。故(VII103.28)准确要求每个完整 $D_p$，而非一张所选 Bloch 图。证毕。

### 103.8 全部效应与Born字典的准确回接

**推论 103.8（三球分支的原完整概率字典）。** 在 $\mathrm{Pair}+\mathrm{EB}_3$ 下，取103.6的同单位 $\Phi:H_3(\mathbb C)\to V$。令 $\rho=\Phi^{-1}x$，则所有原归一态、全部原 proper 效应、原 least 与纯值分别为

$$
\begin{gathered}
\rho\succeq0,\quad\operatorname{tr}\rho=1,\qquad
f_E(x)=\operatorname{tr}(E\rho),\quad0\preceq E\preceq I_3,\\
p=\Phi(vv^*),\quad v^*v=1,
\qquad T_p(x)=\operatorname{tr}(vv^*\rho),\\
q=\Phi(ww^*),\quad w^*w=1,
\qquad T_p(q)=|v^*w|^2,\\
D_p=\Phi\{\rho\succeq0:\operatorname{tr}\rho=1,\ \rho v=0\}.
\end{gathered}
\tag{VII103.30}
$$

有限数学效应族为完整测量恰要求 $E_i\succeq0,\sum_iE_i=I_3$。这识别全部原 proper 区间，但不自动供应每族的实际共同菜单。

证明。103.7先选择复三阶类型，(VII103.21)、(VII103.25)直接给完整区间和 least；标准矩阵迹与秩一乘法给模方公式，正性给 $\operatorname{tr}(vv^*\rho)=0\Longleftrightarrow\rho v=0$。这些是既有 Jordan／Born 字典在新几何域上的参数代入，不是另证 Born 起源。原任意 $u$ 已由(VII103.23)—(VII103.25)准确处理，故不额外要求原坐标中的 $u=\operatorname{tr}$。

实分支和四元分支相同地使用成熟 Jordan 迹及其关联矩阵字典；四元迹配对取实值的 Jordan 迹，归一向量的纯比较仍为 $|v^*w|^2$。Albert 分支仅使用本原幂等元 $c$、平方锥与 $\tau(c\circ x)$，不将任意非结合八元向量的 outer product 当作无条件纯态参数。首项旗标 join 也沿(VII103.21)保留整个 $[0,e]$ 与中央质量，不被矩阵表遗漏。

若另有原实／复 unital PSD section 表示，则现有 [SectionROGFrame][Q103ROG] 的 `whole_pure_carrier` 在原 $\mathrm{ROG}(L)$ 下识别全部原纯点；`rog_frame` 另要求原 $I\in L$，给每个归一原秩一点进入同一个完整正交框架。其 `base` 就是全部 $L\cap\mathrm{PSD}\cap\{\operatorname{tr}=1\}$，不是所选纯子集。在本章分类后的实／复三阶全空间，$L=H_3(\mathbb F)$、原生域 $\mathbb F=\mathbb R$ 或 $\mathbb C$，谱分解满足 ROG 且 $I\in L$，因此可直接消费；在已有一般 ROG 表示的交集中，也只按这些原前件消费。对应Blueprint的全截面正泛函PSD提升、完整原效应的共同提升及其正补应用均保留原 unital 条件，不将环境 $E\le I$ 偷加到任意截面。它们与既有ROG框架不作为本章新的普遍重构，也未用于从(VII103.2)取得 $S$；本章无ROG输入的载体首先走103.4的既有一般桥。证毕。

### 103.9 反事实、容量与旗标边界

**命题 103.9（两种原控制及其准确含义）。** $\mathrm{Pair}$ 连同二纯整球不能替代 $\mathrm{EB}_{\ge1}$；完整 $S$ 连同 $\mathrm{Pair}$ 也不能删除排除球中的容量限制。允许线段的域不能称为简单模型或厚射影平面；这些控制不构成两条候选公理的完整独立性证明。

证明。直接复用VII102.5—102.8的整个加权 $3\mid n$ 自由和，$n\ge3$、$u_0=1-2\varepsilon,u_1=u_2=\varepsilon$、$v_j=1/n$、$0<2\varepsilon<1/n$。两侧都至少三个顶点，任意两不同原纯点的整个最小面是真边，所以它满足 $\mathrm{Pair}$ 及 $\mathrm B$。轻源 $a_i$ 的整个排除集却为原 facets 的并

$$
D_{a_i}=\bigcup_{j=1}^n
\operatorname{conv}(P\setminus\{a_i,b_j\}).
\tag{VII103.31}
$$

VII102.8已经给两点分别读零而其中点最低读数为 $n\varepsilon/[2(n-1)]>0$ 的原全效应计算。因此此并不凸，不能是一个整个仿射球，也不能由一张 least 原效应的零面给出；它失败 $\mathrm{EB}_{\ge1}$ 及 $S$。这里只引用已有的全载体值和面，不另造反例或重复计算。

再取经典四态 $K=\Delta_3$、全部仿射 proper 效应。对顶点 $p_i$，least 是重心坐标 $e_i$，互易为 $e_i(p_j)=\delta_{ij}$，故完整 $S$ 成立；任意二顶点最小面为真边，故 $\mathrm{Pair}$ 成立。但 $D_{p_i}$ 是另外三个顶点张成的整个三角形，既不是线段也不是严格凸二球，所以失败 $\mathrm{EB}_{\ge1}$。其原面链高为四。这说明本章排除球要求不仅约束局部形状，还约束容量，不能把103.6误读为无秩限制的旧 $S$ 包。

相反，103.7的 $\Delta_0*B^d$ 真正满足两条候选，球源背后却是线段，旗标背后才是整个球。$d=1$ 为三角形，每条关联线只有两个纯点；$d\ge2$ 的球源线仍只有两个纯点。因此 $\mathrm{EB}_{\ge1}$ 域没有统一厚度，只有再要求全部 $D_p$ 非线段才成为103.3的射影平面／103.7的四个简单分支。

以上不证明 $\mathrm{EB}_{\ge1}$ 单独能否推出 $\mathrm{Pair}$，不声称两者是最少独立公理，也不以本章特殊域替代一般高维问题。一般 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 在该排除球域之外仍未由这些控制解决；加权族本身失去 $\mathrm{Z0}$，经典四态本身满足 $\mathrm A$，两者均不能充作该一般问题的反例。证毕。

### 103.10 完整原装饰元组中的rank-three候选

**定义与定理 103.10（所选载体共同域内的完整同数据替换）。** 固定VI89.7—89.10／V88.6—88.8的同一个原装饰元组 $\mathcal O$、原来源域与共同 $\mathfrak S(\mathcal O)$。选定非空 $\mathcal J\subseteq\{A,D,E\}$，只在明确共同域

$$
\mathcal D_{3,\mathcal J}:\quad
\text{原包的共同载体／来源域，且 }
\forall X\in\mathcal J,\ h(K_X)=3
\tag{VII103.32}
$$

内比较。令 $\mathsf R_S$ 是该旧完整包中将几何项按VI89.4写成全部 $S_X$ 的同数据形式。用 $\mathcal N(\mathcal O)$ 指它除这些几何项外的全部原合同，逐字按原定义继承而不删量词。定义本章完整候选

$$
\begin{aligned}
\mathsf R_{\rm exclusion,3}^{\mathcal J}(\mathcal O):\quad
&\mathcal N(\mathcal O)\ \land\!
\bigwedge_{X\notin\mathcal J}S_X\\
&\land\!\bigwedge_{X\in\mathcal J}
 (\mathrm{Pair}_X+\mathrm{EB}_{\ge1,X}).
\end{aligned}
\tag{VII103.33}
$$

完整继承 $\mathcal N$ 在这里准确包括下列原内容，均不是排除球的推论。

原准备、测试、过程、参考、读回和装饰数据仍是同一组。原概率像 $K_X=\{k_\sigma\}$ 自身非空、有限仿射维、紧、单位为一；全部原中点在原标签内实现，不先取闭凸完成。原测试像自身闭，含零、单位，闭于中点、补和有界倍增，且同一测试对全部原准备实现同一效应表。正带质量输出保留全部原中点实现图，包括重复标签和每个同中点实现；原加权缩放遍及全部非负质量，含零、次归一和不等质量。其他过程及参考只在自身完整相关联合输入域上下降；边缘或乘积输入不代替全部相关输入，不符合中点下降条件者保留原全实下降合同。

同一个原实双线性 $L:D\times A\to E$、同一个原实线性读回 $p:E\to D$、同一个 $\omega=1_D/\tau_D1_D$ 及VI89.7中 $K,M,J,H,B_1,U,G,Q$ 的原定义全部保留，尤其 $K(a)=pL(\omega,a)$、$M(a,b)=pL(K(a),b)$ 两次使用同一个原 $p$。两实张成与全实 $Z$ 保持

$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,\qquad
B_1M(a,b)=\tau_A(a)Jb\quad(a,b\text{ 全实}).
\tag{VII103.34}
$$

原全锥正性、原单位／迹／内积／伴随／二次表示、含秩一分支的完整(83.8)、VI(89.13)中 $\Pi_i,\mathsf C_i,\mathsf D_A,\mathcal T$ 的定义及两尺度Hilbert–Schmidt等式、C2与整个 $G=1_E$ 均保留；$F=\mathsf P_{U^{-1/2}}M$ 仍在原正性和张成给 $U>0$ 后定义，不由新几何预设等距。精确 PRE 之后才读原 H13：存在同一个原资格态 $\rho\in\mathcal H(F)$，其整个原输出 $I^{\rm raw}\rho$ 为正。资格仍用VI89.7原 $c_i,n_i,D_{ik},\pi_{ik},\alpha_{ik},\beta_{ik}$，保留每个活跃块上至少一条严格负方向、原未归一单位和迹伴随、全部块共享总迹一、非活跃块零质量和空活跃集；不逐块换态，不由输出反选资格。这些原式的完整定义直接采用VI89.7，不将面高三误作其中任何有类型尺度参数的重定义。

共同 $\mathfrak S$ 逐项保留设备／事件／来源绑定、全部菜单、过程与分支、参考／副本／相关联合、记录／权限／控制／原钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、零与不等质量、实际混合服务、所有合法未来、旧支撑及每个中间切口。VI89.9的复型和Born、指定复合与读回、实际同事件CP、Kraus、实际仪器和更新、Lüders及时间的各自完整消费者合同，以及VI89.10的原生／细化来源接口，均原样按其有类型适用域继承；没有另行假定其结论已由状态球得到。

在共同域(VII103.32)内，有准确双向

$$
\boxed{\begin{aligned}
\mathsf R_{\rm exclusion,3}^{\mathcal J}(\mathcal O)
&\Longleftrightarrow\mathsf R_S(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm polar}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{\rm zero\text{-}ball}(\mathcal O)
\Longleftrightarrow\mathsf R_{\rm mid}(\mathcal O)\\
&\Longleftrightarrow\mathsf R_{86}^{\rm ev}(\mathcal O)
\Longleftrightarrow[\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}]^{\rm ev}(\mathcal O).
\end{aligned}}
\tag{VII103.35}
$$

证明。逐所选 $X$ 在其同一原 $V_X,C_X,u_X,K_X,[0,u_X]$ 上应用103.6，得到 $\mathrm{Pair}_X+\mathrm{EB}_{\ge1,X}\Longleftrightarrow S_X+h(K_X)=3$。共同域已明确包含后一个高度约束，故可精确替换，非所选几何项与 $\mathcal N$ 不动。余下等价逐项复用VI89.8／V88.7。反向的同锥同单位线性运输保留原全部效应、零关系、整个最小面和面链高；所以返回的是真正原 $D_p$ 与原 $H(p,q)$，不是在新模型中重选资格或效应。若在不先限制高度的旧共同域中书写，准确等式应为

$$
\mathsf R_{\rm exclusion,3}^{\mathcal J}
\ \Longleftrightarrow\
\mathsf R_S\ \land\!\bigwedge_{X\in\mathcal J}h(K_X)=3,
\tag{VII103.36}
$$

不能删去右侧的共同域限制并宣称与无秩限制旧包全域等价。

若再把所选 $\mathrm{EB}_{\ge1,X}$ 换成 $\mathrm{EB}_{3,X}$，则由103.7所得是旧包与“每个所选载体为复三能级”的交集。该静态选择不用由复合去选复数，但也不代付任何原复合或来源合同。尤其当旧消费者另给 $D=A\otimes A$、$E=D\otimes A$ 的完整秩乘法时，若 $A$ 秩三，则 $D,E$ 秩分别为九、二十七；不能再同时要求它们面高三。选 $\mathcal J=\{A,D,E\}$ 与这种合同的交集为空。这里的同数据等价仍正确，但不为这个不相容交集伪造物理源或非空模型。

所有消费者继续按VI89.9的准确接口：同事件实线性提升式、实际各输入块探针及全矩阵核条件才认证CP；若原递归参考已给同事件CP则直接复用，不能重复列作未解。Kraus是CP后的矩阵表示，实际仪器还需完整菜单、分支、接线、记录、同族粗粒化、共同重置输入行一致与未校准旁观者预算；条件态仅在分支质量正时归一。Lüders还需同一分支的锐效应、接受态中性和原输出校准。时间还需原物理时间上的连续齐次可逆自同构群、原钟／单位及实际动态来源。VI89.10中原几何、密度、全部原字和terminal futures、联合菜单／全部有符号关系、原细标签／粗归组、记录后条件未来、source-adoption map及资源合同也保持各自量词。已由原入口导出的后果直接复用；数学凸组合、面极性、三元单位尺和全效应字典不自动取得准备、装置、调用权限或这些过程来源。证毕。

### 103.11 数学归属与保留的母目标

**约定 103.11（连接增量及准确来源）。** 本章承重增量为(VII103.2)在无ROG、无矩阵、无维数预选的同一原全效应载体上到完整 $S$ 与原面高三的连接：完整 $D_p$ 的中心先给一张原共同暴露尺；任意真面的相对内点支撑把它纳入某个整个 $D_p$；二纯真面随后给点—球双射和唯一交点；原球内对径将该同一尺固定为全域 least，并给全部纯值互易。由此才有(VII103.20)、所选共同域内(VII103.35)及每个完整 $D_p$ 为三球的复三能级选择。103.5给该新域的直接三元零关系提升，其框架概念和一般完备性仍是旧桥内容。

凸支撑、严格凸球的面与仿射等号条件是成熟中间工具。零对称、完整 $S$ 的定义及原全效应接口、VI89.4／V88.4、88.10及Library的整个一般有限EJA桥、VI90.8的逐效应延拓、Jordan面高与秩、成熟秩二／三分类、Jordan二次表示归一、Born／全部效应字典、SectionROGFrame及其whole-section提升应用、VII102的加权全效应反事实，都按上文精确前件复用，不重计为新谱性、自对偶、projectivity、一般重构、分类或矩阵概率定理。

Alfsen—Shultz原文 [*State spaces of Jordan algebras*, Acta Math.140 (1978),155—190][Q103AS] 的 Corollary 7.5（印刷p188）要求 Hilbert ball property 与每个 norm-exposed face 的 projectivity；仅有本章103.2的暴露性不能直接代付后者。本章主路不调用这一独立重构准则，因为103.4已经满足并直接消费既有完整 $S$ 桥。该文在本章实际承担的分类引用限于103.7已说明的 Lemma 3.10、Proposition 7.6证明及其明确所引的有限类型归属；不另展开 Veronese 或一般 projectivity 替代路线。二次表示的准确公式、保正、自伴随与逆由V75.1及[Library所列成熟来源][Q103C]继承，适用于所有有限EJA，含Albert；不以结合矩阵计算替代八元分支。

这些连接采用 `repo-derived` 的纸面归属，不作全球原创、文献穷尽、Lean kernel保证、经验实现或整体 $\Omega$ 本体断言。一般高维 $\mathrm B+\mathrm{Z0}\Rightarrow\mathrm A$ 的域外问题与完整物理来源母目标仍保留；本章关闭的是(VII103.2)所明定有限维域中的全部几何桥，不能因其为受限域而略去已得完整反向，也不能把域外未决写成域内缺口。两条候选的逻辑独立性及最少公理数未在这里证明。

### 103.12 原排除球与三点单位尺的白话

**命题 103.12（关系候选的完整几何解释）。** 在定义103.1的明确载体前提下，两条原关系可以准确说成：任意两个不同的纯状态，总能一起待在整体的一块真正边界面里；对每个纯状态，把所有能被某张确认它的原测试读零的状态全部收集起来，得到的整个集合是一块非退化实心球，线段也允许算球。这些关系在本章域内等价于完整互易least和恰三阶状态几何，含103.7全部分支，并按103.10保留来源与过程合同。

证明与解释。每个纯点背后的排除球，起初不是先给一张最低测试再取零集。先在这块球的中心找一张确认原点、在中心读零的原测试；两侧对称且读数非负，迫使整块球都读零。这才得到一张同时排除整个球的原尺。任何真正的边界面又能被一张支撑尺放进这样的排除球，所以两纯点所在的整个最小边界也只能是一块球。两块不同排除球恰交一个纯点，点与背后的球一一相配。

拿某个纯点作读一端，它背后的排除球与每块经过它的球交于唯一纯点。原尺在这一块球上同时读一和零，便把交点锁定在几何对面；球上其他刻度于是都固定了。任何别的确认尺只能在每块球上更高，全部纯点又生成整个原状态体，所以同一把尺在全域都是最低的。交换两个纯端点，在同一块球里算出的刻度相同，这才得到完整数值互易。

再取两个互相排除的纯点。它们的共同边界球背后有第三个纯点，与两者都互相排除。前两把尺在共同边界上凑成一；若三者的余尺在整体别处变负，按真正的最低读数归一，就会把那个负值点又判进这块读零边界，产生矛盾。因此第三把原尺恰好补足单位：三个纯点用同一组三把尺共同区分，三把尺的总和就是原单位。这里不是分别找三对不同的二元测试来冒充一个三元测量。

原面链只有纯点、整块排除球、整个状态体三层。既有的一般Jordan桥因此直接落在秩三，成熟分类才给实、复、四元和八元四个简单三能级类型，它们背后的球分别为二、三、五、九维，整体态空间分别为五、八、十四、二十六维。若允许线段，还必须保留“一整块球加一个独立旗标点”的join，经典三角形也在其中；所以仅说球不能暗中说成简单量子。若要求每个完整排除球都是三维实心球，才准确选出复三能级以及它的全部密度态、全部零一有界效应和模方纯比较。

这些是同一个原载体上的状态与概率结构，不凭几何自动获得实际复合、CP事件、仪器、更新、钟或来源。完整候选在所选载体面高三的共同域内精确替换旧几何项，其余来源、菜单、参考、过程和未来合同逐项继承；不相容的共同域仍是不相容的，未解的一般域仍未解。由103.2—103.10得上述全部陈述。证毕。

[Q103VI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md
[Q103S]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge
[Q103AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf
[Q103C]: ../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input
[Q103ROG]: ../../../Blueprint/D5/S3/Quantum/Foundation/SectionROGFrame.md

## 追加锚（本行以下为增补区）

## 104. 正交三角形的局部提升、纯点紧性与厚球面控制

### 104.1 原全效应域与只量化正交对的入口

**定义 104.1（局部Pair与完整排除尺族）。** 完全采用103.1的同一个非零有限维实 $V$、闭尖生成锥 $C$、严格正原单位 $u$、整个紧基 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$、整个原 $[0,u]_{C^*}$，以及原 $F_p,T_p,D_p,E_p,H(p,q)$。纯点集起初不假定闭。保留103.1的 $\mathrm{EB}_{\ge1}$，将全 $\mathrm{Pair}$ 的量词改为

$$
\mathrm{Pair}_{\perp}:\quad
p,q\in P,\ p\perp q\ \Longrightarrow\ H(p,q)\ne K.
\tag{VII104.1}
$$

这里 $p\perp q$ 仍指存在原 proper 效应在 $p,q$ 取一、零。补效应给 $p\perp q\Longleftrightarrow q\perp p$，且 $p\not\perp p$；没有先给内积正交。定义

$$
\mathcal A_p=\{a\in F_p:a(x)=0\ (x\in D_p)\}.
\tag{VII104.2}
$$

直接复用103.2：仅 $\mathrm{EB}_{\ge1}$ 已使每个 $D_p$ 成为非点紧暴露极大真面，且 $\mathcal A_p\ne\varnothing$；全部非空真面只有纯单点和这些整球。因此任意两个不同非点真面至多交于一点，非空交点必纯，且 $h(K)=3$。每个 $a\in\mathcal A_p$ 的零面恰为整个 $D_p$，因为任何额外零点本身就在 $D_p$ 的原定义中。此时还不称 $a$ 为 least，不假设 $\mathcal A_p$ 单点。

球的对径始终在该整个仿射球内部定义。下文的“逐效应延拓”指每个局部效应分别存在一张原全域 proper 延拓；三结果共同完成则要求同一族原非负效应的和恰为 $u$。两种量词不相同，也均不直接指实际装置。

### 104.2 局部Pair恰好恢复每张已有球的全部对径

**定理 104.2（正交对、球对径与逐效应延拓）。** 在 $\mathrm{EB}_{\ge1}$ 下，下列三项等价：$\mathrm{Pair}_{\perp}$；每个 $D_p$ 中任意纯 $q$ 的球内对径 $r$ 均满足 $q\perp r$；每张 $D_p$ 的全部 $[0,1]$ 值仿射效应都有原 $[0,u]$ 中的延拓。这里每个 $D_p$ 本身确为原二纯最小面，但未断言任意二纯点都共处这样的球。

证明。设 $\mathrm{Pair}_{\perp}$ 成立，取 $q\in P\cap D_p$。103.2使 $H(p,q)=D_r$，其中 $r$ 为原纯点。零对称给 $r\in D_p\cap D_q$。任取 $a_q\in\mathcal A_q$；它在球 $D_p$ 上于 $q,r$ 取一、零。球上 proper 仿射函数同时达到两端，便迫使二者为对径。这是103.4中球支持等号条件的直接应用，亦适用于线段。特别地 $q\perp r$。

反之，设全部所述对径均原零。对 $p\perp q$，在 $D_p$ 内取 $q$ 的对径 $r$。有 $r\in D_p$ 及 $r\in D_q$，零对称给 $p,q\in D_r$。所以 $H(p,q)\subseteq D_r\ne K$，即得(VII104.1)。

任一球 $F=D_p$ 有至少两个不同极点，它们都是原纯点，二者生成的原最小面是 $F$ 的非点面，故只能等于整个 $F$。因此可在这些已有球上直接使用[VI90.8][Q103VI]的逐效应论证，而不预付全 $\mathrm B$。明确地，在球图中写

$$
 h(z)=\alpha+v\cdot z,\qquad
 s=\|v\|\le\min(\alpha,1-\alpha).
\tag{VII104.3}
$$

$s>0$ 时沿方向 $v/s$ 的直径效应为 $b(z)=(1+(v/s)\cdot z)/2$。原对径零见证的限制必恰为 $b$，而

$$
 h=(\alpha-s)1+2s b+(1-\alpha-s)0
\tag{VII104.4}
$$

给 proper 延拓；$s=0$ 时取 $\alpha u$。反向延拓每个直径效应即给原对径零见证。这里复用的是VI90.8的效应分解，不另计为新归一化或新扩张定理。证毕。

### 104.3 原正交对的唯一第三点和共同三结果

**定理 104.3（受限前件下的joint三元提升）。** 在 $\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$ 下，每个 $p\perp q$ 都有唯一第三纯点 $r$，满足

$$
 D_p\cap D_q=\{r\},\qquad H(p,q)=D_r.
\tag{VII104.5}
$$

三点两两原零。任意指定 $a_p\in\mathcal A_p,a_q\in\mathcal A_q$ 都能在原全空间共同完成：

$$
 a_r:=u-a_p-a_q\in\mathcal A_r,\qquad
 a_i(j)=\delta_{ij},\qquad a_p+a_q+a_r=u.
\tag{VII104.6}
$$

每个纯点都属于这样的三元框架；不存在四个不同的两两原零纯点。因而原数学效应的最大共同可区分纯点数恰为三。

证明。$H(p,q)=D_r$ 已由104.2的前半证明得到，且 $r\in D_p\cap D_q$。因 $q\in D_p$ 而 $q\notin D_q$，两面不同，交只能为该纯单点。这也给 $r$ 的唯一性。$p,q$ 在球 $D_r$ 上为对径；$a_p,a_q$ 分别取一、零两端，故二者在整个 $D_r$ 上相加为一。

置 $h=u-a_p-a_q$。有 $h|_{D_r}=0$、$h(r)=1$、$h\le u$。这里尚未知道 $h\ge0$；精确复用103.5的全域最小值归一论证。若 $c=\min_Kh<0$，在最小面选纯 $x$ 达到它，则

$$
 g=\frac{h-cu}{1-c}\in[0,u],\qquad g(r)=1,\quad g(x)=0.
\tag{VII104.7}
$$

原定义使 $x\in D_r$，与 $h(x)<0=h|_{D_r}$ 矛盾。所以 $h\ge0$，并且 $h\in\mathcal A_r$，得到(VII104.6)。新增处是该已有论证只需正交对的真面前件，未重证或重计103.5的归一化方法；此时也未把 $h$ 认作某个预选唯一 $a_r$。

每个非退化 $D_p$ 有纯点 $q$，从而每个 $p$ 都可如此完成。第四个两两原零纯点必须属于 $D_p\cap D_q=\{r\}$，所以不能不同于 $r$。任何共同可区分纯族必两两原零，而(VII104.6)确给一个三元完备效应族，容量断言遂成立。它不宣称每个混态已有正交谱分解，也不从数学效应族制造实际共同菜单。证毕。

### 104.4 点球双射、唯一确认与已有球上的least

**定理 104.4（局部极性和比较的准确范围）。** 在同一弱入口下，$p\mapsto D_p$ 已是全部原纯点与全部非点真面之间的双射。每个 $a_p\in\mathcal A_p$ 都唯一确认 $p$，所以每个原纯点暴露。任意非零 $b\in C^*$ 若零于 $D_p$，则其全域最大值唯一在 $p$ 达到，且 $b/b(p)\in\mathcal A_p$。

对每个已有真球 $F$ 和 $p\in P\cap F$，任取球图 $\chi:F\to B^d$，有

$$
 T_p(\chi^{-1}z)=a_p(\chi^{-1}z)
 =\frac{1+\chi(p)\cdot z}{2},
 \qquad a_p|_F\le g|_F\quad(g\in F_p).
\tag{VII104.8}
$$

若纯 $p,q$ 共处某个真面，则 $T_p(q)=T_q(p)$。这些结论尚不包括全域 least、$\mathcal A_p$ 的无条件唯一性或不共真面的纯点之间的非零数值互易。

证明。满射已由103.2给出。若 $D_p=D_q=L$，在 $L$ 取纯 $r$。零对称使 $p,q\in D_r$，且 $D_r\ne L$，因为 $r\in L$、$r\notin D_r$。104.2使 $p,q$ 各自在 $D_r$ 内的对径均属于 $D_p=D_q=L$。不同真球的交至多一点，故这两个对径相同；对径映射为对合，遂有 $p=q$，单射成立。

若 $a_p(q)=1$ 且 $q$ 纯，则 $a_p$ 见证 $D_p\subseteq D_q$。极大性与单射迫使 $q=p$。任意一值混态作有限纯分解，其每个正权纯点也取一，故整个一值面为 $\{p\}$。原非负效应 $u-a_p$ 的零面因此为 $\{p\}$，给暴露性。

对 $b$，令 $M=\max_Kb>0$，在最大面取纯 $s$。$b/M\in F_s$，于是 $D_p\subseteq D_s$，极大性和单射给 $s=p$。归一后属于 $\mathcal A_p$，前段的唯一确认又使其最大面仅为 $p$。此论证没有证明所有这样的 $b$ 成一条射线。

最后写 $F=D_s$。由 $p\in D_s$ 和104.2，$p$ 的 $F$ 内对径 $r$ 属于 $D_p$；$a_p$ 在这两个端点取一、零。103.4的同一球计算给(VII104.8)。具体地，任意 $g\in F_p$ 的限制必为 $1-\lambda+\lambda\chi(p)\cdot z$，$0\le\lambda\le1/2$，所以

$$
 (g-a_p)(\chi^{-1}z)
 =(1/2-\lambda)(1-\chi(p)\cdot z)\ge0.
\tag{VII104.9}
$$

原 $a_p$ 本身参加 $F_p$ 的最小化，故在整个 $F$ 上 $T_p=a_p$。交换球内的两个纯点，用内积对称得到互易。若某个 $g\in F_p$ 未在全域满足 $g\ge a_p$，负差可在一个原纯 $q$ 处检出；(VII104.9)迫使这个 $q$ 不与 $p$ 共处任何真面。这准确定位了局部比较尚未覆盖的范围。证毕。

**推论 104.5（带原补预算的逐效应延拓）。** 固定任意 $a_p\in\mathcal A_p$。对 $D_p$ 的每个 proper 仿射效应 $h$，存在原线性 $\widehat h$ 满足

$$
 0\le\widehat h\le u-a_p,\qquad
 \widehat h|_{D_p}=h,\qquad\widehat h(p)=0.
\tag{VII104.10}
$$

证明。采用(VII104.3)。$s>0$ 时取球纯点 $q=\chi^{-1}(v/s)$，任取 $a_q\in\mathcal A_q$。104.3给 $a_q\le u-a_p$，104.4给 $a_q|_{D_p}=(1+(v/s)\cdot z)/2$。故可取

$$
 \widehat h=(\alpha-s)(u-a_p)+2s a_q.
\tag{VII104.11}
$$

两个系数非负，系数和 $\alpha+s\le1$；限制和在 $p$ 的读数均如所需。$s=0$ 时取 $\alpha(u-a_p)$。这仍是 $\forall h\ \exists\widehat h$，未提供一个对所有 $h$ 共同线性、正且保单位的选择，更未提供互补正投影及其对偶核像条件，故不能改称 projectivity。证毕。

### 104.5 三结果完成还强制全部原纯点闭

**定理 104.6（无需先假设的纯点紧性）。** $\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$ 推出 $P$ 在原 $K$ 中闭，从而 $P$ 紧。

证明。设原纯序列 $p_j\to x\in K$。对每个 $p_j$，按104.3选同一原三元框架 $(p_j,q_j,r_j)$ 及其效应 $(a_j,b_j,c_j)$，满足(VII104.6)。原 $K$ 与整个 $[0,u]$ 紧，有限乘积中可取一个共同子列使

$$
 q_j\to y,\quad r_j\to z,\quad
 (a_j,b_j,c_j)\to(a,b,c)\in[0,u]^3.
\tag{VII104.12}
$$

此处不预设 $y,z$ 纯。连续评价和原单位等式给

$$
 a+b+c=u,\qquad a(x)=1,\quad a(y)=a(z)=0,
 \quad b(y)=1,\quad b(z)=0.
\tag{VII104.13}
$$

特别地 $y\ne z$。作 $x$ 的任意有限原纯分解 $x=\sum_i\lambda_i s_i$，其中 $\lambda_i>0$、$\sum_i\lambda_i=1$。原 proper 效应 $a$ 在 $x$ 取一，迫使所有 $a(s_i)=1$。同一个 $a$ 因而见证

$$
 y,z\in D_{s_i}\qquad\text{对每个 }i.
\tag{VII104.14}
$$

两个不同的非点真面至多交于一点，故含同样两个不同点 $y,z$ 的这些 $D_{s_i}$ 全部相同。104.4的点球单射遂迫所有 $s_i$ 相同，故 $x$ 本身纯。有限维中序列闭即闭，结合原 $K$ 紧即得结论。证明只用了已得joint完成、全效应紧性和点球单射，未用全 $\mathrm{Pair}$ 或完整 $S$。它增添了一个真实的受限后果，但本身不证明任意两排除球必相交。证毕。

### 104.6 已有正交模格与尚缺的覆盖律

**定理 104.7（精确的剩余关联缺口）。** 在本章弱入口下，含空面与 $K$ 的整个原面格 $\mathcal L(K)$ 已为完整正交模格。对非空面定义

$$
 F^\perp=\bigcap_{q\in P\cap F}D_q,
 \qquad\varnothing^\perp=K.
\tag{VII104.15}
$$

则 $\{p\}^\perp=D_p$、$D_p^\perp=\{p\}$、$K^\perp=\varnothing$。在此同一域内，下列条件准确等价：

$$
\begin{aligned}
&\forall p,q\in P,\ p\ne q:\ D_p\cap D_q\ne\varnothing\\
&\quad\Longleftrightarrow\ \mathrm{Pair}\\
&\quad\Longleftrightarrow\ \mathcal L(K)\text{ 满足覆盖律}\\
&\quad\Longleftrightarrow\ S\\
&\quad\Longleftrightarrow\ \text{同原锥、同原单位的rank-three有限EJA表示}.
\end{aligned}
\tag{VII104.16}
$$

覆盖律指：对面 $F$ 及不在其中的纯点 $q$，$F\vee\{q\}$ 与 $F$ 之间没有严格中间面。完整 $S$ 仍含原全锥序 least 和全部纯数值互易，不用唯一确认或局部 least 替代。

证明。103.2和104.4已给全部面类型及点球双射。全部面闭，任意交是面，面族的任意 join 可取包含其并的所有面的交，故格完整。零对称先给 $p\in D_p^\perp$。若纯 $s\in D_p^\perp$，则 $P\cap D_p\subseteq D_s$；球的极点凸生成整球，故 $D_p\subseteq D_s$，极大性和单射给 $s=p$。任意混点的有限纯分解留在定义(VII104.15)的每张面中，故也只能为 $p$。同理，若 $K^\perp$ 非空，其中的纯点 $s$ 将满足 $s\in D_s$，矛盾。

逐一检查面类型，便得反序对合 $F^{\perp\perp}=F$，以及 $F\wedge F^\perp=\varnothing$、$F\vee F^\perp=K$。正交模律唯一非平凡的真包含是 $\{q\}\subsetneq D_p$。此时 $p\perp q$，104.3使 $D_p\cap D_q=\{r\}$，104.2使 $q,r$ 为 $D_p$ 的对径，故

$$
 D_p=\{q\}\vee\{r\}
     =\{q\}\vee(D_p\wedge\{q\}^\perp).
\tag{VII104.17}
$$

其余包含为空面、相等或顶面情形，正交模恒等式直接成立。

若 $D_p\cap D_q$ 非空，交中有纯 $r$，零对称给 $p,q\in D_r$，所以 $H(p,q)\ne K$。反向若全 $\mathrm{Pair}$ 成立，103.2使 $H(p,q)=D_r$，于是 $r\in D_p\cap D_q$。这证明(VII104.16)首个等价。

若存在 $H(p,q)=K$，选一个含 $p$ 的非点真面 $L$；这样的 $L$ 可由 $s\in P\cap D_p$ 和零对称取 $L=D_s$。严格链 $\{p\}\subsetneq L\subsetneq\{p\}\vee\{q\}=K$ 违反覆盖律。若全 $\mathrm{Pair}$ 成立，则两个不同原子的join是非点极大真面，它与任一所含原子间不能插入面；非点极大面加面外原子得到 $K$，同样不能插入面。空面加原子的情形也成立，穷尽全部情况。这证明覆盖律等价。

余下等价直接复用103.4—103.6及[Library完整S桥][Q103S]，参数逐字取本章原 $V,C,u,K,P,[0,u]$。本章已由EB得到 $h(K)=3$，故完整 $S$ 的既有一般EJA桥恰落在秩三；同单位反向也恰为103.6。这里不重新证明正对偶剥离、谱性、自对偶、projectivity、滤波纯性或分类，更不在取得 $S$ 以前借用这些结论。证毕。

**开放问题 104.8（弱入口是否自动覆盖）。** 在同一原有限维全效应域中，$\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$ 是否强制(VII104.16)的首项，仍为 open。既未证明这一蕴含，也未给出满足它全部前件而失败覆盖的同域反例。缺失纯对的准确形状是

$$
 H(p,q)=K
 \ \Longleftrightarrow\ \frac{p+q}{2}\in\operatorname{ri}K
 \ \Longleftrightarrow\ D_p\cap D_q=\varnothing.
\tag{VII104.18}
$$

中点等价的证明如下：边界中点有一张非零非负支撑尺读零，非负性迫使两个端点都在其原零真面；反向真面不含整体相对内点。最后一个等价已由104.7证明。若空交发生，对任意 $a_p\in\mathcal A_p,a_q\in\mathcal A_q$，紧性和准确零面给 $\min_{D_q}a_p>0$、$\min_{D_p}a_q>0$。局部三角形和纯点紧性尚未排除这种内部纯弦。

仅有正交模律也不能在逻辑上替代覆盖律：两个三原子Boolean格在零、顶元处作水平和，其中非平凡的可比元素都在同一Boolean块，正交模恒等式按块成立；每条正交边也都在一个三元块中。但跨块两原子的join为顶元，其间可插入第一块的二原子join，故不满足覆盖律。这是抽象格的区别，不是满足本章凸域的反例；它不结算开放问题104.8。

### 104.7 有限原纯点分支完全闭合

**定理 104.9（有限纯点只能为经典三角形）。** 在本章弱入口下，若全部原 $P$ 有限，则 $K$ 是经典三角形，因而(VII104.16)全部成立。

证明。令 $m=\operatorname{affdim}K$。有限纯点使 $K$ 为多面体；若 $m\ge3$，一个facet至少二维，却按103.2须为有有限极点的非退化球。维数至少二的欧氏球有无限极点，矛盾。$m=0,1$ 时纯点的整个排除集不可能为非点球，故 $m=2$，$K$ 为凸多边形。取104.3的一组三元框架 $p,q,r$。三对的原最小面都是非点真面，在二维多边形中只能是边，所以 $[p,q],[q,r],[r,p]$ 都是多边形边。多边形边界图是一个循环，含三循环便只有这三个顶点。因此 $K=\operatorname{conv}\{p,q,r\}$。其 least 是三重心坐标，纯比较为 $\delta_{ij}$，直接复用经典全效应字典即可。有限分支闭合不推出一般无限紧纯点分支闭合。证毕。

### 104.8 齐性、面高三和厚球真面的控制载体

**定义与定理 104.10（原矩阵截面及锥齐性）。** 对整数 $n\ge2$，取

$$
\begin{gathered}
 V_n=\mathbb R\oplus\mathbb R^{n\times2}\oplus\operatorname{Sym}_2(\mathbb R),
 \qquad \dim V_n=2n+4,\\
 M(a,R,S)=\begin{pmatrix}aI_n&R\\R^{\mathsf T}&S\end{pmatrix},\\
 C_n=\{(a,R,S):M(a,R,S)\succeq0\},\qquad
 u_n(a,R,S)=a+\operatorname{tr}S,\qquad K_n=C_n\cap\{u_n=1\}.
\end{gathered}
\tag{VII104.19}
$$

锥模型本身按 `literature-attested` 归属：[Tunçel—Vandenberghe §5.1，印刷页701][Q104MN]将形如 $\begin{pmatrix}\alpha I_L&U^{\mathsf T}\\U&V\end{pmatrix}$、$U\in\mathbb R^{K\times L}$、$V\in\operatorname{Sym}_K(\mathbb R)$ 的PSD锥称为 matrix norm cone。与(VII104.19)的逐项对应为 $K=2,L=n,\alpha=a,U=R^{\mathsf T},V=S$，所以本章 $C_n$ 在矩阵嵌入下正是该成熟锥。原文的Ishi一般结构参数为 $r=K+1=3$，与104.11在本章证明的归一基面高 $h(K_n)=3$ 一致；此处对应同一个模型，不另主张新锥或新分类。

这是闭尖生成锥及严格正单位的整个有限维紧基，效应仍取整个 $[0,u_n]$。锥内部恰为

$$
 a>0,\qquad Q_M:=S-R^{\mathsf T}R/a\succ0.
\tag{VII104.20}
$$

锥 $C_n$ 齐性；这里指线性锥自同构群在锥内部传递，不要求这些变换保持 $u_n$。

证明。矩阵嵌入单射，PSD锥的闭性和尖性被保留；$M(1,0,I_2)\succ0$ 给该线性子空间内点，所以锥生成 $V_n$。PSD给 $a\ge0,S\succeq0$；若 $u_n=0$，则 $a=0,S=0$，PSD再迫 $R=0$，故单位严格正。单位切片中 $0\le a\le1$、$0\le\operatorname{tr}S\le1$，且每个 $|R_{ij}|^2\le aS_{jj}$，所以切片有界而紧。

当 $a>0$ 时，成熟Schur补消元给 $M\succeq0\Longleftrightarrow Q_M\succeq0$，且正定恰为(VII104.20)。若 $a=0$，则 $R=0$，该点在边界；若 $Q_M$ 有非零核向量 $v$，则 $(-Rv/a,v)$ 是矩阵核向量，其PSD二次型支撑尺在此为零而在 $M(1,0,I_2)$ 严格正，故也在边界。因此(VII104.20)确给全部相对内点。

令 $\lambda>0,T\in\mathbb R^{2\times n},A\in\mathrm{GL}_2(\mathbb R)$，则合同变换

$$
 L=\begin{pmatrix}\lambda I_n&0\\T&A\end{pmatrix},
 \qquad M\longmapsto LML^{\mathsf T}
\tag{VII104.21}
$$

保持(VII104.19)的线性子空间，顶部块变为 $\lambda^2aI_n$；其逆仍为同形，所以限制后是锥自同构。任意内点 $M(a,R,S)$ 可从 $M(1,0,I_2)$ 得到：取

$$
 \lambda=\sqrt a,\qquad T=R^{\mathsf T}/\sqrt a,
 \qquad A=Q_M^{1/2}.
\tag{VII104.22}
$$

直接乘法给顶部 $aI_n$、交叉 $R$ 和底部 $R^{\mathsf T}R/a+Q_M=S$，证明传递。Schur补、PSD核面字典和合同变换均为标准方法，本控制的用途在于后面的完整原零集合计算，不将这些方法本身认领为新理论。证毕。

### 104.9 所有纯射线与所有原真面

**定理 104.11（整个面分类与厚度）。** (VII104.19)中全部极端射线准确由下列非零向量生成

$$
 p_X=(1,X,X^{\mathsf T}X)\quad(X\in\mathbb R^{n\times2}),
 \qquad (0,0,ww^{\mathsf T})\quad(0\ne w\in\mathbb R^2).
\tag{VII104.23}
$$

原纯点是它们各自除以 $u_n$ 后的全部点。全部非零、非射线的真锥面的归一基准确为 $B^2$ 或 $B^{n+1}$：前一类来自

$$
 \mathcal F_0=\{(0,0,S):S\succeq0\},
\tag{VII104.24}
$$

后一类来自非零核向量 $(t,v)\in\mathbb R^n\oplus\mathbb R^2$、$v\ne0$ 的面

$$
 \mathcal F_{t,v}=\{(a,R,S)\in C_n:Rv=-at,\ Sv=-R^{\mathsf T}t\}.
\tag{VII104.25}
$$

所以 $h(K_n)=3$；$n=2$ 时非点真面只有厚 $B^2,B^3$，没有线段面。

证明。先说明为何以下分类穷尽所有面，而不只列出候选点。对任意 $M\in C_n$，其整个最小锥面是

$$
 \operatorname{face}_{C_n}(M)
 =\{N\in C_n:\ker M\subseteq\ker N\}.
\tag{VII104.26}
$$

右侧由PSD非负尺 $N\mapsto\operatorname{tr}(P_{\ker M}N)$ 暴露；零读数等价于每个核向量都被 $N$ 消灭。反向若 $N$ 满足核包含，在 $W=\operatorname{range}M$ 上 $M$ 正定，而 $N$ 支撑在同一个 $W$，故对足够小 $\varepsilon>0$，$M-\varepsilon N\succeq0$。差仍在原线性子空间，因而属于 $C_n$；任何包含 $M$ 的锥面由 $M=(M-\varepsilon N)+\varepsilon N$ 都须包含 $N$。这证明(VII104.26)。任一非零面取其相对内点，其最小面就是原面，故逐个分类 $M$ 的核已分类全部面，包括起初未要求闭的面。

若 $a=0$，PSD的二阶主子式迫 $R=0$。$S$ 秩一时(VII104.26)给对应的射线；$S$ 秩二时给整个 $\mathcal F_0$。其归一切片是实二阶密度矩阵，坐标 $(S_{11}-S_{22},2S_{12})$ 恰给整个 $B^2$。

若 $a>0$，写 $X=R/a$。Schur消元使核为

$$
 \ker M=\{(-Xv,v):v\in\ker Q_M\}.
\tag{VII104.27}
$$

$Q_M=0$ 时，对一个原 $N=(b,Y,Z)$ 施加这全部核关系，依次得到 $Y=bX,Z=bX^{\mathsf T}X$。所以最小面恰为 $\mathbb R_+p_X$，包括任意秩的 $X$，没有只保留环境秩一射线。$Q_M$ 秩二时是整体内点，最小面为整个锥。$Q_M$ 秩一时其核由某个 $(t,v)$、$v\ne0$ 张成，最小面正是(VII104.25)。

把 $v$ 连同 $t$ 同比例缩放，再用底部正交坐标把 $v$ 化为 $e_2$，不会改变单位。面内全部矩阵可且只能写为

$$
 R=(x,-at),\qquad
 S=\begin{pmatrix}b&-x\cdot t\\-x\cdot t&a\|t\|^2\end{pmatrix}.
\tag{VII104.28}
$$

对向量 $(z,\beta,\gamma)$ 的二次型变为
$a\|z-\gamma t\|^2+2\beta x\cdot(z-\gamma t)+b\beta^2$。
因此面锥精确等价于

$$
 a,b\ge0,\qquad ab\ge\|x\|^2,
 \qquad u_n=d_ta+b,\quad d_t=1+\|t\|^2.
\tag{VII104.29}
$$

在单位切片上，显式仿射坐标

$$
 z_0=d_ta-b,\qquad z'=2\sqrt{d_t}\,x
\tag{VII104.30}
$$

给 $z_0^2+\|z'\|^2\le1$；逆为 $a=(1+z_0)/(2d_t)$、$b=(1-z_0)/2$、$x=z'/(2\sqrt{d_t})$，所以是整个 $B^{n+1}$。任意 $(t,v)$ 都可取此锥的相对内点，故这些面确实出现。

上述各秩情形穷尽所有非零 $M$。归一基 $K_n$ 的非点真面均为严格凸球，球的非空真面只有纯单点，故面链恰有三层。$n=2$ 的球维数分别为二和三，遂得最后断言。对照 $n=1$ 时同一线性空间恰为整个 $\operatorname{Sym}_3$，锥为实三阶PSD；此时 $X$ 只有一行，不能有秩二。增加一行后允许 $X=I_2$，其原极端射线在环境矩阵中秩二；这是下面控制的代数区别，不是新物理结论。证毕。

### 104.10 一张原纯点处的全部正零尺和全部确认效应

**定理 104.12（完整原确认面的参数化）。** 只取 $n=2$，记 $u=u_2$、$p=p_{I_2}/3$。所有在 $p$ 为零的原正线性泛函恰为

$$
 g_B(a,R,S)=\operatorname{tr}(BS)-2\operatorname{tr}(BR)
             +a\operatorname{tr}B,\qquad B\succeq0.
\tag{VII104.31}
$$

所有原 $f\in F_p$ 恰为 $f_B=u-g_B$，参数准确满足

$$
 0\preceq B\prec I_2,\qquad
 \operatorname{tr}\bigl(B(I_2-B)^{-1}\bigr)\le1.
\tag{VII104.32}
$$

等价地，以

$$
 Q=B(I_2-B)^{-1}\succeq0,\quad\operatorname{tr}Q\le1,
 \qquad B=Q(I_2+Q)^{-1}
\tag{VII104.33}
$$

参数化整个确认面，包含 $Q=0$ 所给 $f=u$。

证明。任意原线性泛函唯一写为

$$
 g=\alpha a+2\operatorname{tr}(M^{\mathsf T}R)+\operatorname{tr}(BS),
 \quad M\in\mathbb R^{2\times2},\quad B\in\operatorname{Sym}_2.
\tag{VII104.34}
$$

若 $g\ge0$，在全部 $a=0$ 的原边界态上检验给 $B\succeq0$。在全部原射线 $p_Y$ 上有
$\alpha+2\operatorname{tr}(M^{\mathsf T}Y)+\operatorname{tr}(BY^{\mathsf T}Y)\ge0$。
若又 $g(p)=0$，此二次多项式在 $Y=I_2$ 达到零的全局最小值。其梯度给 $M=-B$，值本身给 $\alpha=\operatorname{tr}B$，得到(VII104.31)。反向对 $a>0$ 写 $Y=R/a$、$Z=S-R^{\mathsf T}R/a\succeq0$，则

$$
 g_B=a\operatorname{tr}\bigl(B(Y-I_2)^{\mathsf T}(Y-I_2)\bigr)
          +\operatorname{tr}(BZ)\ge0.
\tag{VII104.35}
$$

$a=0$ 时 $R=0$，只余 $\operatorname{tr}(BS)\ge0$。所以已穷尽所有原正零尺，不借环境PSD效应子菜单。

$f\in F_p$ 当且仅当 $g=u-f\ge0$、$g(p)=0$ 及 $f\ge0$；故已知 $f=u-g_B$。在 $a=0$ 上 $f\ge0$ 强制 $I_2-B\succeq0$。若 $Bv=v$、$\|v\|=1$，取 $Y=-t vv^{\mathsf T}$，在 $p_Y$ 上的二次项沿此方向为零，线性项为 $-2t$，大 $t$ 时 $f<0$。所以必须 $B\prec I_2$。

此时对所有原 $a>0$ 点完成平方，得到

$$
\begin{aligned}
 f_B(a,R,S)={}&a(1-\operatorname{tr}Q)\\
 &+a\operatorname{tr}\bigl((I_2-B)(Y+Q)^{\mathsf T}(Y+Q)\bigr)\\
 &+\operatorname{tr}\bigl((I_2-B)Z\bigr).
\end{aligned}
\tag{VII104.36}
$$

取 $Y=-Q,Z=0$ 表明非负性必要地要求 $\operatorname{tr}Q\le1$；该条件又使右侧全部非负，且在 $a=0$ 时 $f_B=\operatorname{tr}((I_2-B)S)\ge0$。这证明(VII104.32)充分必要，反变换给(VII104.33)。由于原 $g_B\ge0$，$f_B\le u$ 也已自动满足，参数化确为整个 $F_p$。证毕。

### 104.11 整个排除集合是曲面圆盘，混合缺口恰为六分之一

**定理 104.13（全效应零集合与精确下包络）。** 在104.12的整个原载体中，

$$
 D_p=\left\{\frac{p_{-Q}}{1+\operatorname{tr}(Q^2)}:
                Q\in\operatorname{Sym}_2,\ Q\succeq0,\operatorname{tr}Q=1\right\}.
\tag{VII104.37}
$$

它全部由原纯点组成，与闭圆盘同胚，却非凸，因而不是仿射面球。取

$$
 Q_1=\operatorname{diag}(1,0),\quad Q_2=\operatorname{diag}(0,1),
 \quad q_i=p_{-Q_i}/2,
 \quad m=(q_1+q_2)/2=(1/2,-I_2/4,I_2/4),
\tag{VII104.38}
$$

则 $q_i\in D_p$，但 $m\in\operatorname{ri}K_2$，并且

$$
 T_p(q_1)=T_p(q_2)=0,\qquad T_p(m)=\frac16.
\tag{VII104.39}
$$

证明。$a=0$ 的非零点有 $S\succeq0,S\ne0$，而 $I_2-B\succ0$，所以每个原 $f_B$ 在其上严格正。$a>0$ 时(VII104.36)的三项非负；第一项为零须 $\operatorname{tr}Q=1$，正定权重下第二、三项同时为零恰须 $Y=-Q,Z=0$。所以 $f_B$ 有归一零点当且仅当 $\operatorname{tr}Q=1$，且零面只含 $p_{-Q}/(1+\operatorname{tr}Q^2)$。遍历104.12的全部参数即得(VII104.37)，没有遗漏非纯排除态。

实对称PSD的迹一 $Q$ 构成 $B^2$。上述映射连续且单射，逆在像上为 $Q=-R/a$；参数域紧，故为同胚。其像虽是一张曲面圆盘，却不能据此叫作仿射球，因为下面的混合明确离开它。

$Q_i$ 对应 $B_i=Q_i/2$，所给原确认效应明确为

$$
 f_1=\tfrac12a+\tfrac12S_{11}+S_{22}+R_{11},\qquad
 f_2=\tfrac12a+S_{11}+\tfrac12S_{22}+R_{22}.
\tag{VII104.40}
$$

104.12已证明它们 proper；亦可看其补分别为 $\tfrac12(a+S_{11}-2R_{11})$、$\tfrac12(a+S_{22}-2R_{22})$，都是PSD二次型的非负读数。直接代入有 $f_i(p)=1,f_i(q_i)=0$。而 $m$ 的Schur补为

$$
 I_2/4-(-I_2/4)^{\mathsf T}(-I_2/4)/(1/2)=I_2/8\succ0,
\tag{VII104.41}
$$

所以 $m$ 是整个原 $K_2$ 的相对内点，$D_p$ 非凸。更精确地，全部原确认效应在此读数为

$$
 f_B(m)=1-\frac54\operatorname{tr}B.
\tag{VII104.42}
$$

若 $Q$ 的两个特征值为 $\eta_1,\eta_2\ge0$，约束为 $\eta_1+\eta_2\le1$，则

$$
 \operatorname{tr}B=\frac{\eta_1}{1+\eta_1}+\frac{\eta_2}{1+\eta_2}
 \le\frac23.
\tag{VII104.43}
$$

这是递增严格凹函数 $t/(1+t)$ 的两变量界，最大值恰在 $\eta_1=\eta_2=1/2$ 达到；可直接取 $Q=I_2/2,B=I_2/3$。所以(VII104.42)的最小值是 $1-5/6=1/6$。两端点已有零见证且效应非负，得到(VII104.39)。因此同一 $T_p$ 不仿射；若原全锥序 least 存在，下包络就等于该线性效应，与(VII104.39)矛盾，所以该纯点没有这样的 least。这是整个原效应区间的零拼合失败，不是一个选定有限菜单的失败。证毕。

### 104.12 控制反驳的条件及其不反驳的候选

**命题 104.14（厚球加齐性不能代付排除集拼合）。** $K_2$ 具有齐性锥、面高三和全部厚球非点真面，但既不满足 $\mathrm{EB}_{\ge1}$，也不满足 $\mathrm{Pair}_{\perp}$；其全部原纯点集不闭。因而它只反驳以“所有非点真面都是厚球，即使再加锥齐性”替换完整排除集条件的推理，不是开放问题104.8的同域反例。

证明。厚球、面高和齐性已由104.10—104.11给出，$D_p$ 非凸由104.13给出，故EB失败。又 $p\perp q_1$，但 $p_{I_2}$ 和 $p_Y$、$Y=\operatorname{diag}(-1,0)$ 的核分别为 $\{(-I_2v,v)\}$ 和 $\{(-Yv,v)\}$。其交为零，因为

$$
 (I_2-Y)v=\operatorname{diag}(2,1)v=0\ \Longrightarrow\ v=0.
\tag{VII104.44}
$$

PSD矩阵之和的核是各核之交，所以归一态 $p,q_1$ 的中点矩阵正定，属于整个 $K_2$ 的相对内部。因此 $H(p,q_1)=K_2$，连正交对的Pair也失败。

最后，对实 $t\to+\infty$，全部原纯点中有

$$
 \frac{p_{tI_2}}{1+2t^2}\longrightarrow (0,0,I_2/2).
\tag{VII104.45}
$$

极限是 $\mathcal F_0$ 的混态，等于 $(0,0,Q_1)$ 与 $(0,0,Q_2)$ 两个不同原纯点的平均，故纯点集不闭。这与104.6相容：该模型失败其弱入口，而非推翻弱入口所强制的纯点紧性。上述齐性是锥内点齐性，不额外宣称保原单位的纯态传递或实际可逆服务。证毕。

### 104.13 保持原装饰元组的完整弱候选

**定义与定理 104.15（量词削减候选及已知单向）。** 固定103.10的同一 $\mathcal O$、原来源与过程域、非空 $\mathcal J\subseteq\{A,D,E\}$，并只在其共同 $\mathcal D_{3,\mathcal J}$ 中比较。$\mathcal N(\mathcal O)$ 逐字取103.10的全部非几何原合同，未选载体仍保留完整 $S_X$。定义

$$
\begin{aligned}
 \mathsf R_{\perp,3}^{\mathcal J}(\mathcal O):\quad
 &\mathcal N(\mathcal O)\ \land\!\bigwedge_{X\notin\mathcal J}S_X\\
 &\land\!\bigwedge_{X\in\mathcal J}
       (\mathrm{EB}_{\ge1,X}+\mathrm{Pair}_{\perp,X}).
\end{aligned}
\tag{VII104.46}
$$

所选载体仍是原概率像自身的整个有限维紧基和全部原效应，不取完成体、不选纯子集或效应子菜单。其 $h(K_X)=3$ 已由EB推出，与共同域一致。现有结论准确为

$$
 \mathsf R_{\rm exclusion,3}^{\mathcal J}
 \ \Longrightarrow\ \mathsf R_{\perp,3}^{\mathcal J}.
\tag{VII104.47}
$$

若每个所选 $X$ 的 $P_X$ 有限，或另已证明每个所选载体任意两排除球相交，则反向成立，并沿103.10返回全部既有完整包。一般反向仍为开放问题104.8；这只是一项量词更弱的完整候选，未证明其模型类严格扩大，也未证明它与完整量子包等价。

证明。全Pair蕴含正交对Pair，非几何合同与未选项逐字相同，所以(VII104.47)成立。附加有限性时104.9给全Pair，附加相交性时104.7给全Pair；逐载体恢复103.10的旧候选后直接用(VII103.35)，没有更换任何原标签或来源。一般反向正好需要104.7的覆盖缺口，当前局部三元提升不能填补它。

准确的条件消费可列为

| 同一原载体上的条件 | 已供应的状态／概率结论 | 仍须原合同供应的内容 |
| --- | --- | --- |
| EB加正交Pair | joint三结果、点球双射、纯点紧、局部least互易、正交模面格 | 覆盖律及全域least互易尚为open；不据此声称一般Jordan或完整QM |
| 再补覆盖律 | 同单位rank-three EJA及整个原全效应字典 | 实际来源、过程与其余消费者仍用103.10 |
| 上一行再要求全部 $D_p$ 维数至少二 | 103.7的四个简单三阶类型，排除直和旗标分支 | 此厚度条件没有单独选择复数 |
| 覆盖律加全部 $D_p\simeq B^3$ | 同载体 $H_3(\mathbb C)$、全部密度态／效应与103.8的Born字典 | 复合、指定事件CP、仪器、更新、时间与来源仍各守原合同 |

表中后面三行全部直接消费103.6—103.8：原 $\Phi$ 满足 $\Phi(J_+)=C,u\Phi=\tau_J$，不是预先把 $u$ 换为矩阵迹。复三阶分支的概率准确为 $f_E(x)=\operatorname{tr}(E\Phi^{-1}x)$、$0\preceq E\preceq I_3$，纯比较为 $|v^*w|^2$；此处只作原字典回接，不重计Born或分类证明。$\mathrm{EB}_{\ge2}$ 只有在覆盖闭合后才按既有分类排除直和，不在弱入口下预称所有模型简单。

$\mathcal N$ 的引用保留103.10列出的全部量词：原准备／测试／过程／参考／读回与装饰；原像自身紧及全部中点实现、全部非负质量、零和不等质量、完整相关联合域；同一个 $L$、同一个 $p$ 两次和同一 $\omega$；两实张成、全实 $Z$、完整(83.8)、VI(89.13)的两尺度等式、C2、整个 $G=1_E$；精确PRE后的同一资格态、活跃块严格负方向、共享总迹一、非活跃零质量和整个H13输出。共同来源合同、菜单／分支、记录／权限／控制／钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、合法未来、旧支撑与每个中间切口亦按原定义保留。

VI89.9—89.10的每个原生／细化消费者继续使用其全部原字及terminal futures、联合有符号关系、标签归组、记录后条件未来、source-adoption和资源合同。同事件CP按VI89.9的完整原提升、实际探针及相容核条件认证；若已由充分递归参考取得，则直接复用。Kraus、实际仪器、TP／TNI、Lüders和物理时间各按既有前件消费，不能从抽象效应反向制造装置，也不把已得后果重新列成未付条件。

若原复合合同使 $A,D=A\otimes A,E=D\otimes A$ 的秩为 $3,9,27$，仍不能同时对三者加要求秩三的EB入口；选择全部三者时交集为空。新Pair量词不解除此冲突，也不将rank-three几何强加于所有寄存器。证毕。

### 104.14 参考端点路线、来源归属与完整白话

**命题 104.16（新旧关系的量词边界和数学归属）。** [VI101][Q103VI]的有限参考端点定理不能直接代付104.8的覆盖缺口。该路线每个参考端点仍对全部原纯目标满足互反，并保留对全部原纯目标的互补和；本章只有共真面纯点之间的(VII104.8)，且无整体中心对称输入。若要转用VI101，必须另证其全部原前件及载体对应，不能从“参考端点有限”删掉全目标量词。

证明。VI(101.1)要求每个 $p_i,q_i$ 的 $T_{p_i}(r),T_{q_i}(r)$ 对全部 $r\in P$ 满足 $\mathrm E2_i,\mathrm R_{i,+},\mathrm R_{i,-}$，再由支持约束积分得到整椭球。本章未覆盖的纯对正是(VII104.18)的内部弦，因而104.4不能向其提供这些全目标读数；joint三角形仅给其自身三点及已有真球上的读数，未给所有原纯目标上的互补和。因此本章给出的逐球公式尚不构成该定理的完整前提映射。这说明现有推理的接口边界，不宣称两种额外条件永远不能共同研究。

本章的承重增量按 `repo-derived` 归属：原Pair前件收缩到正交对后的局部结构、无需预设的纯点紧性，以及(VII104.19)原全效应模型中完整 $D_p$、确认面和 $1/6$ 缺口的计算。103.2的面穷尽、103.5的最小值归一、VI90.8的局部效应凸分解、103章的一般 $S$／同单位反向／成熟分类与Born字典均为直接复用。matrix norm cone本身及其齐性为成熟结果[Q104MN]，Schur补、PSD面核字典、有限维凸分解、球支持等号条件和齐性合同均为标准中间工具。104.10—104.11的坐标与面结构仅为后续消费准备，不另计新锥或新分类；在这一成熟控制模型上的 `repo-derived` 增量只计104.12—104.14的完整原 proper 确认面、整个 $D_p$、$1/6$ 缺口及其与弱候选的关系。

一般重构的来源仍为[Library完整S接口][Q103S]及其中明确归属的Niestegge proper-effect剥离、Barnum—Müller—Ududec Theorem 16；厚球及分类的成熟归属沿用[Alfsen—Shultz原文][Q103AS]和103.7。唯一确认不等于 proper least，暴露面或正交模面格也不等于该Theorem 16要求的projectivity；这些条件在本章只有补覆盖后沿既有桥共同取得。上述新综合不主张世界首创、文献穷尽、经验实现、内核形式核验或完整物理公理最少性。

完整白话是：仍只看原来的整块状态物体、全部纯状态和所有合法零一尺。对每个纯点，把能被某张确认它的尺排除的状态全收齐，要求这整个集合是一块实心球；再只要求本来就能互相排除的两个纯点一起留在一块真正边界面。这个较弱入口已能把这样的两点补成一个三角形，三把原尺同时非负，总和恰为原单位。点和背后的排除球也已经一一相配，每把整球零尺只会确定接受自己的那个纯点；在任何已有共同边界球里，最低刻度和交换两端的读数都固定了。

这些共同三把尺还阻止纯点序列掉到混态：若纯点逼近某点，就连同另外两点及三把尺一起取极限。极限里仍有两个可区分的零点，迫使极限点的每个纯分解组分背后都有同一块排除球；点球一一对应使这些组分只能相同。所以纯点集确已闭且紧。但尚缺的一步仍是：会不会有两个纯点的连线中点已经钻进整体内部，使它们没有共同边界球、背后的两块排除球完全错开？正交三角形只在已有关联处工作，正交模关系也只组织这些关联，尚未证明这种错开不能发生。有限纯点时已经排除，状态体只能是经典三角形；一般无限紧纯点时仍为open。

厚球控制说明为何“每块真边界都圆”不够。这里所有非点真面都是真实的二维或三维实心球，锥内部甚至可以通过线性保正变换彼此搬运；但同一个纯点可用两把不同原尺分别排除两个纯端点，却不能用任何确认尺排除二者的平均。平均已经在整体内部，最低读数严格为六分之一。完整排除集合因而是一张弯曲圆盘，连凸集都不是。这个模型没有满足新候选的全部前件，所以不能说候选已被反驳；它准确排除的是只数厚球、再加齐性就替代整个排除集合拼合的捷径。

若在同一原域补上任意两排除球相交，已有桥便立即给完整三阶Jordan状态与全效应；若再要求每个完整排除球都是三维，才准确得到复三能级的密度矩阵和Born模方字典。实际准备、共同菜单、过程、复合、CP、仪器、更新、物理钟及来源仍由原合同承担。量词收缩是一项完整候选的改写提案，已证后果与未证逆向如上分开；它不是已经完成的更简洁完备物理公理。上述解释逐项由104.2—104.15及本命题的量词核对给出。证毕。

[Q104MN]: https://doi.org/10.1017/S0962492922000113 "Levent Tunçel and Lieven Vandenberghe, Linear optimization over homogeneous matrix cones, Acta Numerica 32 (2023), 675–747, §5.1, p. 701. Matrix norm cone."

## 追加锚（本行以下为增补区）
