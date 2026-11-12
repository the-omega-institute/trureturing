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
