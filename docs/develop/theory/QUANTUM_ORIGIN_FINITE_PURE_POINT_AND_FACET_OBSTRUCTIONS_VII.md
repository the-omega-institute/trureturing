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

## 99. 原有限全效应的边四边形、指定投影与facet延拓障碍

### 99.1 整个原载体、两种比较与实际边

**定义 99.1（有限全混态零拼合域）。** 本章的VII97.x—99.x指本卷，VI89.x、VI90.x指[第六卷](QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md)，V88.x指[第五卷](QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)。取非零有限维实空间 $V$、闭尖生成凸锥 $C$、在 $C\setminus\{0\}$ 上严格正的原线性单位 $u$，并使用

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
\tag{VII99.1}
$$

$P$ 是整个原基的全部纯点，$x,y$ 遍历全部原混态，$[0,u]$ 是整个原区间。紧基张成 $V$，故 $[0,u]$ 及非空 $F_p$ 紧，上式最小值达到；零排除等价于存在同一张 $f\in[0,u]$ 在 $p$ 取一、在 $x$ 取零。本章假设这个完整 $\mathrm{Z0}$，不假设 $\mathrm B$、least确认、自对偶、正定配对、正交模律、Jordan乘积、ROG表示或正滤子，也不加入标签归一化或实际装置前提。

$m\ge1$ 时直接复用VII97.2—97.5：$p\mapsto D_p$ 是顶点到facet的双射，$h_p\in[0,u]$ 是零面为 $D_p$ 且 $h_p(p)=1$ 的唯一规范facet效应，且 $h_p$ 只在 $p$ 达到一。记

$$
T_{pq}:=h_p(q),\qquad
0\le T_{pq}<1\ (p\ne q),\qquad
T_{pq}=0\ \Longleftrightarrow\ T_{qp}=0.
\tag{VII99.2}
$$

这里 $T_{pq}$ 是已指定的规范facet读数，$T_p(q)$ 则仍是遍历全部原确认效应的下包络；不将二者认同。对面 $F$ 沿用 $F^\#=\bigcap_{r\in\operatorname{ext}F}D_r$、$\varnothing^\#=K$，以及VII97.3的反序对合和 $\dim F+\dim F^\#=m-1$。$\operatorname{span}\varnothing=\{0\}$。本章的实际边是 $K$ 的一维面 $E=[p,q]$，$p,q\in P$ 不同；$m=1$ 时允许 $E=K$。取定这样一条边后置

$$
a=T_{qp}=h_q(p),\qquad b=T_{pq}=h_p(q),\qquad
d=1-ab>0,\qquad E^\#=D_p\cap D_q.
\tag{VII99.3}
$$

### 99.2 两张facet效应给整个边效应面和严格外部余量

**定理 99.2（实际边的原效应四边形）。** 在定义VII99.1的前件下，对每条实际边 $E=[p,q]$，令

$$
\begin{gathered}
Q_E=\{f\in C^*:f|_{E^\#}=0\},\qquad
\mathcal I_E=\{f\in[0,u]:f|_{E^\#}=0\},\\
e_E=\frac{(1-a)h_p+(1-b)h_q}{d}.
\end{gathered}
\tag{VII99.4}
$$

则 $Q_E=\mathbb R_+h_p+\mathbb R_+h_q$，且 $\mathcal I_E$ 是整个原 $[0,u]$ 的二维面，准确为

$$
\begin{aligned}
\mathcal I_E
&=\{\alpha h_p+\beta h_q:\alpha,\beta\ge0,
\ \alpha+a\beta\le1,\ b\alpha+\beta\le1\}\\
&=\operatorname{conv}\{0,h_p,e_E,h_q\}.
\end{aligned}
\tag{VII99.5}
$$

$e_E$ 是唯一在 $E^\#$ 恒零、在 $p,q$ 都取一的原效应；其整个零面和一面分别为 $E^\#$ 和 $E$。特别是，对每个原顶点 $r\in P\setminus\{p,q\}$，有严格余量

$$
\Delta_{pqr}:=d-(1-a)T_{pr}-(1-b)T_{qr}
=d\bigl(1-e_E(r)\bigr)>0.
\tag{VII99.6}
$$

若 $m\ge2$，还存在对每个 $s\in\operatorname{ext}E^\#$ 都严格正的系数 $\lambda_s$，使

$$
u=e_E+\sum_{s\in\operatorname{ext}E^\#}\lambda_sh_s.
\tag{VII99.7}
$$

若 $m=1$，则 $E=K$、$E^\#=\varnothing$、$a=b=0$、$e_E=u$，式(VII99.7)的和为空和零，不要求存在任何系数。$m=0$ 没有实际边，因而本定理的边量词为空。

证明。先设 $m\ge2$。VII97.3给 $\dim E^\#=m-2$，所以 $\dim\operatorname{span}E^\#=m-1$，其在 $V^*$ 中的消灭子为二维。$h_p,h_q$ 都消灭这个空间；它们在 $p,q$ 上的评价矩阵为

$$
\begin{pmatrix}1&b\\a&1\end{pmatrix},\qquad \det=d>0,
\tag{VII99.8}
$$

故它们是一组基。不同facets $D_q,D_p$ 互不包含，存在原顶点 $r\in D_q\setminus D_p$ 和 $s\in D_p\setminus D_q$。若 $f=\alpha h_p+\beta h_q\in C^*$，分别在 $r,s$ 评价便给 $\alpha,\beta\ge0$。反向由 $h_p,h_q\in C^*$ 直接成立。因此得到 $Q_E$ 的准确表达。$m=1$ 时 $K=[p,q]$，两张规范facet效应是端点重心坐标，$D_p=\{q\}$、$D_q=\{p\}$，同一矩阵为单位矩阵，且整个 $V^*=\operatorname{span}\{h_p,h_q\}$；上述非负锥表达也成立。

以下对所有 $m\ge1$ 同时论证。对任意 $0\ne f\in Q_E$，令 $M_f=\max_K f>0$。若原顶点 $v$ 达到 $M_f$，则 $f/M_f$ 是原 proper 效应，确认 $v$ 并消灭 $E^\#$，故 $E^\#\subseteq D_v$。反序对合给 $v\in E^{\#\#}=E$。由于 $K$ 是整个有限顶点凸包，$f$ 的极大集也是由其极大顶点生成的面，故

$$
\operatorname{argmax}_K f\subseteq E,\qquad
\max_K f=\max\{f(p),f(q)\}.
\tag{VII99.9}
$$

这对任意非零 $f\in Q_E$ 只给极大集包含于 $E$，没有声称每个这样的 $f$ 都在整条边恒定。零泛函的零一界直接成立。因此 $\alpha h_p+\beta h_q$ 为proper，当且仅当两系数非负且端点值 $\alpha+a\beta,b\alpha+\beta$ 都不超过一，得到(VII99.5)第一行。

该平面区域在坐标轴上的顶点为 $(0,0),(1,0),(0,1)$；另外两条上界直线的交点为

$$
(\alpha_*,\beta_*)=
\left(\frac{1-a}{d},\frac{1-b}{d}\right),\qquad
\alpha_*,\beta_*>0.
\tag{VII99.10}
$$

每条上界在线段轴端的另一约束均严格，交点两坐标为正，故这四点正是全部顶点，按 $0,h_p,e_E,h_q$ 循环排列。$e_E(p)=e_E(q)=1$，由(VII99.9)其一面恰为 $E$；两个严格正系数又使其零面恰为 $D_p\cap D_q=E^\#$。同一可逆矩阵给唯一性，并立即给(VII99.6)。由于所有原效应在 $E^\#$ 非负，若一个严格凸组合在其上恒零，两个分量也都恒零，故 $\mathcal I_E$ 是原区间的面；它含仿射独立的 $0,h_p,h_q$ 且在上述二维消灭子内，维数恰为二。空 $E^\#$ 时它就是整个二维原区间。

为证(VII99.7)，只需标准多面体的facet—对偶极射线对应：VII97.2已列出全部facets，因而 $C^*=\operatorname{cone}\{h_s:s\in P\}$。其有限维分离证明是：这些半空间 $h_s\ge0$ 的交正是 $C$；若某个原正泛函不在这些法向的有限生成闭锥中，分离就给一个在所有 $h_s$ 上非负、在该泛函上为负的向量，与它属于 $C$ 矛盾。这是成熟凸锥对偶步骤，不是额外自对偶前提。

$m\ge2$ 时令 $R=\operatorname{ext}E^\#\ne\varnothing$、$g=u-e_E$、$S_R=\sum_{s\in R}h_s$。$g,S_R$ 都在 $p,q$ 取零；对其他原顶点 $v$，$g(v)>0$。有限性允许取 $\varepsilon>0$，使 $g(v)-\varepsilon S_R(v)\ge0$ 对全部 $v\in P$ 成立，于是 $g-\varepsilon S_R\in C^*$。将它写成上述 $h_s$ 的非负组合。在 $p,q$ 评价为零，迫使每个有非零系数的 $h_s$ 同时消灭 $p,q$，亦即 $s\in D_p\cap D_q=E^\#$，其中用了纯点零排除对称性。因此加回 $\varepsilon S_R$ 后每个 $s\in R$ 的系数都严格正。$m=1$ 时端点重心坐标之和就是 $u$，单独给所述空和分支。证毕。

### 99.3 沿原补面张成的指定分裂及其正性

**定理 99.3（proper质量不代付正投影）。** 在定义VII99.1下，每条实际边都有准确线性直和

$$
V=\operatorname{span}\{p,q\}\oplus\operatorname{span}E^\#.
\tag{VII99.11}
$$

沿这里的原补面张成投到边张成的唯一线性投影为

$$
\begin{gathered}
\Pi_E(x)=\xi_p(x)p+\xi_q(x)q,\\
\xi_p=\frac{h_p-bh_q}{d},\qquad
\xi_q=\frac{h_q-ah_p}{d},\qquad
u\circ\Pi_E=\xi_p+\xi_q=e_E\in[0,u].
\end{gathered}
\tag{VII99.12}
$$

下列条件等价：

$$
\begin{gathered}
\Pi_E(C)\subseteq C;\qquad
q\in D_p;\qquad a=b=0;\\
e_E-h_p\in C^*;\qquad e_E-h_q\in C^*;\qquad
\mathcal I_E\text{ 是平行四边形}.
\end{gathered}
\tag{VII99.13}
$$

这些条件成立时 $\Pi_E$ 的像锥为 $\operatorname{cone}\{p,q\}$；失败时(VII99.12)的总质量效应仍为proper。若 $m=1$，$\Pi_E=1_V$，这些条件全成立；$m=0$ 无边，不构造 $\Pi_E$。

证明。$p,q$ 线性独立，因为它们不同且 $u(p)=u(q)=1$。若 $\eta p+\theta q$ 属于 $\operatorname{span}E^\#$，分别作用 $h_p,h_q$ 并用(VII99.8)可得 $\eta=\theta=0$。当 $m\ge2$ 时两个子空间维数为 $2,m-1$，和为 $\dim V=m+1$；$m=1$ 时第二个为零，也得到(VII99.11)。两个 $\xi$ 消灭补面张成，在 $p,q$ 上分别给 $(1,0),(0,1)$，所以(VII99.12)确是所指定的投影，满足 $\Pi_E^2=\Pi_E$，其质量式由直接相加得到。

还需核对像锥：

$$
C\cap\operatorname{span}\{p,q\}=\operatorname{cone}\{p,q\}.
\tag{VII99.14}
$$

若 $0\ne z$ 属于左边，则 $u(z)>0$，且 $u-e_E$ 消灭 $p,q$，故 $(u-e_E)(z)=0$。于是 $z/u(z)\in K$ 位于 $e_E$ 的整个一面 $E=[p,q]$，给出右边的非负分解；零向量及反向包含直接成立。因此 $\Pi_E$ 正，当且仅当其两个唯一坐标 $\xi_p,\xi_q$ 都属于 $C^*$。

若 $a=b=0$，两坐标就是 $h_p,h_q$，故正；它又固定 $p,q$，所以像锥恰为(VII99.14)。若 $a>0$，取VII99.2证明中的原顶点 $r\in D_q\setminus D_p$，则

$$
\xi_q(r)=-\frac{a h_p(r)}d<0,
\tag{VII99.15}
$$

故 $\Pi_E(r)\notin C$。由(VII99.2)，$a=0$ 当且仅当 $b=0$，且等价于 $q\in D_p$；这排除了只有一个非零交叉值的分支。

另一方面，

$$
e_E-h_p=\frac{1-b}{d}(h_q-ah_p),\qquad
e_E-h_q=\frac{1-a}{d}(h_p-bh_q).
\tag{VII99.16}
$$

当 $a>0$ 时，第一式在同一个 $r$ 为负；交换 $p,q$ 得第二式在某个 $s\in D_p\setminus D_q$ 为负。当 $a=b=0$ 时两式分别为 $h_q,h_p$，故得到两项锥序等价。特别是非接触边上的 $e_E\in F_p$ 不支配 $h_p$，不能把规范facet确认当作least确认。

最后，四边形的循环顶点已为 $0,h_p,e_E,h_q$，所以它是平行四边形当且仅当 $e_E=h_p+h_q$。在 $p,q$ 评价这一等式给 $a=b=0$，反向由公式立即成立，完成全部等价。这里的质量proper只给 $0\le u(\Pi_Ex)\le u(x)$（$x\in C$），没有给 $\Pi_Ex\in C$。它因而不产生正滤子、事件更新或可调用量子操作。证毕。

只有在另行加入有限整个纯集的原全称 $\mathrm B$ 时，VII97.4才保证每个不同纯对都是实际边，且每条边就是该对的整个二态球，局部对径为另一端点。按这个已证对应，VI90.10的全部接触准确成为(VII99.13)对每条边成立，亦即这些指定投影全正；VI90.8的整个二态球逐效应延拓仍按它自己的量词消费。本章未从有限 $\mathrm B+\mathrm{Z0}$ 推出所有 $a=b=0$，因而未证明其一般接触或单纯形结论。

### 99.4 每个非接触纯对的一张局部facet尺排除全部延拓

**定理 99.4（指定局部proper效应的全延拓障碍）。** 在定义VII99.1下，任取有序不同原纯对 $p,q\in P$ 满足 $q\notin D_p$；不要求 $[p,q]$ 是边。令

$$
F=D_p,\qquad M=\max_{x\in F}h_q(x),\qquad
\ell_{p,q}=\frac{h_q|_F}{M}.
\tag{VII99.17}
$$

这里 $[0,1]_{\operatorname{aff}(F)}$ 指 $F$ 上全部实仿射函数中满足 $0\le\ell(x)\le1$ 对每个 $x\in F$ 成立者；零一界只在 $F$ 上要求。则 $0<M<1$，$\ell_{p,q}\in[0,1]_{\operatorname{aff}(F)}$ 是指定的局部proper效应，而

$$
\nexists f\in[0,u]:\quad f|_F=\ell_{p,q}.
\tag{VII99.18}
$$

更准确地，其全部实线性延拓恰为

$$
f=\frac{h_q}{M}+\mu h_p,\qquad \mu\in\mathbb R,
\tag{VII99.19}
$$

而没有任何一个同时满足原 $f\ge0$ 及 $f\le u$。全局仿射延拓到 $K$ 也同样被排除，因为 $\operatorname{aff}K=\{u=1\}$，其仿射函数唯一齐次线性延伸到 $V$。

证明。固定 $k_0\in K$，有 $V=\mathbb Rk_0\oplus\ker u$。$\operatorname{aff}K$ 上的仿射式 $c+L(x-k_0)$ 唯一对应 $V$ 上的线性式 $f(tk_0+w)=tc+L(w)$，所以全局仿射延拓与线性延拓的上述对应保持同一原单位。

不同的 $p,q$ 对应不同facets，所以 $F\not\subseteq D_q$，$h_q$ 在 $F$ 上不恒零，得到 $M>0$。$h_q$ 在整个 $K$ 只在 $q$ 达到一，且 $q\notin F$；由 $F$ 紧知 $M<1$。非负性与最大值定义给局部零一界，并在某个 $F$ 的顶点达到一。

$F$ 为facet，$\dim\operatorname{span}F=m$，故其消灭子是一维且由 $h_p$ 张成。两个延拓的差消灭 $F$，因此(VII99.19)穷尽全部实线性延拓。不同facets又给一个原顶点 $r\in D_q\setminus D_p$。若这样的 $f$ 在整个原锥非负，则

$$
f(r)=\mu h_p(r)\ge0,\qquad h_p(r)>0,
\quad\Longrightarrow\quad\mu\ge0.
\tag{VII99.20}
$$

但在同一个原纯点 $q$ 上随即有

$$
f(q)=\frac1M+\mu T_{pq}>1=u(q),
\tag{VII99.21}
$$

矛盾。这排除了全部延拓，不只是自然猜测 $h_q/M$ 的失败。$m=0$ 没有不同纯对，$m=1$ 的两个不同纯点互相接触，所以这两支都没有符合前件的非接触对；$p=q$ 从未在本定理量词内。

这是 $F=D_p$ 上的一张局部facet效应障碍。除非另有对应证明 $F$ 是VI90.8所量化的某个整个二态球，否则不能把(VII99.18)认作该球的延拓反例，更不能由它断言一般 $\mathrm B+\mathrm{Z0}$ 已失败。即使 $[p,q]$ 本身是边，这个 $F=D_p$ 也不是自动等于 $[p,q]$。证毕。

### 99.5 同一个有理七边形中的非正分裂和不可延拓尺

**命题 99.5（原载体上的非空障碍实例）。** 使用VII97.6的整个七点 $p_i=(1,v_i)$、原锥 $C$、单位 $u(t,x,y)=t$ 及整个原效应区间。该载体已满足全混态 $\mathrm{Z0}$。对实际边 $E=[p_0,p_1]$，有

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
\tag{VII99.22}
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
\tag{VII99.23}
$$

同一个有序非接触对 $p=p_0,q=p_1$ 的facet为 $F=D_{p_0}=[p_3,p_4]$，其(VII99.17)效应满足

$$
M=\frac{28}{87},\qquad
\ell_{p_0,p_1}(p_3)=1,\quad \ell_{p_0,p_1}(p_4)=0,
\tag{VII99.24}
$$

且没有原 proper 延拓。此处 $F$ 的确是 $p_3,p_4$ 的整个最小面，是一维整球；故这一特定facet障碍也给出该整个线段上的局部端点尺不可延拓，但该载体没有全称 $\mathrm B$。

证明。VII97.14—97.15的第 $3,4$ 行分别给 $h_0=s_3/152$、$h_1=s_4/174$，正是(VII99.22)的齐次式。$D_{p_0}=[p_3,p_4]$、$D_{p_1}=[p_4,p_5]$ 给 $E^\#=\{p_4\}$。代入(VII99.4)并合并系数得到 $e_E$，而第 $0$ 行给 $h_4=(20t-2x-y)/42$，所以补效应也符合(VII99.7)。逐个代入VII97.11的七个坐标得到表中全部值，未更换基或归一超平面。$h_0(p_5)=7/19$、$h_1(p_5)=0$，代入(VII99.12)给(VII99.23)。两个坐标中第二个为负，(VII99.14)即排除其属于原锥，尽管总质量为正且由proper效应读出。

这也实际区分了两种比较：$e_E\in F_{p_0}$，从而

$$
T_{p_0}(p_5)\le\frac4{21}<\frac7{19}=T_{p_0p_5}.
\tag{VII99.25}
$$

本式只使用下包络的定义，没有将该上界冒称其精确值。

在 $F$ 的两端，$h_1(p_3)=56/174=28/87$、$h_1(p_4)=0$，所以最大值和局部效应为(VII99.24)。任意全局线性延拓为 $f=(87/28)h_1+\mu h_0$。在同一个 $p_5\in D_{p_1}\setminus D_{p_0}$，非负性迫使 $\mu\ge0$；但 $f(p_1)=87/28+(15/19)\mu>1$，证明全部proper延拓不存在。因为 $[p_3,p_4]$ 是实际边，包含它两端的整个最小面恰是该边；局部 $\ell$ 是它唯一的端点零一仿射尺，故上述球对应在这一实例中明确成立。

另一方面，VII97.6已给 $H(p_0,p_2)=K$，整个七边形不是整欧氏球，故全称 $\mathrm B$ 失败。因此这个实例同时实现本章一般有限 $\mathrm{Z0}$ 域内的严格外部slack、proper总质量、指定分裂非正及局部尺全延拓失败，仍不是VI89.12的 $\mathrm B+\mathrm{Z0}$ 反例。证毕。

### 99.6 数学归属和原消费者的条件边界

**约定 99.6（复用与尚存的桥）。** VII99.2—99.4的边四边形及 $\Delta$ 公式、沿原补面张成的指定投影正性充要条件、以及 $\ell_{p,q}$ 的全部延拓障碍采用 `repo-derived` 归属。它们由VII97.2—97.5的既有完整facet配对、反序对合及规范slack推导；VII99.5直接使用VII97.6的原七边形，不另主张新载体。证明内的有限维支撑／分离、facet法向生成对偶锥、面上极值及二维线性代数是成熟步骤（凸分析来源沿用VII98.6所引 Rockafellar，*Convex Analysis*，§11、§18），不将它们分别计作新定理。

[FinitePureSimplex](../../../Blueprint/D5/S3/Quantum/Foundation/FinitePureSimplex.md)的 `zero_gluing_iff_simplex` 要求整个纯点坐标核维数至多一，`zero_kernel_least_confirmation` 要求该核为零；[WeightedRelationConfirmation](../../../Blueprint/D5/S3/Quantum/Foundation/WeightedRelationConfirmation.md)的加权精确确认值也在完整一关系域内。它们不供应本章任意关系零度的边、投影及facet延拓公式；本章亦不重证这些既有支路。VI90.8—90.10的原全效应限制／接触接口是本章的既有消费者，只有已证的整个面对应才能接入。

Dobbins，*Antiprismless, or: Reducing Combinatorial Equivalence to Projective Equivalence in Realizability Problems for Polytopes*，[arXiv:1307.0071v3 §3 Theorem 3.2、Lemma 3.3、Theorem 3.9](https://arxiv.org/html/1307.0071v3)讨论balanced pair、antiprism和interval polytope的组合实现及存在性边界；这些结果不是(VII99.4)—(VII99.24)在此原锥和原单位上的数值公式或正性、延拓判据。本章只确定每条实际边的上述二维效应面，不主张原 $[0,u]$ 的全部面或全部极端效应分类。该有限来源对应不主张全球原创、文献穷尽或一般开放状态认证。

VI99.7的全实ROG、任意共同支撑维数及余维的 $\mathrm G_2\Longleftrightarrow\mathrm{Z0}\Longleftrightarrow S$ 闭合按其完整ROG表示前件复用；裸有限 $\mathrm{Z0}$ 没有在本章取得该表示。有限 $\mathrm B+\mathrm{Z0}$ 一般域仍须证明每条原边的 $a=b=0$，才能沿VII97.4及VI90.10完成全部接触；VII98.5的临界等号、一般VI89.12和一般有限 $\mathrm B+\mathrm{Z0}$ 的单纯形问题均未由本章解决。指定 $\Pi_E$ 的正性也不是VI90.8所要求的任意整球逐效应延拓的无条件替代。

复型与Born、指定复合、同事件CP和仪器、更新、实际来源及物理时间仍保留VI89.7—89.10及VII98.8—98.9的全部原合同。[原生来源续卷VII](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md)第33—34章的指定 $\mathrm H_8,\mathrm H_3$ 联合供应和第35章的特定候选障碍按既有范围复用；它们不是本章待补缺口。原全字精确细零关系、细Born、实际操作与时间则仍未由这些几何效应供应。以上是明确模型条件内的纸面推导，不声明Lean核验或经验实现。

## 追加锚（本行以下为增补区）
