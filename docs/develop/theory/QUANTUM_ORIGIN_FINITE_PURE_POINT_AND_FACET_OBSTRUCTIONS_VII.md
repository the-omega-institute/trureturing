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
