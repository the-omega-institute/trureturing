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
