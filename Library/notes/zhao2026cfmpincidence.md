---
bibkey: zhao2026cfmpincidence
authors: Xinrong Zhao
year: 2026
title: Combinatorial Ricci Flows and Hyperbolic Structures on a Class of Compact 3-Manifolds with Boundary
doi: 10.48550/arXiv.2601.15174
url: https://arxiv.org/html/2601.15174v2
claim: The general valence-nine theorem and cube monotonicity are existing results; the accompanying theory proves explicitly restricted lower-valence incidence criteria without claiming the full CFMP conjecture.
strata_touched: []
license: citation-only
triage: anchor
---

# CFMP geometry and incidence-dependent length barriers

## Verified locator

- DOI: 10.48550/arXiv.2601.15174
- URL: https://arxiv.org/html/2601.15174v2

## Primary-source scope

1. Francois Costantino, Roberto Frigerio, Bruno Martelli and Carlo Petronio,
   *Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn filling*,
   Commentarii Mathematici Helvetici 82 (2007), 903-934.
   https://arxiv.org/abs/math/0402339
   https://arxiv.org/pdf/math/0402339
   The retrieved v2 contains Conjecture 0.8: every ideal triangulation with
   edge valences at least six is realized by hyperbolic partially truncated
   tetrahedra. The prescribed triangulation, not just some triangulation of
   the same manifold, is the object to be realized. The text distinguishes
   already-proved hyperbolicity of the underlying manifold from this stronger
   realization claim. Equal-valence regular realizations are already known.

2. Ke Feng, Huabin Ge and Bobo Hua, *Combinatorial Ricci flows and the
   hyperbolization of a class of compact 3-manifolds*, Geometry & Topology
   26 (2022), 1349-1384, DOI 10.2140/gt.2022.26.1349.
   https://arxiv.org/abs/2009.03731
   https://arxiv.org/pdf/2009.03731
   Theorems 1.5, 1.6 and 3.9 together with the co-volume/flow arguments in
   Sections 4-5 give the relevant inputs. The general threshold is ten.
   Theorem 1.6 gives convergence from every positive initial
   vector once a genuine zero-curvature metric exists. Theorem 3.9 gives a
   larger genuine-metric cube up to arccosh(3). Our smaller arccosh(2) cube is
   rechecked directly by the displayed cosine inequalities and is not claimed
   as a new discovery.

3. Xinrong Zhao, the present bibkey, arXiv:2601.15174v2, February 5, 2026.
   https://arxiv.org/html/2601.15174v2
   Theorems 1.1/1.5 and 2.12, Lemmas 2.2 and 3.4, and the
   opposite-edge/adjacent-face estimates of Sections 4-6 give the relevant
   inputs. The general threshold is nine. No peer-reviewed publication status
   is asserted here. Its cube monotonicity already controls the four
   adjacent variables. The accompanying theory proves that elementary
   derivative sign explicitly, rather than borrowing the degree-nine theorem
   for a triangulation containing degree-eight edges.

4. Feng Luo and Tian Yang, *Volume and rigidity of hyperbolic polyhedral
   3-manifolds*, arXiv:1404.5365v2.
   https://arxiv.org/abs/1404.5365
   The tetrahedron length characterization, Schlaefli/co-volume formula and
   global rigidity are also explicitly stated
   with original locators in the two flow papers. We do not claim a complete
   independent audit of every proof in Luo-Yang.

5. Ke Feng, Huabin Ge and Yunpeng Meng, *Hyperbolization and geometric
   decomposition of a class of 3-manifolds*, arXiv:2503.07421v1.
   https://arxiv.org/abs/2503.07421
   https://arxiv.org/html/2503.07421v1
   Its mixed-boundary result requires proper gluing, ideal-edge valence at
   least six and hyper-ideal-edge valence at least eleven. It does not prove
   the pure hyper-ideal valence-eight cases considered here. The primary
   theorem statements imply the stated comparison boundary.

## Exact mathematical delta

The new owner is `docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md`.
It fixes actual global edge variables and counts local occurrences, allowing
self-identifications. For caps b_e in (1,2], the local dihedral cosine bound
uses the actual four adjacent cap values and the opposite lower endpoint one.
If the resulting angular sum on every upper face is strictly greater than
2pi, a uniformly positive lower face can be chosen. The full length box is
proved to lie in the nondegenerate geometric domain. A genuine co-volume
minimum in that box is forced into its interior, producing a zero-curvature
metric of the prescribed triangulation. This proof does not assume existence
as an input or treat an arbitrary degenerate limiting vector as a geometry.

The first explicit application allows degree-eight edges and degrees at
least twelve. Caps are 2 and 8/5 in cosh-length. An eight-edge occurrence
with at least three high adjacent edges has squared cosine at most 833/1677,
strictly below 1/2. A high edge has cosine at most 37/43, strictly below
sqrt(3)/2. Thus all required angular sums are strictly inward.
A second application lets six of the eight occurrences have four high
neighbors and leaves the other two unrestricted. Its exact triple-angle
certificate uses cos(3 acos(103/153))=-2862473/3581577 < -7/9.
These conditions are sufficient, not equivalent to min valence eight.
The proof method is classical convex-variational geometry plus the displayed
incidence-dependent estimate. No mathematical first-discovery claim is made
without a further priority review.

## Relation to the contextual spacetime model

Read `CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md`, especially Sections 2-4, at dev
9740a07f66b6f1fe7b9fe634c88c1c9d115e22ff. Its common-world condition requires
repeated references to the same variable to use one shared value; joint
responses are not automatically a Cartesian product of local responses.
Here that means one length per global edge, correct opposite/adjacent roles,
and incidence sums with multiplicity. Independent box corners are only
conservative bounds, not falsely asserted actual global states.
This methodological connection supplies no automatic curvature estimate,
physical spacetime identification or proof of geometric realization.

## Literature and scope boundary

The cited primary sources establish the general valence-ten and valence-nine
results, but do not supply a proof or counterexample for all-eight or all-six
triangulations. No secondary summary is used as a mathematical source. The
source set is not an exhaustive priority review.

The theory volume contains ordinary proofs and source provenance. The
unrestricted degree-eight target and original CFMP conjecture remain open.
The restricted theorem has no numerical hypothesis left unproved; its
additional hypotheses are the explicit incidence rules.

## Second increment: exact identification constraints and nonvacuous families

Section 5 retains the actual equality of a local edge with its opposite when
both represent the same global edge. The upper-face calculation must then
use the SAME cap for both, not independently set the opposite one to its
lower endpoint. With caps two for degrees eight/nine and 19/10 for degrees
at least ten, realization follows if each degree-eight edge has at least six
opposite-identified occurrences, and each degree-nine edge has at least two.
The strict angular sums are certified by exact triple/seven-angle polynomial
identities. This equality constraint need not survive passage to a covering
triangulation, so no such cover-stability claim is made.

Section 6 allows every edge degree at least six, provided each occurrence
of an edge below degree twenty has four adjacent edges of degree at least
twenty. Caps two and 61/50 give exact cosine bounds 2471/4971<1/2 and
389/411<cos(pi/10), respectively. There is no bound on the dimension of the
length space or the tetrahedron count. The length space dimension is the
actual number of GLOBAL edges, and the manifolds are three-dimensional.

Section 7 gives two fully specified actual face-pairings, with odd gluing
permutations, no reversal of an edge, and closed orientable vertex links:
four tetrahedra with edge degrees (8,16) and one genus-three boundary; six
tetrahedra with edge degrees (6,6,24) and one genus-four boundary. Their local
color conditions are verified. Taking cyclic covers produces unbounded,
pairwise nonhomeomorphic families by Euler characteristic. This is a proof
of nonvacuity and unbounded scope, not a claim that the four-tetrahedron
example was previously unknown: CFMP itself reports experimental checks of
all triangulations with at most four tetrahedra. The equal-valence regular
construction is also old and explicitly credited.

Section 8 proves a limitation of the independent-opposite-endpoint cap test.
At a global minimum cap b, every local cosine lower bound is at least
f(b)=(2b^3+b^2+1)/(2b^3+3b^2-1)>=7/9. Therefore the Section 3 certificate
cannot succeed on ANY all-eight or all-nine triangulation, even with
nonuniform caps in (1,2]. Such constant-valence triangulations are nevertheless
geometric by the classical regular-tetrahedron construction. This is a
counterexample to a proposed proof mechanism, not to CFMP or to all possible
coupled barriers. It justifies keeping true equalities and seeking additional
joint constraints instead of tuning the same incomplete cap scheme.

Section 9 uses the exact remaining variational obligation. In a minimum-eight
triangulation the assignment 2pi/d(e) is a strict angle structure. Luo-Yang
Theorems 1.4 and 6.3 already give a unique maximum-volume angle structure and
a positive GENERALIZED length realization. Its only nongeometric tetrahedra
   have angles (0,0,0,0,pi,pi), with the pi angles opposite. Excluding
these flat tetrahedra in the maximum is the missing full-eight existence
step; positive angle feasibility or energy monotonicity does not exclude them.

## Finite verification boundary

The derivative numerator identity, seven displayed cosine evaluations, the
squared three-high bound, all exact triple/seven-angle inequalities, and the
rational no-go factorization have exact finite checks.
Numerical radian margins are display-only; the strict signs have rational
polynomial certificates. A two-variable floating-point root for the
four-tetrahedron example is a diagnostic only; it is not an existence proof
or a certified geometric root.

Three face-pairing packets satisfy the finite checks. Two are the stated (8,16) and
(6,6,24) examples. The third is a second (8,16) packet with an opposite-pair
low edge, checking the Section 5 condition. Exact union-find and an independent
graph-component calculation agree on complete face pairing, orientation parity,
connectedness, oriented-edge reversal, circular normal links, vertex-link Euler
characteristics and all incidence hypotheses. These finite calculations do not
prove the unrestricted conjecture.

No tests of finitely many pairings establish the unrestricted conjecture.
The mathematical theorems quantify over all actual triangulations satisfying
the displayed incidence rules and use the complete analytical proof. Their
priority has not been established by an exhaustive literature review.

## Third increment: nineteen is sharp for the specified two-cap scheme

Section 10 strengthens the isolated-low-edge result from threshold twenty to
nineteen, with exact caps 2 and 153/125. The low cosine is
31193/62443<1/2. The high cosine is 243/257<cos(2pi/19); the proof uses
pi<22/7 and a sixth-order Taylor lower bound at 44/133, whose rational
margin is 15920790096478/64011128373838485. It has no unproved numerical
sign assumption. The previous six-tetrahedron example and all its cyclic
covers satisfy the strengthened rule.

The same section proves nineteen is the smallest threshold attainable by
that SPECIFIED uniform two-cap, independent-opposite-endpoint, per-occurrence
scheme. The scheme permits both low cap b and high cap c to vary in (1,2],
with c<=b. The low requirement forces c^2<3(b-1)/2. Differentiating
(sqrt(3(b-1)/2)-1)/b^2 proves its maximum occurs at b=2, so the best high
cosine is still greater than 47/50>cos(pi/9). Thus threshold eighteen or
smaller cannot satisfy the two simultaneous inequalities. This is a limitation
of that estimate, not a nonrealizability claim at degree eighteen and not
an exclusion of more detailed incidence, positive lower, or nonrectangular
barriers.

Exact finite checks cover the two new cosine values, the Taylor margin, the
derivative identity for the two-cap extremum, the positive-integral formula
for 22/7-pi, and the nineteen-neighbor criterion on the stated packets. These
checks supply no mathematical independence or kernel certification.

## Standard topology and the original face-pairing boundary interface

The generalized-triangulation and vertex-truncation facts below are existing
mathematics, not additional CFMP realization theorems. Primary locators are the
[Regina Handbook, Chapter 3](https://regina-normal.github.io/docs/triangulations.html),
[validity and vertex links](https://regina-normal.github.io/docs/tri-analysis.html#tri-basicprops),
and [truncating vertices](https://regina-normal.github.io/docs/tri-modification.html#tri-truncate).
The handbook allows faces of the same tetrahedron to be paired, describes
edge reversal as an invalid identification, and identifies vertex truncation
with replacement by real boundary components. The
[engine's three-dimensional triangulation interface](https://regina-normal.github.io/engine-docs/classregina_1_1Triangulation_3_013_01_4.html)
gives the corresponding validity and truncation contracts.

The following coordinate argument makes those standard facts explicit for the
actual original face pairing used by CFMP. It preserves occurrences, both
ordered ends and cap marking; it supplies the topology interface used in the
existing finite examples. It is a reuse argument, not a new theory result or
a Lean-certified theorem. References to Sections 1--4 and Proposition 1.1
refer to `docs/develop/theory/CFMP_ORIGINAL_LINK_INTERFACE.md`; Sections 5--11
below number this note's topology discussion. A sphere-link vertex is also
truncated in the displayed model, creating a sphere cap; identifying this
model with a supplied original manifold still requires its actual
triangulation realization.

## 5. 原始截断商与有限闭关系

沿用第 1 节的实际面配对，假设四面体集合 $T$ 有限。取 $\varepsilon=1/4$，在每个四面体使用闭截断单形

$$
K=\left\{z\in\mathbb R^4:\ z_i\ge0,\ \sum_i z_i=1,\ z_i\le3/4\right\}.
$$

令 $X=\coprod_{t\in T}K$。只有在 $z_f=0$ 时，面 $(t,f)$ 的实际配对才生成识别

$$
(t,z)\sim\left(u,P_{\sigma_{t,f}}z\right),\qquad
(P_\sigma z)_i=z_{\sigma^{-1}(i)}.
$$

记其等价闭包为 $R$，商空间为 $Q=X/R$，商映射为 $q$。所有商均使用这组实际面限制；不同出现和端口保留其原始身份。令

$$
U=\{(t,z)\in X:\ \exists v,\ z_v=3/4\},\qquad B=q(U).
$$

**命题 5.1（实际截断商的紧性与分离性）。** 对任意上述有限面配对，$R$ 是 $X\times X$ 的闭子集，$Q$ 紧且 Hausdorff，$q$ 是闭映射，$U$ 饱和且 $B$ 闭。此结论不要求边不反转。

证明。固定源四面体 $t$，以 $(u,\rho,Z)$ 为运输状态，其中 $u\in T$、$\rho\in\operatorname{Sym}(4)$、$Z\subseteq I$。初始状态为 $(t,\mathrm{id},\varnothing)$。在当前四面体 $u$ 选择面 $f$，配对至 $(u',g)$，更新为

$$
(u,\rho,Z)\longmapsto
\left(u',\sigma_{u,f}\circ\rho,\ Z\cup\{\rho^{-1}(f)\}\right).
$$

状态可达性仅记录原始面路径，不要求其零坐标条件已成立。实际关系的精确表达式是

$$
R((t,z),(u,w))\iff
\exists\rho,Z:\ (u,\rho,Z)\text{ 可达},\quad
\bigwedge_{i\in Z}z_i=0,\quad w=P_\rho z.
$$

实际识别路径逐步积累拉回源点的零坐标条件，得到正向蕴含。反向沿状态的见证路径行走，累积条件使每一步实际面识别合法。逆面限制本身也是生成识别，故此描述包含对称闭包，初始状态包含反身性。每个源四面体至多有 $|T|\cdot24\cdot16$ 个状态。固定标签、排列和零坐标集合时，右端条件定义闭集；有限并仍闭。

空间 $X$ 是有限个紧 Hausdorff 多面体的不交并。闭等价关系在紧 Hausdorff 空间上的商是紧 Hausdorff，且商映射闭：闭集的饱和是闭关系与该闭集乘 $X$ 的交集的紧投影，因此闭。这个闭商结论也可由商映射的紧纤维、适当映射的乘积和闭对角线判据得到。坐标排列保留“某坐标等于 $3/4$”，所以 $U$ 饱和；它是有限个闭 cap 面的并，$B$ 由闭商映射得到闭性。

## 6. 实际两端口圈与端点运输

固定一个实际全局边 $e$，令 $O_e$ 为其原始局部出现集合。每个出现恰有两个包含该边的面端口。记 $\tau$ 为同一出现内的端口交换，$J$ 为跨实际配对面的端口运输。二者都是端口集合上的无不动点对合；$J$ 的无不动点性来自原始面配对的无不动面条件。

**引理 6.1（保留环和重边的有向端口圈）。** 两对合生成的实际边分量有两个 $S=\tau\circ J$ 轨道，彼此由 $\tau$ 交换；每个轨道恰好经过 $O_e$ 中每次出现一次。

证明。将 $\tau$ 和 $J$ 看作端口上的两种颜色的完美匹配。一个连通分量是有限交替偶圈；允许两种匹配连接同一对端口。沿圈每次前进两步给出两个奇偶位置轨道，而每个 $\tau$ 配对包含一个奇位置和一个偶位置。实际边关系正是跨 $J$ 并在出现内切换端口生成的连通关系，因此所选分量对应整个 $O_e$。圈长度为 $2|O_e|$，每个两步轨道在每个出现取一个端口。一个出现的情形是两个匹配连接同一对端口，$S$ 有两个单点轨道；两个出现的情形保留两条平行面运输。证明不使用简单图假设。

选择一个轨道，按 $k\in\mathbb Z/m\mathbb Z$ 编号，其中 $m=|O_e|>0$。将该轨道中的端口称为出端口，其同出现的另一个端口称为入端口。跨第 $k$ 个出端口恰到达第 $k+1$ 个出现的入端口。

此后假设第 1 节的边不反转条件。命题 1.1 给出实际边上的两个有序端类。任意边路径可运输一个所选端点，故该端类到达每次出现；若同一端类在某次出现包含两个端点，就违反边不反转。选择其一 $\eta$，则每次出现 $o$ 有唯一端点 $v_o$ 属于 $\eta$；另一端点记为 $w_o$。实际面运输保留这一选择。即使两个端点具有相同的全局角点标签，也不能将这两个端类合并。

## 7. 横截面到圆盘的显式映射

在第 $k$ 次出现中，令 $a$ 为出端口遗漏顶点的坐标，$b$ 为入端口遗漏顶点的坐标。取 $\delta>0$，在闭三角形 $a,b\ge0$、$a+b\le\delta$ 上定义 $r=a+b$，并定义

$$
F_k(a,b)=
\begin{cases}
0,&r=0,\\
r\exp\!\left(2\pi i\dfrac{k+b/r}{m}\right),&r>0.
\end{cases}
$$

出端口面上 $a=0$，角参数为 $k+1$；配对目标的入端口面上 $b'=0$，角参数同为 $k+1$。最后一个出端口与第一个入端口也由指数的周期性一致。

**引理 7.1（实际扇商是圆盘）。** 将上述 $m$ 个闭三角形按实际相邻端口识别，其商由 $F_k$ 同胚到闭圆盘 $\overline D_\delta\subset\mathbb C$。对任意紧区间 $L$，保留第二坐标的同一映射给出实际扇乘区间的商到 $\overline D_\delta\times L$ 的同胚。

证明。$r>0$ 时公式连续；在原点，$|F_k(a,b)|=a+b$ 给出连续性，毋须角参数有极限。相同像先由范数给出相同 $r$，再由指数周期性给出

$$
\frac{k+b/r}{m}\equiv\frac{l+b'/r}{m}\pmod1.
$$

当 $k,l\in\{0,\ldots,m-1\}$ 且两个比值位于 $[0,1]$ 时，这恰好表示同一扇内相同点、相邻端口射线上的配对点，或首尾射线上的配对点。原点则沿连通端口圈全部识别。$m=1$ 时同一三角形的两条射线配对，$m=2$ 时两对相邻射线均须保留；上述纤维描述仍逐项成立。

每个非零圆盘点的方向可选择于一整圈内，再放入这 $m$ 个角区间之一，取 $b=rt$、$a=r(1-t)$ 即得原像。映射因此连续、满射且纤维恰为实际识别类。它从紧商到 Hausdorff 圆盘诱导连续双射，故为同胚。乘紧区间的陈述对整个紧源使用同一个连续映射和纤维论证得到，不预设商与乘积交换。

## 8. 原始边内部的实际邻域

固定实际边内部一点，选择第 6 节的端类及有向端口圈。令

$$
s=\frac{z_{v_o}}{1-r},\qquad
z_{v_o}=(1-r)s,\qquad z_{w_o}=(1-r)(1-s).
$$

在中心边 $r=0$ 上，截断条件给出 $1/4<s<3/4$。选取包含该点纵向参数于内部的闭区间 $[A,C]\subset(1/4,3/4)$，取 $\delta=1/16$，并以 $0\le r\le\delta$ 为横截面参数。上述两个端点坐标均大于 $\delta$，另外两个坐标至多为 $\delta$，故在同一原四面体内，两个大坐标唯一恢复该局部边出现。端点坐标严格小于 $3/4$，因此这些 patch 不碰 cap。

实际配对保留 $r,s$；仅两个横向面可能有零坐标，它们恰给出第 7 节的射线配对。由引理 7.1，整个闭 patch 的实际商经 $(F_k,s)$ 同胚到 $\overline D_\delta\times[A,C]$。闭 patch 是饱和的，其商到 $Q$ 的像也是紧到 Hausdorff 的连续单射，故上述同胚确实描述 $Q$ 的该子空间。

限制到 $r<\delta$、$A<s<C$。其完整原像在 $X$ 中相对开：这组严格不等式和两个端点坐标大于 $\delta$ 可在每个原四面体内直接表达。它仍饱和，因为实际面运输保留所选端点和纵向参数。按商拓扑定义，其像是 $Q$ 的开邻域，坐标目标为 $D_\delta\times(A,C)$，即实三维空间的开子集。

## 9. cap 顶点及其余四种局部情形

在原始有序端 $(t,v,w)$ 对应的 cap 顶点处，选择其实际端类，取

$$
u=3/4-z_{v_o},\qquad
z_{v_o}=3/4-u,\qquad z_{w_o}=1/4+u-r.
$$

令 $0\le u,r\le\delta=1/16$。则

$$
11/16\le z_{v_o}\le3/4,\qquad
3/16\le z_{w_o}\le5/16,\qquad
0\le a,b\le1/16.
$$

两个大坐标再次唯一恢复实际局部边出现，且还区分所选 cap 端点。只有两个横向面能提供识别；它们保留 $u,r$，恰给出实际扇的射线关系。唯一可能的 cap 坐标是 $v_o$，cap 条件等价于 $u=0$。

**命题 9.1（实际 cap 顶点的带标记半空间坐标）。** 上述闭 patch 商经 $(F_k,u)$ 同胚到 $\overline D_\delta\times[0,\delta]$。限制到 $r<\delta$、$u<\delta$ 得到 $Q$ 中的开邻域 $V$，其坐标目标为 $D_\delta\times[0,\delta)$，且

$$
(F,u)(V\cap B)=D_\delta\times\{0\}.
$$

证明。引理 7.1 给出闭 patch 的紧商同胚，闭 patch 饱和，故它同胚于 $Q$ 中的实际像。较小 patch 的完整原像可写成 $r<\delta$、$u<\delta$，连同已自动满足的两个大坐标严格下界；这些条件在原始 $K$ 中相对开。原始面限制保留这些条件，因此原像饱和，商像开。目标在 $\mathbb C\times[0,\infty)$ 中相对开；最后的标记等式直接来自唯一 cap 坐标及 $u=0$。

其余四种情形的坐标也可以直接写出。配对面上的切向坐标一律通过同一个实际 $\sigma$ 运输，法向坐标在两侧取相反符号。

| 情形 | 坐标与逆公式 | 局部目标 |
|---|---|---|
| 四面体内部 | 省去一个坐标，按总和为一恢复它 | 仿射三维空间的开集 |
| 配对面内部，$z_f=0$ | $h=z_f$，$y_i=z_i/(1-h)$；逆为 $z_f=h$、$z_i=(1-h)y_i$ | 切向开圆盘乘开法向区间 |
| cap 内部，$z_v=3/4$ | $u=3/4-z_v$，$y_i=z_i/(1/4+u)$；逆为 $z_v=3/4-u$、$z_i=(1/4+u)y_i$ | 切向开圆盘乘 $[0,\delta)$ |
| cap 侧边内部，$z_v=3/4,z_f=0$ | $u=3/4-z_v$、$h=z_f$、$t=z_w/(1/4+u-h)$；另一个顶点为 $c$ | 开切向区间乘开法向区间乘 $[0,\delta)$ |

最后一行的完整逆公式为

$$
z_v=3/4-u,\quad z_f=h,\quad
z_w=(1/4+u-h)t,\quad z_c=(1/4+u-h)(1-t).
$$

在配对目标侧取实际运输后的 $v,w,c$，并把 $h$ 的符号取反；合并两侧后，逆公式中的非负重心坐标使用 $|h|$。选择 $t$ 的闭区间 $I$ 严格位于 $(0,1)$，令 $\mu=\inf_{t\in I}\min(t,1-t)>0$，再选 $\delta\le1/16$ 满足 $\delta<(1/4-\delta)\mu$，则整个 patch 上 $z_w,z_c>\delta$。这个半径依赖所选点的切向正坐标余量；不对所有 cap 侧边中心强行使用同一个半径。只有 $f$ 能有零坐标，只有 $v$ 能达到 cap 上界。因此两侧除了 $h=0$ 的原面配对外没有额外识别，且 cap 恰为 $u=0$。

配对面内部同样先选取面内部的紧切向圆盘，再选法向半径，使另外三个坐标均严格大于该半径且小于 cap 上界。两侧紧半盒在 $h=0$ 上由实际运输相接；连续映射的纤维正好是该配对，由紧到 Hausdorff 获得闭盒同胚。取切向圆盘的内部和 $|h|<\delta$，其完整原像相对开且由唯一小面条件给出饱和性，因而得到商中的开邻域。即使两配对面属于同一原四面体，它们的小 patch 也由不同的唯一小坐标区分，互不重叠。cap 侧边取 $t\in\operatorname{int}I$、$|h|<\delta$、$u<\delta$，其饱和开原像给出对应的半空间开邻域。两个无配对的内部情形直接使用仿射或有理逆公式和严格坐标余量，cap 内部同样取切向圆盘的内部及 $u<\delta$。

## 10. 六种坐标的汇合与实际 cap 链接

**定理 10.1（由原始面配对构造的带边界三维拓扑流形）。** 有限原始面配对满足边不反转时，$Q$ 是紧三维拓扑流形，边界标记恰为 $B$。具体地，$Q\setminus B$ 的每点具有与实三维开集同胚的开邻域；$B$ 的每点具有与标准闭半空间的相对开集同胚的开邻域，且局部同胚将 $B$ 精确送到高度为零的平面。空 $T$ 给出空流形。

证明。$K$ 的点至多有两个零坐标，否则剩下的一个坐标等于一，违反截断上界；至多有一个 cap 坐标，否则坐标总和大于一。因此“零坐标数为零、一、二”和“有无 cap 坐标”恰好产生六种情形。第 8 节、第 9 节及其表格为它们逐一构造实际商的开邻域。没有 cap 的三种情形给出实三维开集，有 cap 的三种给出闭半空间的相对开集，并都保留高度零标记。命题 5.1 给出 Hausdorff 性和紧性。紧性选出有限个这样的图卡覆盖；每个图卡有可数基，有限并给出 $Q$ 的可数基。故满足拓扑流形的分离性和可数性条件。这些半空间图卡确定的流形边界为 $B$。

令 $L$ 为第 1 节同一原始角点三角形的实际链接商。每个原角点 $(t,v)$ 的三角形写为

$$
\Delta_v=\left\{\lambda:\lambda_v=0,\ \lambda_i\ge0,\ \sum_i\lambda_i=1\right\}.
$$

其边 $\lambda_f=0$ 按实际 $\sigma_{t,f}$ 配对，且只允许 $f\ne v$。

**命题 10.2（链接到实际边界 cap 的原代表对应）。** 对任意有限原始面配对，映射

$$
[t,v,\lambda]\longmapsto
\left[t,\frac34e_v+\frac14\lambda\right]
$$

给出 $L\cong B$。在定理 10.1 的边不反转条件下，这是原始链接与 $Q$ 的流形边界的同胚。

证明。cap 点具有唯一坐标等于 $3/4$，所以在识别前可由该坐标恢复 $v$，并将其余坐标乘四恢复 $\lambda$。该映射是有限不交并上到 $U$ 的同胚，且与实际坐标排列交换。对于 $f\ne v$，$\lambda_f=0$ 等价于目标点的 $z_f=0$；$f=v$ 不可能提供 cap 点的面识别。每一条从 cap 出发的实际识别路径始终留在 cap 中，逆映射因此逐步恢复链接识别路径。诱导映射的纤维精确，得到从紧链接商到 Hausdorff 子空间 $B$ 的连续双射，故为同胚。这里的链接商紧性仅需其源有限紧三角形并的连续商；没有预先假设链接是曲面。

## 11. 拓扑结论的适用范围

第 5–10 节给出同一原始面配对上的书面拓扑构造，使用有限闭关系、显式扇坐标和紧到 Hausdorff 的同胚判据。环、重边、同一四面体的不同配对面，以及两个端点具有相同全局角点标签的情形都保留原始出现身份。结论不要求可定向性、角结构或双曲度量，也没有文献原创性声明。

同一个原始流形 $N$ 的边界对应仍须连接其原始理想剖分的实际实现。若该实现已给出 $Q\cong N$，可通过边界不变性传递上述标记；若只给出内部或删点空间的同胚，还需 collar 或端部延拓论证。任意内部同胚不能直接宣称延拓到 cap。上述拓扑坐标也不提供共同六边长度或全局双曲能量的物理识别。

## 12. 实际三槽面映射的四坐标扩展

本节把第 1–10 节使用的四坐标排列直接连接到 `RawFacePairing` 的实际三槽数据。输入只是原始配对 $p$，不另要求调用者提供 $\sigma$ 或断言其与边槽相容。这里是有限排列及既有等价接口的普通应用，不提出新的通用数学定理或原创性主张。

原始数据的参考源码为 `D5/S3/Geometry/Hyperideal/EdgeStarTransitions.lean`，修订 `2a2c0ee5482b2fe7d2e988a5b39bf76d934372d9`，文件 SHA256 为 `bebd11bec484fbf269f9089b9dd88196e0aa4034c329297ef36c7175a0fcd976`。本节独立使用下面五字段数据及第 12.1 节的有限 incidence 表，不要求该模块已成为可导入的供应者：

```lean
facePair : Equiv.Perm (T × Fin 4)
faceMap : T × Fin 4 → Fin 3 ≃ Fin 3
pairInvolutive : facePair * facePair = 1
pairFixedFree : ∀ x, facePair x ≠ x
mapInverse : ∀ x n, faceMap (facePair x) (faceMap x n) = n
```

边编号依次为 $(01,02,03,23,13,12)$；面编号是省去的顶点 $f$。`faceMap x` 作用于 `faceEdge x.2` 的三个**边槽**，不能未经转换直接当作递增面顶点的排列。

### 12.1 原始边槽的对顶点坐标

令 $\nu_f(n)$ 为面 $f$ 中与边槽 $n$ 对应边相对的顶点。由原始 `faceEdge` 和 `edgeVertices` 两张表得到：

| 省去的顶点 $f$ | 边槽 0 的端点 | 边槽 1 的端点 | 边槽 2 的端点 | $(\nu_f(0),\nu_f(1),\nu_f(2))$ |
|---|---|---|---|---|
| 0 | $(2,3)$ | $(1,3)$ | $(1,2)$ | $(1,2,3)$ |
| 1 | $(0,2)$ | $(0,3)$ | $(2,3)$ | $(3,2,0)$ |
| 2 | $(0,1)$ | $(0,3)$ | $(1,3)$ | $(3,1,0)$ |
| 3 | $(0,1)$ | $(0,2)$ | $(1,2)$ | $(2,1,0)$ |

每行的三个顶点互不相同且均不等于 $f$。对任何 $v$，原始边槽的端点关系正好是

$$
v\in\operatorname{endpoints}(\operatorname{faceEdge}(f,n))
\quad\Longleftrightarrow\quad
\exists r\ne n:\ \nu_f(r)=v.
$$

这条有限表关系同时确定端点所属的原始边槽，保留原始四面体、面及槽身份。

### 12.2 从实际配对唯一得到 $\sigma$

令 $\chi_0$ 为三槽恒等排列，$\chi_f=(0\ 2)$ 对所有 $f\ne0$。用 `Equiv.finSuccEquiv' f` 把省去的顶点送到 `none`，并按递增顺序把其余顶点送到 `some n`；再用 $\chi_f$ 修正为上述原始边槽顺序。记此复合为

$$
F_f:\operatorname{Fin}4\simeq\operatorname{Option}(\operatorname{Fin}3),
\qquad
F_f=\operatorname{optionCongr}(\chi_f)\circ
\operatorname{finSuccEquiv}'(f).
$$

因此 $F_f(f)=\mathrm{none}$ 且 $\nu_f(n)=F_f^{-1}(\mathrm{some}\ n)$。若 $x=(t,f)$、$p.\mathrm{facePair}(x)=(t',g)$、$m_x=p.\mathrm{faceMap}(x)$，定义

$$
\sigma_x=F_g^{-1}\circ\operatorname{optionCongr}(m_x)\circ F_f.
$$

相应的局部 Lean 定义为：

```lean
let chi : Fin 4 → Equiv.Perm (Fin 3) :=
  fun f => if f = 0 then 1 else Equiv.swap 0 2
let frame : Fin 4 → (Fin 4 ≃ Option (Fin 3)) :=
  fun f => (Equiv.finSuccEquiv' f).trans (Equiv.optionCongr (chi f))
let vertex : Fin 4 → Fin 3 → Fin 4 :=
  fun f n => (frame f).symm (some n)
let sigma : T × Fin 4 → Equiv.Perm (Fin 4) :=
  fun x => (frame x.2).trans
    ((Equiv.optionCongr (p.faceMap x)).trans
      (frame (p.facePair x).2).symm)
```

既有等价的正反复合恒等式立即给出

$$
\sigma_x(f)=g,\qquad
\sigma_x(\nu_f(n))=\nu_g(m_x(n)).
$$

`pairInvolutive` 给出 $p.\mathrm{facePair}(p.\mathrm{facePair}(x))=x$。对 `mapInverse` 在 $m_x^{-1}(n)$ 处代入，得到

$$
m_{p.\mathrm{facePair}(x)}=m_x^{-1}.
$$

代回定义即得 $\sigma_{p.\mathrm{facePair}(x)}=\sigma_x^{-1}$。此处不需要 `pairFixedFree`，也不需要 $T$ 有限或非空。

结合第 12.1 节的端点关系和 $m_x$ 的单射性，得到实际边槽的双向相容性：

$$
v\in\operatorname{endpoints}(\operatorname{faceEdge}(f,n))
\quad\Longleftrightarrow\quad
\sigma_x(v)\in
\operatorname{endpoints}(\operatorname{faceEdge}(g,m_x(n))).
$$

因此端点的运输与 `RawFacePairing.edgeStep` 使用的是同一实际边槽配对。

### 12.3 递增顶点索引不能直接代替原始槽索引

取两个不同原始四面体，将其省去顶点 1 的面配对，且 `faceMap` 交换边槽 0 和 1。这两个槽的原始边分别是 $02$ 和 $03$。

若错误地把面顶点的递增排列 $(0,2,3)$ 当作边槽排列，交换槽 0 和 1 会交换顶点 0 与 2，因而把边 $02$ 送回边 $02$，没有送到规定的目标边 $03$。正确的对顶点次序是 $(3,2,0)$；同一槽交换应交换顶点 3 与 2、固定顶点 0，恰把 $02$ 送到 $03$。这是原始配对上的具体索引反例，并非来自全局边标签的退化。

### 12.4 在实际截断载体上的运输

使用第 1 节的同一截断载体

$$
K=\left\{z:\operatorname{Fin}4\to\mathbb R\ \middle|
\bigl(\forall i,\ 0\le z_i\le3/4\bigr)\land\sum_i z_i=1\right\}.
$$

由实际配对导出的局部移动为

$$
P_x(z)_i=z_{\sigma_x^{-1}(i)}.
$$

每个目标坐标的非负性和截断上界由相应源坐标继承。既有 `Equiv.sum_comp` 用于 $\sigma_x^{-1}$ 给出

$$
\sum_iP_x(z)_i=\sum_i z_i=1,
$$

所以 $P_x$ 确实把 $K$ 送入 $K$。由逆相容性还有 $P_{p.\mathrm{facePair}(x)}\circ P_x=\mathrm{id}_K$。对任何原始坐标 $v$，

$$
P_x(z)_{\sigma_x(v)}=z_v.
$$

特别地，省去顶点 $f$ 的原始面被送到配对面 $g$，且有精确等式及零坐标等价

$$
P_x(z)_g=z_f,\qquad
z_f=0\ \Longleftrightarrow\ P_x(z)_g=0.
$$

cap 条件同样保留：

$$
\bigl(\exists v,\ z_v=3/4\bigr)
\quad\Longleftrightarrow\quad
\bigl(\exists i,\ P_x(z)_i=3/4\bigr).
$$

正向见证为 $i=\sigma_x(v)$，反向见证为 $v=\sigma_x^{-1}(i)$。这给出原始截断坐标上的运输，而不是任意外加的 cap 标记。第 8–10 节的配对面、原始边和 cap 公式须使用这一导出的 $\sigma_x$。

### 12.5 来源、复用与核验范围

上述扩展只使用原始两张有限表、`RawFacePairing` 的逆相容字段和既有 `Equiv` 接口。Mathlib 修订为 `db584cd6d46c92f209a44c0f1c829460d327499d`；直接复用 `Mathlib/Logic/Equiv/Fin/Basic.lean` 中的 `Equiv.finSuccEquiv'`，`Mathlib/Logic/Equiv/Option.lean` 中的 `Equiv.optionCongr`，以及 `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` 中由 `Equiv.prod_comp` 生成的 `Equiv.sum_comp`。其加法接口是

```lean
Equiv.sum_comp (e : ι ≃ κ) (g : κ → M) :
  (∑ i, g (e i)) = ∑ i, g i
```

其中两端索引类型有限，$M$ 为加法交换幺半群。本节给出这些既有等价与有限重排的参数对应。

本节给出书面坐标对应，尚未提供其经 Lean kernel 核验的应用。实际有序端点关系、端点不反转条件、商拓扑以及边和 cap 图卡仍需连接到原始配对上的证明项。有限坐标适配不替代这些拓扑义务，也不提供原始流形 $N$ 的端部延拓。

## 13. 实际识别纤维与有界面路径

本节沿用第 5 节的有限 $T$、截断载体 $K$ 和实际面限制，并使用第 12 节从原始三槽数据导出的 $\sigma$。记 $n=|T|$。下面的界不要求可定向性、角结构或双曲度量；除最后的改进外，也不要求边不反转。

### 13.1 零坐标数区分识别纤维

坐标排列保持零坐标数。截断条件保证 $K$ 中的点至多有两个零坐标：若至少三个坐标为零，则剩余坐标为一，与 $z_i\le3/4$ 矛盾。因此实际关系的每个等价类始终处于同一个零坐标层。

**命题 13.1（实际纤维的有限上界）。** 对任意 $x=(t,z)\in X$，其实际识别类 $[x]_R=q^{-1}(q(x))$ 满足：

| 源点的零坐标数 | 实际识别类的基数上界 |
|---|---|
| 0 | 1 |
| 1 | 2 |
| 2，两个非零坐标相等 | $6n$ |
| 2，两个非零坐标不等 | $12n$ |

在边不反转条件下，最后一行也改进为 $6n$。

证明。没有零坐标时没有合法的面移动，等价类是单点。只有一个零坐标 $f$ 时，唯一合法移动是跨面 $(t,f)$ 的配对；目标的唯一零坐标是配对面 $g$，所以目标的唯一合法移动就是逆配对。第 12.2 节的逆相容性使它回到原点。这给出至多两点，且允许配对面属于同一四面体。

有两个零坐标时，其余两个坐标为正，之和为一。实际移动只排列原来的坐标值，不改变它们。在每个目标四面体中，两个非零坐标相等时只需选择它们所在的无序顶点对，共 $\binom42=6$ 种；不等时还须选择两种赋值方向，共 $12$ 种。因此所有可达点分别落在至多 $6n$ 或 $12n$ 个实际点中。这里不把不同四面体的出现合并，也不假设所有候选点都可达。

若边不反转，固定源边的一个端点并沿实际面路径运输。同一个目标局部边出现上的端点像是唯一的：两条路径若把它送到相反端点，先走第一条路径，再逆走第二条路径，就产生返回源出现却交换两个端点的实际路径，违反不反转条件。故每个目标局部边出现至多产生一个可达坐标点；全部出现至多 $6n$ 个。非零坐标相等时，该计数改进已经由坐标值本身给出，不需要不反转。

### 13.2 每个识别都有短的实际见证路径

原始面限制在实际载体上是可逆的，逆移动仍是原始面限制。因此 $R$ 的任意识别都有有限合法面路径见证，包括长度零的路径。

**命题 13.2（有界实际路径）。** 若 $xRy$，则存在从 $x$ 到 $y$ 的合法原始面路径，其长度不超过 $|[x]_R|-1$。从而任意实际识别都有长度至多 $12n-1$ 的面路径；在边不反转条件下，统一界可改为 $6n-1$。这两个统一界仅在给定 $x\in X$ 时使用，此时 $n\ge1$。没有零坐标时可取长度零，只有一个零坐标时可取长度至多一。

证明。取一条长度最短的合法面路径。若其顶点序列重复同一个实际点，可删除两次到达该点之间的整段路径。删除前后接合处是完全相同的带四面体标签的坐标点，故保留的后半段每个原始零坐标条件仍成立，终点也不变。这与最短性矛盾。因此最短路径有 $L+1$ 个互异实际点，全部位于 $[x]_R$ 中，给出 $L+1\le|[x]_R|$。结合命题 13.1 即得各界。

删环保留实际面移动本身。它不依赖简单图，不把平行面移动合并，也不把两个不同出现因全局标签相同而视作重复点。

### 13.3 以有限面字重新表达闭关系

命题 13.2 给出第 5 节有限状态证明之外的直接闭性表达。取 $N=12n-1$。对每个源四面体 $t$ 和每个长度 $L\le N$ 的面字 $(f_0,\ldots,f_{L-1})$，只按原始配对计算标签序列 $t_j$ 及累积排列 $\rho_j$：

$$
t_0=t,\qquad \rho_0=\mathrm{id},\qquad
(t_{j+1},g_j)=p.\mathrm{facePair}(t_j,f_j),\qquad
\rho_{j+1}=\sigma_{t_j,f_j}\circ\rho_j.
$$

该面字在源点 $z$ 上合法，当且仅当

$$
z_{\rho_j^{-1}(f_j)}=0\qquad(0\le j<L).
$$

故它的实际识别图为

$$
\Gamma_{t,(f_j)}=
\left\{\bigl((t,z),(t_L,P_{\rho_L}z)\bigr):
 z\in K,\quad z_{\rho_j^{-1}(f_j)}=0\ (j<L)\right\}.
$$

源条件是 $K$ 中有限个闭坐标超平面的交。坐标排列连续，因而 $\Gamma_{t,(f_j)}$ 是该紧闭源的连续像，在 Hausdorff 空间 $X\times X$ 中闭。标签和面字有限，命题 13.2 恰给出

$$
R=\bigcup_{t\in T}\ \bigcup_{L=0}^{N}\ \bigcup_{(f_j)\in(\operatorname{Fin}4)^L}
\Gamma_{t,(f_j)}.
$$

于是 $R$ 是有限闭集的并。空 $T$ 时 $X$ 与 $R$ 都为空，闭性直接成立，不使用负的路径长度上界。在边不反转条件下，可用 $N=6n-1$ 得到同样的表达。

该表达将每一步原始零坐标条件拉回同一个源点，并保留累积排列及目标四面体。只检查最终排列而遗漏中间零坐标条件，不能判定一条面字是否合法。第 5 节的 $(u,\rho,Z)$ 可达状态表达与这里的有界实际面字表达描述同一个关系；后者给出路径长度界，前者通过至多 $24n\cdot16$ 个有限状态压缩面字的枚举。

这些是原始配对上的书面有限组合与拓扑论证，尚未给出经 Lean kernel 核验的实际应用。纤维有限或面字有界本身不提供第 8–10 节的局部图卡、原始流形 $N$ 的实现或端部延拓。

## 14. 有限运输群与闭门条件的统一商定理

第 5 节的有限状态证明可推广到不必紧的载体。关键条件是运输排列来自同一个有限群，且每一个原始识别只在闭的源条件上生效。下面明确保留生成关系的等价闭包，并由它推出统一条件；统一条件不作为调用者的额外假设。

### 14.1 对象与统一条件

令 $T$、$J$ 为有限集合，$T$ 带离散拓扑；令 $Y$ 为 Hausdorff 空间，有限群 $\Gamma$ 通过同胚 $P_g:Y\to Y$ 作用，满足

$$
P_1=\mathrm{id},\qquad P_hP_g=P_{hg}.
$$

每个 $j\in J$ 指定源标签 $s_j$、目标标签 $t_j$、运输元素 $g_j\in\Gamma$ 和闭集 $D_j\subseteq Y$。在 $X=T\times Y$ 上，以

$$
(s_j,y)\longrightarrow(t_j,P_{g_j}y),\qquad y\in D_j
$$

为实际生成识别，令 $R$ 为这组识别的等价闭包，$Q=X/R$，$q:X\to Q$ 为实际商映射。不要求生成识别本身对称，也不要求各个 $D_j$ 在群作用下不变。

对 $Z\subseteq\Gamma\times J$，定义闭的源条件集

$$
A_Z=\bigcap_{(h,j)\in Z}P_h^{-1}(D_j),\qquad A_\varnothing=Y.
$$

定义统一运输断言

$$
G(t,u,g,Z)\iff
\forall y\in A_Z:\ R((t,y),(u,P_g y)).
$$

**命题 14.1（实际识别的有限统一条件）。** 对任意 $t,u\in T$、$y,z\in Y$，

$$
R((t,y),(u,z))\iff
\exists g\in\Gamma,\ Z\subseteq\Gamma\times J:
G(t,u,g,Z),\quad y\in A_Z,\quad z=P_g y.
$$

证明。对实际生成关系的等价闭包归纳。生成识别 $j$ 取 $g=g_j$、$Z=\{(1,j)\}$；反身识别取 $g=1$、$Z=\varnothing$。

若正向见证为 $g,Z$，反向取 $g^{-1}$ 和

$$
Z^- = \{(hg^{-1},j):(h,j)\in Z\}.
$$

对每个 $z\in A_{Z^-}$，有 $P_{g^{-1}}z\in A_Z$；在该点使用原统一断言，再用 $R$ 的对称性。这给出对所有反向源点有效的同一个见证。

若前后两段见证为 $g,Z$ 和 $k,W$，复合取 $kg$ 和

$$
Z\star_g W=Z\cup\{(hg,j):(h,j)\in W\}.
$$

其条件集精确满足

$$
A_{Z\star_g W}=A_Z\cap P_g^{-1}(A_W).
$$

因此同一源点 $y$ 与中间点 $P_g y$ 同时满足两段的条件，两个统一断言由传递性组合。实际源点也满足这个并集条件。反向蕴含直接将 $G(t,u,g,Z)$ 应用于实际 $y$。整个归纳保留原始标签和实际运输，且不要求为不同源点重新选择 $g,Z$。

### 14.2 闭商、有限纤维与分离性

**命题 14.2（无需载体紧性的闭商）。** 在上述条件下，$R$ 是 $X\times X$ 的闭集，$q$ 是连续闭商映射，所有纤维有限且满足

$$
|q^{-1}(q(t,y))|\le |T|\,|\Gamma|.
$$

此外，$q$ 为 proper map，$Q$ 为 Hausdorff 空间。若 $Y$ 紧，则 $Q$ 也紧。

证明。对每个 $t,u,g,Z$，令

$$
E_{t,u,g,Z}=\{((t,y),(u,P_g y)):y\in A_Z\}
$$

当 $G(t,u,g,Z)$ 不成立时，将该集合取为空。$A_Z$ 闭，$P_g$ 连续且 $Y$ Hausdorff，所以每个 $E$ 是闭的受限图；离散标签条件也闭。命题 14.1 把 $R$ 表达为这些集合的有限并。全部索引数至多

$$
|T|^2\,|\Gamma|\,2^{|\Gamma|\,|J|}.
$$

纤维中的每个点都形如 $(u,P_g y)$，因此纤维基数有上述上界；不同 $u,g$ 可以给出相同点，不要求达到该界。

为证明闭商，取闭集 $C\subseteq X$，令 $C_t=\{y:(t,y)\in C\}$，它是 $Y$ 的闭集。$C$ 的饱和在目标标签 $u$ 上精确等于

$$
\bigcup_{t,g,Z:\,G(t,u,g,Z)}P_g(C_t\cap A_Z).
$$

每一项是闭集在同胚下的像，故闭；索引有限，所以饱和闭。实际商拓扑给出 $q(C)$ 闭，因此 $q$ 是闭映射。此步没有把非紧空间中的一般闭集投影当作闭集。

有限纤维是紧集。连续闭映射具有紧纤维，故 $q$ proper；$q\times q$ 也 proper。它满射且闭，因此为商映射。目标对角线的原像正是已证闭的 $R$，商映射反映闭性，所以 $Q$ 的对角线闭，$Q$ Hausdorff。若 $Y$ 紧，有限离散 $T$ 使 $X$ 紧，$Q$ 由连续满射得到紧性。

### 14.3 原始截断商的参数对应与边界

第 5 节取 $Y=K$、$\Gamma=\operatorname{Sym}(4)$、$J=T\times\operatorname{Fin}4$。生成识别 $j=(t,f)$ 的源标签为 $t$，目标标签为 $(p.\mathrm{facePair}(t,f)).1$，群元素为第 12 节从原始三槽面映射导出的 $\sigma_{t,f}$，闭条件为

$$
D_{(t,f)}=\{z\in K:z_f=0\}.
$$

对于 $(h,(t,f))$，拉回条件等价于 $z_{h^{-1}(f)}=0$。因此所有 $A_Z$ 都可压缩成四个坐标中的一个零集合；命题 14.1 在此恰恢复第 5 节的有限零条件运输。一般纤维界为 $24|T|$，第 13 节使用实际零坐标层和边不反转进一步给出 $12|T|$ 或 $6|T|$ 的界。

同一群运输若保持某个闭集合 $U\subseteq X$ 的标记，逐生成识别检查标记不变即可推出 $U$ 饱和，继而 $q^{-1}(q(U))=U$ 且 $q(U)$ 闭。原始 cap 的标记是“存在坐标等于 $3/4$”，它由坐标排列保持。不变标记须在实际源和目标标签之间检查，不能只检查各标签内的集合相同。

本节给出统一条件、闭饱和及商分离性的书面证明，未提供经 Lean kernel 核验的形式化，也不申报外部开放问题结算或文献原创性。标准 proper-map 判据、乘积定理、商拓扑与闭对角线判据直接复用钉版 Mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d` 的 `Mathlib/Topology/Maps/Proper/Basic.lean`、`Mathlib/Topology/Constructions.lean` 和 `Mathlib/Topology/Separation/Hausdorff.lean`。本节不构造原始商的局部图卡，不替代原始端点不反转、六层局部图卡及同一原始流形 $N$ 的端部延拓义务。

## 15. 与实际面粘合相容的几何块同胚

本节处理共同真长度已经取得后的拓扑接口。设 $p$ 是固定的有限原始面配对，$K$、$Q$、$q$ 和 $B$ 仍取第 5 节的实际截断载体、生成商和 cap 标记。每个标签 $t$ 对应一个紧、非退化、全超理想四面体的极面截断块 $P_t\subset\mathbb H^3$，保留原来的四个六边形侧面、四个三角形截断面、十二个顶点和十八条边。这里需要各块确有同一完整面格，不能用平坦块或仅有部分面的集合替代。

对每个原始面配对 $(t,f)\leftrightarrow(u,g)$，假设两个几何六边形之间有同胚的双曲等距映射 $I_{t,f}$，它按实际 $\sigma_{t,f}$ 对应全部顶点和边，且逆向使用 $I_{u,g}=I_{t,f}^{-1}$。这项输入只给定被配对的侧面映射；没有假设整个块的相容同胚。令 $Q_{\rm geom}$ 为这些实际侧面等距映射所生成的等价商，令 $B_{\rm geom}$ 为全部截断三角形在该商中的像。

**命题 15.1（保留完整面格的相容实现）。** 可以构造各个 $h_t:K\to P_t$ 的同胚，逐面、逐边、逐顶点保留上述对应，并同时满足

$$
h_u(P_{\sigma_{t,f}}z)=I_{t,f}(h_t(z))\qquad(z_f=0).
$$

它们因此诱导带标记同胚

$$
\overline h:(Q,B)\longrightarrow(Q_{\rm geom},B_{\rm geom}),
\qquad \overline h(q(t,z))=[t,h_t(z)].
$$

自粘合、重边和同一个全局边的多个局部出现都使用原始面映射；构造不另加全局边标签，不要求块间存在一个全局等距映射，也不要求角和为 $2\pi$。

### 15.1 双曲面格的等距自然中心

使用 Lorentz 内积 $L$ 和未来单位双曲面模型

$$
\mathbb H^3=\{X:L(X,X)=-1,\ X_0>0\}.
$$

对于一个紧凸双曲多边形或多面体的全部顶点 $X_1,\ldots,X_n$，定义

$$
S=\sum_{j=1}^nX_j,\qquad
c=\frac{S}{\sqrt{-L(S,S)}}.
$$

未来单位向量满足 $-L(X_i,X_j)=\cosh d(X_i,X_j)\ge1$，因此

$$
-L(S,S)\ge n^2>0,\qquad S_0>0.
$$

归一化有定义，且 $c\in\mathbb H^3$。在 Klein 坐标 $x_j=X_{j,\mathrm{sp}}/X_{j,0}$ 中，$c$ 的投影为

$$
\frac{\sum_j X_{j,0}x_j}{\sum_j X_{j,0}}.
$$

所有权重严格正。每个支撑面上的顶点满足同一个线性等式，其余顶点满足严格内侧不等式；故这个中心位于该多边形或多面体的相对内部。

侧面等距映射保留这个中心。具体地，六边形所在的全测地平面对应一个三维、签名 $(2,1)$ 的 Lorentz 子空间。选三个不在同一条双曲直线上的顶点；它们构成该子空间的线性基。等距映射保留这三个基向量的 Lorentz Gram 矩阵，因而它们的像定义一个 Lorentz 线性等距映射。其余顶点由与三个基向量的内积唯一确定；所以该线性映射也把它们送到原等距映射规定的像。对于任意侧面点 $Y$，距离保留给出它和三个基点的 Lorentz 内积；在线性等距延拓与原侧面等距映射下，这三个内积相同。目标子空间非退化且三个像构成基，故两个像相等。因此该线性延拓在整个侧面上等于 $I_{t,f}$，包括中心。它保留未来分支、求和和上述正归一化，因而把源侧面中心送到目标侧面中心。中心的定义不依赖某个指定顶点或边。

对 $A,C\in\mathbb H^3$，记 $G(A,C,s)$ 为从 $A$ 到 $C$ 的双曲测地段上、距离比例为 $s\in[0,1]$ 的点。当 $D=d(A,C)>0$ 时，

$$
G(A,C,s)=\frac{\sinh((1-s)D)}{\sinh D}A
       +\frac{\sinh(sD)}{\sinh D}C;
$$

当 $A=C$ 时取 $G(A,A,s)=A$。这给出连续的插值；在 $D\downarrow0$ 时两个系数分别趋于 $1-s,s$。等距映射与 $G$ 交换。Klein 投影把该测地段送到相同端点的直线段；当端点不同，投影参数随 $s$ 严格递增。

### 15.2 先共同边，再整个边界，最后块内部

参考块 $K$ 的每条边按其两个端点作仿射参数 $s\in[0,1]$；把它送到对应几何边的 $G(A,C,s)$。把端点次序颠倒时，两边都把 $s$ 改成 $1-s$，所以这项定义与无向边的选择无关。原始坐标排列是仿射映射，保留这个规范化参数；几何侧面等距映射保留弧长比例。因此所有配对在共同边上相容。

对参考块的每个六边形或三角形面 $F$，取其全部仿射顶点的平均 $c_F$，它位于 $F$ 的相对内部。参考面的每个非中心点唯一写成

$$
x=(1-s)c_F+sb,\qquad 0<s\le1,\quad b\in\partial F.
$$

在对应几何面 $F_t$ 中取第 15.1 节的中心 $c_{F_t}$，定义

$$
h_F(c_F)=c_{F_t},\qquad
h_F((1-s)c_F+sb)=G(c_{F_t},h_{\partial F}(b),s).
$$

这里 $h_{\partial F}$ 已由共同边上的定义给出。凸性使每条从中心出发的射线恰有一个边界终点。Klein 模型中的直线段对应以及参数的严格单调性，证明 $h_F$ 是连续双射；源面紧、目标 Hausdorff，所以它是同胚。中心处的连续性由边界紧性和测地段插值给出：$s\downarrow0$ 时距离不超过 $s$ 乘以中心到边界的最大距离。

各面同胚在共同边上使用完全相同的 $h_{\partial F}$，且把面相对内部送到对应面的相对内部；不同面的像只在对应共同边或顶点相交。因此有限闭面上的拼接是整个块边界的连续双射，紧到 Hausdorff 的判据使其成为同胚。对于被配对的两个参考六边形，$P_\sigma$ 保留全部顶点的平均及仿射射线参数；$I_{t,f}$ 保留全部几何顶点的 Lorentz 中心、共同边映射和测地段插值。逐点代入上述公式，得到两个整个六边形的相容性，而非仅有顶点或边的相容性。

最后，参考块取 $c_K=(1/4,1/4,1/4,1/4)$；几何块取其全部十二个顶点的 Lorentz 中心 $c_t$。每个非中心参考点唯一写成 $(1-s)c_K+sb$，其中 $b\in\partial K$、$0<s\le1$。以

$$
h_t(c_K)=c_t,\qquad
h_t((1-s)c_K+sb)=G(c_t,h_{\partial K}(b),s)
$$

延拓。紧凸块的相同射线论证证明这是同胚，且在全部边界面上恰恢复先前的映射。块中心的选取不需要在不同块之间相容，因为所有识别都发生在边界侧面。

### 15.3 实际生成商与原始流形的对应

设 $h(t,z)=(t,h_t(z))$。这是有限带标签不交并之间的同胚。已证的整个面等式把每个原始面生成识别送到一个实际几何生成识别，逆同胚给出反方向。对生成、反身、对称和传递分别应用这两项对应，得到两个完整等价闭包的等价性；传递中的每个中间点都使用同一个 $h$。商拓扑的通用性质因而给出 $\overline h$ 及连续逆映射。它逐块把四个 cap 面送到四个几何截断面，所以精确保留 $B$ 和 $B_{\rm geom}$。这里商同胚直接复用完整关系相容的商同胚定理，不以待证商的 Hausdorff 性为额外前提。

**推论 15.2（共同真长度的拓扑实现）。** 对一个已固定实际理想剖分的紧流形 $N$，解开该剖分的原始截断实现 $r:Q\cong N$，并保留 $r(B)=\partial N$。若每个实际块都真正、非退化，而且被配对六边形的三条交替边有相同长度，则上述几何粘合商与同一个 $N$ 带边界同胚。

证明。对于右角六边形，按边界循环把三条交替边记为 $a_0,a_1,a_2>0$，把连接 $a_i$ 和 $a_{i+1}$ 的边记为 $b_i$，下标按三取模。标准右角六边形余弦律给出

$$
\cosh b_i=\frac{\cosh a_{i+2}+\cosh a_i\cosh a_{i+1}}
                       {\sinh a_i\sinh a_{i+1}}.
$$

此式在实际超理想侧面上是 [Feng–Ge–Hua, arXiv:2009.03731v2, 第 2.1 节 Lemma 2.3、式 (2.2)](https://arxiv.org/html/2009.03731v2#S2.E2)，参数对应为 $a_i,a_{i+1},a_{i+2}=l_{ij},l_{ik},l_{jk}$，$b_i=x^i_{jk}$。因 $b_i>0$，三条交替边确定其余三条长度。两个六边形的全部六条对应边因此等长；将第一条有向边对齐以后，凸性选择的同侧直角转向及逐段长度唯一确定全部后续边，所以得到保留全部顶点对应的等距映射。反向循环用反射后同样成立。共同全局长度在全部出现上的同一拉回给出这些相等长度；逆配对取等距逆映射。命题 15.1 给出 $\overline h$，再取 $r\circ\overline h^{-1}$。这里 $r$ 是固定理想剖分的实际截断实现，不从裸 $p$ 中制造；若原形式输入只提供内部同胚，仍须单独取得其带标记截断实现或端部延拓。

本节的构造只结算同一完整面格、侧面相容和带标记拓扑实现。它不证明角和为 $2\pi$，不证明粘合度量在边或边界顶点处光滑，也不证明测地完备性或流的收敛。角和、法向链接以及截断面正交性承担相应的度量粘合义务。平坦块不满足本节的非退化完整面格前提。

右角六边形的余弦律使用标准双曲三角学；前述 Zhao 引言中的实际块定义及第 2.1 节的极面截断构造提供六边形全直角以及侧面与截断面正交的对应。Lorentz 归一化中心及逐面再逐块的延拓在这里给出显式书面构造；不申报文献原创性，也未给出经 Lean kernel 核验的应用。仅把商同胚通用定理应用于已经相容的块同胚属于复用；实际需要检查的是这些块同胚的构造和整个面等式。
