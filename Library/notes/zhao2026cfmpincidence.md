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

## 16. 与原始带标记实现相容的光滑双曲度量拼接

本节在第 15 节的相容几何块实现之后处理度量接口。仍使用同一个有限原始面配对 $p$、截断商 $(Q,B)$、实际侧面等距映射 $I_{t,f}$ 和几何商 $(Q_{\rm geom},B_{\rm geom})$。假设每个 $P_t$ 都是紧、凸、真正非退化的完全截断双曲四面体，具有第 15 节的完整面格；截断三角形与相邻侧六边形正交。所有侧面配对保留原始顶点及边的对应，并在反向使用等距逆映射。另假设第 6 节的实际边不反转条件，以及已给定的带标记截断实现

$$
r:(Q,B)\xrightarrow{\cong}(N,\partial N).
$$

对每个实际全局旧边 $e$，将每个局部旧边出现 $o\in O_e$ 的内二面角记为 $\alpha_o$，要求

$$
0<\alpha_o<\pi,\qquad \sum_{o\in O_e}\alpha_o=2\pi.
$$

这里的求和保留全部出现，包括同一四面体中属于同一全局边的不同局部边；环、自粘合和重边均沿原面端口运输处理。该条件不由同胚或共同边长自动给出。

**命题 16.1（实际紧截断块的条件性光滑拼接）。** 在上述条件下，$Q_{\rm geom}$ 上存在与实际商拓扑相容的实解析双曲流形带边界结构及曲率 $-1$ 的 Riemannian 度量 $g$。每个块的包含在其相对内部保持原双曲度量，$B_{\rm geom}$ 恰为流形边界且全测地。由

$$
j=\overline h\circ r^{-1}:N\longrightarrow Q_{\rm geom}
$$

运输图卡及度量，可在同一个带标记 $N$ 上得到这样的结构。各连通分量的 Riemannian 长度距离等于实际块拼接的路径距离，并且完备；沿全测地边界得到的双倍空间是紧、无边界且测地完备的双曲流形。

### 16.1 侧面延拓与实际边的有序端点

一个侧六边形的等距映射唯一延拓为其支撑双曲平面的等距映射。第 15.1 节的 Lorentz 基论证给出该延拓：三个不共线点的 Gram 矩阵确定平面上的线性等距映射。平面的 Lorentz 正交补是一维类空直线，选择该方向的两个符号得到恰好两个环境 $\mathbb H^3$ 等距延拓。局部展开选取把两个相邻块放在公共侧面两侧的那个延拓。仅有面上的相等不能区分这两个延拓。

第 6 节的端口圈给每个 $e$ 一个循环出现序列 $o_0,\ldots,o_{m-1}$，每次出现恰出现一次。选择两个实际端类中的一个为起端；边不反转保证该端类在每个出现中恰有一个端点。实际侧面映射把起端送到起端、终端送到终端，且保留边长。因此所有出现有同一 $\ell_e>0$，并共享从起端量起的有向弧长参数 $t\in[0,\ell_e]$。有限区间上保持两个有序端点的等距映射逐点保持 $t$；它没有轴向平移自由。即使两个端点具有相同的原始角点标签，也仍使用这两个不同的实际端类。

### 16.2 同时展开整个有限旧边的 Fermi collar

将一个有向旧边轴放置为未来单位双曲面上的

$$
\gamma(t)=(\cosh t,\sinh t,0,0).
$$

轴周围的 Fermi 坐标为

$$
F(t,\rho,\theta)=
(\cosh\rho\cosh t,\ \cosh\rho\sinh t,
 \sinh\rho\cos\theta,\ \sinh\rho\sin\theta).
$$

在 $\rho=0$ 时合并全部角坐标。对 Lorentz 形式 $-x_0^2+x_1^2+x_2^2+x_3^2$ 直接微分得到

$$
g_{\mathbb H^3}=d\rho^2+\cosh^2\rho\,dt^2+\sinh^2\rho\,d\theta^2.
$$

每次旧边出现的两个相邻侧面支撑平面包含该轴，故为两条常角平面。起端的截断平面同时正交于这两个侧平面，其法向平行于轴在起端的切向；它就是 $t=0$ 的平面。终端同理为 $t=\ell_e$。其余面均不碰该闭旧边段。在一个块内，闭段紧，所有其余支撑面的内侧不等式在其上严格成立；连续性与紧性给出共同正半径，使该径向管不碰其余面。再对有限个出现取半径最小值，得到 $\varepsilon_e>0$，每个出现的完整 collar 恰为

$$
0\le t\le\ell_e,\qquad 0\le\rho<\varepsilon_e,
\qquad 0\le\theta\le\alpha_{o_i}.
$$

同一个块的不同旧边是两两不交的紧线段，半径还可同时缩小，使其 collars 两两不交。这避免了同一块对同一全局边贡献多次出现时的额外局部识别。侧面配对在 collar 的公共面上保持 $(t,\rho)$：它保持有序轴、到轴的垂距，以及六边形位于轴哪一侧的半平面。

令

$$
\beta_0=0,\qquad \beta_{i+1}=\beta_i+\alpha_{o_i}.
$$

逐出现将 collar 放到 $\beta_i\le\theta\le\beta_{i+1}$ 的扇区。这里的放置按出现编号，不按四面体标签编号。相邻扇区使用规定的侧面映射相接，最后一条射线使用 $\beta_m=2\pi$ 与第一条射线相接。所有 $\alpha_{o_i}>0$，故扇区内部两两不交，且恰覆盖一圈。collars 只碰该旧边的两个侧面，因此没有圈关系以外的识别。所得到的实际饱和商与

$$
\{F(t,\rho,\theta):0\le t\le\ell_e,
\ 0\le\rho<\varepsilon_e,
\ \theta\in\mathbb R/2\pi\mathbb Z\}
$$

同胚且逐扇区等距。连续逆可先在更小的闭径向 collar 上，由有限紧扇商到 Hausdorff 模型的连续双射得到，再限制到相对开 collar。旧边内部的限制是普通双曲球邻域；两个端点的限制分别是双曲半球邻域。

这也精确分开返回等距映射的两项义务。保持有序轴的环境等距映射在 Fermi 坐标中作用为轴向平移及法平面上的固定正交变换。两个有限有序端点使平移量为零。上述按实际端口的一圈扇展开使法向返回为总角 $2\pi$ 对应的恒等变换；其正角区间恰覆盖一次，同时排除反射返回及分支覆盖。无需另加依赖 $t$ 的扭转参数，因为这样的扭转不属于环境双曲等距映射。这里仅讨论旧边周围的局部返回，不要求整个流形的全局 holonomy 平凡。

精确的一圈条件不能替换为“返回旋转为恒等”或“横截面拓扑为圆盘”。总角 $4\pi$ 的锥也具有恒等旋转返回及圆盘拓扑，但其半径 $\rho$ 的横向圆周长为 $4\pi\sinh\rho$，不等于光滑双曲轴周围的 $2\pi\sinh\rho$。

### 16.3 cap 侧边及 cap 顶点的实际半球 link

块内部给出球图卡；侧面内部由两个相反侧的半球组成球；截断面内部直接给出半球。旧边及其端点使用第 16.2 节的同时展开。还需检查截断面与侧面的交边。

在 cap 侧边内部，恰有两个块出现沿唯一侧面相接，分别贡献一个直角四分之一球。展开公共侧面后，两截断支撑平面包含相同 cap 侧边轴，且都正交于同一个侧平面；这个条件唯一确定截断平面。两块的截断内侧半空间也相同：它们都包含被配对六边形在该 cap 侧边的内侧。与此同时，两块处于公共侧平面的相反侧。因此两个直角四分之一球恰填满一个半球，不产生边界折痕。

在一个旧边起端，令 $\tau$ 为沿该旧边指入块内的单位切向，取 $\tau^\perp$ 的正交单位基 $u,v$。第 $i$ 次出现的实际球面 link 为

$$
(\psi,\theta)\longmapsto
\cos\psi\,\tau+\sin\psi(\cos\theta\,u+\sin\theta\,v),
\qquad 0\le\psi\le\frac\pi2,
\quad\beta_i\le\theta\le\beta_{i+1}.
$$

其球面度量为 $d\psi^2+\sin^2\psi\,d\theta^2$，三个角分别为 $\alpha_{o_i},\pi/2,\pi/2$。实际侧面映射保持 $\psi$，并按端口圈连接相邻子午线。边不反转使该端类使用全部旧边出现各一次；这些角区间恰分割一圈，所以该公式诱导实际拼接 link 到圆半球的等距同构。cap 边组成其赤道，赤道作为边界保留。终端改用指向旧边内部的相反轴向，同样得到圆半球。

沿该端点的测地极坐标，邻域度量因此为

$$
ds^2+\sinh^2(s)\,g_{S^2_+},
$$

即双曲半球度量。这里的三维局部 link 是 cap 顶点处的半球；整个原始理想顶点的截断 link 是一个边界曲面，两者不是同一对象。六种实际层由此分别具有球或半球的几何邻域，而不仅具有抽象的拓扑球或半球。

### 16.4 等距转移、全测地边界及实际长度度量

取两个上述展开图卡的重叠点，缩小到该点的共同局部星形邻域。在其中一个三维块扇区上，转移是某个环境双曲等距映射 $A$ 的限制。跨到相邻扇区时，两图卡都使用规定的侧面映射，并把相邻块放到公共侧面的相反侧；第 16.1 节的延拓唯一性强制相邻扇区上的转移仍是同一个 $A$。沿有限局部星形邻域传播可达全部 incident 扇区，旧边及 cap 顶点的一圈一致性已由同时展开给出。低维层上的相等由连续性得到。因此转移局部是一个环境等距映射，不是未加约束的分片等距映射。

边界图卡的转移保留其支撑半空间，并解析延拓到边界平面另一侧。这些图卡在已有实际商拓扑上定义实解析流形带边界。它们的双曲度量拉回相同，拼成正定实解析度量 $g$，其内部截面曲率为 $-1$。由实际层的模型，唯一的流形边界正是 $B_{\rm geom}$；它局部为双曲全测地平面，故全测地。该论证是局部论证，不要求全局可定向，也不把原始面商改写成一个未经给定的群作用商。

对同一连通分量，令 $d_{\rm poly}$ 为有限块路径链长度的下确界：每段在某个实际块中，连续段端点按实际生成关系识别；令 $d_g$ 为上述 Riemannian 长度距离。每条块路径链在商中给出同长度路径，故 $d_g\le d_{\rm poly}$。

反向取一条分片光滑路径，以有限多个较小凸球或凸半球图卡覆盖其像，并细分使各段包含在一个这样的图卡内。将各段换为相同端点的模型测地段不会增加长度。每个图卡内只有有限个展开侧面平面；一条测地段与每个全测地平面至多相交一次，或整段位于其中。因而可将每段再有限细分为块路径；落在公共面上的段分配给任一 incident 块。所得有限链合法，给出 $d_{\rm poly}\le d_g$。所以

$$
d_{\rm poly}=d_g.
$$

该距离是诱导实际商拓扑的真正度量。若 $N$ 不连通，上述断言逐连通分量成立；整体内在长度距离在不同分量间取 $+\infty$，不为它另指定任意有限距离。

### 16.5 完备性、双倍及原始标记的光滑约定

有限个紧块的商紧，因此每个带边界连通分量的 Riemannian 长度度量是紧度量并且完备。沿 $B_{\rm geom}$ 将两份商以恒等映射加倍，在每个半球图卡中把第二份反射到边界平面的另一侧。cap 面内部的两个半球给出球；cap 侧边的四个直角四分之一球给出球；cap 顶点的两个实际圆半球 link 沿赤道给出圆 $S^2$。旧边在 cap 处沿轴向延长，横向角仍为 $2\pi$，没有把两端扇的角和加成 $4\pi$。

在截断支撑平面法向坐标中，度量为

$$
ds^2+\cosh^2(s)\,h_{\mathbb H^2}.
$$

它关于 $s$ 为偶函数且解析，所以反射拼接光滑；cap 侧边和顶点也由已证半球图卡覆盖。双倍因此先得到紧、无边界的光滑双曲流形，再由 Hopf–Rinow 得到测地完备。带边界原空间的完备性指包含边界的内在长度度量完备；不能据此声称所有测地线在边界内无限延伸。删除非空边界后的内部不完备，因为一条法向测地线可在有限长度内到达被删边界。这里所有块完全截断且紧，不涉及 cusp 的完备方程。

通过已固定的 $j=\overline h\circ r^{-1}$ 在原始 $N$ 上使用图卡 $\phi\circ j$，并取 $g_N=j^*g$。这项拉回针对运输得到的光滑结构，故 $j$ 是等距微分同胚，且 $j(\partial N)=B_{\rm geom}$。若另有预先指定的光滑 atlas，仅有带标记同胚 $r$ 并不保证它与该 atlas 光滑相容；要求同一个字面标记相对于额外 atlas 光滑时，该相容性仍是额外义务。

### 16.6 文献对应及条件边界

上述紧完全截断情形对应 [Roberto Frigerio、Carlo Petronio, *Construction and Recognition of Hyperbolic 3-Manifolds with Geodesic Boundary*, arXiv:math/0109012v1](https://arxiv.org/abs/math/0109012v1) 的 Definitions 1.6–1.8（正文第 6–7 页）中 $I=Z=\varnothing$ 的几何实现：没有 ideal vertices 或 length-zero edges，截断面与侧面正交。Definition 1.10（正文第 8 页）在紧可定向流形去除规定的 tori 和 annuli 后，把 partially truncated triangulation 定义为各个 $\Delta^*$ 按指定侧面配对实现原流形；这里沿用其实际剖分语义，由已固定的 $r$ 和第 15 节的 $\overline h$ 保持同一个 marked 对应。Theorem 2.13 及 Remark 2.14（正文第 20 页）区分侧面一致性、实际内边角和 $2\pi$ 与两端 ideal 时的额外返回方程；Remark 2.14 的无 toric end 情形说明内边长度匹配和角和条件已足够处理相应匹配。该定理原文的全局陈述另有可定向、规定剖分及边界负 Euler 特征等前提；这里没有把那些前提从裸面配对中推断出来，而是在既有带标记截断实现上给出上述紧块的直接局部拼接证明。原文随后的 completeness discussion 也明确把有边界流形的完备性与双倍的完备性对应起来，并单独处理非紧端的方程。

本节是标准双曲块拼接结论在原始出现、实际面映射和同一标记上的书面落实，不申报数学原创性或 Lean kernel 核验。它以真正紧块、实际兼容等距配对、边不反转、精确出现角和以及已有带标记实现为条件；不从较弱组合条件制造共同真长度或零缺陷，不将拓扑实现代替光滑度量证明，也不结算独立的实际体积、Schläfli、全局流收敛或预先指定 atlas 的相容性义务。
## 17. 原始六参数块上的实际旧边领圈与参数恢复

本节把第 16.2 节的标准 Fermi 领圈接回原始六参数的极面截断块，给出支撑不等式、逆参数及相对开集的具体公式。所有六个参数独立变化，不假设等边。沿用原始槽序 $12,13,14,34,24,23$，令 $x_{ij}>1$，并要求原始判别式 $D(x)>0$。在原始 Lorentz 模型中，记实际向量为 $V_1,\ldots,V_4$，其 Gram 矩阵为

$$
G_{ii}=1,\qquad G_{ij}=-x_{ij}\quad(i\ne j),\qquad
L(X,Y)=-X_0Y_0+X_{\rm sp}\cdot Y_{\rm sp}.
$$

原始 Gram 构造给出 $\det G<0$、$V_{i,0}\ge0$，且任意两个不同向量的时间坐标之和严格正。每个三阶主子矩阵的行列式为

$$
1-a^2-b^2-c^2-2abc<0\qquad(a,b,c>1).
$$

因此 $H=G^{-1}$ 满足 $H_{ff}>0$。定义实际 Gram 对偶、正尺度及外法向

$$
W_f=\sum_a H_{af}V_a,\qquad
\eta_f=\sqrt{H_{ff}},\qquad n_f=-W_f/\eta_f.
$$

它们满足 $L(V_a,W_f)=\delta_{af}$、$L(n_f,n_f)=1$ 和
$L(V_a,n_f)=-\delta_{af}/\eta_f$。这里的负号固定原块的内侧方向。

原始系数载体与实际块保持字面定义

$$
C_x=\{\lambda\in\mathbb R^4:\lambda_a\ge0,\ \sum_a\lambda_a=1,
\ (G\lambda)_f\le0\ \text{对全部 }f\},
$$

$$
\nu_x(\lambda)=\frac{\sum_a\lambda_aV_a}
 {\sqrt{-L(\sum_a\lambda_aV_a,\sum_a\lambda_aV_a)}},
\qquad P_x=\nu_x(C_x)\subset\mathbb H^3.
$$

对 $\lambda\in C_x$，分母严格正且分子为未来类时向量，这是原始极面截断构造的归一化性质。下面不以另一个半空间块替换 $P_x$。

### 17.1 从实际端点得到完整闭轴和四个严格支撑

固定不同的 $i,j$，令 $k,l$ 为另外两个顶点标签。记

$$
r=x_{ij},\quad s=\sqrt{r^2-1},\quad \ell=\operatorname{arcosh}r>0,
\quad A=\frac{rV_i+V_j}{s},\quad B=\frac{V_i+rV_j}{s},\quad \tau=-V_i.
$$

这两个端点恰是原始系数点 $(re_i+e_j)/(r+1)$ 和 $(e_i+re_j)/(r+1)$ 的归一化。第一个点的 $i$-cut 为零、$j$-cut 为 $1-r<0$，另外两项 cut 严格负；第二个点交换 $i,j$。直接使用 Gram 等式得

$$
L(A,A)=L(B,B)=-1,\quad L(A,B)=-r,\quad
L(\tau,\tau)=1,\quad L(A,\tau)=0,
\quad B=rA+s\tau.
$$

两端点的时间坐标严格正。实际闭轴取

$$
\gamma(t)=\cosh t\,A+\sinh t\,\tau
=\frac{\sinh(\ell-t)}s A+\frac{\sinh t}s B,
\qquad 0\le t\le\ell.
$$

插值的两个系数非负且不同时为零，所以整条轴都在未来单位双曲面上。端点 cap 与相邻侧面的精确支撑为

$$
L(\gamma(t),V_i)=-\sinh t,\qquad
L(\gamma(t),V_j)=\sinh(t-\ell),\qquad
L(\gamma(t),n_k)=L(\gamma(t),n_l)=0.
$$

其余四个支撑在整个闭段上严格成立。对 $n_i$，两端的配对值分别为 $-r/(s\eta_i)$、$-1/(s\eta_i)$；对 $n_j$，分别为 $-1/(s\eta_j)$、$-r/(s\eta_j)$。对 $h\in\{k,l\}$，有

$$
L(A,V_h)=-\frac{r x_{ih}+x_{jh}}s<0,\qquad
L(B,V_h)=-\frac{x_{ih}+r x_{jh}}s<0.
$$

以上非负插值保持这些严格负号。两个端点 cap 则只满足弱不等式，并分别在 $t=0,\ell$ 取零；领圈构造不能把这两个支撑误列为全程严格。

### 17.2 实际二面角、统一半径与字面块成员

令 $c=-L(n_k,n_l)=-H_{kl}/(\eta_k\eta_l)$。互补主子式恒等式给出

$$
H_{kk}H_{ll}-H_{kl}^2
=\frac{\det G_{\{i,j\},\{i,j\}}}{\det G}
=\frac{1-r^2}{\det G}>0,
$$

所以 $-1<c<1$。在旧边的任一实际点，$n_k,n_l$ 都是双曲切空间中的外单位法向；原始内二面角为它们夹角的补角，故 $\alpha=\arccos c\in(0,\pi)$。令

$$
d=\sqrt{1-c^2}=\sin\alpha>0,\qquad
u=\frac{-n_l-cn_k}{d},\qquad v=-n_k.
$$

由实际 Gram 等式，$(A,\tau,u,v)$ 的 Gram 矩阵为 $\operatorname{diag}(-1,1,1,1)$；四个向量因此线性无关并构成原四维环境的基。定义

$$
F(t,\rho,\theta)=\cosh\rho\,\gamma(t)
+\sinh\rho(\cos\theta\,u+\sin\theta\,v).
$$

它满足 $L(F,F)=-1$，且四个 incident 支撑精确为

$$
\begin{aligned}
L(F,V_i)&=-\cosh\rho\,\sinh t,&
L(F,V_j)&=\cosh\rho\,\sinh(t-\ell),\\
L(F,n_k)&=-\sinh\rho\,\sin\theta,&
L(F,n_l)&=-\sinh\rho\,\sin(\alpha-\theta).
\end{aligned}
$$

设 $S$ 为时间坐标严格正、$n_i,n_j$ 及 $V_k,V_l$ 四项支撑严格负的环境开集。第 17.1 节给出 $\gamma([0,\ell])\subset S$。该轴像紧；而 $F$ 连续，在 $\rho=0$ 时与 $\theta$ 无关。对紧参数集 $[0,\ell]\times[0,2\pi]$ 作有限开覆盖，得到 $\varepsilon>0$，使

$$
F(t,\rho,\theta)\in S\quad
(0\le t\le\ell,\ 0\le\rho\le\varepsilon,\ 0\le\theta\le2\pi).
$$

具体地，每个 $(t,\theta)$ 的连续性给出参数邻域及一个正的 $\rho$ 宽度；有限子覆盖的宽度最小值再缩小一半，即同时包含所选闭径向区间。故 $0\le\theta\le\alpha$ 时，前述四项 incident 弱支撑与 $S$ 的四项严格支撑合起来给出全部八项原始支撑。

为确认这些点属于字面 $P_x$，对这样的未来单位点 $w=F(t,\rho,\theta)$ 取实际齐次系数

$$
\beta_f=L(w,W_f),\qquad b_0=\sum_f\beta_f.
$$

实际侧面公式 $L(w,n_f)=-\beta_f/\eta_f$ 给出 $\beta_f\ge0$，且 $n_i$ 的严格支撑给出 $\beta_i>0$，所以 $b_0>0$。Gram 对偶重构给出 $w=\sum_f\beta_fV_f$。令 $\lambda_f=\beta_f/b_0$，则 $\lambda_f\ge0$、$\sum_f\lambda_f=1$，并且

$$
(G\lambda)_f=L(w,V_f)/b_0\le0,\qquad
\sum_f\lambda_fV_f=w/b_0.
$$

因此 $\lambda\in C_x$，其归一化分母为 $1/b_0$，且 $\nu_x(\lambda)=w$。这直接证明实际 Fermi 闭扇区进入原归一化像；没有额外假设半空间刻画或提供成员见证。

### 17.3 从字面块点恢复参数及实际相对开领圈

对任意 $w\in P_x$，其定义立即给出全部八项弱支撑。用上述实际正交基写成

$$
w=aA+b\tau+Cu+Dv,\qquad
a=-L(w,A),\ b=L(w,\tau),\ C=L(w,u),\ D=L(w,v).
$$

单位方程与两个端点 cap 支撑给出

$$
a^2-b^2=1+C^2+D^2,\qquad b\ge0,\qquad rb\le sa.
$$

故 $a\ge0$；单位方程排除 $a=0$，所以 $a>0$。取

$$
q(w)=\sqrt{C^2+D^2},\quad R=\sqrt{1+q(w)^2},\quad
\rho=\operatorname{arsinh}q(w),\quad
t=\operatorname{arsinh}(b/R).
$$

有 $\sinh\rho=q$、$\cosh\rho=R$、$\sinh t=b/R$、$\cosh t=a/R$。从 $b\ge0$ 得 $t\ge0$；第二个 cap 支撑化为 $R\sinh(t-\ell)\le0$，所以 $t\le\ell$。

两个相邻侧面支撑等价于

$$
D\ge0,\qquad dC-cD\ge0.
$$

当 $q>0$ 时取 $\theta=\arccos(C/q)\in[0,\pi]$。由 $C^2+D^2=q^2$、$D\ge0$ 得 $\sin\theta=D/q$。第二项支撑于是给出 $\sin(\alpha-\theta)\ge0$。若 $\theta>\alpha$，则 $-\pi<\alpha-\theta<0$，其正弦严格负，矛盾。因此 $0\le\theta\le\alpha$，且 $w=F(t,\rho,\theta)$。当 $q=0$，取 $\theta=0$；此时 $C=D=0$，同样恢复 $w=\gamma(t)$。

对第 17.2 节选出的同一个 $\varepsilon$，得到精确集合等式

$$
U_{ij}:=\{w\in P_x:q(w)<\sinh\varepsilon\}
=\{F(t,\rho,\theta):0\le t\le\ell,\ 0\le\rho<\varepsilon,
\ 0\le\theta\le\alpha\}.
$$

$q$ 是实际块上的连续函数，故 $U_{ij}$ 在 $P_x$ 中相对开，并包含整个闭旧边。这不声称带侧面和端点的闭扇区在环境 $\mathbb H^3$ 中开。

当 $\rho>0$ 时，上述公式唯一恢复 $\rho,t,\theta$：$\operatorname{arsinh}$ 的严格单调性恢复前两者，而 $\cos$ 在 $[0,\alpha]\subset[0,\pi]$ 上单射，恢复最后一个参数。轴上仅合并角坐标，$t$ 仍唯一。还可确认 $\rho$ 是到实际闭轴的双曲距离：对任意轴参数 $z\in[0,\ell]$，

$$
-L(w,\gamma(z))=R\cosh(t-z)\ge R=\cosh\rho,
$$

且在已恢复的 $z=t$ 取等；$\operatorname{arcosh}$ 单调给出所述距离。

本节给出一个实际块中一条完整闭旧边的书面证明。它补足第 16.2 节标准模型与原始六参数对象之间的支撑、成员和逆参数接口，不申报经 Lean kernel 验证、冻结或消化覆盖，也不申报文献原创性。把它用于原始全局商仍须同时检查有限全部出现的共同半径、同块不同旧边的分离、实际面映射的有序轴及半径运输，以及原始生成关系的饱和与精确纤维；本节没有结算这些全局义务。

## 18. 全部实际旧边出现的共同领圈与原始商饱和

固定第 15 节的有限原始面配对 $p$。每块的六个参数由同一个实际全局旧边函数拉回，满足第 17 节的 $x_{ij}>1$、$D(x)>0$；侧面等距映射保留原始顶点和边对应，反向使用其逆。仍取原始 $X=T\times K$、面生成关系的等价闭包 $R$、商映射 $q:X\to Q$，以及实际带标签不交并 $X_{\rm geom}=\coprod_t P_t$、几何生成关系的等价闭包 $R_{\rm geom}$ 和 $q_{\rm geom}:X_{\rm geom}\to Q_{\rm geom}$。第 15 节的同一个相容块同胚记为 $H(t,z)=(t,h_t(z))$，诱导商同胚 $\overline H$。

令 $E$ 为原始局部旧边出现 $O=T\times\operatorname{Fin}6$ 在面端口运输下的商；记 $[o]\in E$，并保留整个出现集

$$
O_e=\{o\in O:[o]=e\}.
$$

同一块的不同局部边即使属于同一个 $e$，仍是 $O_e$ 中不同的元素。记出现 $o$ 的完整闭旧边为 $S_o$，第 17 节实际法向坐标的半径函数为 $q_o$。其中 $q_o$ 是非负实数函数，与商映射 $q$ 不同。

**命题 18.1（实际共同半径及饱和开邻域）。** 若 $O$ 非空，可以选择一个 $\varepsilon>0$，使每个出现的

$$
U_o(\varepsilon)=\{w\in P_{o.1}:q_o(w)<\sinh\varepsilon\}
$$

都是第 17 节的完整闭旧边 Fermi collar。同块不同局部边的这些 collars 两两不交。对每个 $e\in E$，定义

$$
U_e^{\rm geom}=
\{(t,w):\text{存在 }j,\ [(t,j)]=e,\ w\in U_{(t,j)}(\varepsilon)\},
\qquad U_e=H^{-1}(U_e^{\rm geom}).
$$

这些集合开，包含对应的全部闭旧边出现，并满足精确饱和等式

$$
q_{\rm geom}^{-1}\bigl(q_{\rm geom}(U_e^{\rm geom})\bigr)
=U_e^{\rm geom},\qquad q^{-1}\bigl(q(U_e)\bigr)=U_e.
$$

因此 $q_{\rm geom}(U_e^{\rm geom})$ 和 $q(U_e)$ 是相应商中的开邻域。不同全局旧边的这些商邻域两两不交，且

$$
\overline H\bigl(q(U_e)\bigr)=q_{\rm geom}(U_e^{\rm geom}).
$$

本命题不要求角和 $2\pi$ 或全局边不反转。后者用于统一有向纵坐标，前者用于闭合展开扇区；共同半径和饱和性只使用无向轴及原始面生成识别。若 $O$ 为空，则没有待构造的旧边邻域，结论为空族。

### 18.1 整张实际配对面上的轴与半径运输

设原始面配对的顶点排列为 $\sigma$，源面标签为 $f$，旧边的两个有序端标签 $i,j$ 均不同于 $f$。沿第 17 节的定义，源轴的端点为 $A,B$，目标有序端点为 $A',B'$；实际面等距映射 $I$ 把 $A$ 送到 $A'$、$B$ 送到 $B'$。这包括端点，且与面上点离轴多远无关。共同长度给出同一个 $\ell>0$，并有

$$
\tau=\frac{B-\cosh\ell\,A}{\sinh\ell},\qquad
\tau'=\frac{B'-\cosh\ell\,A'}{\sinh\ell}.
$$

对该闭面上的任意 $w$，等距映射保留 $w$ 与两个 cap 端点的双曲距离，故保留相应 Lorentz 配对。由上述 $\tau$ 的公式得到

$$
a'=-L(Iw,A')=-L(w,A)=a,\qquad
b'=L(Iw,\tau')=L(w,\tau)=b.
$$

第 17 节的实际四向量正交基及单位方程给出

$$
q_o(w)^2=a^2-b^2-1.
$$

目标同样满足此式；两边的半径均非负，因此

$$
q_{o'}(Iw)=q_o(w).
$$

在有序端点一致的约定下，还保留整个面的恢复纵坐标
$t=\operatorname{arsinh}\bigl(b/\sqrt{1+q_o(w)^2}\bigr)$。这里没有添加 collar 半径限制，也没有把面映射的参数运输作为外加前提。

若目标局部槽序颠倒端点，则 $A_{\rm rev}=B$、
$\tau_{\rm rev}=-\sinh\ell\,A-\cosh\ell\,\tau$。于是

$$
a_{\rm rev}=\cosh\ell\,a-\sinh\ell\,b,\qquad
b_{\rm rev}=\sinh\ell\,a-\cosh\ell\,b,
$$

从 $\cosh^2\ell-\sinh^2\ell=1$ 得
$a_{\rm rev}^2-b_{\rm rev}^2=a^2-b^2$，所以半径仍不变。该计算允许每条局部边任选端点顺序；它不声称整个出现圈已有一致的有向 $t$。

### 18.2 闭旧边分离及全部出现的共同缩小

先对有限 $O$ 中每个出现取第 17 节给出的正半径，再取最小值。更小的正半径仍满足同一精确 Fermi 集合等式，而且保留两个非相邻主侧面上的严格内侧支撑。

同一实际块的不同完整闭旧边是不交紧集。确实，$\nu_x$ 在 $C_x$ 上单射：若两个归一化像相同，原始向量 $V_a$ 构成基给出两个系数向量按归一化分母成比例；两者系数和都为 $1$，所以比例为 $1$。沿端标签 $\{i,j\}$ 的整个闭段，归一化前恰有 $i,j$ 两个严格正系数，其余系数为零。端点的两个系数也严格正。不同二元端标签集不能有相同的正系数支撑，故闭段不交。

在原始有限维环境空间固定任意范数。每对不同闭旧边的距离函数在紧乘积上达到严格正的最小值。有限个块及局部边对因此有一个共同正分离常数 $\delta$。没有局部边对时无需此常数。

对出现 $o$，令 $M_o=\max_{0\le t\le\ell_o}\|\gamma_o(t)\|$。实际 Fermi 公式给出统一于整个闭段和全部扇区角的估计

$$
\|F_o(t,\rho,\theta)-\gamma_o(t)\|
\le(\cosh\rho-1)M_o
+\sinh\rho\bigl(\|u_o\|+\|v_o\|\bigr),\qquad \rho\ge0.
$$

右端随 $\rho\downarrow0$ 趋于零。对有限全部出现进一步共同缩小 $\varepsilon$，可使右端在 $0\le\rho<\varepsilon$ 时严格小于 $\delta/3$。若同块两条不同边的 collars 相交，该交点到两条闭段各有上述界；三角不等式使两段距离小于 $2\delta/3$，与分离界矛盾。因此同块不同局部出现的 collars 不交，即使它们在 $E$ 中具有同一个全局标签。本步骤只用环境范数、紧性和实际 Fermi 公式，不依赖内在距离的另一次校准。

### 18.3 原始面生成关系与完整等价闭包的饱和

设 $(t,w)\in U_e^{\rm geom}$，取其出现 $o=(t,\{i,j\})$。第 17 节的严格支撑给出 $L(w,n_i)<0$ 和 $L(w,n_j)<0$，所以该点不在这两个非相邻主侧面上。任何在该点实际可用的面生成识别，其源面必为另外两个相邻主侧面之一。两个端点 cap 上的等式不产生面配对识别。

对于这样的实际生成识别，原始三槽面映射把边 $\{i,j\}$ 运输为目标边 $\{\sigma i,\sigma j\}$。这正是定义 $E$ 的一个面端口运输，故目标出现 $o'$ 仍属于 $O_e$。第 18.1 节给出目标半径等于源半径，而所有出现使用同一个 $\varepsilon$，因此识别后的点属于 $U_{o'}(\varepsilon)$。逆配对应用相同论证，得到生成关系两端的成员资格等价。这也处理两个不同面在同一块中的自配对。

沿生成、反身、对称和传递逐步保持该成员资格，得到

$$
(t,w)\ R_{\rm geom}\ (u,v)
\quad\Longrightarrow\quad
\bigl((t,w)\in U_e^{\rm geom}\iff(u,v)\in U_e^{\rm geom}\bigr).
$$

这证明整个等价闭包的饱和等式。每个 $U_o(\varepsilon)$ 在实际块中相对开，故其带标签有限并 $U_e^{\rm geom}$ 开。商拓扑以商映射原像判开；对这个已证饱和的集合，原像恰为其自身，因此商像开。

第 15.3 节的同一个 $H$ 在两个方向保持整个生成关系及其等价闭包。故 $U_e=H^{-1}(U_e^{\rm geom})$ 在原始 $X$ 中开且 $R$-饱和，商像仍是字面原始 $Q$ 中的开集。代表公式 $\overline H(q(t,z))=q_{\rm geom}(H(t,z))$ 给出命题中的精确商像对应。

不同 $e$ 的实际带标签并不相交：若在同一块相交，则其两个局部出现不同，与第 18.2 节矛盾。若两个商像相交，两个代表属于同一个 $R_{\rm geom}$ 类；饱和性使其中一个代表同时属于两个实际并，再次矛盾。原始商经 $H$ 同样得到不交性。

本节结算实际有限出现的共同半径、同块分离、面半径运输及原始商饱和的书面接口，不申报 Lean kernel 验证、冻结、消化覆盖或文献原创性。精确展开坐标的商纤维、出现角和闭合、全部图卡交叠的等距 germ、解析度量下降及同一带标记 $N$ 上的度量实现仍分别承担其证明义务。

## 19. 原始生成商上两次实际展开的局部 Lorentz 比较

本节展开第 16.4 节的交叠传播论证，保持第 15、18 节的同一个原始商及块标记。令 $\pi=q_{\rm geom}:X_{\rm geom}\to Q_{\rm geom}$，各 $P_t$ 仍是原始六参数的字面归一化截断块，面识别仍是实际 $I_{t,f}$ 及其逆。令

$$
G=\{A\in\mathrm{GL}(\mathbb R^4):L(Au,Av)=L(u,v),\ A(\mathbb H^3)=\mathbb H^3\}.
$$

这里保留未来分支，但不限制空间定向。下述比较以已经下降到原始商的两次展开为输入；不把下降、精确纤维或局部同胚当作比较结论。

**命题 19.1（固定实际分支的交叠 germ）。** 设 $U,V\subseteq Q_{\rm geom}$ 开，$d:U\to\mathbb H^3$、$e:V\to\mathbb H^3$ 为映射，$x\in U\cap V$。对纤维 $F_x=\pi^{-1}(x)$ 中每个实际代表 $a=(t,z_a)$，要求存在 $z_a$ 在 $P_t$ 中的相对开邻域 $N_a$ 及固定 $J_a,K_a\in G$，满足 $\pi(N_a)\subseteq U\cap V$ 和

$$
d(\pi(t,z))=J_a z,\qquad e(\pi(t,z))=K_a z\qquad(z\in N_a).
$$

矩阵固定在整个该块邻域上，不能仅逐点选取。对于每个把代表 $a$ 送到代表 $b$ 的实际面生成识别，另要求 $J_a,J_b$ 将源、目标块的内侧放到公共展开面两侧，$K_a,K_b$ 也如此。此要求针对同一个实际面关联，不以块标签相等或不同代替。则存在原始商中的开邻域 $x\in W\subseteq U\cap V$ 和唯一 $\Lambda\in G$，使

$$
e(y)=\Lambda d(y)\qquad(y\in W).
$$

若 $d,e$ 另外已经证明为图卡，则转移 $e\circ d^{-1}$ 在 $d(W)$ 上是 $\Lambda$ 的限制。该命题不要求先安装光滑结构或商度量，也不由角和条件单独推出输入的分支公式与两侧条件。

### 19.1 有限实际纤维及共同饱和缩小

第 14.3 节从原始四坐标排列运输得到 $|q^{-1}(y)|\le24|T|$。第 15.3 节同一个 $H$ 在两个方向保持生成关系及其等价闭包，所以 $F_x$ 有限，并有相同上界。每个元素保留块和实际点；同块的不同代表、不同局部边的出现、环及重复关联均不合并。

对每个 $a=(t,z_a)\in F_x$，在实际块中取双曲开球截面

$$
B_a(r)=P_t\cap\{z:d_{\mathbb H^3}(z,z_a)<r\}.
$$

选择同一个 $r>0$，使全部 $B_a(r)\subseteq N_a$，并使其避开所有不含 $z_a$ 的主侧面。这样的选择存在：邻域相对开；每个不含中心的侧面是紧闭集，与中心具有严格正距离；代表和侧面均有限。同块不同中心之间也可取两两不交的球截面，因为这些中心的有限两两距离严格正。cap 是保留的边界，不产生额外配对生成识别。

令 $S=\bigcup_{a\in F_x}\{t_a\}\times B_a(r)$。若一个实际面生成识别可用于 $(t,z)\in S$，其面必须含相应中心 $z_a$。原始面映射将该中心送到另一个实际代表 $z_b$，因为它不改变商类。整张实际面上的双曲等距性给出

$$
d_{\mathbb H^3}(I_{t,f}z,I_{t,f}z_a)
=d_{\mathbb H^3}(z,z_a)<r.
$$

这里实际侧面在其全测地支撑平面中凸，所以面内测地段也是环境测地段，面内距离等于环境双曲距离。因此目标属于 $B_b(r)$。反向用实际逆配对得到同样结论。沿生成、反身、对称、传递保持成员资格，得到 $\pi^{-1}(\pi(S))=S$。

$S$ 在实际带标签不交并中开，故 $W=\pi(S)$ 在原始商拓扑中开，并且 $x\in W\subseteq U\cap V$。这是同一个商映射的饱和开像，不是用展开重新定义商拓扑。经 $H$ 拉回，$H^{-1}(S)$ 同样在字面原始 $X$ 中开且 $R$-饱和，其商像通过 $\overline H$ 对应 $W$。

任意 $a,b\in F_x$ 的商像相等，因而原始生成关系的等价闭包提供一条有限的面生成及逆生成链，所有中间代表仍在 $F_x$。反身步骤可省略，对称步骤反向走链，传递步骤拼接链。因此这些实际代表通过实际面关联可达。这一结论来自原始关系，不要求先证明某个图卡、link 或度量连通。

### 19.2 面片相等留下的两个环境延拓

设 $n$ 为单位类空法向，$P=\mathbb H^3\cap n^\perp$。若 $A,C\in G$ 在 $P$ 的非空相对开片上相等，则

$$
A=C\quad\hbox{或}\quad A=C r_n,\qquad
r_n(v)=v-2L(n,v)n.
$$

为证明开片张成 $n^\perp$，取片内一点 $v$ 及 $v^\perp\cap n^\perp$ 中两个正交单位向量 $u_1,u_2$。对充分小的 $s>0$，$v$ 与 $\cosh s\,v+\sinh s\,u_i$ 都在该片内。三者线性无关，故张成三维非退化空间 $n^\perp$。于是 $C^{-1}A$ 在此空间上恒等。Lorentz 保持性使其保持正交补 $\mathbb Rn$；单位方程使 $n$ 的像为 $n$ 或 $-n$，分别得到恒等或 $r_n$。

若 $A,C$ 将同一源半空间送入同一目标半空间，反射情形被排除，因 $r_n$ 交换源面的两侧。面片可以来自 old edge、cap 侧边或 cap 顶点：一个非退化凸侧面在每个点附近都有相对内部点，球截面与它相交就包含支撑平面的非空相对开片。此处不要求中心本身处于面内部，也不要求 cap 外另有一个块。

### 19.3 两次展开的侧符号及关系传播

对 $a\in F_x$，令 $A_a=K_aJ_a^{-1}$。若实际面关联 $I$ 把 $a$ 送到 $b$，共同球截面的面片上有

$$
J_a z=J_b Iz,\qquad K_a z=K_b Iz,
$$

因为 $d,e$ 都在实际商上单值。故 $A_a,A_b$ 在共同 $d$-展开面片上相等。为两次展开的支撑面各选一个单位法向；记 $a$ 块内侧的符号为 $\epsilon_a^d,\epsilon_a^e\in\{-1,1\}$。输入的相反侧放置给出

$$
\epsilon_b^d=-\epsilon_a^d,\qquad
\epsilon_b^e=-\epsilon_a^e,
\qquad \epsilon_b^e\epsilon_b^d=\epsilon_a^e\epsilon_a^d.
$$

$A_a$ 将 $d$-面的 $\epsilon_a^d$ 侧送到 $e$-面的 $\epsilon_a^e$ 侧。$A_b$ 将 $\epsilon_b^d$ 侧送到 $\epsilon_b^e$ 侧，因它是环境线性等距映射，也将另一侧送到另一侧；所以它将 $\epsilon_a^d$ 侧送到 $\epsilon_a^e$ 侧。两者选择同一个法向延拓，第 19.2 节排除反射并给出 $A_b=A_a$。

沿第 19.1 节取得的每条实际生成链传播此等式，全部 $A_a$ 等于某个 $\Lambda\in G$。对任意 $y\in W$ 选代表 $(t,z)\in B_a(r)$，便有 $e(y)=K_a z=\Lambda J_a z=\Lambda d(y)$。不需要选择一棵无环图，也不需要全局 holonomy 平凡；两次展开已经下降，传播只比较已有分支。

唯一性来自整个三维块邻域。每个 $B_a(r)$ 都包含 $P_t$ 的非空三维内部开集；其 $J_a$ 像为双曲空间开片。这样的开片张成 $\mathbb R^4$，可用片内一点及三个独立切向方向的上述双曲曲线证明。因此两个候选 $\Lambda$ 若在 $d(W)$ 上相等，就作为线性映射处处相等。

### 19.4 交叠分量、边界及完成范围

在交叠每个点满足命题条件时，所得唯一 $\Lambda_x$ 局部常值：邻域交集仍开，且包含一个实际块的三维内部片，故两个局部候选必须相等。于是它在每个连通交叠分量上恒定。不同连通分量可以使用不同环境等距映射，不能要求整个不连通交叠共用一个矩阵。

同块不同面的自粘合仍按实际代表与面关联比较；块标签相等不省略关联。若某个固定面关联或稳定子使相反侧条件无法成立，本命题不赋予它图卡资格。仅有面上相等允许一侧恒等、另一侧反射的折叠；相反侧条件必须从实际展开构造或已经证明的局部单射性取得。

有了实际图卡后，空间坐标 $\iota(u)=(\sqrt{1+\|u\|^2},u)$ 中的转移为 $\iota^{-1}\Lambda\iota$，因而有实解析的环境延拓。边界图卡先由环境等距映射把实际 cap 平面与内侧标准化，再限制到相应半空间；不要求一个 $\Lambda$ 全局保持选定的标准半空间。在 old-edge 轴及其两个 cap 端点使用 Cartesian 横向坐标，不能把未定义的极角当作轴上坐标。

这里结算有限实际代表的饱和缩小、生成可达性及固定分支的局部等距比较。它以两次真实分支公式和相反侧放置为明确输入，未构造这些分支，未证明展开的精确商纤维或局部同胚，未申报 Lean kernel、冻结或 atom 覆盖。第 16 节的解析图册、张量下降、曲率、全测地性和同一带标记 $N$ 上的实现仍须在各自接口核验；本节不改变这些完成判据。

## 20. 实际变角旧边展开的精确原始商纤维

沿用第 18 节的原始 $p,K,R,Q,H$、全部实际出现 $O_e$ 及共同 $\varepsilon>0$。对所选全局旧边 $e$，另取第 6 节的原始端点不反转条件，以及实际零缺陷方程

$$
0<\alpha_o<\pi\quad(o\in O_e),\qquad
\sum_{o\in O_e}\alpha_o=2\pi.
$$

角度来自原始六参数块，不作等角替换。第 6 节的两个实际端口对合给出循环枚举 $o_i$，$i\in\mathbb Z/m\mathbb Z$，每个出现恰一次；其出端口配到下一出现的入端口。端点不反转统一有序端点，整面等距运输使全部出现具有同一个 $\ell>0$ 和从起端量起的 $t\in[0,\ell]$。这些数据由原始面配对及其端点运输取得，不把模型关系与原始关系等价作为新增输入。

**命题 20.1（完整闭旧边的实际开管图卡）。** 在原始商开集 $q(U_e)$ 上存在同胚到标准双曲管

$$
\mathcal T_{\ell,\varepsilon}=
\{(\cosh\rho\cosh t,\cosh\rho\sinh t,
\sinh\rho\cos\varphi,\sinh\rho\sin\varphi):
0\le t\le\ell,\ 0\le\rho<\varepsilon,\ \varphi\in\mathbb R\}.
$$

目标取其在未来单位双曲面中的子空间拓扑。该同胚保留原始生成关系的精确纤维及 cap 标记：$B\cap q(U_e)$ 恰对应 $t=0$ 与 $t=\ell$ 的两个端点圆盘。在每个实际出现的整个 collar 上，展开是一个固定的未来 Lorentz 等距映射的限制；相邻出现被放到其公共展开侧面的相反侧。整个闭纵向管不是环境双曲空间的开集；旧边内部及每个端点的进一步局部限制分别给出全空间及半空间图卡。

### 20.1 与实际入出端口一致的三角形参数

对每个出现，取第 17 节实际 Fermi 公式

$$
F_i(t,\rho,\theta)=\cosh\rho\,\gamma_i(t)
+\sinh\rho\,(\cos\theta\,u_i+\sin\theta\,v_i),
\qquad 0\le\theta\le\alpha_i.
$$

将 $\theta=0$ 对准入端口、$\theta=\alpha_i$ 对准出端口。若原法向排序相反，令 $c_i=\cos\alpha_i$、$d_i=\sin\alpha_i$，换成

$$
u_i'=c_i u_i+d_i v_i,\qquad v_i'=d_i u_i-c_i v_i.
$$

三角恒等式使新公式等于旧公式的 $\theta_{\rm old}=\alpha_i-\theta_{\rm new}$，所以此调整保留字面实际点集与正交基。纵向排序独立地按原始有序端类选择；反序时用 $\ell-t$ 及对应反序轴基。

令 $D=\{(s_-,s_+):s_-,s_+\ge0,\ s_-+s_+<\varepsilon\}$，$\rho=s_-+s_+$。定义

$$
k_i(t,s_-,s_+)=
\begin{cases}
F_i(t,\rho,\alpha_i s_+/\rho),&\rho>0,\\
\gamma_i(t),&\rho=0.
\end{cases}
$$

第 17 节的整个实际 collar 等式及参数恢复说明 $k_i$ 是 $[0,\ell]\times D$ 到 $U_{o_i}(\varepsilon)$ 的双射。非轴点的逆为
$s_+=\rho\theta/\alpha_i$、$s_-=\rho-s_+$；轴上两个横坐标都为零，有序 $t$ 仍唯一。

在 $\rho>0$ 处正反公式连续。轴上不要求角度连续：第 18.2 节的估计使法向项统一趋于零，纵向项连续趋于 $\gamma_i(t)$。逆映射的 $\rho=\operatorname{arsinh}(q_i)$ 与第 17 节的 $t$ 恢复式连续；$0\le s_-,s_+\le\rho$ 使逆横坐标在轴上趋于零。离轴时可用 $\theta=\arccos(L(w,u_i)/q_i(w))$ 恢复角度，因 $0\le\theta\le\alpha_i<\pi$。故 $k_i$ 为同胚。

第 18 节同块不同局部边的 collars 不交且相对开。因此保留全部出现标签的有限不交并

$$
M=\coprod_{i=0}^{m-1}([0,\ell]\times D)
$$

经 $k$ 同胚到 $U_e^{\rm geom}$。这一步在同块贡献多次出现时仍保留不同 $i$，没有先把模型标签按块标签合并。

### 20.2 实际生成关系恰对应双向射线识别

令模型有向步 $S$ 将

$$
(i,t,0,\rho)\longrightarrow(i+1,t,\rho,0)
\qquad(0\le\rho<\varepsilon),
$$

其中出现指标模 $m$。原始实际面生成关系 $\mathrm{Gen}_{\rm geom}$ 包含配对的两个方向。在 $M$ 上有精确等式

$$
\mathrm{Gen}_{\rm geom}(k(a),k(b))
\iff S(a,b)\ \lor\ S(b,a).
$$

正向模型步位于源出侧面与目标入侧面。第 18.1 节整面运输保留有序 $t$ 和 $q_i=\sinh\rho$，所以保留 $\rho$。实际端口决定目标是下一出现的入侧面；该边界射线上的 $(t,\rho)$ 恢复唯一，所以源点确实被实际配对送到显示的目标点。逆配对给出反向模型步。

反过来，第 18.3 节严格支撑排除所有非相邻主侧面，cap 上的等式不产生识别。因此每个可用实际生成识别来自该出现的入端口或出端口。$\rho>0$ 时，两相邻侧面的支撑等式分别迫使 $\theta=0$ 或 $\theta=\alpha_i$：扇区内的正弦等式及 $0<\alpha_i<\pi$ 排除其他角。$\rho=0$ 时两侧同时包含轴，三角形中只有零点。原始端口运输给出下一或前一出现，再由整面 $t,\rho$ 保持及参数唯一性得到上述射线步。两个 cap 端点适用同一论证。

加入关系的反向不改变其等价闭包：每个反向步已经由 $\operatorname{EqvGen}S$ 的对称性包含，正向步仍包含于双向关系，两个最小等价闭包相同。实际全闭包限制到 $U_e^{\rm geom}$ 时，也没有域外额外路径：第 18 节的饱和性迫使每个中间代表仍在该集合。将生成、反身、对称、传递提升到该子空间，遂得到

$$
R_{\rm geom}(k(a),k(b))\iff\operatorname{EqvGen}S(a,b).
$$

此式是从原始可用面、整面运输及饱和性推出的结论，不是外加给模型的关系等价假设。

### 20.3 正变角扇展开的全部纤维

令 $\beta_0=0$、$\beta_{i+1}=\beta_i+\alpha_i$，故 $\beta_m=2\pi$ 且前缀和严格递增。在 $\rho>0$ 处令 $\varphi=\beta_i+\alpha_i s_+/\rho$；轴上任选 $\varphi$。模型展开 $\mathcal D:M\to\mathcal T_{\ell,\varepsilon}$ 使用命题中的标准 Fermi 公式。

它在离轴处连续；轴处横向项的范数恰为 $\sinh\rho$，故连续。相同像先由横向范数及 $\sinh$ 在非负半轴单射得到相同 $\rho$，再由 $\cosh\rho\sinh t$ 及 $\sinh$ 单射得到相同 $t$。

若 $\rho>0$，横向方向相等意味着两个 $\varphi$ 模 $2\pi$ 相等。各闭区间 $[\beta_i,\beta_{i+1}]$ 的内部不交；公共端点只有相邻区间端点，以及 $0$ 与 $2\pi$ 的首尾端点。因此同一出现内恢复相同的 $s_-,s_+$，不同出现间恰为相邻射线识别。若 $\rho=0$，全部横坐标为零，沿端口圈把同一 $t$ 的全部轴代表相连。每个方向也被这组正角区间覆盖。于是 $\mathcal D$ 满射，且

$$
\mathcal D(a)=\mathcal D(b)
\iff\operatorname{EqvGen}S(a,b)
\iff R_{\rm geom}(k(a),k(b)).
$$

整个论证包含轴、两个完整端点圆盘和首尾射线，没有把 seam 上相等误当作精确纤维，也没有对半径开域的原始路径只限制两个端点。

### 20.4 开半径商的连续逆及原始 cap 标记

上述连续满射经精确纤维诱导 $M/\operatorname{EqvGen}S$ 到 $\mathcal T_{\ell,\varepsilon}$ 的连续双射。为取得连续逆，固定 $0<r<\varepsilon$，将 $M$ 限制到 $\rho\le r$。这是有限个紧三角形乘闭纵向区间；用它自身的射线关系取商，得到紧空间 $M_r/{\sim_r}$。同一纤维论证给出它到闭半径标准管 $\mathcal T_{\ell,r}^{\rm cl}$ 的连续双射，目标 Hausdorff，故该映射为同胚。

半径在每个射线步及整个等价闭包中保持不变，故 $M_r$ 的包含诱导一个连续映射 $M_r/{\sim_r}\to M/{\sim}$。将它与闭管同胚的逆复合，在相对开目标邻域 $\rho<r$ 上恰等于所求的全局逆，由精确纤维可见。每个 $\rho_0<\varepsilon$ 可选 $\rho_0<r<\varepsilon$，所以逆映射局部连续，进而处处连续。这里没有预设小商具有大商的子空间拓扑，也没有把开管误当紧空间。

$U_e^{\rm geom}$ 在原始几何不交并中开且饱和，因此商映射限制仍是到 $\pi(U_e^{\rm geom})$ 的商映射。具体地，相对开饱和原像也是全源中的开饱和集合，故其商像开。结合 $k$ 及上述精确关系，模型商同胚到这个实际商开集。最后通过同一个 $\overline H$ 拉回 $q(U_e)$，得到命题的原始商同胚。

第 17 节的完整恢复式使两端 cap 等式分别为 $t=0$ 与 $t=\ell$；其他 cap 的支撑在整个所选 collar 上严格为内侧。第 15 节的同一个 $H$ 保留全部 cap 标记，实际配对也保留有序端点，故得到 $B\cap q(U_e)$ 的两个完整端点圆盘，而非另设一个模型边界。端点不反转保证起端和终端沿全部出现不会被同一实际生成路径互换。

### 20.5 固定 Lorentz 分支及两端局部图卡

实际轴基 $A_i,\tau_i,u_i,v_i$ 的 Gram 矩阵是 $\operatorname{diag}(-1,1,1,1)$。定义唯一线性映射 $J_i$，使其把这四个基向量分别送到标准时间、轴向及法平面中角 $\beta_i$ 的正交基

$$
e_0,\quad e_1,\quad
(0,0,\cos\beta_i,\sin\beta_i),\quad
(0,0,-\sin\beta_i,\cos\beta_i).
$$

Gram 矩阵相同给出 Lorentz 等距性；$A_i$ 和 $e_0$ 都在未来分支，故 $J_i$ 保留未来分支。直接代入 Fermi 公式得到 $J_i k_i=\mathcal D|_i$，在整个实际 collar 上使用同一个 $J_i$。

相邻扇区在公共角 $\beta_{i+1}$ 处的内部相位分别为该角之前与之后，差的绝对值均小于 $\pi$。相对于这张全测地面的法向，其正弦符号相反；首尾使用 $2\pi$ 周期性同样成立。故相邻实际块内侧被放到相反侧。这给出第 19 节比较命题在旧边管上的固定分支与两侧输入，并不由面上相等自行推断它们。

在标准管中取 Cartesian 横向坐标 $Z=(Z_1,Z_2)$，则

$$
(t,Z)\longmapsto
(\sqrt{1+\|Z\|^2}\cosh t,\sqrt{1+\|Z\|^2}\sinh t,Z)
$$

同胚到 $[0,\ell]\times\{Z:\|Z\|<\sinh\varepsilon\}$ 所参数化的管，逆纵坐标为 $t=\operatorname{arsinh}(X_1/\sqrt{1+\|Z\|^2})$。在 $0<t<\ell$ 缩小纵向开区间，得到实三维开集；在起端用 $t\ge0$、终端用 $\ell-t\ge0$，并排除另一端，得到半空间中的开集。轴上 $Z=0$ 无角坐标奇点，两个实际 cap 平面就是这两个半空间边界。

本节给出完整实际旧边开管、精确原始商纤维、连续逆、两个端点 cap 标记及固定分支的书面证明。它只使用既有原始端口与端点运输、实际块 collar 及整面半径运输，不宣称新增 Lean 内容准入、kernel 核验、冻结、atom 覆盖或文献原创性。其余点型的图卡、全图册解析结构、张量下降、曲率及同一带标记 $N$ 的度量实现仍需各自完成。

## 21. 原始商的其余点型、实解析图册及实际张量下降

沿用第 15–20 节的同一个原始有限配对、实际六参数块 $P_t$、面等距映射 $I_{t,f}$、生成商 $\pi:X_{\rm geom}\to Q_{\rm geom}$ 和 cap 标记 $B_{\rm geom}$。面配对是原始无不动面的对合；同块不同面的配对仍允许。每条全局旧边满足原始端点不反转，全部实际出现的正内角之和为 $2\pi$。各块保留完整的非退化极面截断面格，参数满足第 17 节的条件。这些条件给出第 20 节的完整实际旧边开管；本节补齐其余点型，并在既有商拓扑上构造实解析图册和正定张量。

**命题 21.1（实际展开图册与张量）。** 在上述条件下，$Q_{\rm geom}$ 有一个带边界实解析图册，其边界恰为 $B_{\rm geom}$。每张图卡先把一个原始商开集同胚展开到双曲开集或双曲半空间中的相对开集，再使用普通三维坐标。展开在每个实际块邻域上是一个固定的未来 Lorentz 等距矩阵的限制；对每个实际可用的面关联，相邻块被放到公共面的相反侧。任意两张展开的转移在每个交叠点附近都是一个未来 Lorentz 等距映射的限制。这些图卡上的双曲切张量因此定义同一个正定实解析张量 $g$。经第 15 节的同一个 $\overline H$，结论拉回字面原始 $(Q,B)$；若另有固定带标记同胚 $r:(Q,B)\to(N,\partial N)$，则通过 $j=\overline H\circ r^{-1}$ 运输到同一个带标记 $N$。

### 21.1 全部八项支撑的字面块刻画

记实际侧面外法向为 $n_f$，cap 外法向为 $V_a$。第 17 节的 Gram 对偶给出

$$
P_t=\{w\in\mathbb H^3:L(w,n_f)\le0\text{ 对全部 }f,
\ L(w,V_a)\le0\text{ 对全部 }a\}.
$$

正向来自原始归一化定义。反向对右侧的实际未来单位点 $w$，令 $\beta_f=L(w,W_f)\ge0$。Gram 对偶重构为 $w=\sum_f\beta_fV_f$。$w\ne0$ 排除全部 $\beta_f=0$，故 $b=\sum_f\beta_f>0$。取 $\lambda_f=\beta_f/b$，则 $\lambda_f\ge0$、$\sum_f\lambda_f=1$，且

$$
(G\lambda)_a=L(w,V_a)/b\le0,\qquad
\sqrt{-L(\sum_f\lambda_fV_f,\sum_f\lambda_fV_f)}=1/b.
$$

因此 $\lambda\in C_x$ 且 $\nu_x(\lambda)=w$。这证明原始归一化像自身的刻画，不另换一个半空间对象。

在每个实际点 $z$，选择足够小的双曲球 $\mathcal B(z,r)$，使所有在 $z$ 严格成立的支撑在整个球上仍严格成立。有限支撑的连续性给出一个共同正 $r$。完整面格于是把局部块精确分为六种：内部点无有效支撑；侧面内部点只有一个 $n_f$；cap 内部点只有一个 $V_a$；cap 侧边内部点只有一个 $n_f$ 和一个 $V_a$；旧边内部点有两个侧面；cap 顶点有两个侧面和一个 cap。最后两种已由第 20 节处理。这里“内部”都是相应面的相对内部，cap 侧边不包含两端顶点。

### 21.2 无配对面点的实际开球及半球

块内部点和 cap 内部点不在任何配对侧面上。因此不存在从这些点出发的面生成步，其整个实际商纤维是单点。取上述小球，并缩小使它不碰任何主侧面；所有附近点也没有可用的面生成步。相应带标签块邻域因而开且饱和，商映射在其上单射。

块内部点的邻域精确为 $\mathcal B(z,r)$。cap 内部点的邻域精确为

$$
\mathcal B(z,r)\cap\{w:L(w,V_a)\le0\}.
$$

商映射限制是同胚：它是连续双射，并且每个源中相对开子集仍在全源中开且饱和，故商像开。分别取恒等展开，得到实际球和半球图卡。cap 内部点图卡的边界是原始 cap 等式；没有把 cap 作为另一个被粘合的面。

### 21.3 唯一配对面的两个实际代表

侧面内部点或 cap 侧边内部点 $z\in P_t$ 恰位于一个配对侧面 $f$。令 $p(t,f)=(u,g)$，$z'=I_{t,f}z$。实际面映射保留完整面格，故 $z'$ 也只位于主侧面 $g$；在 cap 侧边情形，它还位于对应的唯一 cap。反向面配对把 $z'$ 送回 $z$。因此其实际商纤维恰为

$$
\{(t,z),(u,z')\}.
$$

这两个带标签点不同。不同块时标签已区分；同块时，无不动面条件给出 $f\ne g$，而各点位于唯一主侧面的相对内部或 cap 侧边内部。若两点相同，它会同时位于两个不同主侧面，与该点型矛盾。因此同块配对也确有两个不同中心，不能把它压成一个自作用。

在两个中心取同一个小半径 $r>0$，使全部非 incident 支撑保持严格。同块时再取 $2r<d(z,z')$，使两块球截面不交。记

$$
N=P_t\cap\mathcal B(z,r),\qquad
N'=P_u\cap\mathcal B(z',r),\qquad
S=(\{t\}\times N)\cup(\{u\}\times N').
$$

任何可用于 $S$ 中点的实际面生成步只能来自 $f$ 或 $g$。它保留到中心的双曲距离，因而把球截面的面部分送到另一个球截面；逆步亦然。故 $S$ 在全源中开且对整个生成等价闭包饱和，$W=\pi(S)$ 是原始商开集。$S$ 内全部关系只有恒等和这对互逆面识别；一个严格内侧点不产生额外步，cap 等式也不产生步。

### 21.4 固定相反侧延拓及 cap 内侧运输

将 $I=I_{t,f}$ 按第 15.1 节延拓到源、目标的三维 Lorentz 支撑子空间，得到 $U:n_f^\perp\to n_g^\perp$。该延拓保留整个规定面，而不只保留三个所选基点。定义环境线性映射 $E$，使

$$
E|_{n_f^\perp}=U,\qquad E n_f=-n_g.
$$

正交直和分解给出 Lorentz 等距性；源面上的一个未来单位点被送到目标未来单位点，故 $E$ 保留未来分支。对任意源块点 $w$，

$$
L(Ew,n_g)=-L(w,n_f).
$$

因此 $E$ 把源块内侧放到目标面外侧。以目标环境为公共展开空间，源分支取固定 $E$，目标分支取恒等；它们在整个公共面上相等，并将两个块内侧放到相反侧。

在 cap 侧边情形，令源、目标对应的 cap 外法向为 $V_a,V_b'$。由于 $a\ne f$、$b\ne g$，实际 Gram 等式给出

$$
L(V_a,n_f)=L(V_b',n_g)=0.
$$

所以两个 cap 法向分别属于两张侧面支撑子空间。实际侧面中的 cap 边是非退化的闭测地线段，其二维线性张成分别为 $n_f^\perp\cap V_a^\perp$ 和 $n_g^\perp\cap(V_b')^\perp$。$U$ 保留整条规定 cap 线段，因此保持这两个二维张成。在相应三维侧面支撑子空间中，张成的正交补分别为 $\mathbb RV_a$ 和 $\mathbb RV_b'$，故 $UV_a=\pm V_b'$。法向都为单位向量。取源六边形内部一点，它的源 cap 支撑严格负，其像是目标六边形内部点，目标 cap 支撑也严格负；负号会使两者符号相反。因此

$$
EV_a=UV_a=V_b',\qquad L(Ew,V_b')=L(w,V_a).
$$

这证明 cap 内侧和 cap 平面确实由同一个相反侧延拓保持；没有把它们另加为延拓的条件。

定义 $D:S\to\mathbb H^3$，在源分支取 $Ew$，在目标分支取 $w$。它连续并保持实际关系。侧面内部情形，两个展开半球合起来精确为 $\mathcal B(z',r)$。cap 侧边情形，由刚证明的 cap 运输及两侧支撑，它们合起来精确为

$$
\mathcal B(z',r)\cap\{w:L(w,V_b')\le0\}.
$$

同分支像相等给出原点相等；不同分支像相等时，两个相反的侧面支撑必须都为零，故两点在配对面上，并由 $E|_f=I$ 恰按实际生成步识别。因此 $D$ 的全部相等纤维恰为 $R_{\rm geom}|_S$，诱导一个连续双射 $d:W\to D(S)$。

其逆连续可在每个展开点附近由较小闭球检验。选择 $0<s<r$，使该点位于 $\mathcal B(z',s)$。把两个球截面限制到闭半径 $s$，得到有限个紧半球或四分之一球；它们按自身实际面关系的商紧。相同精确纤维给出到展开闭球或闭半球的连续双射，目标 Hausdorff，故为同胚。闭截面到 $S$ 的连续包含诱导到 $W$ 的连续映射；与闭球同胚的逆复合，在 $\mathcal B(z',s)$ 内恰为 $d^{-1}$。这些较小开球覆盖目标，故 $d^{-1}$ 连续。此论证不预设小商具有大商的子空间拓扑。

### 21.5 所有点型的覆盖与解析转移

上述四种图卡与第 20 节的旧边管覆盖全部实际点。旧边内部取排除两端的纵向开区间；cap 顶点取排除另一端的管端邻域。它们都下降到既有原始商开集；每个实际代表附近都有一个固定 Lorentz 分支。四种新图卡的两侧性质已由 $E$ 的法向符号取得，旧边管的两侧性质由第 20.5 节取得。因此任意两张展开在每个交叠点都满足命题 19.1 的全部输入。该命题给出一个更小的商开邻域以及单个 $\Lambda\in G$，使

$$
e\circ d^{-1}=\Lambda
$$

在该邻域的展开像上成立。这是整片交叠的局部等式；不把仅逐扇区选取的不同矩阵当作转移。

对内部图卡，使用空间坐标

$$
\kappa(X)=X_{\rm sp},\qquad
\kappa^{-1}(z)=(\sqrt{1+\|z\|^2},z).
$$

对边界图卡，先用一个固定未来 Lorentz 矩阵 $C$ 把实际 cap 外法向送到 $-e_3$，再使用 $\kappa$。这样的 $C$ 由 cap 平面上的一个未来单位点、两个切向单位向量及外法向的 Lorentz 正交基构造。cap 内侧于是精确为 $z_3\ge0$，得到标准半空间中的相对开坐标域。各图卡的坐标转移局部为

$$
z\longmapsto\kappa\bigl(A\kappa^{-1}(z)\bigr),\qquad
A=C_e\Lambda C_d^{-1}\in G,
$$

其中内部图卡可取 $C=1$。平方根的自变量处处严格正，故此公式在整个 $\mathbb R^3$ 实解析；其逆由 $A^{-1}$ 给出。在边界交叠处，转移保持实际 cap 标记及内侧，因此限制到标准半空间的相对开域，并由同一公式解析延拓到边界外侧。实解析性质在开邻域上局部成立，足以构成带边界实解析图册，不要求整张不连通交叠使用一个矩阵。

实际商已由第 14–15 节得到 Hausdorff 性及紧性。刚构造的局部图卡给出开覆盖；紧性选出有限子覆盖，而每个球或半球坐标域有可数基，其原像的有限并为整个商的可数基。因此图册使用的是原始商的 Hausdorff、第二可数拓扑。所有边界坐标等式逐点对应实际 cap，且内部点的图卡是普通开球，故流形边界恰为 $B_{\rm geom}$。

### 21.6 显式实际张量及同一标记的运输

双曲面在 $X$ 的切空间是 $X^\perp$，$L$ 在其中正定。空间坐标中的实际切张量为

$$
\gamma_z(u,v)=u\cdot v-
\frac{(z\cdot u)(z\cdot v)}{1+\|z\|^2}.
$$

这是对 $\kappa^{-1}$ 求导后将两个导数代入 $L$ 得到的公式。Cauchy–Schwarz 给出

$$
\gamma_z(u,u)\ge\frac{\|u\|^2}{1+\|z\|^2}>0\qquad(u\ne0).
$$

其系数对称且实解析，分母处处正。边界处也在整个三维切空间使用同一公式，不只在 cap 的二维切空间定义张量。

在每张坐标图中用 $\gamma$ 定义 $g$。对任意交叠，前述解析转移来自固定 Lorentz 等距映射 $A$。链式法则及 $L(A\xi,A\eta)=L(\xi,\eta)$ 给出

$$
\gamma_{F(z)}(DF_z u,DF_z v)=\gamma_z(u,v),\qquad
F=\kappa A\kappa^{-1}.
$$

所以两张图对同一个实际切向量给出相同张量值；$g$ 良定义、正定、对称且实解析。每个实际块分支的拉回就是该块上 $L$ 的切限制。这是张量下降的具体关系，并非以“各图已经等距”为前提再声明下降。

最后沿同一个 $\overline H$ 运输图册、cap 标记和张量到 $(Q,B)$。若已给定 $r$，在 $N$ 上使用 $\phi\circ j$ 和 $g_N=j^*g$，其中 $j=\overline H\circ r^{-1}$；它保留字面标记并使 $j$ 成为所运输解析结构的等距微分同胚。若 $N$ 另外预先指定一个光滑或解析 atlas，本节没有证明它与运输 atlas 相容。

本节结算其余实际点型的精确商图卡、全图册的解析转移及实际张量下降的书面义务，沿用标准双曲拼接理论，不申报文献原创性或 Lean kernel 核验。曲率张量、全测地性、有限块路径链距离与该张量长度距离的相等、反射双倍及测地完备性仍各有其证明义务；这里没有用解析张量的存在代替这些结论，也没有新增冻结或消化覆盖。

## 22. 实际下降张量的曲率、全测地 cap 及反射双倍

沿用第 21 节的原始有限面配对、真正非退化紧截断块、完整面格、实际相容面等距映射、原始旧边不反转及全部实际出现角和 $2\pi$。记

$$
M=Q_{\rm geom},\qquad C=B_{\rm geom}.
$$

本节的输入是第 21 节已经构造的实际商解析图册和下降张量 $g$：每张展开 $\mathcal D_\alpha:U_\alpha\to O_\alpha$ 是原始商开集上的同胚，像为 $\mathbb H^3$ 的开集或一个双曲闭半空间的相对开集；在每个交叠点附近，展开转移是一个固定的未来 Lorentz 矩阵；边界像恰为实际 cap 支撑平面，且保留 cap 内侧。张量在每张展开中是 Lorentz 形式的切限制。这里使用整个实际半空间图卡，包括 cap 侧边和 cap 顶点，不再仅凭逐块等距重建图册。

第 16 节已经给出曲率、全测地边界和双倍的概要。本节补明联络及曲率符号、反射转移的相容性、双倍商图卡的连续逆和紧双倍的测地延伸。有限块链距离与 $g$ 的路径距离相等不作为输入，也不在本节结算。

**命题 22.1（同一原始标记上的曲率及实际双倍）。** 在上述条件和第 21 节的实际图册结论下，$g$ 的截面曲率处处为 $-1$，$C$ 是全测地边界。两份同一个 $M$ 仅沿同一个 $C$ 逐点识别所得的拓扑双倍具有与该商拓扑相容的无边界实解析图册和正定实解析度量 $g^{\rm d}$；两份 $M$ 的包含均拉回 $g^{\rm d}$ 为 $g$，交换两份的对合是反射等距映射。该双倍紧，各连通分量测地完备。通过第 15、21 节的同一个 $\overline H:(Q,B)\to(M,C)$ 和同一个 $r:(Q,B)\to(N,\partial N)$，这些结构运输到字面原始 $(Q,B)$、同一个带标记 $N$ 及它们各自的逐点双倍。运输结构不自动与 $N$ 上另行预选的光滑或解析图册相容。

### 22.1 Lorentz 切投影给出的实际 Levi–Civita 联络

在 $\mathbb R^{3,1}$ 中采用

$$
L(X,Y)=-X_0Y_0+X_1Y_1+X_2Y_2+X_3Y_3,
\qquad
\mathbb H^3=\{X:L(X,X)=-1,\ X_0>0\}.
$$

在 $X\in\mathbb H^3$，切空间为 $X^\perp$，$L$ 的切限制记作 $g_{\mathbb H}$。任意环境向量 $W$ 的 Lorentz 切投影为

$$
P_XW=W+L(W,X)X.
$$

因为 $L(X,X)=-1$，右侧与 $X$ 正交，并且它与 $W$ 的差在法向直线 $\mathbb RX$ 上。记 $D$ 为环境的平坦联络；对切向量场 $U,V$，由 $L(V,X)=0$ 微分得到

$$
L(D_UV,X)=-L(V,U)=-g_{\mathbb H}(U,V).
$$

因此投影联络及环境分解是

$$
\nabla_UV=P_X(D_UV)=D_UV-g_{\mathbb H}(U,V)X,
\qquad
D_UV=\nabla_UV+g_{\mathbb H}(U,V)X. \tag{22.1}
$$

这个联络无挠：$D_UV-D_VU=[U,V]$，而被减去的两项相等。它与 $g_{\mathbb H}$ 相容，因为 $L$ 在环境中常系数，且 $L(X,V)=L(X,W)=0$，所以

$$
U\,g_{\mathbb H}(V,W)
=g_{\mathbb H}(\nabla_UV,W)
+g_{\mathbb H}(V,\nabla_UW).
$$

无挠和度量相容唯一确定 Levi–Civita 联络，故式 (22.1) 正是双曲切张量的 Levi–Civita 联络，而不是另外指定的连接。

固定 Lorentz 矩阵 $A$ 保留切投影：

$$
P_{AX}(AW)=A(P_XW).
$$

其导数也是 $A$，环境微分与这个常矩阵交换。因此式 (22.1) 在第 21 节的每个局部交叠上被同一个 $A$ 运输。它给出实际下降张量 $g$ 的同一个 Levi–Civita 联络。边界图卡的系数由其环境双曲开集解析延拓；延拓在相对开半空间上相同的两个系数，其导数在内部相同，并由连续性在边界相同。因此联络和以下曲率公式在整个三维边界切空间上也有确定的值。

### 22.2 Gauss 计算及曲率的负号

固定曲率约定

$$
R(U,V)W=\nabla_U\nabla_VW-\nabla_V\nabla_UW-\nabla_{[U,V]}W.
$$

环境联络平坦，因此

$$
0=D_UD_VW-D_VD_UW-D_{[U,V]}W.
$$

用 (22.1) 展开并取切投影。$D_UX=U$，故 $D_U(g_{\mathbb H}(V,W)X)$ 的切向部分为 $g_{\mathbb H}(V,W)U$；对调 $U,V$ 同理。其余切向部分正好是 $R(U,V)W$。于是

$$
0=R(U,V)W+g_{\mathbb H}(V,W)U-g_{\mathbb H}(U,W)V,
$$

即

$$
R(U,V)W=-g_{\mathbb H}(V,W)U+g_{\mathbb H}(U,W)V. \tag{22.2}
$$

这也是本例的 Gauss 方程；法向 $X$ 是单位类时向量，$L(X,X)=-1$，不能把欧氏单位法向的正号直接搬入本式。对线性无关的 $U,V$，用上述曲率约定定义

$$
K(U,V)=
\frac{g_{\mathbb H}(R(U,V)V,U)}
{g_{\mathbb H}(U,U)g_{\mathbb H}(V,V)-g_{\mathbb H}(U,V)^2}.
$$

分母由正定性严格正，式 (22.2) 的分子是该分母的负数，所以 $K=-1$。局部 Lorentz 转移保持联络及张量，故这个结论下降到 $M$；边界点以解析延拓在其完整三维切空间计算，仍有相同公式。此计算不要求 $M$ 可定向，也不要求其全局 holonomy 平凡。

### 22.3 每张实际 cap 平面的全测地性

一张边界展开的 cap 外法向 $n$ 满足 $L(n,n)=1$，其支撑平面及内侧为

$$
H_n=\{X\in\mathbb H^3:L(X,n)=0\},
\qquad H_n^- =\{X\in\mathbb H^3:L(X,n)\le0\}.
$$

在 $H_n$ 上，常环境向量 $n$ 与 $X$ 正交，故它是 $\mathbb H^3$ 内沿 $H_n$ 的单位法向。若 $U$ 切于 $H_n$，则 $D_Un=0$ 且 $g_{\mathbb H}(U,n)=0$，所以 (22.1) 给出 $\nabla_Un=0$。对两个切于 $H_n$ 的向量场 $U,V$，第二基本形式因此为

$$
\mathrm{II}_{H_n}(U,V)
=g_{\mathbb H}(\nabla_UV,n)
=-g_{\mathbb H}(V,\nabla_Un)=0. \tag{22.3}
$$

也可直接检查测地线。若 $X\in H_n$、$v\in T_XH_n$ 且 $c^2=g_{\mathbb H}(v,v)>0$，则

$$
\gamma(t)=\cosh(ct)X+\frac{\sinh(ct)}{c}v
$$

满足 $\gamma(0)=X$、$\dot\gamma(0)=v$，具有恒定速度 $c$，并满足 $\ddot\gamma=c^2\gamma$。由 (22.1)，$\nabla_{\dot\gamma}\dot\gamma=0$。同时 $L(\gamma(t),n)=0$，故它在其所在局部图卡内始终位于 cap 平面；零初速度对应常曲线。

第 21 节已经把所有实际边界点展开到同一类相对开半空间，$C$ 的像恰为 $H_n$ 中的相对开集。所以 (22.3) 在 cap 面内部、cap 侧边和 cap 顶点均适用。后三者在实际商中不是额外的 Riemannian 角点；它们只是同一个光滑边界在原始块剖分中的不同位置。局部第二基本形式零由交叠转移保持，故 $C$ 全测地。

### 22.4 cap 法向运输及反射的精确相容关系

对单位类空 $n$ 定义环境反射

$$
S_nX=X-2L(X,n)n. \tag{22.4}
$$

直接展开可得 $L(S_nX,S_nY)=L(X,Y)$ 和 $S_n^2=1$。它逐点固定 $n^\perp$，交换 $H_n^-$ 与 $H_n^+$，并在 $n$ 方向上取负号。$H_n$ 含未来单位点，且这些点被固定；因此它保留整个未来双曲面分支。于是 $S_n$ 是 $\mathbb H^3$ 的解析反射等距映射。

设两张边界展开在一个实际边界交叠点附近满足

$$
\mathcal D_\beta=A\mathcal D_\alpha,
$$

其中 $A$ 是第 21 节给出的单个固定未来 Lorentz 矩阵。$A$ 把该点附近的 cap 平面开片送到目标 cap 平面开片，并保留内侧。双曲平面中任意非空相对开片的线性张成为其三维 Lorentz 支撑子空间：取其中一点及两个独立切向方向；若一个线性泛函在该开片上为零，沿两条切向曲线微分可知它在该点及这两个切向方向上为零，而这三者构成支撑子空间的基。故

$$
A(n_\alpha^\perp)=n_\beta^\perp,
\qquad A n_\alpha=\pm n_\beta.
$$

在这个交叠内取一个实际内部点 $Y$。源、目标内侧支撑都严格负；若取负号，Lorentz 等距性会给出

$$
L(AY,n_\beta)=-L(Y,n_\alpha)>0,
$$

与目标内侧相反。因此 $A n_\alpha=n_\beta$。将它代入 (22.4)，得到环境上的精确恒等式

$$
A S_{n_\alpha}=S_{n_\beta}A. \tag{22.5}
$$

这里的 $A$ 是交叠点附近的矩阵，不要求整张不连通交叠使用一个全局矩阵。式 (22.5) 足以把这个局部转移同时延到反射两侧。

### 22.5 字面双倍商、实际开图卡及连续逆

取两份带符号的同一个 $M$，仅作逐点边界识别：

$$
M^{\rm d}=(M\times\{+,-\})/\sim_{\rm d},
\qquad (b,+)\sim_{\rm d}(b,-)\quad(b\in C).
$$

除此以外只有恒等识别。记商映射为 $q^{\rm d}$，两份包含为 $\iota_\pm$。这是真实拓扑双倍；没有新增块面配对、群作用或旧边关系。

$M$ 紧且 Hausdorff，$C$ 作为流形边界是闭集。两份 $M$ 的有限不交并紧，故 $M^{\rm d}$ 紧。它也 Hausdorff：遗忘符号给出连续映射 $c:M^{\rm d}\to M$。当两个不同双倍点的 $c$ 像不同，用 $M$ 中不交开邻域的原像分离；当 $c$ 像相同而双倍点不同，该像属于 $M\setminus C$，在这个开集内选择一个开邻域，其两份像分别是双倍中的不交开集。边界同一点的两份已经识别，不属于需要分离的情形。

对 $M\setminus C$ 的每个内部图卡，在两份上分别使用原展开。其像在双倍中开，因为原像只有指定的一份，且与边界无交。

对 $b\in C$ 选择一张第 21 节的边界图卡，缩小为

$$
\mathcal D:U\xrightarrow{\cong}V\subset H_n^-,
\qquad \mathcal D(U\cap C)=V\cap H_n,
$$

其中 $U$ 是 $M$ 中的开集，$V$ 在 $H_n^-$ 中相对开。$U\times\{+,-\}$ 是开且对双倍识别饱和的集合，故其商像 $U^{\rm d}$ 是原始双倍拓扑中的开集。在两份上定义

$$
\mathcal D^{\rm d}(\iota_+x)=\mathcal D(x),
\qquad
\mathcal D^{\rm d}(\iota_-x)=S_n\mathcal D(x). \tag{22.6}
$$

在边界点两式相同，故它由商的泛性质下降为连续映射

$$
\mathcal D^{\rm d}:U^{\rm d}\longrightarrow V^{\rm d}:=V\cup S_nV.
$$

$V^{\rm d}$ 在 $\mathbb H^3$ 中开：不在 $H_n$ 上的点使用所在开半空间的相对开性；在 $H_n$ 上的点，$V$ 含一个小球与闭内半空间的交，反射后另一份含同一小球的外半空间部分，两者覆盖整个小球。

每份上的映射单射。若两份映到同一点，则该点同时属于 $H_n^-$ 和 $H_n^+$，所以在 $H_n$ 上；反射固定它，$\mathcal D$ 的单射性使两个源点是同一个 $x\in U\cap C$。这正是双倍商的唯一跨份识别。因此 (22.6) 是到 $V^{\rm d}$ 的双射。

其逆连续也可直接核对。在 $V^{\rm d}$ 的两个相对闭集

$$
V=V^{\rm d}\cap H_n^- ,\qquad
S_nV=V^{\rm d}\cap H_n^+
$$

上，分别定义

$$
X\longmapsto\iota_+(\mathcal D^{-1}X),\qquad
X\longmapsto\iota_-(\mathcal D^{-1}S_nX).
$$

它们连续，并在交集 $V\cap H_n$ 上因同一点边界识别而相同。有限闭集粘合引理给出连续的共同逆。因此双倍图卡确是实际开商域上的同胚；这里没有从张量的偶性推出拓扑图卡，也没有假设某个子商已经拥有正确的子空间拓扑。

### 22.6 双倍图册、张量及全部边界剖分层

在两个 seam 图卡的交叠边界点附近，使用第 22.4 节的同一个 $A$。正份上转移为 $A$；负份上，式 (22.5) 给出

$$
S_{n_\beta}\mathcal D_\beta
=S_{n_\beta}A\mathcal D_\alpha
=A S_{n_\alpha}\mathcal D_\alpha.
$$

所以在包含 seam 两侧的整个小邻域上，双倍展开转移仍是一个 $A$。在远离 seam 的交叠上，两张图卡的展开各由原展开或原展开后接一次固定反射组成；其转移是相应的固定 Lorentz 矩阵组合。例如，负份内部原展开与 seam 反射展开之间的转移是 $A S_{n_\alpha}$。这处理了全部交叠，而不是只证明 seam 本身的映射相同。

对双倍展开再使用第 21 节的空间坐标 $\kappa$。所有转移局部为 $\kappa A\kappa^{-1}$，因而实解析；所有 seam 图卡的像是完整双曲开集，所以新流形没有边界。紧性给出有限图卡子覆盖，各坐标域的可数基共同给出第二可数性，故这确是双倍原商拓扑上的实解析流形。

在每张双倍展开中取 $L$ 的切限制。固定 Lorentz 转移保留它，因此定义正定实解析张量 $g^{\rm d}$。正份的拉回是 $g$；负份由 $S_n$ 的 Lorentz 等距性也拉回为 $g$。同一投影联络和式 (22.2) 给出双倍处处截面曲率 $-1$，包括 seam 点。交换两份的对合 $\tau$ 在 seam 展开中为 $S_n$，在两份内部对应原图卡之间为恒等模型映射，故它是实解析等距对合，固定点集恰为同一个 seam $C$。

cap 剖分的多块出现已包含在这些实际半空间图卡中。具体地，cap 面内部每份贡献一个半球，双倍给完整球；cap 侧边每份的两个直角四分之一球先经实际侧面识别填成一个半球，两份共四个四分之一球填成球；cap 顶点每份的全部实际旧边出现，按第 20 节的一个 $2\pi$ 正角圈填成半球，两份半球沿同一个 cap 平面填成球。用旧边领圈的轴向参数看，反射把端点内侧轴向延到外侧；横向的出现角圈在每一侧仍各是同一个 $2\pi$ 圈，不把两侧的角串接成 $4\pi$。在球面 link 中相应是两个圆半球沿赤道成为 $S^2$。同块的重复出现仍按实际出现区分；没有把两个不同代表误认成一块，也没有另加 seam 点识别。这些描述由已证半空间图卡及 (22.6) 给出，不作为取代它们的 link 假设。

### 22.7 紧双倍的测地完备及 Hopf–Rinow 条件

双倍的紧性已直接来自有限紧块的实际商和两份逐点边界识别。它现在是无边界的有限维光滑 Riemannian 流形，故可以在它的单位切丛上使用普通测地方程。

先核对单位切丛

$$
S M^{\rm d}=\{(x,v):g_x^{\rm d}(v,v)=1\}
$$

紧。选择有限个切丛坐标平凡化，其底空间紧子集 $K_i$ 覆盖整个紧底空间，并各包含在相应图卡内。在 $K_i$ 上，正定张量矩阵的最小特征值有正下界 $a_i>0$。单位向量的坐标因此满足 $\|v\|^2\le a_i^{-1}$；它们组成 $K_i$ 与这个闭有界向量球之积中的闭集，故紧。有限个这样的紧集覆盖 $S M^{\rm d}$，所以单位切丛紧。

Levi–Civita 联络定义光滑测地喷流。在切丛坐标中，其方程为

$$
\dot x^k=v^k,\qquad
\dot v^k=-\Gamma^k_{ij}(x)v^iv^j.
$$

度量相容给出沿其积分曲线

$$
\frac{d}{dt}g^{\rm d}(v,v)=2g^{\rm d}(\nabla_vv,v)=0,
$$

故该喷流切于单位切丛。紧、无边界流形上的光滑向量场是完备的：局部存在唯一性给每个点一个在正负小时间内可用的流邻域；紧性取有限覆盖及共同正时间。沿任何积分曲线可用这个统一时间不断续接，因此有限时间不能成为最大存在区间的端点。这应用于 $S M^{\rm d}$，得到全部单位速度测地线在 $\mathbb R$ 上存在。任意非零速度测地线按其恒定速度作时间缩放归于单位速度情形；零速度曲线为常曲线。于是每个初始切向量对应的双倍测地线都能双向无限延伸，各连通分量测地完备。

也可从 Hopf–Rinow 核对同一结论的标准条件。每个连通分量是无边界、连通、有限维的光滑正定 Riemannian 流形，并且是紧底空间的闭子集。其 Riemannian 路径距离取该张量的分片光滑曲线长度下确界。任意一点经有限个坐标线段可达的集合及其补集都开，故连通性保证每两点之间存在这样的有限分片光滑路径，距离有限。它诱导原流形拓扑：在一个较小凸坐标球上，正定张量与欧氏张量有上下常数界；直线段给局部距离上界，而从更小坐标球退出较大坐标球的曲线有统一正长度下界，排除从远处绕行破坏局部拓扑的可能。因此该连通分量是紧度量空间，进而距离完备。Hopf–Rinow 的“Riemannian 距离完备等价于测地完备”适用。这个距离是双倍张量自身的路径距离；这里没有把它认作尚待校准的实际块链距离。

若原空间不连通，以上完备结论逐双倍连通分量成立；跨分量的内在路径距离为 $+\infty$。原空间带边界时，双倍测地线可穿过 seam 进入另一份；双倍的完备性并不声称原空间内的所有测地线都可留在同一份中无限延伸。若某原分量无边界，其双倍就是该分量的两份不交副本，本论证同样适用。

### 22.8 同一原始商、同一标记及结论范围

第 21 节使用的同一个 $\overline H:(Q,B)\to(M,C)$ 是运输图册的等距微分同胚；把每份都用 $\overline H$ 映射，因它逐点保持边界对应，得到两个实际双倍之间的同胚

$$
\overline H^{\rm d}:D(Q,B)\longrightarrow M^{\rm d}.
$$

同样，对固定的 $j=\overline H\circ r^{-1}$，两份上的 $j$ 下降为

$$
j^{\rm d}:D(N,\partial N)\longrightarrow M^{\rm d}.
$$

在 $(Q,B)$ 和 $N$ 上使用第 21 节的运输图册，并在它们的字面双倍上拉回本节图册及 $g^{\rm d}$。于是 $\overline H^{\rm d}$ 和 $j^{\rm d}$ 是所运输结构的等距微分同胚；曲率、全测地边界和双倍测地完备性随之保留。这保持原始商和原始标记，没有借一个无关双曲流形替换 $N$。若 $N$ 另外预选图册，则该字面标记相对于预选图册光滑或解析仍需单独证明；即使存在某个其他平滑化对应，也不能代替这个相容性义务。

本节沿用标准双曲几何和全测地边界加倍方法。部分截断剖分、面一致性及非紧端完备方程的文献范围仍按第 16.6 节的 [Frigerio–Petronio](https://arxiv.org/abs/math/0109012v1) 对应；本节只用已经建立的紧、完全截断实际图册。Hopf–Rinow 使用其无边界连通 Riemannian 流形版本；本节已经逐项给出这些条件，测地完备性另由上面的紧单位切丛论证直接给出。

本节完成的是在第 21 节条件之上的书面曲率、全测地性、实际反射双倍及紧双倍测地完备证明。有限块链距离的精确校准、预选图册相容性、非紧端和退化块仍不由本节结算；本节不申报文献原创性、Lean kernel 核验、冻结或 atom 覆盖。
