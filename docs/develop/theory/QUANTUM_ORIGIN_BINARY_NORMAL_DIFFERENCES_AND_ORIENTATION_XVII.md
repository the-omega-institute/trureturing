# 二元法向差分、连通射线与量子定向

## 175. Unsplit normal differences without a supplied Bell resource

### 175.1 The unchanged domain and the smaller binary relation

**Definition 175.1 (the original finite carriers and an unsplit difference).** Retain exactly [XVI173.1][Q175XVI]: a fixed integer $n\ge2$, the actual real spaces $W_N=\operatorname{Herm}_{n^N}(\mathbb C)$ at every finite $N$, closed convex cones $C_N$, the scalar $W_0=\mathbb R,C_0=\mathbb R_+$, complete ambient trace duals, every minimum/maximum tensor bound, actual positive permutations and their positive inverses, and canonical reassociation. The trace pairing is $\langle X,Y\rangle=\operatorname{Tr}(XY)$. Initially no pointedness, generation, trace positivity, transpose reciprocity or positive matrix operation is assumed.

For any closed convex cone $K\subseteq E_d:=\operatorname{Herm}_d(\mathbb C)$, let

$$
\begin{aligned}
\mathsf A(K):\quad &X\in K,\ Y\in K^*,\ \langle X,Y\rangle=0,\\
&\operatorname{rank}(X-Y)=1
\quad\Longrightarrow\quad X=0\ \text{or}\ Y=0,\\
\mathsf N(K):\quad &\exists X\in K\ \exists Y\in K^*,\quad\langle X,Y\rangle>0.
\end{aligned}
\tag{175.1}
$$

The rank is the ordinary complex matrix rank, not Schmidt rank, a tensor rank or native extremality. Both signs of a Hermitian rank-one difference are included. The universal condition constrains a pair only when its zero pairing and one-dimensional difference both hold. It uses the scalar pairing and the rank of a difference, without requiring the operator equation $XY=0$. The existential condition says that some original preparation has a nonzero readout under some original test, without specifying either resource.

The binary candidate and the separate ternary condition are

$$
\begin{aligned}
\mathsf Q_{\mathrm A}&:=\mathsf A(C_2)\wedge\mathsf N(C_2),\\
\mathsf T&:\quad\exists\,0\ne\psi\in(\mathbb C^n)^{\otimes3},\quad
\psi\psi^*\in C_3,\quad\min_i r_i(\psi)\ge2,\quad\max_i r_i(\psi)=n.
\end{aligned}
\tag{175.2}
$$

The $r_i$ are the three actual vector flattening ranks, exactly as in XVI173.5. No Bell membership is part of (175.2). Ordinary rank, the complex carrier and the specified tensor identifications remain supplied geometry.

### 175.2 Four cones from two connected ray families

**Theorem 175.2 (complete classification of an unsplit normal difference).** For every integer $d\ge1$ and closed convex cone $K\subseteq E_d$, the following are equivalent:

$$
\begin{aligned}
&\mathsf A(K);\\
&K\in\bigl\{\{0\},\ E_d,\ \operatorname{PSD}_d,\ -\operatorname{PSD}_d\bigr\};\\
&X\in K,\ Y\in K^*,\ \operatorname{Tr}(XY)=0\Longrightarrow XY=0.
\end{aligned}
\tag{175.3}
$$

In particular transpose reciprocity is unnecessary for this four-cone classification. It excludes the first two cones if separately imposed, recovering XVI174.2's signed conclusion.

**Proof.** Write $\mathcal P_d=\{vv^*:v^*v=1\}$. Its elements have Hilbert–Schmidt norm one, and it is the connected continuous image of the complex unit sphere, namely $\mathbb{CP}^{d-1}$. At $d=1$ it is a single point.

For $P\in\mathcal P_d$ and $\sigma\in\{+1,-1\}$, apply [Moreau, §4.b, printed p.281][Q175M] to $K$ and its nonpositive polar $K^\circ=-K^*$:

$$
\sigma P=A_\sigma-B_\sigma,\qquad
A_\sigma=\Pi_K(\sigma P)\in K,\quad B_\sigma\in K^*,\quad
\langle A_\sigma,B_\sigma\rangle=0.
\tag{175.4}
$$

This is the unique orthogonal cone decomposition. Since the difference has rank one, $\mathsf A(K)$ gives either $B_\sigma=0,A_\sigma=\sigma P$, or $A_\sigma=0,B_\sigma=-\sigma P$. Thus

$$
\Pi_K(P)\in\{0,P\},\qquad\Pi_K(-P)\in\{0,-P\}.
\tag{175.5}
$$

Moreau §5.b, printed p.282, proves that $\Pi_K$ is nonexpansive. Consequently each continuous map

$$
P\longmapsto\|\Pi_K(P)\|_2^2,\qquad
P\longmapsto\|\Pi_K(-P)\|_2^2
\tag{175.6}
$$

has values in $\{0,1\}$ and is constant on $\mathcal P_d$. Denote these two constants by $(a,b)$. If a projection in (175.5) is zero, (175.4) places its negative in $K^*$. If it is nonzero, the input itself belongs to $K$. Positive spectral sums, the full bipolar identity and ordinary PSD self-duality therefore give the complete table:

| $(a,b)$ | Containments forced by all positive and negative rays | Result |
| --- | --- | --- |
| $(0,0)$ | $\pm\operatorname{PSD}_d\subseteq K^*$ | $K^*=E_d$, so $K=\{0\}$ |
| $(1,1)$ | $\pm\operatorname{PSD}_d\subseteq K$ | $K=E_d$ |
| $(1,0)$ | $\operatorname{PSD}_d\subseteq K$ and $\operatorname{PSD}_d\subseteq K^*$ | $K=\operatorname{PSD}_d$ |
| $(0,1)$ | $-\operatorname{PSD}_d\subseteq K$ and $-\operatorname{PSD}_d\subseteq K^*$ | $K=-\operatorname{PSD}_d$ |

For example, the first row uses the fact that positive and negative spectral parts span every Hermitian matrix; the third uses duality to turn its second containment into $K\subseteq\operatorname{PSD}_d$. No self-duality or transpose relation for the unknown $K$ was used.

Each of the four cones satisfies the last condition of (175.3). For $K=\{0\}$ or $E_d$, one factor of every primal–dual pair is zero. For either signed PSD cone, the standard PSD support argument gives $XY=0$ from zero trace; for the negative cone apply it to $-X,-Y$.

Finally suppose the last condition. Hermiticity and $XY=0$ imply $YX=0$ and orthogonal ranges. Hence $X-Y$ is the direct sum of the restrictions of $X$ and $-Y$ on their mutually orthogonal ranges, so

$$
\operatorname{rank}(X-Y)=\operatorname{rank}X+\operatorname{rank}Y.
\tag{175.7}
$$

If its left side is one, one factor is zero. This proves $\mathsf A(K)$ and completes all implications. Empty cones are excluded by the definition of a convex cone containing zero; no properness or nonzero assumption was hidden. $\square$

### 175.3 Finite composition supplies the orientation

**Theorem 175.3 (binary reconstruction with no designated cup or cap).** On Definition 175.1's original all-finite domain,

$$
\mathsf Q_{\mathrm A}\quad\Longleftrightarrow\quad
C_2=\operatorname{PSD}_{n^2}.
\tag{175.8}
$$

In particular the Bell memberships of XVI173.4 and the entire zero-support relation of XVI174.1 are consequences of this candidate.

**Proof.** Apply Theorem 175.2 with $d=n^2$. Condition $\mathsf N(C_2)$ excludes $C_2=\{0\}$ and $C_2=W_2$, because respectively every preparation or every complete-dual test is zero. It leaves only the two signed PSD cones.

The negative choice is incompatible with the existing two-copy minimum and maximum bounds. If $C_2=-\operatorname{PSD}_{n^2}$ and $X\in C_1$ is nonzero, the minimum bound gives $X\otimes X\in-\operatorname{PSD}_{n^2}$. But a nonzero real eigenvalue $\lambda$ of the Hermitian $X$ gives a strictly positive eigenvalue $\lambda^2$ of $X\otimes X$, a contradiction. Therefore $C_1=\{0\}$.

Its complete dual is $W_1$. The maximum bound then requires

$$
\langle F\otimes G,Z\rangle\ge0
\quad(F,G\in W_1,\ Z\in C_2).
\tag{175.9}
$$

Replacing $F$ by $-F$ forces equality for every product test. Such products span $W_2$, so $C_2=\{0\}$, again a contradiction. Thus only positive PSD remains. This argument uses the actual tensor product of a system with itself, rather than assuming a sign for its trace.

Conversely, if $C_2=\operatorname{PSD}$, Theorem 175.2 gives $\mathsf A(C_2)$. A nonzero ordinary rank-one projection used as both $X$ and $Y$ has positive pairing, proving $\mathsf N(C_2)$. Its use in this converse does not designate a resource in the forward premise. Once the equality is obtained, the ordinary Bell dyad belongs to both original binary cones; XVI173.3 can then supply all-finite transpose reciprocity. The Bell construction is downstream of the reconstruction. $\square$

**Theorem 175.4 (unchanged ternary seed and the full quantum theory).** On the same domain,

$$
\mathsf Q_{\mathrm A}\wedge\mathsf T
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{for every finite }N\ge0.
\tag{175.10}
$$

**Proof and exact supplier correspondence.** Theorem 175.3 supplies $C_2=\operatorname{PSD}$. Consume precisely the already proved direction of [XVI173.5][Q175XVI] starting from that equality, not its earlier Bell hypothesis. Its XVI171.8–171.9 suppliers give the unique one-body sign $C_1=\varepsilon\operatorname{PSD}_n$ and, for every $N$, pointedness, generation, compact signed trace-one bases, and strict positivity of $\varepsilon^N\operatorname{Tr}$ away from zero.

The ordinary nonzero positive dyad at odd level three in $\mathsf T$ selects $\varepsilon=+1$ by XVI171.10. This sign selection uses no flattening ranks. At this point take the entire original trace-one bases, all their extrema, the complete duals, whole proper intervals and every finite unit decomposition. Every structural premise of [XIII166.12, condition 1 implies condition 5][Q175XIII] is now paid: the fixed actual complex tensor carriers and scalar object, all finite min/max bounds, actual permutations with positive inverses and reassociation, both low-level PSD equalities, and the just-earned ordinary properness and strictly positive multiplicative trace. The three flattening requirements in $\mathsf T$ are exactly XIII166.2, with one full leg and no native-extremality requirement. That supplier gives every finite PSD equality. Its finite positive success factors retain the original XIII166.10–166.11 scope, with no uniform resource or probability bound asserted.

For the converse take the full usual PSD hierarchy, Theorem 175.3, and the ordinary GHZ vector $\sum_j|jjj\rangle$, whose three ranks are $n$. This includes the scalar level. $\square$

### 175.4 The inherited state, measurement and process dictionary

**Corollary 175.5 (the standard finite axioms and their dependencies).** Under (175.10), the full dictionary of XVI173.6 applies in the original coordinates:

| Relation now obtained | Standard quantum content and its dependency |
| --- | --- |
| Whole positive trace-one cones | All density matrices; pure states are unit rank-one projectors |
| Complete trace dual and all finite unit decompositions | Every effect and POVM; $p(\ell\mid\rho)=\operatorname{Tr}(E_\ell\rho)$ |
| Least confirmation over the entire proper interval | $T_{vv^*}(ww^*)=|v^*w|^2$ |
| Actual joint cones and unit slices | Full entangled tensor composition and partial traces |
| Every real-linear map positive with all original finite spectators | Rectangular CP/Choi/Kraus correspondence |
| Whole-input TNI/TP budgets and finite TP-sum families | Mathematical branches, channels and instruments |

The normalized minimal face of two distinct pure rays is a real three-ball; the complete pure locus at level $N$ is $\mathbb{CP}^{n^N-1}$. These are derived native geometries after cone identification. The ambient matrix rank used in (175.1) precedes that identification.

**Proof.** Theorem 175.4 gives exactly the entire finite cones, ordinary trace, tensor identifications and full menus required by XVI173.6, whose mature matrix ingredients are the cited Watrous state, measurement and Choi/Kraus results. Substitute the identity coordinate transport, $d_N=n^N$ and every original finite spectator. For CP maps the real Hermitian map has its unique complex-linear extension; the output budget is the full Kraus-square operator inequality, not merely a scalar total Choi trace. Zero maps, scalar input/output and zero-probability branches retain that supplier's conventions.

The same substitution in XVI173.10 retains its distinct extra premises: an actual event-saturated theory for physical availability; a positive sharp-effect update fixing every accepted pure ray for the specified Lüders rule; and a given continuous trace-preserving order-automorphism group for Hamiltonian time. None is supplied by the mathematical nearest-point projection in (175.4). No clock, energy scale or numerical $\hbar$ is derived. $\square$

### 175.5 Countermodels locate the work done by the two relations

**Proposition 175.6 (nonzero readout and the ternary condition have separate roles).** Deleting $\mathsf N$ permits a complete full-space hierarchy satisfying $\mathsf A(C_2)$ and $\mathsf T$. Deleting $\mathsf T$ permits the ordinary alternating-sign PSD hierarchy satisfying $\mathsf Q_{\mathrm A}$. Deleting $\mathsf A$ permits the positive-trace, Bell-extreme transported hierarchy of XVI174.6, even with $\mathsf N$ and $\mathsf T$.

**Proof.** First set $C_N=W_N$ for every $N\ge1$, keeping $C_0=\mathbb R_+$. Each complete positive dual at a nonempty level is zero. The minimum products span the entire joint real space and include their negatives, so their conic hull is all of it. Maximum bounds are vacuous when both blocks are nonempty; scalar blocks give the same cone. Permutations and reassociation preserve these spaces. Thus the whole weak domain holds. Theorem 175.2 gives $\mathsf A(C_2)$, and any GHZ dyad supplies $\mathsf T$, but every primal–dual readout at level two is zero.

Second set $C_N=(-1)^N\operatorname{PSD}_{n^N}$. As in XVI173.8, signs multiply under every tensor split, complete duals have the same signs, and every actual permutation is positive with positive inverse. Level two is PSD, so $\mathsf Q_{\mathrm A}$ holds. Odd level three contains no nonzero ordinary positive dyad, hence fails $\mathsf T$. Binary orientation alone does not choose all odd-level traces.

For the third claim use exactly XVI174.5–174.6: at $n=2$, $c=4/5,s=3/5$, the Hilbert–Schmidt orthogonal Pauli map is

$$
R(I)=cI+sZ,\quad R(Z)=-sI+cZ,\quad R(X)=X,\quad R(Y)=Y,
\qquad \widehat C_N=R^{\otimes N}(\operatorname{PSD}_{2^N}).
\tag{175.11}
$$

That supplier proves the entire weak domain, pointedness, generation, strict ordinary positive trace, all proper menus, original extreme Bell membership in both binary cones and the unchanged $\mathsf T$. The Bell paired with itself already supplies $\mathsf N$.

There is an explicit pair failing the new conditional, in addition to XVI174.21's failure of the full zero-support relation. Put $P_j=|j\rangle\langle j|$, $A_j=R(P_j)$ and

$$
\begin{aligned}
H&=R_2\bigl((9P_0\otimes P_0+16P_1\otimes P_1)/25\bigr)
 =\operatorname{diag}(288,84,84,337)/625,\\
J&=R_2\bigl(12(P_0\otimes P_1+P_1\otimes P_0)/25\bigr)
 =\operatorname{diag}(288,84,84,-288)/625.
\end{aligned}
\tag{175.12}
$$

The two inverse images are nonzero PSD matrices on disjoint diagonal supports. Orthogonality of $R_2$ and complete self-duality of $\widehat C_2$ give $H\in\widehat C_2$, $J\in\widehat C_2^*$ and $\operatorname{Tr}(HJ)=0$. Direct subtraction gives

$$
H-J=P_1\otimes P_1,\qquad\operatorname{rank}(H-J)=1,
\qquad H\ne0,\quad J\ne0.
\tag{175.13}
$$

This is exactly a forbidden one-dimensional normal difference. The quantifiers in (175.1) range over whole cones and need no normalization of this pair. As in XVI174.7, this model is order-isomorphic to quantum theory; the failure is alignment with the supplied matrix directions, not failure of abstract quantum representability. $\square$

### 175.6 The intrinsic replacement that becomes vacuous

**Proposition 175.7 (native membership cannot define the missing directions).** For every closed convex cone $K$ in a finite-dimensional real inner-product space, every $X\in K,Y\in K^*$ with $\langle X,Y\rangle=0$ satisfies

$$
X-Y\in K\cup(-K^*)\quad\Longrightarrow\quad X=0\ \text{or}\ Y=0.
\tag{175.14}
$$

Consequently replacing ordinary rank-one differences in (175.1) solely by native extreme rays of $K$ or negative native extreme rays of $K^*$ makes that implication automatic for every such cone. It cannot supply the alignment proved in Theorem 175.3.

**Proof.** If $X-Y\in K$, dual positivity gives $0\le\langle X-Y,Y\rangle=-\|Y\|^2$, hence $Y=0$. If $Y-X\in K^*$, it gives $0\le\langle X,Y-X\rangle=-\|X\|^2$, hence $X=0$. Every suggested native ray lies in the corresponding union. No extremality assumption is needed for the calculation.

For a complete nonquantum control, XVI172.11–172.13 supply odd-prime Wigner simplex hierarchies on the actual carriers with all finite min/max bounds, full duals and menus, positive trace, nonzero readouts and the unchanged ternary seed, but non-PSD ordinary matrices. The automatic implication (175.14) holds on them too. Thus this particular intrinsic replacement proves nothing new, even on the full structural domain. This does not exclude other intrinsic relational axioms; it identifies the precise loss caused by this replacement. $\square$

**Proposition 175.8 (finitely sampled projection choices are insufficient).** At $d\ge2$, no finite list of ordinary positive rank-one projections can replace the universal ray family in the projection argument by testing only (175.5) on that list and its negatives.

**Proof.** For a nonempty list $P_1,\ldots,P_m$, let $K=\operatorname{cone}\{P_1,\ldots,P_m\}$. This finitely generated cone is closed and contained in PSD. Each $P_j\in K\cap K^*$, so its unique Moreau splits give $\Pi_K(P_j)=P_j$ and $\Pi_K(-P_j)=0$. Also $\mathsf N(K)$ holds. Nevertheless $K\ne\operatorname{PSD}_d$: a rank-one PSD matrix outside the finitely many listed rays cannot be their positive sum, since a rank-one positive sum forces every nonzero summand's range into its one-dimensional range. Such an unlisted ray exists at $d\ge2$. This is a counterexample for sampled projection data on one closed cone, not an asserted extension to the original all-finite domain. An empty list is weaker still. $\square$

### 175.7 Source scope and the geometric candidate in ordinary language

**Proposition 175.9 (the exact simplification and its limit).** The candidate removes a designated Bell resource and replaces the unrestricted matrix-product zero condition by a one-dimensional no-split condition. It leaves the fixed ambient rank geometry explicit.

**Proof and attribution.** Moreau's cone decomposition and projection continuity in §4.b/§5.b are literature-attested inputs. The two connected ray families and the four-case classification in Theorem 175.2 extend the one-family argument of XVI174.2; finite tensor self-composition in Theorem 175.3 then chooses the positive binary orientation. These, the explicit pair (175.12) and the native-ray obstruction are repository-derived deductions, with no claim of global literature priority. The all-finite propagation and complete quantum dictionary are precisely the credited suppliers of Theorem 175.4 and Corollary 175.5, rather than new proofs of standard quantum mathematics.

The restriction to rank-one differences is logically sufficient for the full zero-support property on closed cones by (175.3); it is not strictly weaker there. On the whole original domain, both $\mathsf Q_{\mathrm A}$ and XVI174.2's binary candidate are equivalent to $C_2=\operatorname{PSD}$. The simplification changes the supplied relations and eliminates a named entangled resource; it does not establish a minimum independent axiom count or a globally shortest description. Matrix rank and the connected complex ray geometry have not been derived from native order, as Proposition 175.7 makes concrete. $\square$

**命题 175.10（完整白话与三维图景）。** 在175.1的固定复矩阵关系空间里，候选可以完整地说成：至少有一对原准备和原测试能读出非零；当另一对准备与测试彼此正交，它们相减却只剩一条一维方向时，其中一边就必须本来是零。再给原来那颗三体种子——每个切口都非乘积、至少一条腿铺满本地维数——即得到175.4的全部有限量子对应。

**证明与图景。** 拿任意正向或反向的一维方向，分成“锥内最近部分”和“对偶法向部分”。新的二元关系不让一条方向被这两边共同凑出，所以它只能整个留下或整个落空。正方向连成一片，反方向也连成一片，连续性使每片都只能统一选择。于是只剩零锥、全空间、正锥和负锥四种形状。一次非零读数排除前两种；一个系统与自己复合时，任意非零方向总能产生正的平方方向，排除二体负锥。贝尔配对因此成为所得正锥里的成员，无须先把它递进来。一体仍有奇偶朝向，三体种子的正性选定朝上，它的展平秩再接上已有传播。最终任意两条不同纯射线的完整归一面都是一颗实三维球，所有有限层接回密度矩阵、玻恩读数、全部 POVM 与完全正过程。这里真正删去的是预先指定贝尔资源及零对之间的矩阵乘法要求；一维矩阵方向本身仍是给定关系，具体更新和时间仍按175.5另给条件。$\square$

[Q175XVI]: https://github.com/the-omega-institute/trureturing/blob/d134e4ba707ea7d86a12c2bc674f60aa8dd0e21e/docs/develop/theory/QUANTUM_ORIGIN_BINARY_BELL_ORBITS_AND_SINGLE_ATTENUATOR_XVI.md
[Q175XIII]: https://github.com/the-omega-institute/trureturing/blob/00427ae2ba9c9e3f6c37f2e5496b9127b6fbc6c0/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q175M]: https://www.numdam.org/item/BSMF_1965__93__273_0.pdf

## 追加锚（本行以下为增补区）

## 176. One-sided normal differences and preparation–test inclusion

### 176.1 The unchanged carrier and two binary relations

**Definition 176.1 (positive differences and self-testing).** Keep the entire weak all-finite domain of Definition 175.1, including the actual complex Hermitian tensor carriers, complete trace duals, every minimum/maximum partition, scalar object, positive actual permutations and their inverses, and canonical reassociation. Keep its ternary condition $\mathsf T$ only for the intermediate seed presentation below; Definition 176.9 gives the final candidate without that seed. For a closed convex cone $K\subseteq E_d=\operatorname{Herm}_d(\mathbb C)$ define

$$
\begin{aligned}
\mathsf A_+(K):\quad
&X\in K,\ Y\in K^*,\ \operatorname{Tr}(XY)=0,\\
&X-Y=vv^*\text{ for some }v\ne0
\quad\Longrightarrow\quad X=0\text{ or }Y=0,\\
\mathsf I(K):\quad
&\operatorname{Tr}(XZ)\ge0\quad\text{for every }X,Z\in K.
\end{aligned}
\tag{176.1}
$$

Thus $\mathsf I(K)$ is exactly the inclusion $K\subseteq K^*$ under the supplied Hilbert–Schmidt identification. It does not assert the reverse inclusion or positivity of a matrix operation. Each original preparation, under that identification, defines a nonnegative test on all original preparations. This is a condition on two elements of the same cone, not an assumed full state–effect equivalence.

For comparison with §175, the seed presentation is

$$
\mathsf Q_{+,\mathrm T}:=\mathsf A_+(C_2)\wedge\mathsf I(C_2)\wedge\mathsf T.
\tag{176.2}
$$

Only positive ordinary rank-one differences are tested in $\mathsf A_+$. The negative differences in $\mathsf A$ are omitted, and no nonzero binary readout or Bell resource is designated. Both the ordinary complex rank-one family and the positive-definite trace identification remain supplied geometry. In particular $\mathsf I$ is not a claim that preparation and test types have already been intrinsically identified without a pairing.

### 176.2 What the positive half actually controls

**Theorem 176.2 (the exact one-sided classification).** For every $d\ge1$ and every closed convex cone $K\subseteq E_d$,

$$
\mathsf A_+(K)
\quad\Longleftrightarrow\quad
\bigl(\operatorname{PSD}_d\subseteq K\bigr)
\quad\text{or}\quad
\bigl(K\subseteq-\operatorname{PSD}_d\bigr).
\tag{176.3}
$$

The inclusions here need not be equalities. This is precisely the freedom lost by deleting the negative normal differences from Theorem 175.2.

**Proof.** For each unit rank-one projection $P$, Moreau's decomposition, with positive-dual sign convention, is

$$
P=X-Y,\qquad X=\Pi_K(P)\in K,\quad Y\in K^*,\quad
\operatorname{Tr}(XY)=0.
\tag{176.4}
$$

If $\mathsf A_+$ holds, its two possible splits give $\Pi_K(P)=P$ or $0$. The nonexpansive projection and the connected family $\mathbb{CP}^{d-1}$ make $\|\Pi_K(P)\|_2^2\in\{0,1\}$ constant, exactly as in the positive-family part of Theorem 175.2. If the constant is one, every $P$ belongs to $K$ and positive spectral sums give $\operatorname{PSD}_d\subseteq K$. If it is zero, (176.4) gives $-P\in K^*$ for every $P$. Hence $-\operatorname{PSD}_d\subseteq K^*$, whose dual inclusion is $K\subseteq-\operatorname{PSD}_d$. This uses Moreau's cited decomposition and continuity, not positivity of its projection as an operation.

Conversely let $X,Y$ satisfy the antecedent of $\mathsf A_+$ and put $P=X-Y=vv^*$. If $\operatorname{PSD}_d\subseteq K$, then $P\in K$, and

$$
0\le\operatorname{Tr}(PY)
=\operatorname{Tr}((X-Y)Y)=-\|Y\|_2^2.
\tag{176.5}
$$

Thus $Y=0$. If $K\subseteq-\operatorname{PSD}_d$, then $-P\in K^*$ and

$$
0\le\operatorname{Tr}(X(-P))
=\operatorname{Tr}(X(Y-X))=-\|X\|_2^2,
\tag{176.6}
$$

so $X=0$. These arguments include the zero and full-space cones where applicable. $\square$

**Corollary 176.3 (one inclusion closes the positive branch).** On one closed Hermitian cone,

$$
\mathsf A_+(K)\wedge\mathsf I(K)
\quad\Longleftrightarrow\quad
K=\operatorname{PSD}_d\ \text{or}\ K\subseteq-\operatorname{PSD}_d.
\tag{176.7}
$$

**Proof.** In the positive branch of (176.3), $\operatorname{PSD}_d\subseteq K\subseteq K^*$. Duality also gives $K^*\subseteq\operatorname{PSD}_d$, so all are equal. Every subcone of $-\operatorname{PSD}_d$ satisfies $\mathsf I$: the trace product of two negative semidefinite Hermitian matrices is nonnegative. Theorem 176.2 supplies its $\mathsf A_+$. The PSD case has both properties as well. $\square$

### 176.3 Finite composition removes the residual branch

**Lemma 176.4 (a negative binary subcone collapses the whole hierarchy).** On the weak domain of Definition 175.1, if $C_2\subseteq-\operatorname{PSD}_{n^2}$, then $C_N=\{0\}$ for every $N\ge1$.

**Proof.** For $X\in C_1$, the minimum inclusion puts $X\otimes X\in C_2$. If $X\ne0$, some nonzero Hermitian eigenvalue $\lambda$ gives its tensor square the positive eigenvalue $\lambda^2$, contradicting the proposed containment. Thus $C_1=\{0\}$ and its complete dual is $W_1$.

The maximum inclusion at $1+1$ then tests every $Z\in C_2$ against all $F\otimes G$ with $F,G\in W_1$. Both signs of each such test are present. Every resulting pairing is zero, and product Hermitian tests span $W_2$, so $C_2=\{0\}$. Inductively, if $C_{N-1}=\{0\}$, the maximum inclusion at $1+(N-1)$ uses the full duals $W_1,W_{N-1}$ and the same spanning argument gives $C_N=\{0\}$. Scalar partitions retain $C_0=\mathbb R_+$. $\square$

**Theorem 176.5 (binary dichotomy and the full candidate).** On that same domain,

$$
\begin{aligned}
\mathsf A_+(C_2)\wedge\mathsf I(C_2)
\quad&\Longleftrightarrow\quad
C_2=\operatorname{PSD}_{n^2}
\ \text{or}\ (C_N=\{0\}\text{ for all }N\ge1),\\
\mathsf Q_{+,\mathrm T}\quad&\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\text{ for every finite }N\ge0.
\end{aligned}
\tag{176.8}
$$

**Proof.** Corollary 176.3 and Lemma 176.4 give the first forward implication. Binary PSD and the all-zero nonempty hierarchy each satisfy both binary relations, giving its converse.

The nonzero primal dyad in $\mathsf T$ excludes the all-zero hierarchy; no separate $\mathsf N(C_2)$ is needed. Thus $\mathsf Q_{+,\mathrm T}$ gives $C_2=\operatorname{PSD}$. It now supplies $\mathsf Q_{\mathrm A}$ by Theorem 175.3, so Theorem 175.4 with precisely the unchanged $\mathsf T$ gives every finite PSD equality. Its suppliers first recover $C_1=\varepsilon\operatorname{PSD}_n$ and signed properness; the positive odd-level dyad selects $\varepsilon=+1$; its three flattening ranks then pay the full hypotheses of XIII166.12. No rank requirement is used to exclude the zero hierarchy, whereas all three remain in the propagation step. Conversely the standard PSD hierarchy satisfies both binary relations and has the full-rank GHZ seed used in Theorem 175.4. $\square$

### 176.4 A complete countermodel to omitting preparation–test inclusion

**Theorem 176.6 (all-finite product-block-positive control).** Deleting $\mathsf I(C_2)$ from (176.2) permits a hierarchy with pointed generating cones, strictly positive ordinary trace, complete duals and full effect menus, every finite structural bound, $\mathsf A_+(C_2)$, $\mathsf N(C_2)$ and the unchanged $\mathsf T$, yet $C_2\ne\operatorname{PSD}_{n^2}$.

**Proof.** Let $\operatorname{Sep}_N$ be the cone generated by all ordinary rank-one fully single-leg product dyads. Define, on the actual carriers,

$$
\begin{aligned}
C_N=\operatorname{BP}_N:=\bigl\{X\in W_N:
\langle v_1\otimes\cdots\otimes v_N,
X(v_1\otimes\cdots\otimes v_N)\rangle\ge0
\text{ for all }v_1,\ldots,v_N\in\mathbb C^n\bigr\},\\
C_0=\mathbb R_+.
\end{aligned}
\tag{176.9}
$$

The normalized product projections form a compact set of trace one. Its convex hull is compact, and its conic hull is closed because the trace fixes every conic scale. Thus $\operatorname{Sep}_N$ is closed; complete duality and the bipolar identity give

$$
\operatorname{BP}_N=\operatorname{Sep}_N^*,\qquad
\operatorname{BP}_N^*=\operatorname{Sep}_N.
\tag{176.10}
$$

All $\operatorname{BP}_N$ are closed convex cones and contain ordinary PSD. They are generating because PSD spans the ambient Hermitian space. Product projections span that space too, so if $X,-X\in\operatorname{BP}_N$, every product expectation is zero and $X=0$. This proves pointedness.

For strict trace positivity use the following finite set of unit one-body projections: the $n$ coordinate projections, and for every $i<j$ the four projections onto

$$
\frac{e_i+e_j}{\sqrt2},\quad\frac{e_i-e_j}{\sqrt2},\quad
\frac{e_i+\mathrm i e_j}{\sqrt2},\quad
\frac{e_i-\mathrm i e_j}{\sqrt2}.
\tag{176.11}
$$

They span $\operatorname{Herm}_n$ and sum to $(2n-1)I_n$. Their $N$-fold products span $W_N$ and sum to $(2n-1)^N I_{n^N}$. All pairings with $X\in\operatorname{BP}_N$ are nonnegative. If $\operatorname{Tr}X=0$, this finite sum forces each pairing to vanish, so $X=0$. Hence ordinary trace is strictly positive away from zero. In finite dimension the resulting whole trace-one base is compact. The effect interval and all finite trace-unit decompositions are taken from the complete dual (176.10), rather than a selected test list.

For any partition $a+b=N$, a product $X\otimes Y$ of block-positive elements is nonnegative on every fully product vector: its expectation is the product of two nonnegative numbers. This proves the minimum inclusion. Products of elements of $\operatorname{Sep}_a$ and $\operatorname{Sep}_b$ conically generate exactly $\operatorname{Sep}_N$. Equations (176.10) therefore give the stronger maximum equality

$$
\operatorname{BP}_a\otimes_{\max}\operatorname{BP}_b
=\operatorname{BP}_{a+b}.
\tag{176.12}
$$

This holds for every finite split, not just $1+(N-1)$; permutations and their inverses preserve the full product family, reassociation is the actual identity, and scalar splits give the same cones.

Since $\operatorname{PSD}_{n^2}\subseteq\operatorname{BP}_2$, Theorem 176.2 gives $\mathsf A_+(C_2)$. Choosing $I$ on both sides gives $\mathsf N(C_2)$, since $I\in\operatorname{Sep}_2$. The ordinary GHZ dyad is PSD and hence belongs to $C_3$; each flattening rank is $n$, so $\mathsf T$ holds.

Nevertheless $C_2$ is larger than PSD. Let $B=\Omega\Omega^*$ with $\Omega=\sum_j e_j\otimes e_j$ as in XVI173.2. Cauchy–Schwarz gives

$$
|\langle\Omega,a\otimes b\rangle|^2
\le\|a\|^2\|b\|^2,
\qquad I-B\in\operatorname{BP}_2.
\tag{176.13}
$$

Its eigenvalue on $\Omega$ is $1-n<0$. Both $B$ and $I-B$ belong to the native primal cone, whereas

$$
\operatorname{Tr}\bigl(B(I-B)\bigr)=n-n^2<0.
\tag{176.14}
$$

Thus $\mathsf I(C_2)$ fails by an explicit pair, and $B\notin C_2^*$. The two preparations cannot both be interpreted as tests using the supplied trace identification. All actual native state–test probabilities still remain nonnegative by complete duality. $\square$

**Proposition 176.7 (the other omissions also have full controls).** Deleting $\mathsf A_+(C_2)$ permits XVI174.6's transported hierarchy even with $\mathsf I(C_2)$ and $\mathsf T$. Deleting $\mathsf T$ permits both the all-zero nonempty hierarchy and the alternating-sign PSD hierarchy.

**Proof.** The transported hierarchy has $C_2=C_2^*$ for the actual trace inner product, so $\mathsf I(C_2)$ holds. Its entire weak domain and unchanged $\mathsf T$ are proved in XVI174.6. The nonzero complementary pair $H,J$ in (175.12)–(175.13) has $H-J=P_1\otimes P_1$ positive rank one. It therefore violates the positive half itself, not merely a discarded negative test.

The all-zero cones at nonempty levels have full ambient duals; their minimum bounds are zero and their maximum bounds force zero by product-test spanning. They satisfy the binary relations but have no nonzero seed. Finally $C_N=(-1)^N\operatorname{PSD}_{n^N}$ is the complete alternating-sign hierarchy of Proposition 175.6. Its binary cone is PSD, while no nonzero ordinary positive dyad belongs to its negative three-body cone. Both failures are on the original all-finite domain. $\square$

### 176.5 A nonempty ternary reference replaces the supplied entangled seed

**Lemma 176.8 (one normalized preparation earns the strong domain).** On Definition 176.1's weak domain, suppose $\mathsf A_+(C_2)$, $\mathsf I(C_2)$ and

$$
K_3:=C_3\cap\{\operatorname{Tr}=1\}\ne\varnothing.
\tag{176.15}
$$

Then $C_1=\operatorname{PSD}_n$, $C_2=\operatorname{PSD}_{n^2}$, and all finite cones are pointed and generating with strictly positive ordinary trace. Their whole trace-one bases are nonempty and compact. In particular, with $D=n^3$,

$$
m_3=I_D/D\in\operatorname{relint}K_3,
\qquad P_3=\operatorname{ext}K_3\ne\varnothing.
\tag{176.16}
$$

**Proof.** The first equivalence of Theorem 176.5 and (176.15) exclude the all-zero hierarchy, so $C_2=\operatorname{PSD}$. Consume XVI171.8–171.9 with the same actual carriers, full duals and every finite tensor bound. These give $C_1=\varepsilon\operatorname{PSD}_n$, all-level pointedness and generation, and strict positivity of $\varepsilon^N\operatorname{Tr}$ on $C_N\setminus\{0\}$. A trace-one member of $C_3$ makes $\varepsilon^3=+1$, so $\varepsilon=+1$. This uses an arbitrary normalized preparation, not a matrix dyad or any flattening rank.

For (176.16), tensor the finite spanning projector family of (176.11). Every product belongs to $C_3$ by repeated minimum inclusion from the earned $C_1$. They span $W_3$ and their sum is $(2n-1)^3I_D$. A strictly positive combination of a finite spanning family in a cone lies in its interior: small changes of all coefficients still remain positive and their linear synthesis map is onto. Hence $I_D\in\operatorname{int}C_3$ and its trace normalization is relative interior in the full base. Compactness follows from closedness and strict trace positivity; finite-dimensional compact convexity supplies an extreme point. All hypotheses of XIII166.1, without any seed premise, are now earned. $\square$

**Definition 176.9 (flat least confirmation at one ternary reference).** On the domain just earned in Lemma 176.8, take the entire interval and each whole confirmer set

$$
\begin{aligned}
\mathcal E_3&=\{F:F,I_D-F\in C_3^*\},\\
\mathcal F_p&=\{F\in\mathcal E_3:\operatorname{Tr}(Fp)=1\},\\
T_p(x)&=\min_{F\in\mathcal F_p}\operatorname{Tr}(Fx)
\qquad(p\in P_3,\ x\in K_3).
\end{aligned}
\tag{176.17}
$$

These are actual minima: the full proper interval is compact on a pointed generating finite-dimensional carrier; $I_D$ belongs to it and confirms every normalized $p$, so each closed $\mathcal F_p$ is nonempty compact. The final candidate $\mathsf Q_{\mathrm{flat}}$ requires $\mathsf A_+(C_2)$, $\mathsf I(C_2)$, (176.15), and

$$
\mathsf E_3:\qquad T_p(m_3)=T_q(m_3)\quad(p,q\in P_3).
\tag{176.18}
$$

The common value is not supplied. The last condition constrains native preparations and the confirmation sets defined from the whole original test menu. It is evaluated only after the first three conditions have paid its domain via Lemma 176.8. No distinguished entangled preparation, ordinary three-body rank, pure-state closedness, spectrality, least effect or affine confirmation law is assumed.

**Theorem 176.10 (the final all-finite candidate without a supplied seed).** On the original weak all-finite domain,

$$
\mathsf Q_{\mathrm{flat}}
\quad\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\quad\text{for every finite }N\ge0.
\tag{176.19}
$$

Under these conditions the common value in (176.18) is $1/D$, and equivalently the entire native $P_3$ lies on a sphere about $m_3$ of one common, initially unspecified radius; its squared radius is then $1-1/D$.

**Proof and exact supplier correspondence.** Lemma 176.8 has paid precisely the strong actual-coordinate domain of [the pure-endpoint volume, Definition 175.1][Q176E]: the same $n$, actual $W_N$, both low PSD equalities, every closed pointed generating finite cone, strictly positive multiplicative ordinary trace, scalar object, all original bases and pure sets, complete trace duals, full proper intervals and finite unit decompositions, every finite min/max partition, positive actual permutations with positive inverses, and canonical reassociation. Its reference $m=I_{n^3}/n^3$ and its complete confirmer sets are exactly (176.16)–(176.17). Thus (176.18) is its condition $\mathsf E$, with all original pure labels retained.

Apply that volume's Theorem 175.2, condition 3 implies condition 7. Its proof first fixes the common value using actual $1|23$ pure anchors; the Gurvits–Barnum whole-cone norm bound forces every native pure point to have Hilbert–Schmidt norm one. Invertible local filters, the Marciniak rectangular classification, and the other two block-positive cuts supply three-body PSD; complete Bell polarity supplies equality. Only after that equality does its proof construct the GHZ dyad and invoke XIII166.12 for all finite levels. These are the source theorem's proved intermediate suppliers, not additional premises here. In particular neither the GHZ dyad nor its flattening ranks have been supplied to $\mathsf Q_{\mathrm{flat}}$.

The same source theorem identifies the unknown comparison value and the unknown-radius sphere condition. Conversely the standard PSD hierarchy satisfies the binary relations, has nonempty $K_3$, and has $T_p(m_3)=\operatorname{Tr}(pm_3)=1/D$ for every native pure $p$. This proves (176.19) and the numerical conclusions. This reconstruction of an entire cone is not the false assertion that the full ambient sphere consists of pure states. $\square$

### 176.6 Quantum correspondence, geometric economy and the remaining bridge

**Corollary 176.11 (the inherited full finite theory).** Under $\mathsf Q_{\mathrm{flat}}$, every conclusion and every separate realization condition of Corollary 175.5 applies in the original coordinates.

**Proof and correspondence.** Theorem 176.10 supplies its exact cone hypothesis. Whole trace-one cones give all density states and rank-one pure states; complete proper intervals and all unit decompositions give all POVMs and the Born pairing; the actual joint cones give tensor composition and partial traces; positivity with every original finite spectator gives the rectangular CP/Choi/Kraus dictionary, with the whole-input TNI/TP budgets for mathematical instruments. The corresponding Watrous suppliers and scalar and zero-branch conventions are precisely those reused in 175.5, rather than new proofs of those standard results.

For two distinct pure states inside one resulting matrix block, the minimal normalized face is a real three-ball, and the full pure locus at level $N$ is $\mathbb{CP}^{n^N-1}$. The larger object containing these binary balls is the entire positive Hermitian cone with its finite tensor hierarchy. Event saturation, a specified sharp nondisturbing update for Lüders, and a supplied continuous order-automorphism group for Hamiltonian time retain the distinct assumptions of 175.5. No physical clock or value of $\hbar$ is obtained. $\square$

**Proposition 176.12 (what has and has not become simpler).** Relative to $\mathsf Q_{\mathrm A}\wedge\mathsf T$, the intermediate presentation (176.2) deletes the negative rank-one difference tests and the independent nonzero-readout premise, at the cost of the preparation–test inclusion $\mathsf I(C_2)$. The final candidate replaces the three-body matrix seed and all of its flattening-rank requirements by a nonempty normalized slice and native reference flatness. No globally minimal axiom set is claimed.

**Proof and source scope.** Theorem 176.2 identifies exactly the extra cones admitted by the positive half. Theorem 176.6 shows that this loss survives every finite composite requirement, strict trace positivity, nonzero readout and the original ternary seed. Thus these standing structures cannot silently replace $\mathsf I$. Corollary 176.3 and Lemma 176.4 show precisely how one inclusion and self-composition repair it, and why the seed itself now pays the nonzero condition. On the fixed all-finite domain both complete candidates are equivalent to the same full PSD hierarchy, by Theorems 175.4 and 176.5. This is an alternative allocation of assumptions, not a strict weakening there or a shortest-description theorem.

Moreau's decomposition and nonexpansiveness are the literature inputs at [printed pp.281–282][Q175M]. The one-family argument, hierarchy collapse, and product-block-positive control are paper deductions on the stated carriers; the separable/block-positive polar pairing follows directly from their definitions in (176.9)–(176.10). No general literature priority is claimed. The all-finite propagation and standard quantum dictionary are the explicitly credited existing suppliers above.

The reference-flatness theorem used in 176.10 is credited to [the pure-endpoint volume][Q176E], not presented as a new proof here. Lemma 176.8 supplies its previously missing strong-domain entry from the one-sided binary relations and a nonempty slice. The positive-half countermodels in 176.6–176.7 concern the explicitly stated seed presentation; they do not assert independence of the final candidate's reference-flatness and binary clauses. The three-body simplification eliminates an external entanglement-rank condition, while comparison still quantifies every native pure target and its whole confirmer set. Equal confirmation values are a constraint on those definitions, rather than an assumption that their functions are affine.

The external complex carrier, positive binary rank-one family and trace identification have not been reconstructed from native zero relations. Proposition 175.7 still rules out the particular native-extreme-ray replacement that makes the constraint automatic. The already established one-interior-reference recipe criterion in the [Pinelis source-context note][Q176P] is a distinct intrinsic route, with its full VII102.4 B1–B3 hypotheses; it is not a consequence of the positive half or a newly established result here. A bridge deleting the remaining supplied binary rank geometry remains unproved. These statements are paper mathematics, not Lean-kernel certification. $\square$

**命题 176.13（完整白话候选）。** 在175.1给定的复矩阵关系空间里，候选可以说成：任何两份二体原准备，用同一把迹标尺比较都不能给负数；一份二体准备与一个原测试互不响应时，如果两者之差恰好是一条正向的一维线，它们就不能各留一块。三体层确实能准备一个归一对象，而且所有原纯准备在同一个均匀参考态上的最低确认代价相同。这些条件恰好给出176.10的全部有限量子锥，不再预送一颗指定纠缠性质的种子。

**证明与图景。** 把任意正向一维线分成锥内最近部分和对偶法向部分，第二条关系使整片相连的一维线只能统一留下或统一落空。留下时，量子正锥已全部在里面；第一条关系又让每份准备都能充当非负测试，于是把外面多出的部分挡掉。落空时，二体锥只能朝负面；但一份对象和自己复合总会产生正的平方方向，所以这种二体选择迫使每个非空层都归零。一个三体归一对象让整体不能归零，也选定一体的正朝向。到这里，原状态、原测试与均匀参考才都已就位。最后一条关系说，不同纯准备面对这份均匀背景时，没有谁能用更便宜的确定确认占便宜；已有完整菜单的范数界将它们推到同一个外接球面，原可逆过滤与三种切分再排掉非量子支路，贝尔极性夹出整个三体量子锥，纠缠种子成为结论后才向全部有限层传播。仅保留正向差分时，176.6的大块正锥仍能混进来，说明二体修补不能靠原种子和非零读数默默支付。所得局部画面仍是两条纯线撑起一颗三维球，整体是相容的有限量子锥层级；高维纯态只占外接球面的特定射影轨迹。三体种子的外部秩条件已删去，二体的一维线和迹标尺仍是给定地基，具体测后更新与时间保留176.11的额外条件。$\square$

[Q176P]: https://github.com/the-omega-institute/trureturing/blob/1888fc22e76ba8b59fb974ef5db8f5e1b23904f1/Library/Convexity/pinelis2012extremepoints.md
[Q176E]: https://github.com/the-omega-institute/trureturing/blob/02e623db8cc5dd8e6b413d337edbe4991f33e178/docs/develop/theory/QUANTUM_ORIGIN_PURE_ENDPOINT_RECIPROCITY_AND_QUANTUM_RECONSTRUCTION_XVII.md

## 追加锚（本行以下为增补区）

## 177. 中心三项配方、两条欧氏轴与原生全有限量子候选

**定义 177.1（由局部凸体定义的确认）。** 设 $F$ 是有限维实仿射空间中的紧凸体，仿射维数 $d\ge2$，中心为 $m$，且中心对称、严格凸。令 $W=\operatorname{span}(F-m)$，$B=F-m$；$B$ 自身的 Minkowski 泛函记为 $N$。因此 $B=\{x:N(x)\le1\}$，其全部纯点为 $m+\partial B$；没有另外指定内积、光滑性或可逆运动群。以下将 $m$ 平移为 $0$，纯点简记为 $p,q\in\partial B$。

只从这个凸体定义完整的内禀仿射效应和确认读数：

$$
\begin{gathered}
\mathcal E_F=\{e:F\longrightarrow[0,1]:e\text{ 为仿射函数}\},\\
T_q^F(x)=\min\{e(x):e\in\mathcal E_F,\ e(q)=1\},\qquad
J(q)=\{\ell\in W^*:N^*(\ell)=1,\ \ell(q)=1\}.
\end{gathered}
\tag{177.1}
$$

有限维支持超平面定理给出非空紧集 $J(q)$。这里的 $\mathcal E_F$ 是由面定义的数学集合；若 $F$ 属于更大的状态空间，不假设这些函数已经延拓成大空间的 proper 效应，也不假设物理过滤可用。

**定义 177.2（只含目标的中心三角形关系）。** 对固定 $p\in\partial B$，$\mathsf\Delta_F(p)$ 表示：每个以 $p$ 为一顶点、三个纯标签仿射不共线的正权中心三角形，都满足

$$
\begin{gathered}
a,b,c>0,\quad a+b+c=1,\quad q,r\in\partial B,\quad
ap+bq+cr=0\\
\Longrightarrow\qquad
 aT_p^F(p)+bT_q^F(p)+cT_r^F(p)=T_p^F(0).
\end{gathered}
\tag{177.2}
$$

不另检查二标签配方，也不要求目标 $-p$ 的三角形。右侧是同一确认定义对中心的读数，不另指定概率常数。该关系只约束原读数与实际中心配方的相容性，不预设 $T_q^F$ 对任意混合为仿射。

**定理 177.3（中心配方精确刻画一条欧氏直和轴）。** 在定义177.1的域中，$\mathsf\Delta_F(p)$ 当且仅当存在实线性泛函 $b_p$，满足 $b_p(p)=1$，并且

$$
N(x)^2=b_p(x)^2+N\bigl(x-b_p(x)p\bigr)^2
\qquad(x\in W).
\tag{177.3}
$$

此时 $W=\mathbb Rp\oplus_2\ker b_p$，且中心关系对任意有限项配方都成立。欧氏直和轴是既有 Banach 空间概念；本条所推导的是它与原始完整确认菜单的目标入项中心三角形关系的等价。

证明。完整确认集的计算复用 [VI，101.2的完整效应式及其证明][Q177VI] 中仅使用中心对称凸体的部分。精确参数是附着于本面自身的锥 $C_F=\{(t,x):t\ge N(x)\}$、单位 $u_F(t,x)=t$、基 $\{(1,x):x\in B\}$；其整个 proper 区间恰是本面的全部仿射效应。该计算不消费101.1的参考互反，其原证明在中心对称性得到后直接逐参数计算。它给出

$$
T_q^F(x)=\tfrac12\left(1+\min_{j\in J(q)}j(x)\right),\qquad
T_q^F(0)=\tfrac12.
\tag{177.4}
$$

在光滑严格凸范数模型中，唯一支持函数的相应公式见 [N177，§7，式(5)，印刷页7][Q177N]；该文定理7.1在其光滑前件下用全部转移概率互反刻画 pre-Hilbert 空间。本证明保留可能多值的 $J(q)$，不用光滑性，也不假设全部目标间的互反。

现假设 $\mathsf\Delta_F(p)$。令 $H(x)=N(x)^2/2$。复用 VI101.4证明中(101.6)的范数平方次梯度公式，按因子 $1/2$ 缩放：

$$
\partial H(x)=N(x)J\bigl(x/N(x)\bigr)\quad(x\ne0),
\qquad \partial H(0)=\{0\}.
\tag{177.5}
$$

该公式只要求有限维范数，不消费VI的端点互反。沿直线的左右导数分别为次梯度在该方向上的最小值与最大值，复用其证明所引的 Rockafellar 方向导数表示。记

$$
A(x)=\min_{s\in\partial H(x)}s(p),\qquad
B(x)=\max_{s\in\partial H(x)}s(p).
\tag{177.6}
$$

若 $x\notin\mathbb Rp$、$t>0$，三个标签

$$
p,\qquad \frac{x}{N(x)},\qquad
-\frac{x+tp}{N(x+tp)}
$$

仿射不共线；以 $t,N(x),N(x+tp)$ 为未归一正权，正好调出中心。由(177.4)、$T_p^F(p)=1$ 及 $J(-q)=-J(q)$，三角形关系化为

$$
B(x+tp)=A(x)+t.
\tag{177.7}
$$

凸函数在同一直线上的右导数单调，故 $A(x)\le B(x)\le B(x+tp)=A(x)+t$。这对所有 $t>0$ 成立，强制 $A(x)=B(x)$。若 $x=sp$，(177.5)直接给每个次梯度在 $p$ 上均取值 $s$，包括 $s=0$。因此共同读数 $L(x)=A(x)=B(x)$ 在整个 $W$ 上有定义。(177.7)先给正向平移，再交换起点给任意实平移，得到

$$
L(x+tp)=L(x)+t,\qquad
H(x+tp)=H(x)+tL(x)+t^2/2.
\tag{177.8}
$$

第二式沿 $p$ 积分，经过零点时左右导数仍相同。还不能仅由平行线公式宣称 $L$ 线性。令 $z=\lambda x+(1-\lambda)y$，$0\le\lambda\le1$。对任意实 $t$，凸性先给

$$
H(z+tp)\le\lambda H(x+tp)+(1-\lambda)H(y+tp).
$$

代入(177.8)，得到

$$
\begin{aligned}
0\ge {}&H(z)-\lambda H(x)-(1-\lambda)H(y)\\
&+t\bigl[L(z)-\lambda L(x)-(1-\lambda)L(y)\bigr].
\end{aligned}
$$

由于 $t$ 可取任意正负值，一次项系数必须为零，故 $L$ 仿射；$L(0)=0$ 又给实线性。取 $b_p=L$，则 $b_p(p)=1$，并在(177.8)取 $t=-b_p(x)$ 得到(177.3)。此处同时推出每个 $J(q)$ 的全部元素在 $p$ 上读数一致；二项配方是结论，没有先行假设。

反之设(177.3)。在 $x=tp+z$、$z\in\ker b_p$ 的坐标中，$H(x)=t^2/2+N(z)^2/2$，所以每个 $s\in\partial H(x)$ 在 $p$ 上取值 $t=b_p(x)$。由(177.5)，对单位 $q$ 的所有 $j\in J(q)$ 都有 $j(p)=b_p(q)$。于是 $T_q^F(p)=(1+b_p(q))/2$，而任何有限中心配方的加权 $b_p$ 值为零，给出全部有限中心配方关系，特别给出(177.2)。$\square$

**定理 177.4（三维面的两目标闭合）。** 在定义177.1的三维域中，存在两个中心化方向独立的纯目标 $p_1,p_2$ 满足 $\mathsf\Delta_F(p_1),\mathsf\Delta_F(p_2)$，当且仅当 $F$ 仿射同构于整个闭 Euclidean 三球。

证明。对每个 $p_i$ 使用177.3。其平方范数分解说明 $H$ 在 $p_i$ 处的唯一次梯度为 $b_{p_i}$：在 $\mathbb Rp_i\oplus\ker b_{p_i}$ 中，平方范数为轴坐标平方加横向范数平方，后者在零点的导数为零。因此 $J(p_i)=\{b_{p_i}\}$，$J(-p_i)=\{-b_{p_i}\}$。177.3证明已给每个单位 $q$ 的所有 $j\in J(q)$ 满足 $j(p_i)=b_{p_i}(q)$。代入(177.4)，得到对全部纯 $q$ 的

$$
\begin{gathered}
T_{p_i}^F(q)=T_q^F(p_i)=\tfrac12(1+b_{p_i}(q)),\\
T_{-p_i}^F(q)=T_q^F(-p_i)=\tfrac12(1-b_{p_i}(q)),\\
T_{p_i}^F(q)+T_{-p_i}^F(q)=1.
\end{gathered}
\tag{177.9}
$$

这些正是 [VI，定义101.1][Q177VI] 的两个独立参考对 $(p_i,-p_i)$、共同中心 $0$、$s_i=p_i$ 下的 $\mathrm E2_i,\mathrm R_{i,+},\mathrm R_{i,-}$。采用177.3所用的本面锥 $C_F$，闭、尖、生成、严格正单位、全基与全效应均满足该条目的原域。仿射维数 $d=3$，所以参考方向数 $2=d-1$。直接应用既有 VI101.4—101.5 得到同一个 $N^2$ 为正定二次型；不重证余维一欧氏直和结论。

反向在球的内积坐标中，(177.4)为 $T_q^F(p)=(1+G(q,p))/2$，故全部目标和全部有限中心配方都满足关系，任选两个独立目标即可。$\square$

**命题 177.5（两个目标与三项标签各有实际作用）。** 在上述中心对称严格凸三维类中，把三项检查降为两项，或把两个独立目标降为一个，都不能强制椭球。

证明。取

$$
N(x,y,z)^2=x^2+\sqrt{y^4+z^4}.
\tag{177.12}
$$

这是 $\mathbb R\oplus_2\ell_4^2$ 的范数；它严格凸，并在非零点可微，即支持泛函唯一。对 $e_y=(0,1,0)$、$e_z=(0,0,1)$，平行四边形两侧分别为 $2\sqrt2$ 与 $4$，故不是内积范数。对目标 $e_x$，177.3的分解直接成立，因此它通过所有有限中心配方。

任意严格凸中心对称体的两标签中心配方必为等权对径配方：$aq+(1-a)r=0$ 及 $N(q)=N(r)=1$ 强制 $a=1/2,r=-q$。在任何光滑的这种范数中，$J(q)$ 单值，故由(177.4)这类检查对每个目标均自动通过。因而(177.12)也给出“全部目标、但只有两标签”的反例。

三标签可以实际区分它。令 $c=2^{1/4}$，取 $e_y,e_z,-(e_y+e_z)/c$，权分别为 $1,1,c$ 除以 $2+c$。对目标 $e_y$，单位球的支持泛函在三个标签上的目标读数分别为 $1,0,-c^{-3}$。由(177.4)，配方平均比直接中心读数 $1/2$ 多出

$$
\frac{1-1/\sqrt2}{2(2+2^{1/4})}>0.
\tag{177.13}
$$

所以一个目标确实容许一个非欧氏横向平面，而第三个标签能暴露这个平面。上述反例只证明局部判据在所述范数体类中的必要区分，不是全有限复合层级的反模型。$\square$

**命题 177.5a（所有实际纯对的量词赚得局部正则性）。** 设 $K$ 是有限维紧凸基，$P=\operatorname{ext}K$。若每个不同 $p,q\in P$ 的实际最小面 $F(p,q)$ 中心对称且仿射维数三，则每个这样的面自动紧且严格凸。其相对边界恰为 $P\cap F$。在其内禀完整菜单中，对纯目标 $a,b$ 有

$$
T_a^F(b)=0\quad\Longleftrightarrow\quad b=2m_F-a.
\tag{177.10}
$$

故两个不同目标的中心方向独立，当且仅当 $T_a^F(b)>0$。

证明。任取中心对称实际面 $F$，中心为 $m$。若 $y\in\overline F$，则 $z=2m-y\in\overline F\subset K$，且 $m=(y+z)/2\in F$。实际面性质迫使 $y,z\in F$，故 $F$ 闭；它包含于紧 $K$，因而紧。

若三维 $F$ 不严格凸，其边界有非平凡线段。在线段内部点取支撑超平面，得到一个非单点真支撑面 $G$，其仿射维数至多二。$G$ 是紧凸体，也是 $K$ 的实际面；取其两个不同极点 $x,y$，它们亦为 $K$ 的极点。于是 $F_K(x,y)\subset G$，与所有原纯对均生成三维面矛盾。因此 $F$ 严格凸，实际面极点性质给 $\operatorname{ext}F=P\cap F=\partial_{\rm rel}F$。此推论使用所有原纯对的量词，不适用于单独给定的任意三维凸体。

把中心移到零。(177.4)及紧支持集说明，$T_a^F(b)=0$ 当且仅当某个 $j\in J(a)$ 满足 $j(b)=-1$。$j(-a)=-1$，而严格凸性使该支撑面的点唯一，故 $b=-a$；反向立即成立。两个不同单位方向线性相关只可能互为对径，得到最后的等价。$\square$

**定义 177.6（完整原生候选 $\mathsf Q_{\rm center}$）。** 采用 [VII，定义102.1][Q177VII] 的同一全有限强分块实层级：$V$ 实有限维且 $\dim V>1$，$W_N=V^{\otimes_{\mathbb R}N}$；每层 $C_N$ 闭、尖、生成，$u_N=u^{\otimes N}$ 严格正；每个有限分块均满足原 min/max 界，全部原置换正且逆正，重括号为规范恒等识别，保留标量对象。全基、全纯点、整个对偶和 proper 区间均按 VII102.1取得。不给定复数、矩阵载体、矩阵秩或指定纠缠准备。

只在整个三份基 $K_3$ 上附加下列关系。面均为包含给定点的最小实际凸面，$F(\varnothing)=\varnothing$。

1. 对每个不同 $p,q\in P_3$，整个 $F(p,q)$ 仿射维数三且中心对称。由177.5a，它已紧且严格凸，可用其自身完整仿射菜单定义177.1的读数。对每一个这样的面 $F$，分别要求存在 $a_F,b_F\in P_3\cap F$，满足 $a_F\ne b_F$、局部 $T_{a_F}^F(b_F)>0$，以及 $\mathsf\Delta_F(a_F)$、$\mathsf\Delta_F(b_F)$。这里三个标签与三个物理份数是不同的两个计数。
2. 由第一项和177.4，每个实际二元面已是完整仿射三球，因而其在纯点 $p$ 的二维切方向 $\tau_p(q)$ 有 [XIII，定义160.2][Q177XIII] 的规范含义。要求同一原域的 TC：

$$
\begin{gathered}
a,b,p\in P_3,\quad a\ne b,\quad p\notin F(a,b)\\
\Longrightarrow\quad
\tau_p(y)\subseteq\tau_p(a)+\tau_p(b)
\quad(y\in P_3\cap F(a,b)).
\end{gathered}
\tag{177.14}
$$

3. 另用整个 $C_3$ 的全局效应区间 $\mathcal E_3=[0,u_3]_{C_3^*}$ 定义 $T_p^{(3)}$，令 $p\perp q$ 当且仅当 $T_p^{(3)}(q)=0$，$p^\perp=\{q\in P_3:p\perp q\}$。要求原 NC：

$$
p\notin F(p^\perp)\qquad(p\in P_3).
\tag{177.15}
$$

第一项中目标的精确量词是逐面存在，而非一对全局目标：

$$
\begin{gathered}
\forall p,q\in P_3,\quad p\ne q,\quad F=F(p,q),\\
\exists a_F,b_F\in P_3\cap F:\quad
 a_F\ne b_F,\quad T_{a_F}^F(b_F)>0,\quad
 \mathsf\Delta_F(a_F)\land\mathsf\Delta_F(b_F).
\end{gathered}
\tag{177.15a}
$$

第二项约束二元面之间的切方向关系；第三项约束原零关系生成的整个面。第三项不能用面内效应替换全局效应。该定义是三项条件的合取；没有声称其中任一项已由另两项推出。

**定理 177.7（从原生配方到同一全有限复量子层级）。** 在定义177.6的强实层级上，复用 [XIII，定理160.5][Q177XIII] 及 [VII，约定102.4的 B1—B3、定理102.11][Q177VII] 的全部供应条件，则 $\mathsf Q_{\rm center}$ 当且仅当存在整数 $n\ge2$ 及一个固定实线性同构

$$
\theta:V\longrightarrow\operatorname{Herm}_n(\mathbb C)
$$

使对每个有限 $N\ge0$，在原张量产品的同一套坐标中有

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{177.16}
$$

这里 $\theta^{\otimes0}=\mathrm{id}_{\mathbb R}$；正层使用实 Hermitian 张量到 Kronecker 矩阵空间的规范识别。

证明。177.5a先赚得每个实际二元面的紧性、严格凸性，并把局部不正交目标转换成两个独立方向；对每个 $F(p,q)$ 分别应用177.4，才把第一项精确变成整个 $K_3$ 上的全称 L2；第二、三项就是同一原域的 TC、NC。XIII160.5的参数取 $V'=W_3,C'=C_3,u'=u_3$，全部纯点、全局菜单和实际面均保持原样。闭、尖、生成与严格正性由强域给出。故该既有重建定理给出一个保单位的整锥同构

$$
\Phi:\operatorname{Herm}_r(\mathbb C)\longrightarrow W_3,
\qquad\Phi(\operatorname{PSD}_r)=C_3,\qquad u_3\Phi=\operatorname{Tr}.
\tag{177.17}
$$

其分类、复数域识别和原邻点排核均属于该供应结果，不在这里重证。特别地，使用它的完整效应结论，而非把先前的面内效应擅自延拓：对每个原纯 $p=\Phi(P)$ 和原基点 $x=\Phi(\rho)$，

$$
T_p^{(3)}(x)=\operatorname{Tr}(P\rho).
\tag{177.18}
$$

于是任意原纯配方 $x=\sum_i a_iq_i$ 均满足

$$
T_p^{(3)}(x)=\sum_i a_iT_{q_i}^{(3)}(p).
\tag{177.19}
$$

这是整个三份域的 $S_3$，包含全部纠缠输入、任意有限项数和零权重，不只是二元面上的局部关系。

接入 VII102.11 时，供应不能只写成未校准的“有一个量子表示”。其102.4各项的精确对应为：B1分别取原 $(W_j,C_j,u_j)$，$j=1,2,3$；VII102.3以实际纯旁观者把(177.19)降到 $S_2,S_1$，给 least/self-dual/谱及面保纯供应。B2取原 $1|1,2|1,1|2$ 复合；正态乘积、正效应乘积、单位、精确产品配对及局部层析，分别由原 min/max 界和整个实张量载体给出。B3使用同一个原二份产品、三份恒等重括号和在整个 $C_3$ 上的原旁观交换；其正性及逆正性都来自强域。它所给的是一套共同方向，不能用分层任取的矩阵坐标替代。这些供应均按 VII102.4引用的既有桥使用。

因此 VII102.11给出同一个 $\theta$，把所有有限层识别为某个有限复 $C^*$ 直和代数 $A=\bigoplus_{i\in I}M_{n_i}(\mathbb C)$ 的标准张量幂。还须排掉额外经典中心：若 $|I|\ge2$，三份直和中至少有两个不同中心扇区；各取一个归一秩一纯点 $p,q$。直和 PSD 的实际支持面规则给

$$
F(p,q)=\operatorname{conv}\{p,q\},
$$

因为其正锥面只是两条位于不同扇区的极射线之和。这个面的仿射维数是一，与第一项矛盾。故只有一个块。$\dim V>1$ 排除 $n=1$，得到(177.16)。全部原产品、效应产品、置换与重括号由所用 VII 定理在同一坐标中保持标准形式。

反向在标准复 PSD 层级中，XIII160.5的反向已给 L2、TC、NC。每个实际二元面在 Bloch 坐标中是三球；177.4的反向给任意两条独立目标方向的中心关系。标准层级满足强域的全部有限分块条件。因此完整候选成立。$\square$

**推论 177.8（现有有限量子公理的对应）。** 在177.7的条件与供应范围内，原数据得到下表中的完整有限维数学对应。

| 原定义或关系 | 所得量子结构 | 推导依据 |
| --- | --- | --- |
| 整个归一基 $K_N$ 与全部极点 | 全部密度矩阵与全部复纯射线 | (177.16)及 PSD 谱分解 |
| 整个 proper 区间、其全部有限单位分解 | $0\preceq E\preceq I$ 与全部有限 POVM | 同一整锥同构的完整对偶 |
| 原态—效应配对 | $f_E(\rho)=\operatorname{Tr}(E\rho)$，纯射线间为模平方 | (177.18)及 VII102.12 |
| 原复合、原单位和置换 | 标准张量幂、所有纠缠态与偏迹 | VII102.11保持同一产品校准 |
| 对每个原有限旁观者的正性 | 矩形 CP、Choi 与 Kraus 描述 | VII102.13的既有完整合同 |
| 逐输入不增迹预算与分支和预算 | 数学 CP-TNI 分支与 CP 仪器 | 同一 Choi/Kraus 对应及 VII102.14—102.15 |

证明。前三行来自整锥等式及对偶，不再预设状态或效应的小菜单；第四行使用同一个 $\theta^{\otimes N}$。后两行逐项复用 VII102.12—102.15 已列明的有限矩形供应、零分支和零质量边界。把数学分支认作全部可用事件仍需该卷的事件饱和条件；选择理想锐中性更新才得到 Lüders 规则；指定连续可逆时间群才接入相应酉生成元与 Hamiltonian 描述。这些不是中心配方关系独自给出的物理选择，物理时钟与 $\hbar$ 的标定也不由此推出。$\square$

**命题 177.9（几何简化、反事实边界与文献范围）。** 完整候选把复矩阵载体和外供二元秩几何，换成原实凸体的中心、目标入项三角形与两个局部不正交目标的确认关系；局部内积由这些定义间关系重建。其余几何合同为实际三维二元面、TC及全局NC，强域的尖性、生成性和严格正单位仍是前件。

证明。177.3的配方桥与177.4的有限参考应用没有使用复数、矩阵秩、环境 Euclidean 度量、光滑支持函数或纯态可逆传递。它们从两条可检测的欧氏轴得到整个三维面；177.7才通过已有整锥分类识别复数及全有限产品。在最终坐标中，二元面的纯边界为 $S^2$，所有有限纯点整体为 $\mathbb{CP}^{n^N-1}$，二元球是整个正 Hermitian 锥及其张量层级的实际支持面。不是把整个高维外接球面都认成纯态。

若删第三标签或第二方向，177.5的光滑非椭球给出明确局部反例。若保留局部球而删全局NC，[XIII160.7][Q177XIII] 的平衡商是满足 L2、TC 却存在真实邻点面塌缩的单锥控制；其每个球也满足177.4的中心关系。该控制没有给出全部有限复合，不用它主张完整强域中的独立性。TC仍是独立保留的合同；本章没有证明它可由局部配方推出，也没有另给删TC的全有限反模型。

与176.10比较，所去掉的是外供复载体、普通秩一族及迹配对；所保留或新支付的是强实层级、实际面三维性、中心对称性及TC、NC；面的紧性与严格凸性已由177.5a推出。二者模型域不同，不能宣称在176的同一弱域上免费减假设，也不宣称全局最短公理数。所有约束也没有变成无前提真理：模型定义给出对象和操作范围，候选约束这些定义之间的相容关系。

文献范围如下。Niestegge [N177][Q177N] §7式(5)、定理7.1及定理9.2分别供应光滑模型的支持函数转移公式、完整互反的 Hilbert 刻画及相应状态空间对应；它们不被另列为本章新结果。欧氏直和方向的概念与结构属于既有 $L^2$-summand 理论；仓内余维一闭合直接复用 VI101.4—101.5，相关书目为 Aizpuru–García-Pacheco, *L²-summand vectors in Banach spaces*, Proc. AMS 134, 2109–2115, DOI [10.1090/S0002-9939-06-08243-8][Q177A]；本章不以尚未核对的该文定理作为证明前提。177.3的目标入项三角形到欧氏轴判据、177.4在本候选中的有限目标应用、177.5a的实际面量词提升和177.7的参数接合是本章纸面推导；不主张已证明文献优先权。XIII160.5、VII102.4与102.11及其量子字典明确作为既有供应复用。$\square$

**命题 177.10（完整白话候选）。** 在能任意有限复合的实概率关系空间里，取整个三份系统。任意两个纯准备撑起的实际小面都只有三个仿射方向，并且有对称中心。在每个小面选两个不同且局部并非完全可区分的纯目标：只要目标本身与另外两个纯标签围成三角形并调出中心，这三个标签反过来确认目标的平均代价，就必须等于目标直接确认中心的代价；两个目标都如此。不同小面在共同纯点处的切方向按177.14相容，而全局上与某纯点互不响应的所有邻点，即使一起生成实际面，也不能把它吞进去。这个候选在177.7列明的供应范围内恰好重建全部有限复量子层级。

证明与图景。一个有中心的实际面若有闭包缺口，中心反射与面性质会把缺口补回来；若它还有平边，边上两纯点就只能撑起至多二维的面，与所有纯对都撑起三维面矛盾。固定一个目标，只要求每个包含它的中心三角形都给同一比较平均值，就会钉住沿该目标的确认斜率：沿线凸性排除不同支持尺的分歧，整个平方长度的凸性再迫使斜率成为线性函数。这里一致的是每个标签处把中心读数压到最低的确认尺，常数确认尺不在其中；所有对径两项关系则成为结论。一条目标方向因此变成一条满足勾股分解的轴，但旁边仍能藏一块非欧氏平面。第二条独立目标方向再锁住一条轴，三维里只剩一条横向直线，已无处藏曲折的范数，整个小面便是一颗球。球与球还须能沿共同端点拼接，且不能把原本不同的整体关系压成同一点：切方向相容支付拼接，全局零邻点不吞回自身排除塌缩。已有整锥定理遂把整个三份对象识别成复量子锥，其完整确认关系再经实际复合推广到所有有限份数。最终画面是许多两条纯线撑起的三维球，嵌在同一个复射影纯态几何和正锥层级中。这里球的度量、复数和一维矩阵线不再预送；三维性与中心对称性、概率复合合同、拼接与非塌缩仍明写在候选里，具体事件、测后选择与时间另有177.8的条件。$\square$

[Q177N]: https://arxiv.org/pdf/2208.07135v1
[Q177A]: https://doi.org/10.1090/S0002-9939-06-08243-8
[Q177XIII]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q177VII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q177VI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md

## 追加锚（本行以下为增补区）


## 178. 原零关系的二元混合封闭与有限量子几何

### 178.1 从两个零读数到一张共同确认尺

**定义 178.1（完整原域与零中点关系）。** 采用 XIII160.1 的有限维实原域：$C\subset V$ 闭、尖、生成，$u$ 严格正于非零正元，$d=\dim_{\mathbb R}V\ge1$。始终取整个 $K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$、完整 $\mathcal E=[0,u]_{C^*}$ 及

$$
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
N_p=\{q\in P:T_p(q)=0\},\quad D_p=\{x\in K:T_p(x)=0\}.
\tag{178.1}
$$

对固定原纯目标 $p$，定义

$$
\boxed{\quad\mathsf Z_2(p):\quad
x,y\in K,\quad T_p(x)=T_p(y)=0
\ \Longrightarrow\ T_p\!\left(\frac{x+y}{2}\right)=0.\quad}
\tag{178.2}
$$

第二端点遍历整个混态域，不只遍历纯点。反向蕴含已由 minimum 达到和效应非负性给出，不是另一条公理。各零读数的达到者可以不同；条件只要求平均之后仍有一张合法原确认尺。

**定理 178.2（二元递归、共同确认与尖锐有限检查界）。** 对每个 $p\in P$，以下条件等价：

1. $\mathsf Z_2(p)$；
2. $D_p$ 是凸集；
3. 存在 $e_p\in\mathcal F_p$，使 $D_p=K\cap\ker e_p$；空面允许；
4. 存在同一张 $e_p\in\mathcal F_p$，同时消去全部 $N_p$；
5. 任意有限纯零配方 $q_i\in N_p$、$a_i\ge0$、$\sum_i a_i=1$ 都满足 $T_p(\sum_i a_iq_i)=0$；
6. 只对 $1\le k\le d-1$ 及 $q_1,\ldots,q_k\in N_p$ 检查 $T_p(k^{-1}\sum_iq_i)=0$。

这些条件还给出 $D_p=\operatorname{conv}N_p=F_K(N_p)$，因此给出原 NC：$p\notin F_K(N_p)$。其中 $F_K(\varnothing)=\operatorname{conv}\varnothing=\varnothing$。若条件失败，存在 $2\le r\le d-1$ 个不同纯零邻点，使其等权混合具有严格正的实际 minimum。

证明。紧凸生成与完整菜单的紧性按 XIII160.1 使用，不要求 $P$ 闭。选任意有限维范数；紧的 $\mathcal F_p$ 有共同对偶范数上界 $M$，故

$$
|T_p(x)-T_p(y)|\le M\|x-y\|.
\tag{178.3}
$$

因此 $D_p$ 闭。闭中点凸集由二进有理插值和极限而凸，得到1等价2。若 $x=ty+(1-t)z\in D_p$、$0<t<1$，取在 $x$ 读零的达到者 $f\in\mathcal F_p$；非负性迫 $f(y)=f(z)=0$。所以 $D_p$ 始终具有零分解遗传性，凸时便是实际真面。

若非空 $D_p$ 凸，取 $x\in\operatorname{ri}D_p$ 及达到 $T_p(x)=0$ 的 $e_p$。对每个 $y\in D_p$，相对内部性质给出 $x=ty+(1-t)z$，其中 $z\in D_p$、$0<t<1$；故 $e_p(y)=0$。反向由 $0\le T_p\le e_p$ 给出 $K\cap\ker e_p\subseteq D_p$，得到3。若 $D_p=\varnothing$，取 $e_p=u$。这里赚得的是已在 $p$ 读一的共同确认者，比 XIII160.10 仅给共同正支撑更强。

3蕴含4；4蕴含5，因为同一 $e_p$ 在有限零混合读零。反过来，对任意 $x\in D_p$，取其有限纯分解和一个在 $x$ 读零的达到者；每个正权纯分支都属于 $N_p$，故始终有 $D_p\subseteq\operatorname{conv}N_p$。5给反向包含，于是 $D_p$ 凸，并完成1—5的等价。它是包含 $N_p$ 的实际面，又等于其凸包，故恰为 $F_K(N_p)$。$T_p(p)=1$ 给 NC。

5立即蕴含6。为证明6足够，令

$$
A_q=\{f\in\mathcal F_p:f(q)=0\}\qquad(q\in N_p).
\tag{178.4}
$$

每个 $A_q$ 是非空闭子集。若没有共同确认者，紧的 $\mathcal F_p$ 给出一个有限最小不相容族 $A_{q_1},\ldots,A_{q_r}$；$r\ge2$。对每个 $j$，删去 $A_{q_j}$ 后可选 $f_j$，它消去所有 $q_i$、$i\ne j$，而 $f_j(q_j)>0$，否则完整交非空。因而

$$
f_j(q_i)=0\ (i\ne j),\qquad 0<f_j(q_j)\le1.
\tag{178.5}
$$

这张对角非零评价表使 $q_1,\ldots,q_r$ 实线性独立，所以 $r\le d$。若 $r=d$，写 $p=\sum_i c_iq_i$；对 $f_j$ 评价得 $c_j=1/f_j(q_j)\ge1$，而对 $u$ 评价却得 $\sum_i c_i=1$，与 $r\ge2$ 矛盾。因此 $r\le d-1$。这些标签的等权混合没有读零的确认者，紧性又使实际 minimum 严格正，违反6。若 $N_p$ 为空，共同确认者 $u$ 直接存在；$d=1,2$ 时也不会出现上述不相容族。重复标签和零权由删去冗余项处理。$\square$

**命题 178.3（$d-1$ 不能一般降低）。** 对每个 $r\ge2$，存在 $d=r+1$ 维完整原域与一个原纯目标，其全部少于 $r$ 标签的纯零配方均读零，却有一个 $r$ 标签配方读 $1/r$。

证明。在 $\mathbb R^{r+1}$ 中取标准基 $p=e_0,q_i=e_i$，并置

$$
z=\frac{\sum_{i=1}^r q_i-p}{r-1},\qquad
u(x)=\sum_{i=0}^r x_i,\qquad
K=\operatorname{conv}\{p,q_1,\ldots,q_r,z\},\qquad C=\operatorname{cone}K.
\tag{178.6}
$$

这些点都在 $u=1$；紧性给闭锥与严格正单位，基向量给生成性，单位给尖性。$p,z$ 分别唯一最大、最小化 $x_0$；$q_i$ 唯一最大化 $x_i+x_0/2$。故所列点恰为全部原纯点。

一张确认 $p$ 的原效应由 $b_i=f(q_i)$ 完全确定。它的精确条件是

$$
0\le b_i\le1,\qquad \sum_i b_i\ge1,\qquad
f(z)=\frac{\sum_i b_i-1}{r-1}.
\tag{178.7}
$$

上界 $f(z)\le1$ 已由 $\sum_i b_i\le r$ 给出。在 $b_j=1$、其余为零处得到合法 $f_j$，它同时消去 $z$ 和所有 $q_i$、$i\ne j$。所以 $N_p=\{q_1,\ldots,q_r,z\}$，每个少于 $r$ 标签的配方都留下一个未使用的 $q_j$，由同一 $f_j$ 消去。另一方面(178.7)给

$$
T_p\!\left(\frac1r\sum_{i=1}^r q_i\right)
=\min\frac1r\sum_i b_i=\frac1r.
\tag{178.8}
$$

这证实有限检查界的尖锐性。该多面体不满足 L2，结论只针对一般原域的有限检查成本。$\square$

### 178.2 局部量子球仍能隐藏多层零混合失败

**命题 178.4（平衡商的共同确认秩与精确中点深度）。** 使用 [XII159.1、159.3][Q178XII] 的既有平衡商族，$m\ge3$：

$$
H=\operatorname{diag}(I_m,-I_m),\quad
\pi:\operatorname{Herm}_{2m}(\mathbb C)\to
\operatorname{Herm}_{2m}(\mathbb C)/\mathbb RH,\quad
C_m=\pi\operatorname{PSD}_{2m},\quad u_m\pi=\operatorname{Tr}.
\tag{178.9}
$$

它满足完整原域、实际 L2 和 AD。对全部原纯目标及少于 $m$ 个纯零邻点，任意有限混合仍实际读零；全混态条件 $\mathsf Z_2$ 却失败。以纯零邻点为叶、以中点为内部节点的二叉配方树，其首次可出现非零节点的最小高度恰为

$$
h_m=\lceil\log_2m\rceil.
\tag{178.10}
$$

证明。模型、全纯点 $p_v=\pi P_v$、原全效应

$$
\{E:0\preceq E\preceq I,\ \operatorname{Tr}(EH)=0\}
\tag{178.11}
$$

及纯态 minimum $T_{p_v}(p_w)=|v^*w|^2$，均直接复用 XII159.1，不重报其最早 $m$ 点面塌缩为新结果。实际支持二维面是整颗 Bloch 球；对径向量正交，纯 minimum 因而给 AD。其局部三角形条件也由177.4反向成立。

先把既有谱计算用于共同消去。设 $\rho\succeq0$、$\operatorname{Tr}\rho=1$、$\rho v=0$ 且 $\operatorname{rank}\rho<m$。置 $h=v^*Hv$。XII159.1证明中的压缩 $Q_vHQ_v|_{v^\perp}$（$Q_v=I-P_v$）的谱为 $+1$、$-1$ 各 $m-1$ 次及 $-h$。若 $h>0$，不大于 $-h$ 的谱子空间复维数为 $m$，故可取单位 $b\perp v,\operatorname{ran}\rho$，满足 $\delta=b^*Hb\le-h$。于是

$$
E=P_v+\frac{h}{-\delta}P_b
\tag{178.12}
$$

属于(178.11)，确认 $p_v$ 且消去 $\pi\rho$。若 $h<0$，取不小于 $-h$ 的正谱子空间并用 $E=P_v+(-h/\delta)P_b$；若 $h=0$，取 $E=P_v$。这给任意秩小于 $m$ 的零邻点支持一张共同确认者，没有把低秩实际面保真误当作全效应延拓。少于 $m$ 项的零配方满足该秩界，包括删去零权后的重复标签。

为读出失败，固定正扇区的 $p=p_{e_1}$。对负扇区上的任意密度矩阵 $\sigma$，XII159.3的原谱公式在此可直接算为

$$
T_p(\pi\sigma)=\lambda_{\min}(\sigma).
\tag{178.13}
$$

确实，确认者的正块迹至少一，而核正交约束迫负块迹同样至少一，所以 $\operatorname{Tr}(E\sigma)\ge\lambda_{\min}(\sigma)$；取最小特征向量 $b\in E_-$，原合法效应 $P_{e_1}+P_b$ 达到等号。这个中间公式属于已有谱供应的应用。

把负扇区正交基分成大小为 $r,s\ge1$ 的两组，$r+s=m$。令 $x,y$ 分别为两组均匀密度矩阵的原像，则

$$
T_p(x)=T_p(y)=0,\qquad
T_p\!\left(\frac{x+y}{2}\right)=\frac1{2\max(r,s)}>0.
\tag{178.14}
$$

例如 $m=4,r=s=2$，两个二纯点混合各读零，中点却读 $1/4$。对所有纯输入的二元零检查仍全部通过，因为其支持秩至多二、小于 $m$。

高度为 $h$ 的二叉中点树至多有 $2^h$ 个叶位置，故 $2^h<m$ 时每个节点都由上述共同确认者保持零。反向置 $L=2^{h_m}$，取满树，左右半树分别使用互不相交的负坐标标签组；把 $m$ 个标签分组，使每组大小至多 $L/2$，余下叶位置重复本组标签。因为 $L/2<m\le L$，每个非根节点只涉及少于 $m$ 个标签，故读零。根的负扇区密度矩阵的对角项为 $n_j/L$，其中 $n_j\ge1$、$\sum_jn_j=L<2m$；至少一个 $n_j=1$。由(178.13)，根读数精确为 $1/L>0$。这证明(178.10)。

因此任意固定纯标签数或固定中点树高度，都不能替代量化全部混态的(178.2)。这是单锥控制；没有构造违反新条件的全有限张量层级，不据此声称完整强域中的独立性。$\square$

### 178.3 不用切方向的新完整候选

**定义 178.5（原生三角形、对径零与零平均）。** 全部采用177.6的强实全有限背景，含 $\dim V>1$、$W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正乘法单位、每个有限 min/max 分块、全对偶与全菜单、原正置换及正逆、规范重括号和标量层。不给定复载体、矩阵秩或纠缠种子。只在整个 $K_3$ 要求下列三项：

* **局部中心三角形。** 每个不同原纯对的实际面 $B$ 中心对称且仿射三维；每个 $B$ 分别存在 $a_B\ne b_B$、$T^B_{a_B}(b_B)>0$，并各满足177.6第一项的目标入项三角形律。明确地，对目标 $a$ 和任意非退化正权中心三角形

$$
\lambda a+\mu q+\nu r=m_B,\qquad
\lambda,\mu,\nu>0,\quad\lambda+\mu+\nu=1,
$$

要求 $\lambda T^B_a(a)+\mu T^B_q(a)+\nu T^B_r(a)=1/2$。局部读数只使用该面自身的完整仿射菜单；其紧性与严格凸性仍由177.5a供应。
* **对径零响应。** 对每个上述实际面 $B$ 和每个 $p\in P_3\cap B$，$T^{(3)}_p(2m_B-p)=0$，即原 global AD。
* **二元零平均。** 对每个 $p\in P_3$ 以及任意 $x,y\in K_3$，满足 $\mathsf Z_2(p)$；这里 $T^{(3)}$ 用整个三复制原效应区间。

记三项合取为 $\mathsf Q_{\rm zero}$。局部存在目标对的量词逐面分别成立；AD 与零平均量化完整全局对象，没有把面内尺提前当成可延拓的全局尺。

**定理 178.6（同一坐标下的全部有限量子锥）。** 在定义178.5的完整强域内，$\mathsf Q_{\rm zero}$ 当且仅当存在整数 $n\ge2$ 及固定实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使所有有限 $N\ge0$ 满足

$$
\boxed{\quad\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.\quad}
\tag{178.15}
$$

$N=0$ 时 $\theta^{\otimes0}=\mathrm{id}_{\mathbb R}$；正层使用实 Hermitian 张量到 Kronecker 矩阵空间的规范识别。原产品、完整对偶配对、单位、位置置换和重括号都由同一个 $\theta$ 保持。

证明。局部条款逐面应用177.5a及177.4，得到整个三复制域的 L2。178.2以 $V'=W_3,C'=C_3,u'=u_3$ 给原 NC；第二项恰给同一域的 AD。由此字面满足 [XIII162.16][Q177XIII] 的 $\mathsf R_3=\mathrm{L2}_3+\mathrm{NC}_3+\mathrm{AD}_3$。其背景(162.20)—(162.21)中的全有限原 min/max、单位、层析、正置换与恒等重括号均由178.5保留；其全基、纯点及全菜单正是这里的对象。

直接消费该既有定理：XIII162.10先给整个 $C_3$ 的复矩阵类型；其实际纯旁观者面供应低两层，同一个二复制产品及三复制交换供应共同方向，随后调用其已明确指定的161及VII102传播尾部。故得到同一个 $\theta^{\otimes N}$ 的(178.15)，不把各层任取坐标混作一致坐标，也不重新输入 TC、完整 S3 或 B1—B3。$\dim V>1$ 排除 $n=1$。

反向，在标准复 PSD 层级，实际二元面是 Bloch 三球，任意两个非对径目标满足局部中心三角形律；对径投影正交给 AD。原全菜单的 minimum 为 $T_p(\rho)=\operatorname{Tr}(P\rho)$，非负线性读数给零平均。其全部有限背景和标量层均为标准结构，故 $\mathsf Q_{\rm zero}$ 成立。$\square$

**推论 178.7（量子公理对应与表达的节省）。** 在178.6的范围内，以下对应沿用 XIII162.9、177.8及其各自指定的既有字典。

| 原对象或关系 | 所得有限量子结构 |
| --- | --- |
| 整个 $K_N$、全部 $P_N$ | 全部密度矩阵、复纯射线及叠加射影几何 |
| 整个效应区间与全部有限单位分解 | $0\preceq E\preceq I$、PVM 与数学 POVM |
| 原态—效应配对及完整确认 minimum | $f_E(\rho)=\operatorname{Tr}(E\rho)$，纯对为重叠模平方 |
| 原全部有限复合、单位收缩及置换 | 标准复张量、全部纠缠态及偏迹 |
| 对每个有限原旁观者的正性与全输入质量预算 | 数学 CP、矩形 Choi/Kraus、CP-TNI 分支和 CP 仪器 |

证明与边界。前三行由同一整锥同构及完整对偶，第四行由同一个张量幂坐标，末行逐项消费 XIII162.9 的(162.23)及其完整矩形、零分支和零质量合同。把所有数学分支认作实际可用事件仍须事件饱和；理想锐中性条件才给指定 Lüders 更新；另给连续保锥保单位的实时间群才得到其酉表示与生成元。时钟和 $\hbar$ 标定不由静态零关系推出。

与177.6在同一强域比较，177.7和178.6都等价于(178.15)。本章的全局入口只要求球内对径的原零关系与整基上的二元零平均，不需要在候选中陈述切方向或零邻点的最小实际面包。前者保留 AD 的刻度成本，后者由178.2支付 NC；在标准模型中 TC 随之恢复。这里简化的是关系语言和接合接口，不是已证明独立公理数严格减少。局部三维性、中心对称性、目标三角形与全部有限复合背景仍显式保留；没有证明 Z2 单独自动给 AD，也没有把没有同域反模型说成已证独立性。$\square$

**命题 178.8（数学归属与完整白话候选）。** 本章使用有限维紧性、闭中点凸性、实际面的线段性质及矩阵谱作为成熟中间工具。178.2的有限不相容评价表、178.3的尖锐原域、178.4的共同消去支持及中点深度转换，以及178.6的精确原域接合构成本章的纸面推导；不主张文献优先权。XII159的平衡商、完整效应及原谱公式，177的局部欧氏轴定理，XIII162的重建和全有限传播均按其原有条件复用。

证明与图景。先保留一整套能任意有限复合的实概率空间及全部原尺，只检查整个三份系统。任意两个纯准备撑起一张有中心的三维实际面；每张面各选两个局部不完全可区分的目标，只检查分别包含目标的中心三角形的反向确认平均。已有两轴证明把这张面钉成球。球的每条直径都要能被原全域尺读成一和零。再只加一条混合规矩：若两个状态都能在确认同一个纯目标时读成零，把它们平均后仍应能读零；这两个状态本身可以已经是混合。递归做下去，原先各有一把尺的全部零分支便能共用一把真正确认目标的尺，零邻点组成的实际面因而不会吞回目标。已有整球重建和共同产品传播于是得到复射影纯态几何、正 Hermitian 锥及其全部有限张量层级。若只看纯端点，平衡商里的小球全都圆、每对纯读数也都正确，却能在混合树的深处忽然冒出正读数；(178.10)精确算出最早露馅的层数。三维小面的方向数、局部三角形的标签数、三份物理系统和混合树的高度是四个不同计数。这套候选把外部公理写成原定义之间的相容约束，并不把它们宣布为无前提真理；事件、更新和时间继续保留178.7列明的条件。$\square$

[Q178XII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md

## 追加锚（本行以下为增补区）


## 179. 零影超平面、二目标面束与同原量子重建

### 179.1 共同零影与尚未支付的交点

**定义 179.1（纯零极性与实际零影超平面）。** 全部沿用178.1的有限维完整原域，且 $d>1$。记 $p\perp q$ 当且仅当 $T_p(q)=0$。对任意 $A\subseteq P$ 置

$$
A^\perp=\{r\in P:\ r\perp a\text{ 对所有 }a\in A\},\qquad
H_A=\bigcap_{a\in A}D_a,\qquad H_\varnothing=K.
\tag{179.1}
$$

在实际 L2 下，每个实际二元球 $B=F_K(a,b)$，$a\ne b$，给一条纯点线 $\ell_B=P\cap B$。这里的线是整颗球的纯边界，不是两个标签间的实线段。定义原域条件

$$
\boxed{\quad\mathsf{ZH}:\quad
\text{每个 }D_p\text{ 是凸集，且 }
N_p\cap\ell_B\ne\varnothing
\quad(p\in P,\ B\text{ 为任意实际二元球}).\quad}
\tag{179.2}
$$

称之为实际零影超平面条件。凸性约束整个混态零集；第二项只要求相交，不预先指定交点、对径或非零概率。纯点 $p$ 可以在 $B$ 内，也可以在球外。几何超平面的“超”指每条纯点线的相交性质，不指 $\operatorname{aff}D_p$ 在原实空间中余维一。

**命题 179.2（两目标确定一个共同零面）。** 假设 L2 和全混态 $\mathsf Z_2$。对同一实际球 $B$ 内任意两个不同纯点 $a,b$，有

$$
\boxed{\quad D_a\cap D_b
=\bigcap_{c\in\ell_B}D_c
=\operatorname{conv}(\ell_B^\perp).\quad}
\tag{179.3}
$$

对任意纯目标 $p$，$N_p\cap\ell_B$ 只能是空集、单点或整个 $\ell_B$。这些结论不要求 AD、数值 pure PR 或面效应延拓。

证明。补效应交换一与零，给纯零对称性；这是 XIII162.1 的既有原菜单事实。178.2使每个 $D_p$ 成为实际暴露面。因此 $D_a\cap D_b$ 是紧实际面。若其纯点 $r$ 同时零于 $a,b$，对称性使实际面 $D_r$ 包含 $a,b$，进而包含整个 $F_K(a,b)=B$。于是 $r$ 零于 $\ell_B$ 的每个纯点；反向显然。紧面的纯凸生成给(179.3)。同球内任意两个不同纯点的原实际面都是整个 $B$，因为三球没有真非点面，所以结果与选哪两个目标无关。

同样，$D_p\cap B$ 是 $B$ 的闭面，只能为空、球面单点或整个球。其纯点集恰为 $N_p\cap\ell_B$，给最后结论。任意族 $H_A$ 亦是实际暴露面：取178.2的共同确认者 $e_a$，从其有限维线性张成中选有限基，所选非负效应的平均在 $K$ 上取零，当且仅当所有 $e_a$ 都取零。空族用零效应。这个有限维交零面的成熟步骤只是上述面束计算的中间工具。$\square$

**定理 179.3（相交律给实际 coatom 与纯点—超平面对应）。** 在 L2 和 $\mathsf{ZH}$ 下，每个 $D_p$ 都是非空的实际 coatom，映射 $p\mapsto D_p$ 是 $P$ 到全部实际 coatoms 的双射，且

$$
q\in D_p\quad\Longleftrightarrow\quad p\in D_q.
\tag{179.4}
$$

对每个 $p\in\ell_B$，$N_p\cap\ell_B$ 恰为 $p$ 在球 $B$ 内的对径单点。因此 AD 是(179.2)的后果。

证明。178.2把(179.2)的凸性变为全混态 $\mathsf Z_2$、同一原确认者及 NC。非平凡紧底有至少两个纯点，相交律使每个 $N_p$ 非空。又 $p\notin D_p$，所以 $D_p$ 是非空真面。

设有真实际面 $G\supsetneq D_p$。取 $r\in P\cap(G\setminus D_p)$ 和 $s\in P\setminus G$；存在性由原紧底的有限纯分解及面性质给出，不要求先证明 $G$ 暴露或闭。实际球 $B=F_K(r,s)$ 与 $N_p$ 相交于某纯点 $t$。因为 $t\in D_p$，有 $t\ne r$，而 $G$ 包含 $r,t$。L2和球的严格凸面结构给 $F_K(r,t)=B$，于是 $G$ 包含 $s$，矛盾。因此 $D_p$ 是 coatom。

固定 $p\in\ell_B$。由179.2和相交律，$N_p\cap\ell_B$ 是一个单点 $t$：整个球的情形被 $T_p(p)=1$ 排除。取达到 $T_p(t)=0$ 的原确认者。其在球上的限制在 $p,t$ 分别取一、零；三球上非恒定仿射效应的最大、最小点必是对径点，所以 $t=2m_B-p$。这正给 AD，过程中没有把局部尺当作可全域延拓的尺。

若 $D_p=D_q$、$p\ne q$，在 $B=F_K(p,q)$ 上，相同的零交点同时是 $p$ 与 $q$ 的对径点，迫使 $p=q$，矛盾。因此映射单射。满射直接复用 XIII162.12证明中的 coatom 极标接口：原 NC 使每个非空 coatom $G$ 都有纯极标 $r$，满足 $F_K(N_r)=G$。178.2给 $F_K(N_r)=D_r$，故 $G=D_r$。非平凡底没有空 coatom。(179.4)仍仅为纯零对称性，不冒充非零读数互易。$\square$

### 179.2 从零关系的严格反包含赚得确认刻度

**定义 179.4（严格零分离）。** 在178.1完整原域上定义

$$
\mathsf{Sep}_0:\qquad
N_p\subseteq N_q\ \Longrightarrow\ p=q
\qquad(p,q\in P).
\tag{179.5}
$$

它正是 [Emir—Kruml—Paseka—Vetterlein，Definition 8][Q179E] 的 strongly irredundant 条件在原零关系上的实例，不作为新定义内容申领；它同时排除相同零影和不同纯点间的零影严格包含，仅有 $N_p=N_q\Rightarrow p=q$ 不替代它。以下不假设 L2。该文的关系公理 (L1)、(L2) 与本卷的实际三球 L2 是不同条件，不能因符号相同而互换。

**定理 179.5（正零支撑的唯一最大点与 coatom 正规形）。** 在有限维完整原域且 $d>1$ 时，下列条件等价：

1. NC 与 $\mathsf{Sep}_0$；
2. 对每个 $p$，存在非零 $g\in C^*$ 消去 $N_p$；而每个这样的 $g$ 的整个 $K$ 上最大点恰为 $p$；
3. 全混态 $\mathsf Z_2$，每个 $D_p$ 是 coatom，且 $p\mapsto D_p$ 单射。

因此严格零分离加 NC 已经给原 proper 共同确认者和零平均闭合，但这里没有由它们推出 L2 或 AD。

证明。XIII160.10在同一完整原域上供应 NC 与非零正共同支撑存在性的等价；这一步没有把支撑预称为确认者。假设1，取任意非零正 $g$ 消去 $N_p$，令 $M=\max_Kg>0$。选纯最大点 $r$。则 $g/M\in\mathcal F_r$ 且消去全部 $N_p$，故 $N_p\subseteq N_r$。严格零分离迫使 $r=p$。所有纯最大点都如此，最大面由其纯点生成，故最大面恰为 $\{p\}$；特别地 $M=g(p)$。这证明2，也精确支付了原先缺少的 proper 上界：

$$
e_p=\frac{g}{g(p)}\in\mathcal F_p,\qquad e_p|_{N_p}=0.
\tag{179.6}
$$

反过来，2中的存在性给 NC。若 $N_p\subseteq N_q$，取消去 $N_q$ 的非零正 $g$；它也消去 $N_p$，故其唯一最大点既是 $p$ 又是 $q$，得严格零分离。

由(179.6)及178.2得到 $\mathsf Z_2$，所以 $D_p=F_K(N_p)$。选包含这个真面的 coatom $G$。XIII162.12的同域极标接口给 $G=F_K(N_r)$、$N_r=P\cap G$。因此 $N_p\subseteq N_r$，严格零分离给 $r=p$，从而 $G=D_p$。若 $D_p=D_q$，取纯点即得 $N_p=N_q$，故 $p=q$。于是1给3。

最后由3和178.2得 NC。若 $N_p\subseteq N_q$，则 $D_p=\operatorname{conv}N_p\subseteq\operatorname{conv}N_q=D_q$。coatom 性给相等，单射再给 $p=q$。这证明3给1。

由此不能越过对径缺口：一个原效应在 $p$ 有唯一全域最大点，并不保证其在每颗经过 $p$ 的球上最低值为零。例如球上效应 $(3+z_1)/4$ 在 $p=(1,0,0)$ 唯一取一、在对径取 $1/2$。这只是限制效应的范围控制，不是完整 L2 加上述前件的反模型。$\square$

**命题 179.6（严格零分离与双零闭包的边界控制）。** 严格零分离单独不推出 NC 或 $\mathsf Z_2$；而 NC、严格零分离及所有实际面双零闭合，也不能在删除球条件后代替正交模律或度量自对偶。

证明。第一条复用178.4及 XII159的平衡商。其纯点一一对应复射线，$N_{p_v}$ 恰为 $v^\perp$ 的全部纯射线。两个同维复超平面若包含便相等，所以严格零分离成立；每个实际二元球的复二维支持也总与 $v^\perp$ 相交，所以它还通过全部纯零影相交检查。其 NC 和 $\mathsf Z_2$ 却失败。因此179.5中的 NC 不能被静默删去；(179.2)的纯影相交也不能吸收整混态零面的凸性。这是既有单锥控制的应用，不是全有限独立性结果。

第二条直接使用 [FINITE PURE VII97.3、97.6—97.7][Q179F] 的既有完整有理七边形。按其模七编号，$D_{p_i}=Q_i=[p_{i+3},p_{i+4}]$，故 $N_{p_i}=\{p_{i+3},p_{i+4}\}$ 两两不同且不可严格包含。各 $D_{p_i}$ 为实际边，所以全混态 $\mathsf Z_2$、NC 与严格零分离成立；其整个面格的双零闭合按97.3复用。然而

$$
F=\{p_0\}\subset G=[p_0,p_1],\qquad
F^\perp=Q_0=[p_3,p_4],\qquad
G\cap F^\perp=\varnothing,
$$

所以 $F\vee(G\cap F^\perp)=F\ne G$。度量自对偶的失败已由97.6的三环读数证明，这里不重复该计算。七边形的实际二元面不全是三球，不能据此否定一般 L2 加 $\mathsf Z_2$ 到 AD 的命题。这个控制只说明：零极性、所有面双零闭合与正交模分解是不同义务。$\square$

### 179.3 一条零影几何条件的完整有限候选

**定义 179.7（三复制零影候选）。** 完整保留178.5的强实全有限背景，以及该定义第一项逐实际面的局部中心三角形条件。把其余全局入口换为整个 $C_3$ 上的 $\mathsf{ZH}$，记新候选为 $\mathsf Q_{\rm hyp}$。所用 $K_3,P_3,\mathcal E_3$ 均为原完整对象，既不只检查产品纯点，也不以一体零影代替三复制零影。

**定理 179.8（零影超平面与全部有限量子层级）。** 在定义179.7的精确背景内，下列等价：$\mathsf Q_{\rm hyp}$；178.5的 $\mathsf Q_{\rm zero}$；存在固定整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使全部有限 $N\ge0$ 满足

$$
\boxed{\quad\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.\quad}
\tag{179.7}
$$

证明。177.5a与177.4在每张原实际面上给 L2，参数对应与178.6相同。179.3把同一个三复制原域的 $\mathsf{ZH}$ 送为 NC 与 AD；178.2给 $\mathsf Z_2$。因此得到178.5的完整候选，直接消费178.6，得到(179.7)及同一坐标、所有有限分块、标量层和单位的结论，不重新分类或另选各层坐标。

反向须核对额外的球外量词。在标准 $D\times D$ 复矩阵层，$p=P_v$ 的完整混态零面为 $\mathcal D(v^\perp)$。实际二元球由一个复二维子空间 $S$ 给出。维数公式使

$$
\dim_{\mathbb C}(S\cap v^\perp)\ge1.
\tag{179.8}
$$

若 $S\subset v^\perp$，零影包含整条纯线；否则交是一条复射线，所以只交一个纯点。故无论 $p$ 是否位于该球，都满足(179.2)。其零面凸性、原全菜单和局部三角形由178.6的标准反向给出。由178.6已知 $\mathsf Q_{\rm zero}$ 等价于(179.7)，三项等价完成。$\square$

**推论 179.9（较简洁的整体几何与量子公理字典）。** 在179.8的范围内，第 $N$ 层的纯点—零影对应为

$$
\mathbb CP^{n^N-1}\ni[v]
\longmapsto\mathbb P_{\mathbb C}(v^\perp),\qquad
\ell_B=\mathbb CP^1\simeq S^2.
\tag{179.9}
$$

它是非退化的纯零关联极性；179.3的实际 coatoms 正是这些超平面的全部密度矩阵底。这里不把纯零影误画成整颗高维欧氏球。

证明与对应。179.8取得的同一个完整正锥、原单位和完整对偶，直接支付178.7的全部字典：态归一化给密度矩阵和纯射线，原配对给 Born 规则，有限单位分解给数学 PVM/POVM，同一张量幂坐标给全部有限复合、纠缠和偏迹，对全部原有限旁观者的正性与全输入质量预算给数学 CP/Choi/Kraus 及 CP 仪器。实际面的完整双零闭合、支持投影和 least 确认者在这里按 XIII162.11复用，不能倒填为裸 $\mathsf Z_2$ 的前件或结论。

在单系统矩阵大小 $D=n^N\ge2$ 时，纯零影为 $\mathbb CP^{D-2}$，其整个混态面实仿射维数是 $(D-1)^2-1$；它在 $K_N$ 中余维 $2D-1$，通常远大于一。这解释了定义179.1的关联超平面用语。$N=0$ 的标量底只有一个纯点，零影为空，没有二元球；它沿179.8的标量约定保留。

全局候选现在可表成“每个纯点的混态零影是实际面，纯影遇到每条二元线”；对径位置及纯点—coatom 一一对应成为推导结果。简化发生在几何语言与局部—整体接口，不声称逻辑前件严格变弱或独立公理数减少。实际事件饱和、指定 Lüders 更新、连续时间群、时钟和 $\hbar$ 均继续保留178.7的对应条件；静态零关联没有支付它们。$\square$

**命题 179.10（数学归属、未决桥与完整白话候选）。** 179.2的同球二目标零面束、179.3的实际 coatom 与单射推导、179.5的严格零分离正规形，以及179.8对整个三复制域及球外相交量词的接合，采用 `repo-derived` 综合推导归属。零关系的 Galois 恒等式、有限维暴露面交和球上仿射极值为成熟中间工具；XIII160.10、162.12、162.16，177—178与有限纯点卷VII97按原有范围使用，不主张新分类或文献优先权。几何超平面的“每线交一点或全线”用语复用 [Saniga 的原定义][Q179H]，并不借用该文有限构型的分类；本章的点是全部原纯点，线由 L2 给唯一实际二元球的纯边界，179.2证明其零影子空间性质。严格零分离及 Dacey 条件分别见 [Q179E] 的 Definition 8与13；本章没有从前者偷渡后者。

证明与边界。一般 $\mathrm{L2}+\mathsf Z_2\Rightarrow\mathrm{AD}$ 仍未由本章证明，亦没有同域反模型；(179.2)的相交要求不能冒称零平均的免费后果。179.5并未证明一般 $D_p$ 自动为 coatom，或 $\mathsf{Sep}_0$ 自动由 L2 加 $\mathsf Z_2$ 给出。179.6也不反驳这些保留 L2 的命题。上述明确前件下的完整候选与这些开放问题分开。

白话上，先保留能任意有限复合的实概率空间及全部原测试，只看整个三份系统。局部仍让任意两个纯准备撑起一张有中心的三维小面，每张面上的两个中心三角形目标把它锁成球。全局只看一件几何关系：确认某个纯准备时，所有能读成零的状态必须组成一张实际面，而且它的纯点零影要遇到每颗二元球。于是从球内目标出发，零影在这颗球上既不能全占，也不能落空，只能交一个点；一与零的刻度把这个点钉成几何对径。若零影还能藏在更大的真面里，从大面内外各取一个纯点，它们的球就会被相交律拉回大面，产生矛盾，所以零影已经是极大真面。两个不同目标也不能拥有同一张零影。不同球之间，随便挑球内哪两个不同目标，它们共同看不见的部分都一样；两目标已经确定整球的共同零底。已有重建遂把这个画面识别为同一个复射影空间：小球是复射影直线，每个纯点对应一张正交超平面，混态则填满相应的正 Hermitian 面及全部有限张量层。这里把外部公理改写为原定义间可检验的零关联相容性，没有声称它是无前提真理；若要进一步删去“每球必相交”，仍须真正闭合前段的开放桥。$\square$

[Q179F]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md
[Q179E]: https://arxiv.org/html/2103.13764v1 "K. Emir, D. Kruml, J. Paseka, T. Vetterlein，Linear orthogonality spaces as a new approach to quantum logic，Definition 8、Definition 13。"
[Q179H]: https://arxiv.org/html/1101.0977v1 "M. Saniga，Geometric Hyperplanes: Desargues Encodes Doily，几何超平面的定义段。"

## 追加锚（本行以下为增补区）
