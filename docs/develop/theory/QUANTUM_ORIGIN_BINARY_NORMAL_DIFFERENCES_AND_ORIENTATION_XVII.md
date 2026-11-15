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

第二条直接使用 [FINITE PURE VII定理97.3、命题97.6及式(VII97.7)][Q179F] 的既有完整有理七边形。按其模七编号，$D_{p_i}=Q_i=[p_{i+3},p_{i+4}]$，故 $N_{p_i}=\{p_{i+3},p_{i+4}\}$ 两两不同且不可严格包含。各 $D_{p_i}$ 为实际边，所以全混态 $\mathsf Z_2$、NC 与严格零分离成立；其整个面格的双零闭合按97.3复用。以下用该定理的混态面正交补 $F^\#=\bigcap_{a\in P\cap F}D_a$，区别于(179.1)的纯点极集。此时

$$
F=\{p_0\}\subset G=[p_0,p_1],\qquad
F^\#=Q_0=[p_3,p_4],\qquad
G\cap F^\#=\varnothing,
$$

所以 $F\vee(G\cap F^\#)=F\ne G$。度量自对偶的失败已由97.6的三环读数证明，这里不重复该计算。七边形的实际二元面不全是三球，不能据此否定一般 L2 加 $\mathsf Z_2$ 到 AD 的命题。这个控制只说明：零极性、所有面双零闭合与正交模分解是不同义务。$\square$

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

白话上，先保留能任意有限复合的实概率空间及全部原测试，只看整个三份系统。局部仍让任意两个纯准备撑起一张有中心的三维小面，每张面上的两个中心三角形目标把它锁成球。全局只看一件几何关系：确认某个纯准备时，所有能读成零的状态必须组成一张实际面，而且它的纯点零影要遇到每颗二元球。于是从球内目标出发，零影在这颗球上既不能全占，也不能落空，只能交一个点；一与零的刻度把这个点钉成几何对径。若零影还能藏在更大的真面里，从大面内外各取一个纯点，它们的球就会被相交律拉回大面，产生矛盾，所以零影已经是极大真面。两个不同目标也不能拥有同一张零影。对同一颗球，共同零底不依赖球内选哪两个不同目标；两目标已经确定整球的共同零底。已有重建遂把这个画面识别为同一个复射影空间：小球是复射影直线，每个纯点对应一张正交超平面，混态则填满相应的正 Hermitian 面及全部有限张量层。这里把外部公理改写为原定义间可检验的零关联相容性，没有声称它是无前提真理；若要进一步删去“每球必相交”，仍须真正闭合前段的开放桥。$\square$

[Q179F]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md
[Q179E]: https://arxiv.org/html/2103.13764v1 "K. Emir, D. Kruml, J. Paseka, T. Vetterlein，Linear orthogonality spaces as a new approach to quantum logic，Definition 8、Definition 13。"
[Q179H]: https://arxiv.org/html/1101.0977v1 "M. Saniga，Geometric Hyperplanes: Desargues Encodes Doily，几何超平面的定义段。"

## 追加锚（本行以下为增补区）

## 180. 二元面中的零关系分解与实际线恢复

### 180.1 只在面内要求的一条生成等式

**定义 180.1（二元面的零关系分解）。** 沿用178.1的完整有限维原域，$d>1$。在实际 L2 与全混态 $\mathsf Z_2$ 下，178.2已使每个 $D_p$ 成为实际面。所有 join 均在原实际面格中取，不在另造的零闭包格中取。定义

$$
\boxed{\quad\mathsf J_2:\qquad
B=\{p\}\vee(B\cap D_p)
\quad(B\text{ 为实际二元球},\ p\in P\cap B).\quad}
\tag{180.1}
$$

这里不输入中心、对径、coatom 或球外目标的相交条件。它是正交模恒等式 $G=F\vee(G\wedge F^\perp)$ 在“单点包含于二元面”上的实际化片段；定义中的 $D_p$ 仍由整个原菜单产生。尚未给一般实际面的正交补，故不能在此宣布原面格已经正交模。

**定理 180.2（二元分解、实际替换与完整候选）。** 在实际 L2 和全混态 $\mathsf Z_2$ 下，下列条件等价：$\mathsf J_2$；AD；以及

$$
\forall p\ne q\in P\ \exists r\in P:\quad
p\perp r,\qquad F_K(p,q)=F_K(p,r).
\tag{180.2}
$$

它们还等价于179.1的 $\mathsf{ZH}$。最后一个等价消费既有单系统重建，并非从一般 coatom 性免费推出相交。

证明。179.2使 $B\cap D_p$ 只能为空、球面单点或整个 $B$；$p\notin D_p$ 排除最后一种。若(180.1)成立，交不能空，因为 $\{p\}\vee\varnothing=\{p\}\ne B$。取其唯一点 $r$，一张原确认效应在 $p,r$ 取一、零。球上仿射极值把 $r$ 锁为对径，得到 AD。反向，AD给 $r=p_B^*\in B\cap D_p$，两个不同纯点生成整个球，得到(180.1)。同一个证明也给(180.2)：它要求正交替换后仍生成同一张原实际面，因而没有把替换点的局部性留给图示。

$\mathsf{ZH}$ 给 AD 是179.3。反向，$\mathsf Z_2$ 由178.2给 NC，故 L2、NC、AD 字面满足 XIII162.10，取得同原单位的完整复 PSD 表示。179.8反向中复二维支持与 $v^\perp$ 的交维数论证适用于这个单系统，给所有球外及球内目标的相交；混态零面凸性已保留。故恢复 $\mathsf{ZH}$。这里没有重证分类。$\square$

### 180.2 零关系已经赚得的结构与尚缺的交换方向

**命题 180.3（有限秩、不可约及一个交换方向）。** 全混态 $\mathsf Z_2$ 使任意两两原零正交纯族实线性独立，故正交秩至多 $d$。实际 L2 使 $(P,\perp)$ 在179.10所引文献的意义下不可约。在 L2 加 $\mathsf Z_2$ 下，还自动有

$$
p\perp q\ \Longrightarrow\
\exists g\ne p,q:\quad g\not\perp p,\qquad
\{p,q\}^\perp=\{p,g\}^\perp.
\tag{180.3}
$$

证明。对有限正交纯族 $p_1,\ldots,p_k$，178.2给共同确认者 $e_i$，满足 $e_i(p_j)=\delta_{ij}$。对任意线性关系逐一作用 $e_i$，得全部系数为零，所以 $k\le d$；不存在更大的无限正交族，因为其中可取 $d+1$ 点。不能以逐对不同的确认者替代这里的共同确认者。

若有非空分区 $P=A\sqcup A'$ 且所有跨部点正交，取 $a\in A,b\in A'$。原一零效应使它们在实际球 $B=F_K(a,b)$ 中对径。在同球内与 $b$ 正交的点只能是 $a$，与 $a$ 正交的点只能是 $b$。每个球面纯点若在 $A$ 便只能为 $a$，若在 $A'$ 便只能为 $b$，与整个 $S^2$ 边界矛盾。这种不可约性不是正交图连通性的同义词。

最后对 $p\perp q$，在该球取 $g\ne p,q$。一零极值使 $g\not\perp p$；179.2的共同零面束使两对的纯共同零集相等，得到(180.3)。它是文献的关系条件 (L2)，不是本卷实际三球 L2 的另一名称。$\square$

**定义 180.4（关系交换与实际线恢复）。** 将文献的另一个关系条件单独写为

$$
\mathsf{EX}_0:\quad
p\ne q,\ p\not\perp q\ \Longrightarrow\
\exists r\perp p:\ \{p,q\}^\perp=\{p,r\}^\perp.
\tag{180.4}
$$

它是179.10所引原文的 (L1)，不申领为新关系定义。另定义实际线的忠实恢复条件

$$
\mathsf{PL}:\qquad
P\cap F_K(p,q)=\{p,q\}^{\perp\perp}\qquad(p\ne q).
\tag{180.5}
$$

179.2只给(180.5)从左到右的包含。右侧纯点不预先拥有球内位置；将它叫作射影线不会支付反向包含。

**定理 180.5（忠实恢复赚得严格零分离，并定位替换点）。** 在 L2 加全混态 $\mathsf Z_2$ 下，$\mathsf{PL}$ 蕴含 $\mathsf{Sep}_0$，从而由179.5给每个 $D_p$ 为 coatom 及标签单射。另给 $\mathsf{EX}_0$ 后可推出 $\mathsf J_2$，但本章没有证明 $\mathsf{PL}$ 单独推出 $\mathsf{EX}_0$ 或 AD。

证明。固定纯点 $p$。双零运算保包含，故对每个 $q\ne p$，

$$
\{p\}^{\perp\perp}\subseteq\{p,q\}^{\perp\perp}
=P\cap F_K(p,q).
\tag{180.6}
$$

若某个 $B=F_K(p,q)$ 等于 $K$，原域就是整颗三球，完整菜单直接给 $\{p\}^{\perp\perp}=\{p\}$。否则取 $q'\in P\setminus B$。两个实际球 $B,F_K(p,q')$ 的交是各自的面，含 $p$；若还含别的点，严格凸球的面结构迫两球相等，与 $q'\notin B$ 矛盾。因此(180.6)使 $\{p\}^{\perp\perp}=\{p\}$。若 $N_p\subseteq N_q$，对称性给 $q\in\{p\}^{\perp\perp}$，所以 $q=p$。这证明严格零分离；178.2给 NC，故179.5适用。

也可不借 $\mathsf{PL}$，直接从 $\mathsf{EX}_0$ 得严格零分离：若 $N_p\subseteq N_q$ 且 $p\ne q$，先由反自反性排除 $p\perp q$；(180.4)给 $r\in N_p$，但 $N_p\cap N_q=N_p\cap N_r$ 又要求 $r\in N_r$，矛盾。

现在固定 $p\ne q$。若 $p\perp q$，直接取 $r=q$ 满足(180.2)。否则(180.4)给 $r\perp p$ 及共同零集相等，所以
$r\in\{p,r\}^{\perp\perp}=\{p,q\}^{\perp\perp}=P\cap F_K(p,q)$。
两个不同球面纯点生成同一原球，得到(180.2)，再用180.2。这里恰由(180.5)支付了替换点的原球位置。$\square$

### 180.3 不把正交模性升级为模性

**命题 180.6（保留关系交换一侧的抽象控制）。** 有有限正交秩、不可约、严格零分离且满足 Dacey 条件和(180.3)的纯关系空间，却不满足(180.4)。因此这些抽象性质不能免费补上180.5缺少的交换方向；该控制不构成原 L2 凸域的反模型。

证明。先复用有限纯点卷 VII 的§104.6中开放问题104.8之后的两个三原子 Boolean 格水平和控制。其六点实现分为两块，每块三个点，只有同块不同点正交。闭集恰为空、全体、六单点和六个同块二点集。按这四类检查极大正交子集，直接得到 Dacey；各点的零邻域是不同二元集，给严格零分离；任何正交直和分区都被另一块的点排除。跨块 $a,b$ 共同零集为空，而任意 $r\perp a$ 与 $a$ 仍留有本块第三个共同零点，故(180.4)失败。该既有控制也失败(180.3)，不能就此声称保留了本章已经赚得的一侧。

要保留(180.3)，改取 $X=\mathbb CP^2\sqcup\mathbb CP^2$，各块内用通常复正交，跨块无正交。其正交闭集格是两个复 qutrit 子空间格的水平和：除空、全体外，闭集是某一块的复一维或二维子空间的纯射线。各真闭集的极大正交集是该子空间的基；全体的极大正交集是任一块的三元基。故 rank 为三且满足 Dacey。相同维数正交超平面的包含迫相等，异块零影不包含，给严格零分离；不可约性仍由跨块不正交给出。同块正交 $p,q$ 的复二维张成中选第三射线 $g\ne p,q$，即得到(180.3)。但跨块两点共同零仍为空，而任何与首点正交的替换点都在同一 qutrit 块内，两者有第三条共同正交射线，故(180.4)失败。

[Categories of orthogonality spaces，v2 Theorem 5.6][Q180C] 的逆向证明从有限高完备正交模格直接跳到模格；上述水平和不允许这一步。在前一个六点控制中，取第一块中 $x=\{a_1\}\subset z=\{a_1,a_2\}$、另一块 $y=\{b_1\}$，便有 $x\vee(y\wedge z)=x$ 而 $(x\vee y)\wedge z=z$。本章不消费该逆向及依赖它的 [Q179E] Lemma15、18逆向；Definition8、13及可直接证明的正向性质不受影响。两个控制只检验关系／格推断，不支付全部原混态、效应菜单或实际球。$\square$

### 180.4 量子层级与完整白话候选

**定义 180.7（三复制二元分解候选）。** 完整保留178.5的强实全有限背景和逐实际面的局部中心三角形条件。只在整个原 $K_3$ 要求全混态 $\mathsf Z_2$ 及(180.1)，记为 $\mathsf Q_{\rm join}$。混态、纯点、完整效应、原产品、全部有限 min/max 分块、单位、正置换及逆、规范重括号与标量层均不更换；不只检验产品点。

**定理 180.8（完整同坐标重建）。** 在上述精确背景下，$\mathsf Q_{\rm join}$ 等价于179.7的 $\mathsf Q_{\rm hyp}$，也等价于存在固定 $n\ge2$ 及同一个 $\theta:V\overset\sim\longrightarrow\operatorname{Herm}_n(\mathbb C)$，使对全部有限 $N\ge0$ 有 $\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N}$、$u_N=\operatorname{Tr}\circ\theta^{\otimes N}$。

证明。177.5a及177.4逐面给 L2。180.2在完整三复制原域把 $\mathsf J_2$ 变为 AD，178.2给 NC，直接消费178.6或XIII162.16，得到同一个张量幂坐标，包括 $N=0$。反向标准复 PSD 的全部混态零面凸，支持二维球内的对径点零响应，180.2给(180.1)。与179.7的等价由179.8衔接，不额外假设 $\mathsf{PL}$、$\mathsf{EX}_0$、Dacey或模律；这些不是新候选的隐藏输入。$\square$

**推论 180.9（简化的性质、量子字典与边界）。** 本候选把179.1的球外目标—全部线相交，换成球内单点—实际面的一个生成等式。它不用预先指定对径或原面格的完整正交补，识别出更大正交模结构的二元片段；没有证明独立前件数量减少。180.3的有限秩及交换方向、180.5的实际定位桥与180.6的连续块控制采用 `repo-derived` 的关系接合纸面推导归属；180.2的AD正规形、重建分类及量子字典均复用既有结果，不作为新分类或文献优先权申领。

证明与对应。180.8逐字给179.9的全部有限字典：纯点是复射线，混态是密度矩阵，完整原配对给 Born，有限单位分解给数学 PVM/POVM，同一张量幂给纠缠与偏迹；全部有限旁观者正性及全输入质量预算给数学 CP、Choi/Kraus 和仪器。实际事件饱和、指定锐中性更新、原连续可逆时间群及钟和 $\hbar$ 标定继续各守179.9的独立条件。重建之后所有实际面由支持子空间描述，完整正交模结构成为后果，不能倒填为(180.1)之前的前件。

白话上，保留能任意有限复合的实概率空间及所有原测试，仍只在整个三份系统检查。局部中心三角形把任意两纯准备撑起的三维面钉成球。零读数对所有混态的平均封闭，让各自能读零的分支共用一把真正的确认尺。全局再只要求一件面内的事：拿球上的一个纯准备，加上球里对它看不见的那部分，应能重新撑回整颗球。看不见的部分便不能空；球的面结构又不准它是一条边或一块圆盘，只能留下一个纯点，一与零把它钉成对径。已有重建于是把小球接成复射影空间，把所有混态、测试和有限复合接成同一个复 PSD 张量层级。我们从更大的正交模分解中只取了二元面需要的片段；它是原定义之间的相容约束，不是无前提真理。一般 L2 加全混态零凸性是否自动给这条分解式，仍为 open，也没有同域反模型。本章的关系路线仍须闭合另一半交换和替换点的实际球位置，不能拿抽象格的名字代替这两步。$\square$

[Q180C]: https://arxiv.org/html/2003.03313v2 "J. Paseka、T. Vetterlein，Categories of orthogonality spaces，Theorem 5.6；逆向的模性步骤不作为本章供应。"

## 追加锚（本行以下为增补区）

## 181. 二元面的共同确认与包含关系的原序实现

### 181.1 从原零关系构造整球确认效应

**定义 181.1（实际面的忠实确认菜单）。** 沿用178.1的整个有限维原域，$d>1$，保留实际 L2、全混态 $\mathsf Z_2$，并另给180.4的实际线恢复 $\mathsf{PL}$。对实际面 $F$ 写

$$
P_F=P\cap F,\qquad H_F=\bigcap_{p\in P_F}D_p,
\qquad
\mathcal U(F)=\{f\in[0,u]:\{f=1\}=F,\ Z(f)=H_F\}.
\tag{181.1}
$$

空交为 $K$，$Z(f)=K\cap\ker f$。记 $\mathfrak F_2$ 为空面、全部纯单点面及全部实际二元球的集合；这里的下标只规定这三类，不预送一般面格的秩函数。$\mathcal U(F)$ 是原菜单中的集合，既非指定装置，也未定义正投影或 least 效应。180.5及179.5使任意共同确认者 $e_p\in\mathcal F_p$、$Z(e_p)=D_p$ 的全域最大面恰为 $\{p\}$，故 $e_p\in\mathcal U(\{p\})$。

**定理 181.2（二元球及共同零面的同一效应）。** 在181.1的精确前件下，$\mathcal U(F)$ 对每个 $F\in\mathfrak F_2$ 非空。特别地，每颗实际二元球 $B$ 有原效应 $h_B$，同时满足

$$
\{h_B=1\}=B,\qquad Z(h_B)=H_B
=\operatorname{conv}(P_B^\perp).
\tag{181.2}
$$

证明。先用一个原菜单的最大点定位步骤。若非零 $g\in C^*$ 消去纯点集 $A$，令 $M=\max_Kg>0$。任一纯最大点 $r$ 使 $g/M\in\mathcal F_r$，故 $r\in A^\perp$。这只是原全菜单归一化与纯零对称性。由179.2及 $\mathsf{PL}$，$P_B=P_B^{\perp\perp}$；因此，消去 $P_B^\perp$ 的每个非零正泛函，其全部纯最大点都在 $P_B$。

在 $B$ 选几何对径 $a,b$，尚不假设它们正交。任取共同确认者 $e_a,e_b$，令 $t=e_a(b)$、$s=e_b(a)$。单点最大面给 $0\le s,t<1$。取单位球坐标 $a=v,b=-v$，球上的仿射极值给

$$
e_a(z)=\frac{1+t}{2}+\frac{1-t}{2}\langle v,z\rangle,
\qquad
e_b(z)=\frac{1+s}{2}-\frac{1-s}{2}\langle v,z\rangle.
$$

故正泛函

$$
\boxed{\quad
h_{B;a,b}=\frac{(1-s)e_a+(1-t)e_b}{1-st}
\quad}
\tag{181.3}
$$

在整个 $B$ 恒为一，且零集是 $D_a\cap D_b=H_B$，最后的等号复用179.2。上段最大点定位把其全域最大值锁在 $B$，所以最大值恰为一、$h_{B;a,b}\le u$；全部纯最大点恰为 $P_B$，紧最大面的纯凸生成给最大面恰为 $B$。这同时支付了原效应的全域上界，而非只验证球上的限制。单点情形已由181.1支付；空面用零效应。全域本身为球时同一证明给 $h_B=u$、$H_B=\varnothing$。$\square$

### 181.2 正交可加与球内混态目标

**推论 181.3（两项可加和完整混态零面）。** 任取两不同纯点的共同确认者 $e_a,e_b$，有

$$
a\perp b\quad\Longleftrightarrow\quad e_a+e_b\le u.
\tag{181.4}
$$

正交时 $e_a+e_b\in\mathcal U(B(a,b))$。对任意混态目标 $x\in K$ 仍用全菜单定义 $\mathcal F_x=\{e\in[0,u]:e(x)=1\}$、$T_x(y)=\min_{e\in\mathcal F_x}e(y)$ 和 $D_x=\{T_x=0\}$。若 $x\in\operatorname{ri}B$，则

$$
\boxed{\quad D_x=H_B,\qquad \mathcal U(B)\subseteq\mathcal F_x.\quad}
\tag{181.5}
$$

证明。正交时 $e_a(b)=e_b(a)=0$；一零球极值使 $a,b$ 为几何对径，(181.3)遂为 $e_a+e_b$。反向在 $a$ 评价(181.4)右侧，即得 $e_b(a)=0$。

若 $e\in\mathcal F_x$，其最大面含 $x$，因而含最小面 $B$。故任一纯零点 $r$ 都零于全部 $P_B$，即 $r\in P_B^\perp$；零面的纯凸生成给 $Z(e)\subseteq H_B$。原紧菜单使 minimum 达到，所以 $D_x\subseteq H_B$。181.2的 $h_B\in\mathcal F_x$ 给反向包含。这里得到的是最小面为二元球的全部混态目标，不把结论推广到尚未控制的更高实际面。两项可加也不免费给任意正交族的总和上界。$\square$

### 181.3 面包含与效应原序之间的精确缺口

**定理 181.4（支配关系恰好支付对径）。** 固定实际球 $B$、$a\in P_B$ 及其球内几何对径 $b$。任取 $e_a\in\mathcal U(\{a\})$ 和 $h_B\in\mathcal U(B)$。若 $e_a\le h_B$，则 $a\perp b$。对于(181.3)的具体构造，还直接有

$$
e_a\le h_{B;a,b}\quad\Longleftrightarrow\quad a\perp b.
\tag{181.6}
$$

证明。$g=h_B-e_a\ge0$ 消去 $H_B$，且在 $B$ 上等于 $1-e_a$。$e_a$ 的最大面是单点 $a$，故 $t=e_a(b)<1$，$g$ 在球上有唯一最大点 $b$、最大值 $1-t>0$。181.2的最大点定位把全域最大值也锁在球上。因此 $g/(1-t)\in\mathcal F_b$，且在 $a$ 读零，得到 $a\perp b$。这里归一化的是全域正泛函，不是未经延拓的局部尺。

对具体构造可直接显示失败证人。若该直径的 AD 失败，纯零对称性给 $s,t>0$。严格零分离给 $r\in N_b\setminus N_a$，于是

$$
(h_{B;a,b}-e_a)(r)
=-\frac{s(1-t)}{1-st}e_a(r)<0.
\tag{181.7}
$$

故不支配；若 AD 成立，(181.3)就是 $e_a+e_b$，反向立即成立。这是条件失败机制，不声称存在满足本章全部原前件而 AD 失败的凸域。$\square$

**定义 181.5（二阶确认的序相容）。** 在181.1的背景内，要求存在选择 $E_F\in\mathcal U(F)$，对全部 $F,G\in\mathfrak F_2$ 满足

$$
\boxed{\qquad F\subseteq G\quad\Longrightarrow\quad E_F\le E_G.\qquad}
\tag{181.8}
$$

记为 $\mathsf O_2$。反向包含无需另加：若 $E_F\le E_G$，在 $F$ 的每个点评价便得 $E_G=1$，所以 $F\subseteq G$。唯一非平凡的保序义务是纯单点包含于二元球；没有要求所有球单位由同一条选定直径构造，也没有声称这些效应为序 join 或正投影。

**定理 181.6（同一包含关系的完整量子候选）。** 完整保留180.7的强实全有限背景及逐实际面局部中心三角形条件；在整个原三复制域要求全混态 $\mathsf Z_2$、实际线恢复 $\mathsf{PL}$ 及 $\mathsf O_2$，记为 $\mathsf Q_{\rm ord}$。则 $\mathsf Q_{\rm ord}$ 等价于180.7的 $\mathsf Q_{\rm join}$，并等价于180.8的同一个 $\theta$ 下全部有限复 PSD 层级，包括标量层。

证明。局部条件由177.5a及177.4给整个三复制原域的 L2。对每颗实际球与球面每个纯点，(181.8)及181.4给其原对径零，即全部 AD；178.2给 NC，180.2给 $\mathsf J_2$，故直接消费180.8的重建接口。反向在标准复 PSD 层，$\mathsf{PL}$ 与全混态零凸性由 XIII162.11及180.8给出。对支持子空间 $S$ 的空面、纯单点或二元球，取 $E_F(X)=\operatorname{Tr}(\Pi_S X)$；最大面是 $F$，零面是支持于 $S^\perp$ 的面，支持包含给 $\Pi_S\le\Pi_T$，故(181.8)成立。没有给各有限层另选坐标。

181.2在额外 $\mathsf{PL}$ 背景下构造整球确认，181.4定位其到单点确认的原序缺口；完整候选把两边的关系统一为包含的保序实现。它不证明 $\mathsf{PL}$ 或 $\mathsf O_2$ 是裸 L2 加 $\mathsf Z_2$ 的后果，也不声称比180减少独立前件。Born、有限 PVM/POVM、复张量、纠缠、偏迹及带全部原有限旁观者的数学 CP 字典按180.9消费；事件饱和、指定锐中性更新、连续可逆时间、钟与 $\hbar$ 的条件不被静态序相容支付。$\square$

### 181.4 三纯点提升的有限方向空间

**定理 181.7（三球方向控制的条件提升）。** 对三个不同原纯点定义

$$
W_{abc}=\operatorname{aff}(B(a,b)\cup B(a,c)\cup B(b,c)),
\qquad G_{abc}=\{a,b,c\}^{\perp\perp}.
\tag{181.9}
$$

总有 $\dim_{\rm aff}W_{abc}\le8$。若另有 $G_{abc}\subseteq W_{abc}$，则 $F_K(a,b,c)=\operatorname{conv}G_{abc}$。若三点还两两原正交，任取共同确认者并令 $S=e_a+e_b+e_c$，此附加包含还给

$$
S\le u,\qquad \{S=1\}=F_K(a,b,c).
\tag{181.10}
$$

证明。三个球的锥线性张成各为四维；前两个共享 $\mathbb Ra$，第三个与它们之和共享线性独立的 $b,c$。故总线性维数至多 $4+4-1+4-2=9$，归一切片的仿射维数至多八。此读数尚不是整个三点面的维数界。

由179.2的任意交零面工具，$\operatorname{conv}G_{abc}$ 是包含三点的实际暴露面，故含 $F=F_K(a,b,c)$；而 $W_{abc}\subseteq\operatorname{aff}F$。附加包含使两面仿射维数相同，严格真面必降维，故两面相等。正交时181.3给 $e_a+e_b=1$ 于 $B(a,b)$，而 $e_c=0$ 于该球，循环亦然。因此 $S=1$ 于 $W_{abc}$。$S$ 消去三点的共同零集，其纯最大点由181.2的归一化步骤属于 $G_{abc}$；附加包含遂使全域最大值恰为一，且最大面恰为 $\operatorname{conv}G_{abc}=F$。

不加该包含时，三条两项预算只给 $S\le3u/2$。若 $S\le u$ 失败，纯最大点 $r$ 必满足 $r\in G_{abc}\setminus W_{abc}$、$1<S(r)\le3/2$，且三个 $e_i(r)$ 全正；任一项为零会被另外两项预算排除。这是可定位的三点缺陷，尚非其实际存在性或 AD 的反模型。$\square$

### 181.5 有限高度与二元覆盖不能替代原序相容

**命题 181.8（二元闭包的抽象控制与原域边界）。** $\mathsf{PL}$ 已使纯零闭集格中的每个两原子 join 只有空集、单点与整条球线三类子闭集；该二元高度性质、有限高度、有限正交秩、严格零分离、不可约性和180.3的交换方向，作为抽象格条件仍不足以给二元面的正交分解、正交模律或一般覆盖律，因而不能作为(181.8)的免费供应。此控制没有保留每条线的整个 $S^2$，不构成181.1完整原凸域的反模型。

证明。原域中的每个纯零闭集 $A=A^{\perp\perp}$ 都是某个实际暴露面的纯点集，复用179.2的任意交零面工具；$\mathsf{PL}$ 使两原子 join 精确为 $P_B$。其子闭集对应 $B$ 的实际面，三球的严格凸面结构给所述二元高度性质。有限高度来自嵌入实际面包含序，而非把正交秩冒当一般高度。

为检验裸格推断，复用 [Paseka—Vetterlein，Example 3.12][Q181L] 删除一条射线及其正交超平面的机制，取其有限维特化

$$
H=\mathbb C^4,\quad z=\mathbb Ce_2,\qquad
L=\operatorname{Sub}(H)\setminus\{z,z^\perp\}.
\tag{181.11}
$$

顺序及正交补沿用通常子空间格。任意族的通常交若为 $z$，在 $L$ 的 meet 改为零；其通常线性张成若为 $z^\perp$，join 改为 $H$。其余保持原值：保留元素族的交不能恰为被删的 coatom，张成不能恰为被删的原子。故 $L$ 完备且仍为正交格。其原子是除 $z$ 外全部射线；每个保留子空间都由其中保留射线张成，故为原子生成。

两不同原子的 join 是通常二维空间，未被删除，区间高度恰为二。整个高度及正交秩都恰为四：通常子空间维数给上界，链 $0<\mathbb Ce_1<\langle e_1,e_2\rangle<\langle e_1,e_2,e_3\rangle<H$ 达到高度四；射线 $\mathbb Ce_1,\mathbb C(e_2+e_3),\mathbb C(e_2-e_3),\mathbb Ce_4$ 达到正交秩四。

取 $p=\mathbb Ce_1$、$q=\mathbb C(e_1+e_2)$ 及 $B=p\vee_Lq=\langle e_1,e_2\rangle$，则

$$
B\wedge_Lp^\perp=0,\qquad
p\vee_L(B\wedge_Lp^\perp)=p\ne B.
\tag{181.12}
$$

因此正交模性失败；在闭集 $P_B$ 内，$\{p\}$ 已为极大正交集，却只双闭合为自身，Dacey 亦失败。令 $F=B^\perp=\langle e_3,e_4\rangle$，有 $F\vee_Lp=H$，但 $F<p^\perp<H$，所以一般覆盖失败。该模型的纯零闭集格与 $L$ 对应，因为保留子空间由其原子生成。原子极集的包含经正交补反转即给严格零分离。任一正交原子对的二维空间仍可选第三射线避开两端及 $z$，且不正交于两端；这给180.3，也排除跨部全正交的非空分区，给不可约性。

然而，含 $z$ 的二维空间的原子线是 $\mathbb CP^1\setminus\{z\}$，不含 $z$ 时才为整条 $\mathbb CP^1\simeq S^2$。从标准密度态删去对应纯点不会给闭底，取闭包又补回该点，不能据此偷换成原域反模型。原文 Lemma 3.4和Corollary 3.11的格推断明确保留完整覆盖性质；这里没有用底部两原子覆盖替代它。$\square$

### 181.6 数学归属、关系简化与完整白话

**推论 181.9（同一包含关系的两侧）。** 181.2的原共同确认构造、181.3的全菜单混态目标接合、181.4的任意球确认支配判据，以及181.7的条件三点提升，采用 `repo-derived` 纸面推导归属。181.6是既有重建的条件应用，不申领新分类。最大点归一化、球上仿射极值和有限维面降维为成熟中间步骤；181.8的删除机制归 [Q181L] Example 3.12，其有限四维应用只检验本章裸格路线，不申领该机制为新。未证明全球文献优先权。

证明与图景。181.2把原零关系精确恢复的实际二元球送到一张原菜单中的整球确认效应；181.3给其内部混态的同一零面。181.4使“单点确认不超过整球确认”成为支付 AD 的精确原序接口。181.5将空面、单点和二元球上的所有兼容要求统一为一个包含关系在两侧的保序实现；反映包含的方向已自动。简化发生在几何组织：从显式的局部分解换成同一个包含偏序，独立前提的删除仍未证成。181.7把一个可继续追的三元缺陷定位在三颗二元球的至多八维仿射张成之外；所需包含仍为附加条件，尚不关闭一般 $\mathrm{L2}+\mathsf Z_2+\mathsf{PL}\Rightarrow\mathrm{AD}$。

白话上，仍把全部准备、混态和原测试留在同一个能有限复合的实概率系统里，只在整个三份对象检查。局部中心三角形先把任意两纯准备撑起的小面锁成球。混态的零平均封闭后，每个纯点都有一把共同消去其零邻点的确认尺；若两次取零能原样找回每颗实际球，就能把球上两个对径方向的确认尺按原读数配平，造出一把对整球读一、对共同零面读零的尺。球里的混态目标因此也共享这张零面。全局再让一个画面成立：小面放在大面里面，确认小面的尺就不能比确认大面的尺读得更多。把整球尺减去球上一点的尺，差仍为正，而且最高点只能落回球里；球的几何把最高点钉在对径，将这把差尺按最高读数归一，便得到对径的一零见证。已有重建再把这些小球接成同一个复射影空间与全部有限复 PSD 层级。若减完出现负值，就恰好暴露了缺失的序相容，不能拿“整球确认”这个名字抹掉它。包含关系现在在实际面和原测试两侧用同一种顺序表达；它仍是一条明写的定义相容约束，尚不是裸零关系自动给出的定理。$\square$

[Q181L]: https://doi.org/10.1007/s10773-023-05282-3 "J. Paseka、T. Vetterlein，Linear Orthosets and Orthogeometries，International Journal of Theoretical Physics 62，55；Lemma 3.4、Corollary 3.11与Example 3.12。"

## 追加锚（本行以下为增补区）

## 182. 共同零方向的商影体与局部正性不扩张

### 182.1 从零关系定义商影体

**定义 182.1（二元球、共同零方向及正限制锥）。** 完整沿用181.1的单系统前件：有限维实空间 $V$、闭尖生成锥 $C$、严格正单位 $u$、整个紧底 $K$、全部纯点 $P=\operatorname{ext}K$、完整原菜单 $\mathcal E=[0,u]$、实际 L2、全混态 $\mathsf Z_2$ 及实际线恢复 $\mathsf{PL}$。固定实际二元球 $B$，写

$$
\begin{aligned}
L_B&=\operatorname{cone}B,& W_B&=\operatorname{span}L_B,\\
H_B&=\operatorname{conv}(P_B^\perp),& M_B&=\operatorname{span}(\operatorname{cone}H_B),\\
\Sigma_B&=C^*\cap M_B^\perp,&
\Gamma_B&=\{g|_{W_B}:g\in\Sigma_B\},\\
Q_B&=W_B\cap\overline{C+M_B},&
\widehat B&=Q_B\cap\{u_B=1\},\qquad u_B=u|_{W_B}.
\end{aligned}
\tag{182.1}
$$

约定 $\operatorname{cone}\varnothing=\{0\}$，$M_B^\perp$ 为线性消去子，星号为相应空间中的非负对偶；不预设自对偶内积。$\widehat B$ 称为共同零方向的闭商影体。若 $\pi_B:V\to V/M_B$ 为商映射，则 $\overline{C+M_B}=\pi_B^{-1}(\overline{\pi_B(C)})$。因而这是先忘去共同零方向、再在 $W_B$ 中观察闭商锥的定义，不把商影点认作原 $K$ 中的实际准备。即使 $C$ 闭，$C+M_B$ 也不得省略闭包。

**定理 182.2（精确确认菜单的紧性与正限制锥的闭性）。** 对181.1的空面、纯单点或实际二元球 $F$，精确菜单满足

$$
\mathcal U(F)
=\{f\in[0,u]: f|_F=1,\ f|_{H_F}=0\},
\tag{182.2}
$$

故非空、紧且凸。在182.1的精确背景下，$\Gamma_B$ 是闭凸锥；每个 $g\in\Sigma_B$ 都满足

$$
\max_Kg=\max_Bg.
\tag{182.3}
$$

证明。非空性复用181.2。(182.2)从左到右直接。对球的反向，若 $f=1$ 于 $B$ 且零于 $H_B$，181.2的最大点定位使全部纯最大点属于 $P_B$；纯零点 $r$ 因 $f\in\mathcal F_p$ 对所有 $p\in P_B$ 成立而属于 $P_B^\perp$。紧面的纯凸生成遂给精确的一面和零面。对单点 $p$，$f(p)=1$ 且零于 $D_p$；任一纯最大点 $r$ 给 $N_p\subseteq N_r$，严格零分离迫 $r=p$。任一纯零点由 $f\in\mathcal F_p$ 属于 $N_p$，故零面也精确。空面时 $H_\varnothing=K$，右侧只含零效应。右侧是紧区间中的闭仿射截集，给紧凸性；不需把精确菜单换成相对内部。

若非零 $g\in\Sigma_B$，它消去 $P_B^\perp$；181.2的归一化最大点定位及 $\mathsf{PL}$ 给其全部纯最大点在 $P_B$，从而给(182.3)。$g=0$ 时亦然。现令 $g_j|_{W_B}\to\varphi$，其中 $g_j\in\Sigma_B$。球紧且有限维，故 $\max_Bg_j$ 有共同有限上界 $A$；由(182.3)，$0\le g_j\le Au$ 于整个原锥。区间 $[0,Au]$ 紧，取收敛子列，其极限 $g$ 仍在闭集 $\Sigma_B$，且 $g|_{W_B}=\varphi$。所以 $\Gamma_B$ 闭。这里的有界提升由原最大点定位支付，不能只用“闭锥的线性像”推出闭性。$\square$

### 182.2 自动闭合的四维锥与紧影体

**定理 182.3（商影体的精确极化与紧性）。** 在182.1的背景下，已经有

$$
\boxed{\quad
Q_B=\Gamma_B^{*_{W_B}},\qquad
\Gamma_B=Q_B^{*_{W_B}},\qquad
W_B\cap M_B=\{0\}.
\quad}
\tag{182.4}
$$

$Q_B$ 是四维空间 $W_B$ 中的闭、尖、满维锥，$u_B$ 对其每个非零点严格正；$\widehat B$ 是包含 $B$ 的紧三维凸体。这些性质不要求 $Q_B=L_B$。

证明。线性消去子的定义给 $(C+M_B)^*=\Sigma_B$。有限维双极性给 $\Sigma_B^*=\overline{C+M_B}$；限制到 $W_B$，得 $\Gamma_B^{*_{W_B}}=Q_B$。182.2已付 $\Gamma_B$ 闭，第二次双极性遂给(182.4)第二式。此处仅把 [Boyd—Vandenberghe，§2.6.1、练习2.31][Q182B] 的成熟双极性作为中间步骤，不将其另立为新结果。

还需证明单位位于 $\Gamma_B$ 内部。取球坐标 $B=\{(1,z):\|z\|\le1\}$。每个球面点 $a=(1,n)$ 的共同确认者 $e_a$ 消去 $H_B\subseteq D_a$，故属于 $\Sigma_B$；其唯一最大点为 $a$，所以球上的限制形为

$$
e_a(1,z)=\alpha_a+\beta_a\langle n,z\rangle,
\qquad \alpha_a>0,\quad\beta_a>0.
\tag{182.5}
$$

沿三条坐标轴的正负方向各取一个这样的效应。除以各自的 $\alpha_a$ 后，$\Gamma_B$ 含 $u_B+\delta_i^+z_i$ 与 $u_B-\delta_i^-z_i$，其中六个 $\delta$ 均正。其凸包在 $u_B+\operatorname{span}\{z_1,z_2,z_3\}$ 中包围 $u_B$ 的一个相对邻域；再沿正标量缩放，得到 $u_B$ 的四维邻域。因此 $u_B\in\operatorname{int}\Gamma_B$，且 $\operatorname{span}\Gamma_B=W_B^*$。若 $w\in W_B\cap M_B$，全部 $\Gamma_B$ 均消去 $w$，所以 $w=0$。

$\Gamma_B\subseteq L_B^{*_{W_B}}$，而 $L_B$ 满维，故 $\Gamma_B$ 尖；它又有内点，其闭对偶 $Q_B$ 因而满维且尖。若 $0\ne q\in Q_B$ 而 $u_B(q)=0$，从 $u_B\pm\varepsilon\ell\in\Gamma_B$ 对任意 $\ell\in W_B^*$ 评价，得 $\ell(q)=0$，矛盾。因此单位严格正。闭切片 $\widehat B$ 若无界，将无界序列除以范数并取极限，得到非零 $q\in Q_B$ 且 $u_B(q)=0$，仍矛盾。它包含 $B$，故仿射维数恰为三。$\square$

### 182.3 一颗球上的四个等价接口

**定理 182.4（商不扩张、全部局部测试延拓与对径零）。** 固定182.1的一颗实际球 $B$。下列四项等价：

1. $\widehat B=B$，等价地 $W_B\cap\overline{C+M_B}=L_B$；
2. $\Gamma_B=L_B^{*_{W_B}}$，即每个球上正泛函都是消去共同零方向的原正泛函之限制；
3. 每个局部效应 $f\in[0,u_B]_{L_B^*}$ 都有延拓 $g\in[0,u]$，满足 $g|_{W_B}=f$、$g|_{H_B}=0$；
4. $B$ 的每对几何对径 $a,b$ 都满足原 $T_a(b)=0$，即该球全部 $\mathrm{AD}_B$。

证明。182.3给单位严格正于非零 $Q_B$，故影底相等与锥相等互推。再由(182.4)和闭锥 $L_B$ 的双极性，1与2等价；没有把稠密延拓冒当精确延拓。

若2成立，给局部效应 $f$ 选 $g\in\Sigma_B$ 作正延拓。(182.3)使 $\max_Kg=\max_Bf\le1$，故 $g\le u$ 于整个原域，给3。若3成立，球坐标中的局部效应

$$
\ell_a(1,z)=\frac{1+\langle n,z\rangle}{2}
\tag{182.6}
$$

可延拓为确认 $a=(1,n)$、消去 $b=(1,-n)$ 的原效应，给4。

最后设4成立。对任意球面方向 $n$，共同确认者 $e_a,e_b$ 分别消去原零面；由于 $a\perp b$，它们在 $B$ 上恰为 $\ell_a,\ell_b$。任意局部正泛函都有唯一球坐标形 $\varphi(1,z)=s+\langle v,z\rangle$，其中 $s\ge r:=\|v\|$。$r>0$ 时取 $n=v/r$，便有

$$
\varphi=(s+r)e_a|_{W_B}+(s-r)e_b|_{W_B}\in\Gamma_B.
\tag{182.7}
$$

$r=0$ 时任取直径，同式仍成立；零泛函也包含在内。故4给2。此反向只用固定球的 AD，没有先调用全局量子分类。$\square$

**定理 182.5（扩张影点恰好暴露一个缺失的一零方向）。** 若 $\widehat B\supsetneq B$，任取 $y=(1,r)\in\widehat B\setminus B$，令 $\rho=\|r\|>1$、$n=-r/\rho$。则 $a=(1,n)$、$b=(1,-n)$ 的局部效应 $\ell_a$ 不属于 $\Gamma_B$，并且该原直径的 AD 失败。反过来，若某条直径的 AD 失败，则对应 $\ell_a\notin\Gamma_B$，存在 $y\in\widehat B\setminus B$ 满足 $\ell_a(y)<0$。

证明。由(182.6)，$\ell_a(y)=(1-\rho)/2<0$，而 $y\in\Gamma_B^*$，故 $\ell_a\notin\Gamma_B$。若 $a\perp b$，共同 $e_a\in\Sigma_B$ 的限制正是 $\ell_a$，矛盾。反向，$\ell_a\in\Gamma_B$ 会由(182.3)给原 proper 一零延拓，故与 AD 失败矛盾。$\Gamma_B$ 闭，锥分离遂给非零 $q\in\Gamma_B^*=Q_B$，使 $\ell_a(q)<0$。除以182.3支付的正数 $u_B(q)$，即得所需影点 $y$；它不能在 $B$ 上，因为 $\ell_a$ 在 $B$ 非负。

这里在 $y$ 上评价的是 $W_B^*$ 中的线性泛函，不把 $T_a(y)$ 写成原 minimum；$y$ 只需属于闭商影体，不需属于原 $K$。这给失败的精确方向和分离证人，不给满足全部原前件而实际扩张的同域反模型。$\square$

### 182.4 不选择确认族的完整候选及三点结构

**定义 182.6（三复制闭商不扩张候选）。** 保留178.5的强实全有限背景：$\dim V>1$、$W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正乘法单位 $u_N$、全基与全对偶菜单、每个有限 min/max 分块、原正置换及正逆、规范重括号和标量层。另保留该定义第一项逐实际面的局部中心三角形条件；它由177.5a及177.4给整个原 $K_3$ 的 L2。只在整个原 $K_3$ 要求全混态 $\mathsf Z_2$、实际线恢复 $\mathsf{PL}$，以及对每颗实际二元球 $B$ 的单一几何约束

$$
\boxed{\qquad
W_B\cap\overline{C_3+M_B}=\operatorname{cone}B.
\qquad}
\tag{182.8}
$$

其中全部对象按(182.1)用同一原三复制域定义，记完整候选为 $\mathsf Q_{\rm quot}$。不只检查产品纯点，也不另选一族 $E_F$；$M_B$ 完全由原零关系给出。

**定理 182.7（同坐标量子层级与更大支持锥）。** 在182.6的精确强域中，$\mathsf Q_{\rm quot}$ 等价于181.6的 $\mathsf Q_{\rm ord}$，并等价于存在固定整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，对全部有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{182.9}
$$

在此条件结论内，三两正交纯点 $a,b,c$ 的实际三点面是 $\operatorname{PSD}_3$ 的迹一底，仿射维数八；三颗二元球的仿射张成恰为整个三点面的仿射空间。任意秩支持面也满足对应的闭商不扩张。

证明。182.4在整个原三复制域逐球给全部 AD；178.2给同域 NC。因此直接消费178.6及其明确引用的 XIII162.16，得同一个 $\theta$ 的(182.9)，包括单位、全部有限层和 $N=0$；不为各层分别选坐标。181.6已给 $\mathsf Q_{\rm ord}$ 与(182.9)等价。

反向在标准复 PSD 中，对任意支持子空间 $S$ 的面 $F_S$，有

$$
W_{F_S}=\operatorname{Herm}(S),\qquad
M_{F_S}=\operatorname{Herm}(S^\perp),\qquad
\Sigma_{F_S}=\operatorname{PSD}(S)
\tag{182.10}
$$

（最后一式用迹配对识别对偶）。正矩阵若在 $S^\perp$ 上压缩为零，其交叉块也为零，故给最后等式。对 $X\in\overline{\operatorname{PSD}+\operatorname{Herm}(S^\perp)}$，压缩到 $S$ 总为正；若还 $X\in\operatorname{Herm}(S)$，就得 $X\in\operatorname{PSD}(S)$。反向包含直接，故(182.8)成立，并同样适用于任意秩支持面。标准模型的其余局部、零平均及 $\mathsf{PL}$ 条件复用180.8及181.6。

三两正交纯点对应同一空间中三条正交复射线；其张成 $S$ 维数三，实际支持面为迹一 $\operatorname{PSD}(S)$，故维数为 $3^2-1=8$。三颗二元球分别张成三对坐标的 Hermitian 块，合在一起包含三条对角方向及三对复交叉方向，线性张成整个九维 $\operatorname{Herm}(S)$。这在完整重建之后支付181.7的三点包含；不把它倒灌成(182.8)之前的自动前件。因而二元的四维 Lorentz 锥是更大复支持锥的秩二片段，三点提升显出九维 PSD 锥及其八维底。$\square$

**命题 182.8（闭包及空共同零面的端点）。** 即使标准 PSD 满足(182.8)，其中锥和仍可不闭。若 $H_B=\varnothing$，本章全部固定球结论退化为 $B=K$ 的恒等情形。

证明。标准模型中取单位向量 $a\in S$、$c\in S^\perp$，在这两个方向上令 $\varepsilon>0$，有

$$
X_\varepsilon=
\begin{pmatrix}\varepsilon&1\\1&0\end{pmatrix}
=\begin{pmatrix}\varepsilon&1\\1&1/\varepsilon\end{pmatrix}
+\begin{pmatrix}0&0\\0&-1/\varepsilon\end{pmatrix}
\in\operatorname{PSD}+M_B.
\tag{182.11}
$$

第一项为正秩一，第二项支持在 $S^\perp$。极限 $X_0$ 若也在该锥和，其正项在 $a$ 的对角元为零，交叉项却为一；正性迫零对角行列全零，矛盾。此非闭例的交叉方向不在 $W_B$，所以不反驳(182.8)，只说明全局商闭包不能免费删除。若 $S^\perp=0$，此例没有可选的 $c$。

一般背景中，$H_B=\varnothing$ 给 $P_B^\perp=\varnothing$；$\mathsf{PL}$ 给 $P_B=P_B^{\perp\perp}=P$，故 $B=K$、$M_B=0$、$W_B=V$。于是 $Q_B=C$、$\widehat B=K$，没有遗漏空补端点。$\square$

### 182.5 量子公理的对应、简化范围与完整白话

**推论 182.9（几何约束的量子字典及未决关系）。** 182.7与既有179.9、180.9给同一套有限维数学量子结构：

| 现有量子结构 | 本候选中的来源与条件 |
| --- | --- |
| 纯态复射线、混态密度矩阵 | (182.9)的整锥同构，完整原底和全部极点均保留 |
| Born 概率 $\operatorname{Tr}(E\rho)$ | 同一同构下的完整原对偶配对及效应区间 |
| 数学 PVM/POVM、单位分解 | 支持面投影及全部有限正效应分解；实际可用事件仍需事件饱和 |
| 复张量、纠缠、偏迹 | 同一 $\theta^{\otimes N}$、原全部有限复合及乘法单位 |
| 数学 CP、Choi/Kraus 与仪器 | 全部原有限旁观者正性、有限矩形供应及全输入质量预算，含零分支 |
| Lüders 更新、连续时间动力学 | 另选理想锐中性更新、原连续可逆时间群；钟及 $\hbar$ 标定继续独立 |

在本候选的同一原域中，局部球与原全域之间的精确桥是(182.8)。它属于全部支持面的正性与商相容结构的秩二片段；没有从裸 $\mathrm{L2}+\mathsf Z_2+\mathsf{PL}$ 推出它。182.2的紧菜单、闭限制锥及最大点预算，182.3的紧影体和自动交空间分离，以及182.4—182.5的固定球等价与失败定位，采用 `repo-derived` 的关系接合纸面推导归属。双极性、有限维分离、球的仿射极值及标准 PSD 压缩是成熟中间步骤；完整分类及量子字典按既有接口复用，不申领新分类或文献优先权。

证明与图景。182.4把效应延拓与商影体不扩张接为同一条双向桥，182.5把失败落到一个明确方向。相较181.5，所去掉的是任意选择整个忠实确认族的存在量词，改用仅由原 $C$ 和共同零方向定义的几何等式；独立前件数量没有得到减少。保留 $\mathsf{PL}$ 后，一般是否已经排除影体扩张，仍为 open，亦未给同域反模型。182.7的八维三点面是完整候选的后果，不把裸二元条件的三点闭合冒领为已证。

白话上，仍把所有准备、混态和原测试放在同一个能任意有限复合的实概率系统中，只在整个三份系统检查。局部中心三角形先把任意两纯准备撑起的实际小面锁成三维球；零平均封闭让零邻点共用确认尺，两次取零又能找回实际球。现在看这颗球与整个世界的关系：把整颗球都看不见的共同零方向暂时忘掉，再回到球自己的四维锥空间，要求闭影子既不缺点，也不多长出点。若影子在球外鼓出一块，就有一个球内本来合法的一零方向在那块影子上读成负数，因此无法成为原世界的合法测试；相应对径便缺少零关系。影子恰好不扩张时，球上每把正尺都能原样接回全域，最高读数也不会在球外偷偷变大，一零方向遂全部落实。已有重建于是把这些小球接成同一个复射影空间与所有有限复 PSD 层级；三条正交方向撑成八维密度态底，二元小球就是其中的两坐标片。这次更简的是关系的几何表达：不再挑选一大族尺，只要求忘去共同零方向以后原球仍是原球。它是明写的定义相容约束；从更少的零关系自动推出这条约束，仍是下一条数学缺口。$\square$

[Q182B]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf "S. Boyd、L. Vandenberghe，Convex Optimization，§2.6.1（印刷页53）及练习2.31：有限维对偶锥与双极性。"

## 追加锚（本行以下为增补区）

## 183. 原 minimum 的零面斜率与影体尺寸

### 183.1 只用原菜单定义一阶关系

**定义 183.1（共同零面上的出射斜率）。** 先只采用178.1的完整有限维原域、实际 L2 及全混态 $\mathsf Z_2$，不加 $\mathsf{PL}$。固定实际二元球 $B$，选球坐标 $a_n=(1,n)$、$b_n=(1,-n)$，$n\in S^2$。按179.2定义 $H_B=\bigcap_{p\in P_B}D_p$，令 $J_B=\operatorname{cone}H_B$，约定 $\operatorname{cone}\varnothing=\{0\}$。把原 minimum 齐次延伸到原正锥：

$$
\begin{aligned}
m_a(v)&=\min_{f\in\mathcal F_a}f(v),\qquad v\in C,\\
\mathcal R_{B,a}&=\{f\in\mathcal F_a:f|_{H_B}=0\},\\
\delta_{B,a}(x)&=\min_{f\in\mathcal R_{B,a}}f(x),\qquad x\in K,\\
\delta_B(n)&=\delta_{B,a_n}(b_n).
\end{aligned}
\tag{183.1}
$$

下列 $a$ 均属于 $P_B$。这里 $m_a|_K=T_a$，$m_a(0)=0$；非零 $v\in C$ 满足 $m_a(v)=u(v)T_a(v/u(v))$，没有更换原效应菜单。取任意 $z\in\operatorname{ri}J_B$，定义出射斜率

$$
g_{B,a}(x)=\lim_{t\downarrow0}\frac{m_a(z+tx)}{t}.
\tag{183.2}
$$

下条证明此极限存在且与所取相对内点无关。若 $H_B=\varnothing$，唯一可取的 $z$ 是零质量元 $0$，不是归一化准备；若 $H_B\ne\varnothing$，可选 $z\in\operatorname{ri}H_B$，这时 $m_a(z+tx)=(1+t)T_a((z+tx)/(1+t))$，所以(183.2)完全由原归一化读数恢复。

**定理 183.2（斜率、零关系与共同菜单的精确接口）。** 在183.1的较弱背景下，$\mathcal R_{B,a}$ 非空紧凸，(183.2)对每个 $x\in K$ 成立，并且

$$
\boxed{\quad
g_{B,a}(x)=\delta_{B,a}(x)
=\lim_{L\to\infty}\min_{f\in\mathcal F_a}\bigl(f(x)+Lf(z)\bigr).
\quad}
\tag{183.3}
$$

对固定 $B,a,z$，此收敛在 $x\in K$ 上一致，且没有依赖 $z$ 的极限值。令 $\tau_a(x)=\min\{f(x):f\in\mathcal F_a,\ f|_{D_a}=0\}$，则

$$
T_a(x)\le\delta_{B,a}(x)\le\tau_a(x),\qquad
T_a(x)=0\ \Longleftrightarrow\
\delta_{B,a}(x)=0\ \Longleftrightarrow\ \tau_a(x)=0.
\tag{183.4}
$$

这些零值等价不把三者的非零数值等同。特别地，$\delta_B(n)=0$ 当且仅当该原直径满足 AD；较弱背景只保证 $0\le\delta_B(n)\le1$。

证明。178.2给共同确认者 $e_a\in\mathcal F_a$，其零面恰为 $D_a$。因 $H_B\subseteq D_a$，它属于 $\mathcal R_{B,a}$，给非空性；原紧区间的闭仿射截集给紧凸性。非负线性泛函在 $z\in\operatorname{ri}J_B$ 为零，当且仅当它消去整个 $J_B$，等价于消去 $H_B$；此相对内部步骤也包括 $J_B=\{0\}$。因此 $m_a(z)=0$，且

$$
\frac{m_a(z+tx)}t
=\min_{f\in\mathcal F_a}\bigl(f(x)+t^{-1}f(z)\bigr)
\le\delta_{B,a}(x)\le1.
\tag{183.5}
$$

右侧最小值随 $t\downarrow0$ 单调增加。对 $t_j\downarrow0$ 选极小者 $f_j$，则 $0\le f_j(z)\le t_j$。紧性给聚点 $f\in\mathcal F_a$，它消去 $z$，所以属于 $\mathcal R_{B,a}$；同时(183.5)的左侧不小于 $f_j(x)$，极限下界因而不小于 $\delta_{B,a}(x)$。这给(183.3)。固定 $a$ 的紧效应菜单使 $\delta_{B,a}$ 在 $K$ 上 Lipschitz；若一致收敛失败，取有固定残差的 $x_j\to x$ 及上述 $f_j\to f$，同一比较给矛盾。此处使用的是成熟紧罚项机制，在本条内支付原菜单与共同零面的参数对应。

消去 $D_a$ 的共同菜单包含于 $\mathcal R_{B,a}\subseteq\mathcal F_a$，给(183.4)的数值不等式。若 $T_a(x)=0$，则 $x\in D_a$，共同 $e_a$ 已同时消去整个 $D_a$，故 $\tau_a(x)=0$；反向由不等式。这里不要求在 $x$ 达到原 minimum 的每张尺都消去 $D_a$。若 $H_B=\varnothing$，$\mathcal R_{B,a}=\mathcal F_a$，(183.5)对每个 $t$ 已恰等于 $T_a(x)$；在这个较弱背景中不由此声称 $B=K$。$\square$

### 183.2 原斜率精确编码商影体

**定理 183.3（从原菜单到影体支持函数）。** 现在另加 $\mathsf{PL}$，即采用182.1的完整单系统前件及其 $\Gamma_B,Q_B,\widehat B$。把 $B$ 识别到单位三球；以下支持函数、范数及 Hausdorff 距离均取归一切片的三维坐标像。写该支持函数为 $h_{\widehat B}$，定义

$$
A_B=\{v\in\mathbb R^3:u_B+\langle v,\cdot\rangle\in\Gamma_B\},
\qquad
\kappa_B(n)=\max\{\kappa\ge0:\kappa n\in A_B\}.
\tag{183.6}
$$

$A_B$ 是含零内点、包含于单位球的紧凸体，且

$$
\boxed{\qquad
\kappa_B(n)=\frac{1-\delta_B(n)}{1+\delta_B(n)},\qquad
h_{\widehat B}(-n)=\frac{1+\delta_B(n)}{1-\delta_B(n)}.
\qquad}
\tag{183.7}
$$

所以 $\delta_B:S^2\to[0,1)$ 完全确定 $\widehat B$，不必再指定确认效应的选择。若 $R_B=\max_{y\in\widehat B}\|y\|$，则

$$
|\delta_B(n)-\delta_B(m)|\le\frac{R_B}{2}\|n-m\|.
\tag{183.8}
$$

它的零集对径对称；没有由此得到全部正值的对径对称性。定义 $s_B(0)=0$，非零方向上令

$$
s_B(v)=\|v\|\,
\frac{1+\delta_B(-v/\|v\|)}{1-\delta_B(-v/\|v\|)}.
\tag{183.9}
$$

则 $s_B$ 正齐次且 $s_B(v+w)\le s_B(v)+s_B(w)$。这使原斜率在不同方向上的读数受到同一个支持函数的联合约束。

证明。182.2—182.3给 $\Gamma_B$ 闭、$u_B$ 为内点及精确极化。因此 $A_B$ 闭且含零内点；在整个原球上非负迫 $\|v\|\le1$，给紧性。共同确认者唯一最大于 $a_n$，其球内对径读数严格小于一，故 $\delta_B(n)<1$。

对任意 $f\in\mathcal R_{B,a_n}$，令 $q=f(b_n)\in[0,1]$。因为它在球上最大于 $a_n$，球的仿射极值给

$$
f(1,x)=\frac{1+q}{2}+\frac{1-q}{2}\langle n,x\rangle.
\tag{183.10}
$$

常数情形 $q=1$ 也包含在内。除以常数项给 $((1-q)/(1+q))n\in A_B$。反向，若 $\kappa n\in A_B$，取其原正提升 $g\in\Sigma_B$；182.2的预算给 $\max_Kg=\max_Bg=1+\kappa$。所以 $g/(1+\kappa)\in\mathcal R_{B,a_n}$，对径读数恰为 $(1-\kappa)/(1+\kappa)$。菜单最小值与径向最大值均达到，得(183.7)第一式。这一步需要原全域预算，不能只在球上归一化。

采用极体约定 $A^\circ=\{x:\langle v,x\rangle\le1\text{ 对所有 }v\in A\}$，182.3的极化直接给 $\widehat B=-A_B^\circ$。更明确地，$u_B+\kappa\langle n,\cdot\rangle\in\Gamma_B=Q_B^*$ 当且仅当 $1-\kappa h_{\widehat B}(-n)\ge0$；$h_{\widehat B}(-n)\ge1$，故径向端点为其倒数。得(183.7)第二式。

支持函数为 $R_B$-Lipschitz，而 $\delta=(h-1)/(h+1)$ 在 $h\ge1$ 上的导数不超过 $1/2$，给(183.8)。183.2与原纯零对称性给零集对径对称。最后(183.9)恰是整个支持函数 $h_{\widehat B}(v)$，所以齐次性和次可加性成立。这些成熟支持函数性质只作为原斜率接合的中间工具，参见 [Boyd—Vandenberghe，练习2.26、3.35][Q183B]。$\square$

### 183.3 全方向一致极限与几何缺口

**定理 183.4（影体扩张的原读数公式）。** 在183.3的完整背景下，固定 $z\in\operatorname{ri}J_B$，令

$$
D_B=\max_{n\in S^2}\delta_B(n),\qquad
S_t=\sup_{n\in S^2}\frac{m_{a_n}(z+tb_n)}t.
\tag{183.11}
$$

则 $D_B<1$，(183.5)对全部 $n\in S^2$ 一致收敛到 $\delta_B(n)$，且 $S_t\uparrow D_B$。按球坐标中的欧氏 Hausdorff 距离，

$$
\boxed{\quad
d_H(\widehat B,B)=R_B-1
=\frac{2D_B}{1-D_B}
=\lim_{t\downarrow0}\frac{2S_t}{1-S_t}.
\quad}
\tag{183.12}
$$

有限 $t$ 只给扩张量下界。对两套满足183.3前件、已识别到同一单位球坐标的影体 $K_1,K_2$，若其剖面为 $\delta_1,\delta_2$，另有精确式

$$
d_H(K_1,K_2)
=\sup_{n\in S^2}
\frac{2|\delta_1(n)-\delta_2(n)|}
{(1-\delta_1(n))(1-\delta_2(n))}.
\tag{183.13}
$$

若两剖面均不超过 $\overline D<1$，此距离介于 $2\|\delta_1-\delta_2\|_\infty$ 和 $2\|\delta_1-\delta_2\|_\infty/(1-\overline D)^2$ 之间。

证明。183.3给 $\delta_B$ 连续，故最大值达到且严格小于一。若方向上的一致收敛失败，取 $t_j\downarrow0,n_j\to n$，使 $\delta_B(n_j)-m_{a_{n_j}}(z+t_jb_{n_j})/t_j\ge\eta>0$。选相应极小者 $f_j$；因上界为 $D_B$，有 $0\le f_j(z)\le t_jD_B$。紧效应区间给 $f_j\to f$ 的子列，连续评价使 $f(a_n)=1$ 且 $f(z)=0$，所以 $f\in\mathcal R_{B,a_n}$。左侧读数不小于 $f_j(b_{n_j})\to f(b_n)\ge\delta_B(n)$，与 $\delta_B(n_j)\to\delta_B(n)$ 矛盾。没有要求 $\mathcal F_a$ 随目标连续，也没有把有限 $t$ 的上确界写成已达到的最大值。单调性给 $S_t\uparrow D_B$。

由支持函数定义，$\max_n h_{\widehat B}(-n)=R_B$；(183.7)遂给 $R_B=(1+D_B)/(1-D_B)$。因 $B\subseteq\widehat B$，点到单位球的距离是 $\max(\|y\|-1,0)$，得(183.12)。有限 $t$ 时 $S_t\le D_B$，所以相应表达式只给下界；这里没有显式收敛模量，也没有有限 $t$ 的扩张上界。

对(183.13)，成熟支持函数工具给紧凸体的 $d_H(K_1,K_2)=\sup_{\|v\|=1}|h_{K_1}(v)-h_{K_2}(v)|$：Hausdorff 距离不超过 $r$ 等价于两侧分别包含于另一侧加半径 $r$ 球；[Q183B]练习3.35的和公式与包含判据使它等价于支持函数相差不超过 $r$。将(183.7)代入并通分即得所示精确式，两侧界直接由分母估计得到。此为剖面误差与影体误差的对应，不是原罚项的有限参数误差率，也没有给一般高秩面或全量子层级的近似重建定理。$\square$

### 183.4 零面的一阶约束与完整量子候选

**定义 183.5（三复制零斜率候选）。** 完整保留178.5的强实全有限层级、原全部 min/max 分块、完整菜单、乘法单位、正置换及逆、规范重括号和标量层，以及逐实际面的局部中心三角形条件；它们仍先给整个原 $K_3$ 的 L2。只在整个原三复制域要求全混态 $\mathsf Z_2$，以及下述原读数约束：对每颗实际球 $B$、每个球面纯点 $a$ 及其几何对径 $b$，有

$$
\boxed{\qquad
\lim_{t\downarrow0}\frac{m_a(z+tb)}t=0,
\qquad z\in\operatorname{ri}(\operatorname{cone}H_B).
\qquad}
\tag{183.14}
$$

记完整候选为 $\mathsf Q_{\rm germ}$。183.2保证该斜率独立于所选 $z$；空共同零面用 $z=0$，不略去端点。本定义不要求 $\mathsf{PL}$、商锥闭性或确认族选择作为前件，所用 $m_a$ 仍由原菜单定义。

**定理 183.6（从原一阶关系到全部有限量子结构）。** 在183.5的精确强实背景下，$\mathsf Q_{\rm germ}$ 等价于178.5的 $\mathsf Q_{\rm zero}$ 及182.6的 $\mathsf Q_{\rm quot}$，并给同一个 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$、固定 $n\ge2$，使全部有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{183.15}
$$

$\mathsf{PL}$、183.3—183.4的紧影体及其零剖面此时是后果；三两原正交纯点的共同实际面是迹一 $\operatorname{PSD}_3$，仿射维数八，三颗二元球张成它的仿射空间。

证明。先在没有 $\mathsf{PL}$ 的整个原 $K_3$ 使用183.2。(183.14)使每条实际球直径的 $T_a(b)=0$，给全部 AD；全混态 $\mathsf Z_2$ 由178.2给同域 NC。于是字面满足178.5的完整入口，直接消费178.6及其 XIII162.16 供应，得到同一个张量幂坐标的(183.15)，含单位及标量层。反向标准复 PSD 已满足178.5；183.2的零值等价即给(183.14)。与182.6的等价由182.7衔接，不以尚未恢复的 PL 证明最初零斜率。重建之后，标准支持规则才支付 PL 及182.1的全部前件；183.3—183.4于是适用且 $\delta_B=0$。三点结构直接复用182.7在同一重建之后的支持计算。

其余量子字典按182.9的同一原配对与有限旁观者接口消费：纯态为复射线、混态为密度矩阵；原效应配对为 Born 概率，有限正效应单位分解为数学 PVM/POVM；统一张量幂给纠缠与偏迹，全部有限旁观者正性及全输入质量预算给数学 CP、Choi/Kraus 与仪器。实际可用事件仍需事件饱和，Lüders 更新仍需指定理想锐中性更新，Hamiltonian 时间描述仍需原连续可逆时间群，钟与 $\hbar$ 的标定继续独立。这些条件不由一阶零关系吞并。$\square$

### 183.5 简洁几何、反事实与完整白话

**推论 183.7（球面剖面与原定义间的约束）。** 在182.1的完整单系统背景内，原 minimum 在共同零面上的出射斜率剖面 $\delta_B$，经(183.7)的分式变换精确成为影体支持函数；其齐次延伸受(183.9)的次可加关系约束。影体扩张等价于某方向有正斜率，扩张尺寸由(183.12)恢复。因剖面连续，任一严格正方向都带有严格正的开邻域，不能只出现为一个孤立漏点。裸 $\mathrm{L2}+\mathsf Z_2$ 是否已排除这些正方向，及另加 $\mathsf{PL}$ 后是否已排除，仍各为 open；本章没有同域反模型。

证明与范围。前三项是183.2—183.4的直接消费；183.2还说明两种共同菜单在零值上并无额外差别，不能把 $T_a(x)=0$ 而 $\tau_a(x)>0$ 列作该背景内的另一个缺口。183.5把约束前端从环境商锥换成一张原读数的一阶剖面，去掉显式列出的 PL 中间结构；零斜率条件本身仍与 AD 等价，故没有证明独立物理前件减少。更简的几何描述是球面上一张标量剖面，它同时给正测试可延拓的径向范围及影体支持；不是把原影点解释成实际准备，也不是把单标量最大值换名当作新公理来源。

183.2—183.4采用 `repo-derived` 的原菜单、共同零面斜率、全域提升预算与影体尺寸的关系接合归属；紧罚项、球上仿射极值、极体和支持函数的成熟步骤只在此接合内使用。[Q183B]供应支持函数的定义、包含判据及和公式；Hausdorff 恒等式的标准推导已在183.4内展开。183.6是既有量子重建的条件应用，不申领新分类、一般优化定理或文献优先权。

白话上，仍从全部原准备、混态、测试及可任意有限复合的实概率结构出发，只在整个三份系统检查。局部中心三角形把两纯准备撑起的小面锁成球，零平均封闭给共同确认尺。现在先不用谈球外的大商空间：站在整颗球共同看不见的零面里，朝球上某点的对径加入一点准备质量，看确认这个点的最低读数最初涨得多快；共同零面为空时，就从零质量出发。这个最初斜率等于所有消去共同零面的合法确认尺所能达到的最小对径读数。若处处不涨，紧性把零斜率落实成真正的一零尺，已有重建便把小球接成同一个复射影空间与所有有限复 PSD 层级；三个正交方向撑成八维密度态底。若有方向涨起来，在已有实际线恢复的背景下，它精确告诉我们影子往反方向鼓出多少，整颗影子的最大鼓出也由这些原读数恢复。一张球面上的斜率图于是替代了环境商几何的前端描述；不同方向不能随意填数，变换后必须共同组成一个凸体的支持函数。这是原定义之间可证明的关系与明写的零约束，不是已经从更少前提得到了量子。有限步看到的小斜率只给扩张下界，没有收敛速度就不能认定影子已经是球；更新时间、实际事件与物理钟仍守各自条件。$\square$

[Q183B]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf "S. Boyd、L. Vandenberghe，Convex Optimization，练习2.26与3.35：支持函数定义、凸和公式及闭凸集包含判据。"

## 追加锚（本行以下为增补区）

## 184. 跨球斜率的三点预算与原零菜单的共同保持

### 184.1 同一原测试的跨球约束

**定义 184.1（实际球的几何重叠）。** 先只采用178.1的完整有限维原域和实际 L2。对不同原纯点 $a,c$，在其整个最小实际球 $B_{ac}$ 取单位球坐标 $a=(1,n_a)$、$c=(1,n_c)$，定义

$$
q(a,c)=\frac{1+\langle n_a,n_c\rangle}{2},\qquad q(a,a)=1.
\tag{184.1}
$$

球的仿射自同构固定中心、在线性方向上正交，故 $q$ 与图表选择无关。它对称，且 $q(a,c)=1$ 当且仅当 $a=c$。记 $a_B^-$ 为 $a\in P_B$ 在实际球 $B$ 中的几何对径；$q(a,c)=0$ 只表示几何对径，不预先等同于原零关系。另加全混态 $\mathsf Z_2$ 后，使用183.1的原斜率，简写 $d_B(a)=\delta_{B,a}(a_B^-)$。

以下球上仿射极值公式作为中间工具使用。对同一个原效应 $f\in[0,u]$，若 $f(a)=1$，则在每颗经过 $a$ 的实际球 $B$ 上有

$$
f(c)=q(a,c)+(1-q(a,c))f(a_B^-)\qquad(c\in P_B).
\tag{184.2}
$$

若 $f(b)=0$，则在另一颗实际球 $B_{bc}$ 上有

$$
f(c)\le1-q(b,c)\qquad(c\in P).
\tag{184.3}
$$

证明。球上仿射泛函在球面点取得最大值或最小值，迫其线性部分平行该点的径向。按两端读数插值给(184.2)；最小值零时得到 $f(c)=(1-q(b,c))f(b^-_{B_{bc}})\le1-q(b,c)$。常数效应及重合端点直接包含。此处只有球上限制的公式，没有假设局部效应可延拓。$\square$

**定理 184.2（一个原零邻域约束全部相交球）。** 在 L2 和全混态 $\mathsf Z_2$ 下，对每颗实际球 $B$、每个 $a\in P_B$，有

$$
\boxed{\quad
q(b,c)\le(1-d_B(a))(1-q(a,c))
\qquad(b\in N_a,\ c\in P_B).
\quad}
\tag{184.4}
$$

特别地，$q(b,a_B^-)\le1-d_B(a)$ 对同一个 $N_a$ 的全部原纯点同时成立。本条不需要 $\mathsf{PL}$。

证明。178.2给同一共同确认者 $e_a$，满足 $Z(e_a)=D_a$。因为 $H_B\subseteq D_a$，有 $e_a\in\mathcal R_{B,a}$，故 $t=e_a(a_B^-)\ge d_B(a)$。同一张原尺在 $a$ 读一、在任意 $b\in N_a$ 读零。联合(184.2)—(184.3)，得

$$
q(a,c)+(1-q(a,c))t=e_a(c)\le1-q(b,c).
$$

移项即得(184.4)。取 $c=a_B^-$ 给最后结论。$q(b,c)$ 使用的球可以不同于 $B$；本条的两个限制确由同一个原效应同时实现。$\square$

### 184.2 三点余量与有限扩张上界

**定理 184.3（两颗连接球共用一份三点预算）。** 另加 $\mathsf{PL}$，即采用181.1的完整单系统前件。设 $a\perp b$、$c\in P\setminus\{a,b\}$，置

$$
r=q(a,c),\quad s=q(b,c),\quad \varepsilon=1-r-s,\quad
A=a^-_{B_{ac}},\quad B'=b^-_{B_{bc}}.
$$

任取共同确认者 $e_a,e_b$，令 $h=e_a+e_b$。则

$$
\boxed{\quad
\varepsilon=[1-h(c)]+(1-r)e_a(A)+(1-s)e_b(B')\ge0,
\quad}
\tag{184.5}
$$

因而同一个三点配置同时约束两颗实际球：

$$
\boxed{\quad
(1-r)d_{B_{ac}}(a)+(1-s)d_{B_{bc}}(b)\le\varepsilon.
\quad}
\tag{184.6}
$$

此外，$q(a,c)+q(b,c)=1$ 当且仅当 $c\in P_{B_{ab}}$。这个等号不提供向球外传播零斜率的机制。

证明。181.3给 $h\le u$ 且 $\{h=1\}=B_{ab}$。将同一 $e_a,e_b$ 的(184.2)相加再从一减去，得到恒等式(184.5)，其右侧各项非负。共同确认者属于相应受限菜单，故其对径读数不小于对应 $d$，给(184.6)。若 $\varepsilon=0$，(184.5)迫 $h(c)=1$，所以 $c\in B_{ab}$。反向原正交对在其球中是几何对径，球内两个 $q$ 值互补。这里没有将两张分别最优的确认尺假定为能共同达到最优；只对同一对实际选定尺使用恒等式，再以两个菜单下界估计。$\square$

**定理 184.4（实际三点证书给有限方向及整颗影体上界）。** 保留184.3的完整背景。固定实际球 $B$。对某个 $a=(1,n)\in P_B$，若找到同域原纯点 $b\in N_a$、$c\in P_B\setminus\{a\}$，使

$$
r=q(a,c),\qquad s=q(b,c)>0,\qquad \varepsilon=1-r-s,
$$

则

$$
d_B(a)\le\frac{\varepsilon}{1-r}<1,\qquad
h_{\widehat B}(-n)-1
=\frac{2d_B(a)}{1-d_B(a)}
\le\frac{2\varepsilon}{s}.
\tag{184.7}
$$

若有限个 $a_i=(1,n_i)$ 的方向 $-n_i$ 满足

$$
\forall\omega\in S^2\ \exists i:\quad
\langle\omega,-n_i\rangle\ge\cos\theta>0,
\tag{184.8}
$$

并且每个 $i$ 都有上述实际三点证书，记
$\rho=\max_i2\varepsilon_i/s_i$，则

$$
\boxed{\quad
d_H(\widehat B,B)\le\frac{1+\rho}{\cos\theta}-1.
\quad}
\tag{184.9}
$$

证明。(184.4)给 $s\le(1-d_B(a))(1-r)$，故 $\varepsilon\ge(1-r)d_B(a)$。因 $c\ne a$，$1-r>0$；又 $1-r-\varepsilon=s>0$，分式的单调性及183.3给(184.7)。它也允许 $b=c$，不需为此定义 $B_{bc}$。

对有限覆盖，取影体中达到 $R_B=\max_{y\in\widehat B}\|y\|$ 的 $y$。由(184.8)选方向，得到

$$
R_B\cos\theta\le\langle y,-n_i\rangle
\le h_{\widehat B}(-n_i)\le1+\rho.
$$

最后消费183.4的 $d_H(\widehat B,B)=R_B-1$。方向覆盖的支撑函数估计是成熟凸几何工具；新增接口是各支撑上界由同域原零邻点和三点几何余量支付。这里没有证明这些证书自动存在、$\rho$ 自动小或可趋零；$\cos\theta=0$、$s_i=0$ 时不使用该公式。与183.4的有限罚参数下界不同，(184.9)是具备所列实际三点配置后的有限上界，不依赖罚项收敛模量。$\square$

### 184.3 把原零菜单同时保持为一个定义相容条件

**定义 184.5（一个原纯点的零菜单保持）。** 在178.1的完整有限维原域，固定 $a\in P$，写

$$
\mathcal Z_a=\{h\in[0,u]:h(a)=0\}.
$$

条件 $\mathsf{RJ}(a)$ 要求存在同一个实线性映射 $Q_a:V\to V$，使

$$
\boxed{\qquad
Q_a(C)\subseteq C,\qquad uQ_a\le u,\qquad Q_a a=0,\qquad
hQ_a=h\quad(h\in\mathcal Z_a).
\qquad}
\tag{184.10}
$$

此处 $hQ_a$ 是泛函复合；不预给幂等、像为零面、least 确认、正补投影或实际仪器实现。它要求同一张原正映射删去 $a$，同时保留所有在 $a$ 上读零的原测试对全部输入的读数。原正泛函可缩放进 $[0,u]$，故最后一项等价于保持全部 $\{h\in C^*:h(a)=0\}$。

**定理 184.6（共同保持先产生最小元与幂等）。** 只在184.5的完整原域，$\mathsf{RJ}(a)$ 已给

$$
e_a=u-uQ_a=\min\mathcal F_a,\qquad T_a(x)=e_a(x)\quad(x\in K),
\tag{184.11}
$$

并且

$$
Q_a^2=Q_a,\quad e_aQ_a=0,\quad
Q_a(C)\subseteq\operatorname{cone}D_a,\quad
Q_a^*(C^*)=\{h\in C^*:h(a)=0\}.
\tag{184.12}
$$

特别地，该点的 $\mathsf Z_2(a)$ 成为结论。若已有 L2 和全部 $\mathsf Z_2$，则对每颗经过 $a$ 的球和每个 $x\in K$ 还有
$T_a(x)=\delta_{B,a}(x)=\tau_a(x)=e_a(x)$，包括非零数值。

证明。令 $q_a=uQ_a\in\mathcal Z_a$，所以 $q_aQ_a=q_a$。于是 $e_a=u-q_a\in\mathcal F_a$ 且 $e_aQ_a=0$。任取 $f\in\mathcal F_a$，有 $u-f\in\mathcal Z_a$，由正性

$$
u-f=(u-f)Q_a\le uQ_a=q_a,
$$

即 $e_a\le f$。因此 minimum 是同一线性泛函，零集 $D_a=K\cap\ker e_a$ 为实际面。$e_aQ_a=0$ 给像包含；空零面时其锥为 $\{0\}$。

再对任意 $g\in C^*$，$gQ_a$ 非负且在 $a$ 取零，缩放后的保持式给 $gQ_a^2=gQ_a$。生成锥的对偶张成整个 $V^*$，故 $Q_a^2=Q_a$；同一论证说明对偶正像恰为所示原零锥。最后 $e_a$ 同时属于183.2的两个共同菜单，而已是整个 $\mathcal F_a$ 的最小元，故两边的所有非零读数也相等。这里幂等性不需要 $\mathsf{PL}$ 或对径零关系。$\square$

**定理 184.7（原零菜单保持恢复实际对径及双侧互补）。** 采用181.1的 L2、全部 $\mathsf Z_2$、$\mathsf{PL}$ 背景。若固定 $a$ 满足 $\mathsf{RJ}(a)$，则每颗经过 $a$ 的实际球的几何对径均在 $D_a$，并有

$$
Q_a(C)=\operatorname{cone}D_a,\qquad Q_a|_{\operatorname{cone}D_a}=\operatorname{id}.
\tag{184.13}
$$

令 $P_a(v)=e_a(v)a$。这两个正投影满足原空间及整个对偶空间的四条互补关系：

$$
\begin{aligned}
P_a(C)&=C\cap\ker Q_a=\mathbb R_+a,&
Q_a(C)&=C\cap\ker P_a=\operatorname{cone}D_a,\\
Q_a^*(C^*)&=C^*\cap\ker P_a^*
=\{h\ge0:h(a)=0\},&
P_a^*(C^*)&=C^*\cap\ker Q_a^*=\mathbb R_+e_a.
\end{aligned}
\tag{184.14}
$$

满足(184.10)的 $Q_a$ 唯一；其像和核均由原零关系决定：

$$
\operatorname{im}Q_a=\operatorname{span}D_a,\qquad
\ker Q_a=\operatorname{ann}\operatorname{span}\{h\in C^*:h(a)=0\}.
\tag{184.15}
$$

证明。184.6的 $e_a$ 是共同确认者。181.1使其全域最大面恰为 $\{a\}$。对任意纯点 $b\ne a$，令 $B=B_{ab}$，181.2给 $h_B$，其最大面为 $B$。原效应 $k_B=u-h_B$ 满足 $Z(k_B)=B$ 且 $k_B(a)=k_B(b)=0$。保持式给 $k_B(Q_ab)=0$，而

$$
u(Q_ab)=1-e_a(b)>0.
$$

所以真正的原归一化输出 $Q_ab/(1-e_a(b))$ 同时属于 $B$ 和 $D_a$。在整颗球上，原效应 $e_a$ 在 $a$ 取一、在某点取零，迫该零点为 $a_B^-$。这给经过 $a$ 的全部 AD，未把商影点当作实际准备。

若 $b\in N_a$，其输出质量是一，且 $B_{ab}\cap D_a=\{b\}$，故 $Q_ab=b$。178.2的 $D_a=\operatorname{conv}N_a$ 给(184.13)。正像的张成是整个线性像；184.12的对偶正像给核的湮灭子公式，得到(184.15)。幂等投影由其像和核唯一确定。

原空间的两式由像、$uQ_a=u-e_a$ 及 $e_a$ 的单点最大面得到。对偶第一式已由184.12支付。对最后一式，若非零 $g\ge0$ 且 $gQ_a=0$，则 $g$ 消去 $D_a$；182.2用于单点菜单的最大点定位使 $M=\max_Kg=g(a)>0$。于是 $u-g/M\in\mathcal Z_a$，保持式给

$$
u-g/M=(u-g/M)Q_a=uQ_a=u-e_a,
$$

故 $g=Me_a$；反向由 $e_aQ_a=0$。$P_a^2=P_a$、$P_aQ_a=Q_aP_a=0$ 直接成立。两张对偶正投影的单位像分别为 $e_a$ 和 $u-e_a$，所以均为 order-unit 范数收缩。全部四式正是 [Alfsen—Shultz，p.158，式(2.4)][Q184AS] 要求的双侧 quasicomplementarity；在有限维，连续性条件自动。本条没有把点线射影几何与该正投影定义混同，也没有要求 $P_a+Q_a=\operatorname{id}$。$\square$

### 184.4 反事实、完整候选与量子字典

**命题 184.8（正斜率迫使一个原零读数改变）。** 在184.7的几何背景内，设原直径 $a,b=a_B^-$ 有 $d_B(a)>0$。对181.2的 $k_B=u-h_B$，有 $D_a\cap B=\varnothing$。若 $D_a\ne\varnothing$，则

$$
\mu_{a,B}=\min_{x\in D_a}k_B(x)>0.
$$

任取共同确认者 $e\in\mathcal U(\{a\})$，以及任何正线性 $Q$ 满足 $Q(C)\subseteq\operatorname{cone}D_a$、$uQ=u-e$，均有

$$
\boxed{\quad
k_B(Qb)\ge\mu_{a,B}(1-e(b))>0=k_B(b).
\quad}
\tag{184.16}
$$

证明。183.2的零值等价说明 $T_a(b)>0$。球上零点若存在只能是对径 $b$，故整个 $D_a\cap B$ 为空。紧性及 $Z(k_B)=B$ 给 $\mu_{a,B}>0$。181.1给 $e(b)<1$，故 $Qb$ 有严格正质量，其归一化属于 $D_a$，立即给(184.16)。若 $D_a$ 为空，则(184.10)的映射也不可能在此背景存在：184.6会使其正像为零，令 $e_a=u$，违反181.1的单点最大面。这里的反事实只定位 $a,b$ 及同一原测试 $k_B$，不预设满足正斜率的完整原域已经存在。$\square$

**定义 184.9（三复制原零菜单保持候选）。** 保留178.5的强实全有限背景：$\dim V>1$，所有 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成原锥、严格正乘法单位、完整基与全对偶菜单、每个有限 min/max 分块、原正置换及逆、规范重括号和标量层。只在整个原 $K_3$ 要求逐实际面的局部中心三角形、$\mathsf{PL}$，以及每个原纯点的 $\mathsf{RJ}(a)$，记为 $\mathsf Q_{\rm rej}$。不先输入 $\mathsf Z_2$、AD、least、幂等或互补投影。

**定理 184.10（同一个原零约束产生全部有限复层级）。** 在184.9的精确背景中，$\mathsf Q_{\rm rej}$ 当且仅当存在固定 $n\ge2$ 和同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使每个有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{184.17}
$$

证明。局部中心三角形按177.5a及177.4给整个 $K_3$ 的 L2。先逐纯点使用184.6；这一步不需要 $\mathsf Z_2$ 或 $\mathsf{PL}$，从而全部 $\mathsf Z_2$ 成为结论。现在才使用 $\mathsf{PL}$ 下的184.7，得全部 AD；178.2给 NC。因此精确达到178.6及其 XIII162.16 的既有入口，得到同一 $\theta$ 下的(184.17)，含原单位和标量层。反向标准复 PSD 的全部纯点为秩一投影 $a$；取 $Q_a(X)=(I-a)X(I-a)$。若原正效应矩阵 $H$ 在 $a$ 取零，正性迫 $Ha=aH=0$，所以 $hQ_a=h$；其余正性、质量预算和 $Q_aa=0$ 直接成立。标准支持规则还给 $\mathsf{PL}$ 和所列局部几何。

在这个结果之后，184.1的 $q$ 才成为 $|\langle\psi_a,\psi_c\rangle|^2$；(184.5)中两个斜率成本消失，余量是第三点离开原二点支持的质量。三个两两原正交纯点的实际面是迹一 $\operatorname{PSD}_3$，仿射维数八；更高面为同一复空间的支持面。全部原混态、纯射线、效应和配对分别成为密度矩阵、复射影空间、$[0,I]$ 和 Born 读数。数学 PVM/POVM、复张量、纠缠、偏迹，以及对全部原有限旁观者保持正性且满足全输入质量预算的矩形 CP、Choi/Kraus、分支和仪器，按183.6及182.9的同一接口消费。实际事件饱和、指定理想锐中性更新、原连续可逆时间群及物理钟和 $\hbar$ 标定仍各自保留；本条件没有指定实际可用删除装置。$\square$

**命题 184.11（定义约束的组织、归属与完整白话）。** 184.2—184.4提供同一原锥中不同球斜率的共同预算及具名实际三点证书的有限上界；它们没有推出证书自动存在或斜率自动全零。184.6—184.7把共同保持从原效应的二元取零关系提升为唯一原正投影，并支付最小确认和全部非零读数的相等。184.10是既有全有限重建的条件应用；新增成本是每个原纯点的共同正实现及保留的 $\mathsf{PL}$，不申领独立物理前件减少。

证明与归属。共同预算和原零菜单保持到实际对径的接合采用 repo-derived 综合推导；球上仿射极值、支撑函数覆盖估计、正投影和双侧互补概念是成熟中间工具。[Q184AS] p.158给完整 P-projection 定义，不供应这里尚缺的共同映射存在性。仓内 [SAME_READBACK125.4—125.6][Q184SR] 及 [BILATERAL VIII121.1][Q184BR] 已研究 EB3 原域中三个种子的规范零读数保持映射与正性；本章不重报该概念，而在实际 L2、全纯点及184.10的较少预设结构下推导其后果。完整分类、全部有限传播及量子过程字典保持178.6/XIII162.16的原来源，不申领新分类、文献优先权或从无前提推出物理规律。裸 L2 加 $\mathsf Z_2$、另加 $\mathsf{PL}$，以及全部有限 min/max 背景，是否已经能构造这些 $Q_a$ 或排除全部正斜率，仍为 open；$G_{abc}\subseteq W_{abc}$ 也未由三点预算补齐。

白话上，把许多小球重新放回同一个准备和测试系统：两个确实能彼此区分的纯准备，加上第三个纯准备，只能共同花一份确认预算；第三点对它们的几何重叠越大，两颗连接球还能留下的斜率缺陷就越小。若在有限个覆盖方向找到这样的实际三点，整颗影子能鼓出多少便有上界。完整候选再要求一个具体画面：删去纯准备 $a$ 时，所有本来对 $a$ 读零的测试，都由同一张原正映射原样保住。先不叫它投影；共同保持会迫使它再做一次也不改变结果、迫出一把最小确认尺，并在每颗经过 $a$ 的实际球里，把其他纯准备的正质量输出归一化后送到 $a$ 的对径。若对径还有正斜率，某个原本读零的测试反而必须读出正值，便直接违背共同保持。满足条件后，这张映射的像和核都由原零关系唯一确定，成为更大双侧正投影结构的原子部分，随后接上全部有限复量子理论。简化的是共同实现的定义前端：零平均、最小元、幂等和对径零不再分别列入；存在同一正实现及实际线恢复仍是明写的前件，尚未由裸几何内生构造。$\square$

[Q184AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen、F. W. Shultz，State spaces of Jordan algebras，Acta Mathematica 140 (1978)，155–190，p.158，式(2.4)及紧随其后的双侧 P-projection 定义。"
[Q184SR]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "125.4—125.6：EB3 三角的规范零读数保持映射、联合分离与正性条件。"
[Q184BR]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md "121.1：EB3 原域的既有规范映射与正性接口，不是裸 L2 的供应。"

## 追加锚（本行以下为增补区）

## 185. 用原测试暴露二点球的共同删除重建

### 185.1 二元球的原零测试与三点相交

**定义 185.1（二点面暴露条件）。** 采用178.1的整个有限维实原域，$d>1$，并给实际 L2；不先给 $\mathsf Z_2$、$\mathsf{PL}$ 或 AD。对不同纯点 $a,b$ 的整个最小实际面 $B_{ab}=F_K(a,b)$，定义

$$
\begin{gathered}
\mathcal Z(B)=\{k\in C^*:k(x)=0\text{ 对全部 }x\in B\},\\
\operatorname{eh}(B)=K\cap\bigcap_{k\in\mathcal Z(B)}\ker k,\\
\mathsf E_2:\quad
\forall a\ne b\in P\ \exists k_{ab}\in C^*:\qquad
K\cap\ker k_{ab}=B_{ab}.
\end{gathered}
\tag{185.1}
$$

允许 $B_{ab}=K$ 时取零泛函；真球要求非零暴露泛函。这里的 $k$ 是整个原锥上的正测试，缩放后属于原 $[0,u]$。它只用正泛函与准备之间的取零配对，不以纯点双重正交补定义实际球，也不输入球上局部测试的全延拓。

**定理 185.2（二点暴露同时支付纯点分离）。** 在185.1的背景内，$\mathsf E_2$ 等价于下面的原纯点分离条件：对每对不同 $a,b$ 及每个 $c\in P\setminus B_{ab}$，存在原正测试 $k$，满足 $k(a)=k(b)=0$、$k(c)>0$。任一条件成立时，每个原纯点均暴露。若某个 $a$ 另满足184.5的 $\mathsf{RJ}(a)$，则其已由184.6定义的最小确认效应满足

$$
\{x\in K:e_a(x)=1\}=\{a\},\qquad
(uQ_a)(b)>0\quad(b\in P\setminus\{a\}).
\tag{185.2}
$$

证明。使用有限维暴露面交的成熟工具，但核对其原域参数：$\mathcal Z(B)$ 张成空间可选一组来自该正锥的有限基 $k_1,\ldots,k_s$。所有 $k_j$ 在 $K$ 非负，故 $k_B=\sum_j k_j$ 的原零面恰为 $\operatorname{eh}(B)$；零空间情形取空和。若分离条件成立，则 $\operatorname{eh}(B)$ 的每个纯点都在 $B$；原紧面的有限纯凸生成给 $\operatorname{eh}(B)=B$，所以 $k_B$ 暴露实际球。反向用(185.1)的同一张测试。这里从 $k(a)=k(b)=0$ 得 $k|_B=0$，只因原零面是包含 $a,b$ 的实际面。

再固定纯点 $a$。若 $K$ 本身是一颗实际三球，完整原菜单中的球上仿射效应暴露 $a$。否则任取 $b\ne a$，必有 $c\in P\setminus B_{ab}$，因为全部纯点若都属于该紧球，$K$ 就等于它。两颗不同实际三球 $B_{ab},B_{ac}$ 的交是各自的面；严格凸球的非空真面只有单点，且两球维数相同，因此

$$
B_{ab}\cap B_{ac}=\{a\},\qquad
K\cap\ker(k_{ab}+k_{ac})=\{a\}.
\tag{185.3}
$$

这复用180.5的两球相交机制，改由两张原正暴露测试支付交点的暴露。把非零 $k_{ab}+k_{ac}$ 除以其原紧底最大值，再取补效应，得到 $f_a\in[0,u]$ 且 $\{f_a=1\}=\{a\}$。若给 $\mathsf{RJ}(a)$，184.6的 least 性使 $e_a\le f_a$，所以 $\{e_a=1\}\subseteq\{f_a=1\}$；$e_a(a)=1$ 给等号，得到(185.2)。没有从裸 RJ 直接断言该单点最大面。$\square$

### 185.2 同一映射把实际球送到它自己的对径

**定理 185.3（暴露二点球的原删除公式）。** 在实际 L2、$\mathsf E_2$ 下，只对一个固定纯点 $a$ 要求 $\mathsf{RJ}(a)$，已经得到经过 $a$ 的全部实际球对径零关系。更准确地，对任一这样的球 $B$，取单位球坐标 $a=(1,n_a)$、$x=(1,z)\in B$，写

$$
q_B(a,x)=\frac{1+\langle n_a,z\rangle}{2}.
$$

则在原空间中有

$$
\boxed{\quad
 e_a(x)=T_a(x)=q_B(a,x),\qquad
 Q_ax=\bigl(1-q_B(a,x)\bigr)a_B^-.
\quad}
\tag{185.4}
$$

没有预给 $Q_a$ 的像、球保持、纯态保持或完整双侧互补，也不需要其他纯点的 RJ 或 $\mathsf Z_2$。

证明。任取 $b\in P_B\setminus\{a\}$。185.2使 $m=u(Q_ab)=1-e_a(b)>0$。$k_B(a)=0$ 使184.5的同一保持律适用于该正泛函，故

$$
k_B(Q_ab)=k_B(b)=0,\qquad e_a(Q_ab)=0.
$$

第二个等式来自184.6，而非球内投影假设。于是原归一化输出 $y=Q_ab/m$ 确实满足

$$
y\in B\cap D_a.
\tag{185.5}
$$

球上非负且不超过一的仿射函数 $e_a|_B$ 在球面点 $a$ 取一，又在 $y$ 取零。写成 $\alpha+\langle v,z\rangle$，上下极值给 $\alpha+\|v\|=1$、$\alpha-\|v\|=0$；最大方向为 $n_a$。因此 $e_a|_B=q_B(a,\cdot)$，且 $B\cap D_a=\{a_B^-\}$。这先给实际 AD。

对任意混态 $x\in B$，正性与同一保持律仍给 $Q_ax\in C\cap\ker k_B\cap\ker e_a$。若输出非零，严格正的 $u$ 使其可归一化，故属于 $\operatorname{cone}\{a_B^-\}$；若输出质量为零，严格正性使输出就是零。再用 $uQ_a=u-e_a$ 确定系数，得到(185.4)。特别地，所有球内 $x\ne a$ 的非零归一化输出都是该球自己的原对径。这里的几何重叠直到本条推导后才与同一原最低读数相等。$\square$

**命题 185.4（无暴露证书时的精确位置界）。** 在仅有实际 L2及 $\mathsf{RJ}(a)$ 的原域内，对每颗经过 $a$ 的实际球 $B$，仍有

$$
Q_a(\operatorname{cone}B)
\subseteq\operatorname{cone}\bigl(D_a\cap\operatorname{eh}(B)\bigr).
\tag{185.6}
$$

若 $B$ 非暴露，则有原纯点 $c\in\operatorname{eh}(B)\setminus B$：全部在 $B$ 上读零的原正测试也在这个球外纯点读零。因此这些零测试不能判定实际球成员身份；本条不声称任何这样的 $c$ 都能成为 $Q_a$ 的输出，也不声称已构造满足 L2与全纯 RJ 而违反 $\mathsf E_2$ 的模型。

证明。184.6给正像包含 $\operatorname{cone}D_a$。对每个 $k\in\mathcal Z(B)$，有 $k(a)=0$，所以 $kQ_a=k$；输入在 $\operatorname{cone}B$ 时输出仍被全部这些 $k$ 消去。这给(185.6)。185.2证明内的有限正和使 $\operatorname{eh}(B)$ 本身是暴露面；若它等于 $B$，$B$ 就已暴露。严格包含时，若其全部纯点都在 $B$，紧凸生成又会迫两者相等，所以有上述球外原纯点。被合并的是“这些特定零测试全读零”的观察纤维，不是整个原菜单的全部读数。$\square$

### 185.3 完整重建与谱截面的受限入口

**定理 185.5（无需实际线恢复的单系统分类）。** 在同一完整有限维实原域、$d>1$ 内，实际 L2、$\mathsf E_2$ 及全部原纯点的 RJ，当且仅当存在保持原单位的整个锥同构

$$
\Phi:V\overset\sim\longrightarrow\operatorname{Herm}_n(\mathbb C),\qquad
\Phi(C)=\operatorname{PSD}_n,\qquad
u=\operatorname{Tr}\circ\Phi,\quad n\ge2.
\tag{185.7}
$$

同样的分类适用于额外给定任意忠实有限谱截面表示 $A:V\hookrightarrow\operatorname{Herm}_m(\mathbb C)$、$C=\{v:A(v)\succeq0\}$ 的原域：此时只需另检验实际 L2与全纯 RJ，不需 ROG、原纯像秩一或矩阵大小上界。

证明。184.6逐纯点先给全部 $\mathsf Z_2$；178.2于是供应 NC。185.3给全部 AD。现已准确达到 [XIII162.10][Q177XIII] 的 L2、NC、AD 入口，直接消费其完整复 PSD 分类，不从 Hilbert-ball 名称单独借来 projectivity。反向标准复矩阵中 $Q_a(X)=(I-a)X(I-a)$ 满足184.5；二维支持面由 $X\mapsto\operatorname{Tr}(P_{S^\perp}X)$ 暴露，故实际 L2及 $\mathsf E_2$ 均成立。

谱截面分支只需供应 $\mathsf E_2$。直接复用 [VI94.2证明中的(94.8)][Q185VI] 的最小面支持公式；它的该步证明不使用 ROG：对原实际面 $F$ 的相对内点 $z$，令 $S=\operatorname{ran}A(z)$，则

$$
\operatorname{cone}F
=\{v\in C:\operatorname{ran}A(v)\subseteq S\},\qquad
k_F(v)=\operatorname{Tr}\bigl(P_{S^\perp}A(v)\bigr)\ge0,
\quad K\cap\ker k_F=F.
\tag{185.8}
$$

支持包含的一侧为 PSD 面性质；另一侧用 $A(z)$ 在 $S$ 上正定，取充分小 $\varepsilon>0$ 使 $A(z)-\varepsilon A(v)\succeq0$，再用原截面定义及实际面性质。对 $F=K$ 可取零测试。该成熟谱截面工具只在本受限分类的证明中使用，不重报为新增支持公式；共同矩阵表示仍是这一分支的明写前提，不称由裸原关系内生。

取得(185.7)以后，才能运输复 PSD 的支持面规则，恢复原 $\mathsf{PL}$、全部 $Q_a(C)=\operatorname{cone}D_a$、唯一性及184.7的完整双侧互补；这些后果均未参与185.2—185.3的前件。$\square$

**定义 185.6（三复制暴露球删除候选）。** 完整保留178.5的强实全有限背景：$\dim V>1$，全部 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成原锥、严格正乘法单位、每个有限分块的原 min/max、整个原基和全部对偶效应、原正置换及逆、规范重括号和标量层。只在整个原 $K_3$ 要求：任意两不同原纯点生成的实际面为暴露仿射三球，以及每个原纯点的184.5共同零菜单保持，记为 $\mathsf Q_{\rm exposed\,rej}$。前一项精确为实际 L2加 $\mathsf E_2$；也可用原逐实际面的局部中心三角形供应 L2，再单独写 $\mathsf E_2$。不另给 $\mathsf{PL}$、纯点单独暴露、严格输出质量、$\mathsf Z_2$、AD、least或幂等。

**定理 185.7（同一坐标的全有限理论）。** 在185.6的精确背景内，$\mathsf Q_{\rm exposed\,rej}$ 当且仅当存在固定整数 $n\ge2$ 和同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，对全部有限 $N\ge0$ 有

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{185.9}
$$

若三个原纯点 $a,b,c$ 不属于同一实际二点球，其最小实际支持面因此正是复三维支持的完整 PSD 面，归一仿射维数八。它比三张分别给坐标的球更大；共同原测试及共同删除映射经同一坐标运输，而非另取三套不相容的局部表示。

证明。在整个 $K_3$ 上使用185.2—185.3和184.6，取得 L2、AD及全部 $\mathsf Z_2$；178.2给 NC。于是直接消费178.6及其 [XIII162.16][Q177XIII] 的原有限传播入口，得到同一个 $\theta$ 的(185.9)，包括单位和 $N=0$。反向在每个标准复层按185.5供应全部原条件。三点结论在取得表示后用三个秩一向量的复张成：不共二点球恰排除二维支持，三个向量的张成恰为复三维。这里没有先把三点面八维作为重建前提。

在同一表示下，已有178.7、184.10及XIII§162.9的条件字典逐项消费如下。

| 原定义与约束 | 现有量子结构及条件 |
| --- | --- |
| 全锥、严格正单位、原纯点及完整效应菜单 | 密度矩阵、复射线、$0\le H\le I$；原配对为 $\operatorname{Tr}(H\rho)$，包括 Born 读数 |
| 实际暴露二点球与185.4 | 二维复支持的 Bloch 球；原共同删除成为 $(I-a)X(I-a)$，不是预先指定的实际装置 |
| 完整原有限单位分解 | 数学 PVM/POVM；具体事件菜单是否实现全部分解仍须原事件饱和条件 |
| 同一个 $\theta^{\otimes N}$ 与原乘法单位 | 全有限复张量、纠缠及偏迹，保持原产品、置换与重括号 |
| 原映射对全部有限旁观者保正并满足全输入质量预算 | 数学 CP-TNI分支及Choi/Kraus；有限分支族的和满足总预算才为相应的仪器或次仪器，不以单层正性替代此原过程条件 |
| 另给指定锐中性更新或原连续可逆时间群及钟标定 | 相应的 Lüders 更新或酉时间演化；本候选不选择实际设备、Hamiltonian、钟或 $\hbar$ |

以上只消费已取得整个复 PSD 目标之后的字典，不从候选的一个正映射自动宣布所有实际过程已经可用。$\square$

### 185.4 反事实、数学归属及完整白话

**命题 185.8（球形与暴露各自承担的边界）。** 若只保留全纯 RJ而去掉实际 L2，允许非椭球的严格凸状态体，即使所有纯点都单独暴露、全部二点最小面也暴露，仍不能消费185.5。另一方面，保留 L2与全纯 RJ时，是否可不再输入 $\mathsf E_2$，或绕过它推出 AD，仍为 open；185.4只定位该缺口，不提供反模型。

证明。给一个同原全菜单的对照。令 $V=\mathbb R\oplus\mathbb R^3$、$C=\{(t,x):t\ge\|x\|_4\}$、$u(t,x)=t$。纯点为 $a=(1,s)$、$\|s\|_4=1$。写 $\ell_s(x)=\sum_i s_i^3x_i$，则 Hölder不等式给 $|\ell_s(x)|\le\|x\|_4$、$\ell_s(s)=1$。定义

$$
Q_a(t,x)=\frac{t-\ell_s(x)}2(1,-s).
\tag{185.10}
$$

它正、质量不增且 $Q_aa=0$。$\ell_4$ 范数在非零点可微，故在 $a$ 取零的整个原正泛函锥恰为 $\{\lambda(t-\ell_s(x)):\lambda\ge0\}$；直接代入(185.10)使该整个锥共同保持。因此每个原纯点均满足 RJ。严格凸性使任意不同纯点的最小面为整个 $K$，故 $\mathsf E_2$ 成立；同一严格 Hölder等号也使 $e_a=(t+\ell_s(x))/2$ 的最大面为 $\{a\}$。

但此 $K$ 是三维 $\ell_4$ 球，不能仿射同构欧氏球：它的对称中心为零，若是椭球则其 Minkowski范数来自内积并满足平行四边形恒等式，而标准坐标向量的左侧为 $2\sqrt2$、右侧为 $4$。所以实际 L2失败。此例只检验单锥各条件的职责，不是保留 L2的反例，也不宣称给出了满足185.6全部有限复合背景的替代理论。$\square$

**命题 185.9（几何前端的简化及完整白话）。** 本章用 $\mathsf E_2$ 替换184.9的实际线恢复前件 $\mathsf{PL}$：在原 L2及全纯 RJ的共有背景下，181.2给 $\mathsf{PL}\Rightarrow\mathsf E_2$，而185.2—185.5给反向所需的完整量子结构及 $\mathsf{PL}$。它把证明所需的几何接口缩到实际球与原零测试的关系，未证明裸 L2及全纯 RJ自动产生这个接口，也不申领独立物理前件数量严格减少。

证明与归属。185.2—185.5的承重接合为 repo-derived：两实际球的原正测试相加支付单点最大面，再由一张原删除映射的真实归一化输出支付对径；185.4保留未暴露时的准确像位置界。有限维暴露面交、球上仿射极值、严格凸范数与Hölder等号均为成熟中间工具。185.5的谱截面支持公式复用[Q185VI]及其所引 Hildebrand；不重报VI94的ROG分类，也不增加纯像秩一假设。[Q184AS] p.160的Hilbert ball property明确同时要求球形和norm-exposure，p.158及p.188的projectivity与分类各按原接口使用；本章没有声称只有球形就满足这些前件。全部有限复传播与量子字典继续归178.6及XIII162.16，不申领新分类或文献优先权。

白话上，把所有准备和测试留在同一个能有限复合的实概率系统里，只检查整个三份系统。任取两个纯准备，它们撑起一颗实心三球，而且有原测试能把这颗球单独圈出来；再对每个纯点要求同一个删除动作：删掉这个点，但完整保留所有原本对它读零的测试。一个点放在两颗不同的球上，两张圈球测试相加，就能单独认出这个点，因此删除动作不会把别的纯点也完全抹掉。现在在球里另取一个纯准备，删完仍有真实输出；圈球测试保持为零，输出就不能跑到球外。删除点的确认测试又必须在输出上读零，球的几何于是把输出钉在自己的对径。这样，最低读数、对径和球内删除公式成为定义间同一约束的后果；已有重建再把三个不共二点球的纯准备两两撑起的小球接成完整三能级支持面，把整个有限理论接成同一套复矩阵和张量。尚未从裸定义赚得的是那张能圈出整球的原测试；若它不存在，所有消去球的测试还会漏认球外点，不能把这个漏洞画成已经封闭。$\square$

[Q185VI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md "VI94.2证明中(94.8)的谱截面最小面支持公式；该步不依赖ROG。"

## 追加锚（本行以下为增补区）

## 186. 只删自身的原零菜单保持与全部实际面

### 186.1 把非退化性写在两个原元素之间

**定义 186.1（精确的正删除核）。** 先采用178.1的整个有限维实原域，$d>1$，不输入实际 L2、$\mathsf{PL}$ 或任何面暴露条件。对每个原纯点 $a$，要求存在同一实线性映射 $Q_a$，满足184.5的全部 $\mathsf{RJ}(a)$，并另满足

$$
\boxed{\quad
\ker^+Q_a:=C\cap\ker Q_a=\mathbb R_{\ge0}a.
\quad}
\tag{186.1}
$$

记为全纯 $\mathsf{RJ}_{\rm exact}$。此处只规定正锥内的核；不要求整个实线性核是一维。等价地，对全部 $b\in P\setminus\{a\}$，要求 $u(Q_ab)>0$。该等价由全底的有限纯分解支付：非负输出质量之和为零时，每项质量都为零。这是一张同一映射在两个原纯点上的非退化约束，尚未给其正像、幂等、球保持或任何实际设备的可用性。

184.6已给 $e_a=u-uQ_a=\min\mathcal F_a$。因 $u$ 严格正于非零正元，(186.1)也等价于 $\{x\in K:e_a(x)=1\}=\{a\}$。所以全纯 $\mathsf{RJ}_{\rm exact}$ 等价于“全纯 RJ加全部原纯点暴露”：一个方向用 $uQ_a$ 暴露 $a$；另一个方向取暴露 $a$ 的原确认尺 $f_a$，由 $e_a\le f_a$ 得单点最大面。这只说明精确核怎样承担纯点暴露，没有把该额外条件冒称为裸 RJ 的后果。

### 186.2 从单点删除合成同一原空间的面投影

**定理 186.2（精确删除产生全部暴露面的完整正投影）。** 仅在186.1的完整原域，全纯 $\mathsf{RJ}_{\rm exact}$ 已使每个原暴露面都有固定其整个锥的正线性投影。更准确地，对一组原正交纯点 $p_1,\ldots,p_r$ 的同一完整确认族

$$
e_{p_i}(p_j)=\delta_{ij},\qquad
\sum_{i=1}^r e_{p_i}=u,
\tag{186.2}
$$

以及任一指标集 $I\subseteq\{1,\ldots,r\}$，令 $J=I^c$，并写

$$
\begin{gathered}
s_I=\sum_{i\in I}e_{p_i},\qquad
H_I=K\cap\ker s_I,\qquad H_J=\{x\in K:s_I(x)=1\},\\
\mathcal Z_I=\{g\in C^*:g(p_i)=0\ (i\in I)\},\qquad
T_I=Q_{p_{i_k}}\cdots Q_{p_{i_1}},
\end{gathered}
\tag{186.3}
$$

其中 $i_1,\ldots,i_k$ 是 $I$ 的任一排列，空乘积为恒等映射。则

$$
\begin{gathered}
T_I(C)\subseteq C,\quad uT_I=u-s_I,\quad T_I^2=T_I,\\
T_I(C)=\operatorname{cone}H_I,\quad
\ker^+T_I=\operatorname{cone}H_J,\quad
T_I^*(C^*)=\mathcal Z_I.
\end{gathered}
\tag{186.4}
$$

$T_I,T_J$ 在原空间及对偶空间均 quasicomplementary，且为相应范数的收缩，故供应 [Q184AS] p.158的完整双侧 P-projection 接口。固定原正交族及 $I$ 后，$T_I$ 不依赖乘积顺序。这里不输入非零数值互易 $e_a(b)=e_b(a)$，也不要求所有原正投影彼此可交换。

证明。首先明确复用的范围。[最小确认笔记的“Positive dual generation and one common complete frame”][Q186L] 只用全纯 least 性，已给零读数互反、全部正泛函的有限正交确认分解、正交族总预算以及完整族扩展：

$$
0\ne f\in C^*\ \Longrightarrow\
f=\sum_{i\in I}\lambda_i e_{p_i},\quad\lambda_i>0,
\qquad
\{p_i:i\in I\}\text{ 可扩展为(186.2)},\quad r\le d.
\tag{186.5}
$$

本条直接消费该既有结论，不重新申领正谱分解、正交预算或完整族。其完整实载体、原 $u$、全效应及 least 确认者，分别就是此处 $V,C,u,[0,u],e_p$；不使用该笔记另需非零数值互易的 signed-state 或自对偶供应。

对 $i\ne j$，$e_{p_i}(p_j)=0$，所以 RJ使 $e_{p_i}Q_{p_j}=e_{p_i}$；而184.6使 $e_{p_i}Q_{p_i}=0$。逐因子计算得到 $uT_I=u-s_I$，以及 $e_{p_i}T_I=0$ 对所有 $i\in I$ 成立。因此 $T_I$ 正、质量不增，正像包含 $\operatorname{cone}H_I$。在 $p_i$ 处评价质量式，得 $u(T_Ip_i)=0$，严格正性使 $T_Ip_i=0$。

任意 $g\in C^*$ 的 $gT_I$ 非负且消去全部这些 $p_i$，故属于 $\mathcal Z_I$；反之 $g\in\mathcal Z_I$ 被每个因子保持，故 $gT_I=g$。这同时给对偶正像等式，及 $gT_I^2=gT_I$。原正对偶张成 $V^*$，所以 $T_I^2=T_I$。

现取任意原纯点 $b\in H_I$。非负项求和为零使 $e_{p_i}(b)=0$ 对每个 $i\in I$ 成立；零读数互反给 $e_b(p_i)=0$，故 $e_bT_I=e_b$。于是

$$
u(T_Ib)=1,\qquad e_b(T_Ib)=1.
$$

(186.1)所支付的单点最大面迫 $T_Ib=b$。紧暴露面 $H_I$ 由其原纯点凸生成，因此 $T_I$ 固定整个 $\operatorname{cone}H_I$；结合前面的像包含，得到正像等式。对正输入，输出为零当且仅当其 $u$ 质量为零，故正核由 $uT_I=u-s_I$ 精确给出，证明(186.4)。互换 $I,J$ 得另一组公式。

为支付对偶空间的两条互补，记 $\operatorname{ann}^+H=\{g\in C^*:g|_H=0\}$，证明

$$
\mathcal Z_I=\operatorname{ann}^+H_J.
\tag{186.6}
$$

右侧包含于左侧，因为 $p_i\in H_J$。反向，任取 $0\ne g\in\mathcal Z_I$，按既有(186.5)写 $g=\sum_k\mu_k e_{a_k}$。各项非负且 $g(p_i)=0$，故 $e_{a_k}(p_i)=0$，零互反给 $a_k$ 与每个 $p_i$ 正交。既有有限正交预算于是给 $e_{a_k}+s_I\le u$。在 $H_J$ 上 $s_I=1$，迫全部 $e_{a_k}$ 及 $g$ 取零，证明(186.6)；$g=0$ 显然。原正像公式使

$$
\ker^+(T_J^*)=\operatorname{ann}^+H_J
=T_I^*(C^*),\qquad
\ker^+(T_I^*)=T_J^*(C^*).
\tag{186.7}
$$

原空间的两条互补已由(186.4)支付。正性和 $uT_I\le u$ 给原基范数及对偶序单位范数的收缩；有限维连续性自动，故满足所引完整定义。空面与整个 $K$ 分别由零映射和恒等映射处理，锥空面按 $\{0\}$ 约定。

此外，对偶正像给

$$
\ker T_I=\operatorname{ann}_V\operatorname{span}\mathcal Z_I,
\qquad \operatorname{im}T_I=\operatorname{span}(\operatorname{cone}H_I).
\tag{186.8}
$$

幂等投影由线性像及核唯一确定，两者都与排列无关，故得顺序独立。此论断只针对同一原正交族的删除因子。

最后，任意原真暴露面为 $H=K\cap\ker f$、$0\ne f\in C^*$。以(186.5)分解 $f$，全部系数严格正使 $H=H_I$，所以 $T_I$ 供应所需的正收回及完整接口。$H=K$ 用恒等映射。这一步仍没有使用实际 L2。$\square$

### 186.3 正收回把相对暴露变成原暴露

**定理 186.3（精确删除使全部实际面暴露）。** 在186.1的原域内，全部原实际面均闭且暴露，并各有固定其整个锥的正投影。因此，若另给实际 L2，则185.1的 $\mathsf E_2$ 是结论，无需再输入。

证明。只在本接合内部使用一个有限维凸几何工具：每个全局暴露面若有正线性收回并固定该面，就能把该面内的相对暴露测试延拓为全局正测试。具体地，设 $F=K\cap\ker k_F$，$k_F\in C^*$，且 $P_F(C)=\operatorname{cone}F$、$P_F|_{\operatorname{cone}F}=\operatorname{id}$。若 $M$ 是 $F$ 内的相对暴露子面，取 $\operatorname{span}(\operatorname{cone}F)$ 上线性 $h_F$，使 $h_F\ge0$ 于 $\operatorname{cone}F$，$M=F\cap\ker h_F$。$h_F$ 由相对仿射支撑函数以原 $u$ 齐次化取得，不假设任意原局部效应能无条件正延拓。现在该特定延拓明确为

$$
\boxed{\quad
k_M=k_F+h_F\circ P_F\in C^*,\qquad
K\cap\ker k_M=M.
\quad}
\tag{186.9}
$$

两项非负先迫零点属于 $F$，然后 $P_F$ 固定 $F$ 使第二项恰恢复原 $h_F$，故零集没有球外或面外附加点。这是由已经构造的同一正收回供应延拓，不以局部图示代替。

取任意非空原实际面 $G$，不预先假设它闭，选 $x\in\operatorname{ri}G$。从 $F=K$、$k_F=0$、$P_F=\operatorname{id}$ 开始。若当前闭暴露面 $F$ 严格包含 $G$，则 $x\notin\operatorname{ri}F$：否则沿任意 $y\in F$ 到 $x$ 的方向稍越过 $x$，用 $G$ 的面性质就会迫 $y\in G$，与严格包含矛盾。因此 $x$ 在 $F$ 的相对边界，有相对非负支撑函数在 $x$ 取零，形成真相对暴露面 $M\subsetneq F$。

这个 $M$ 包含 $G$。事实上，对任意 $g\in G$，$x\in\operatorname{ri}G$ 使 $x$ 可写成 $g$ 与某个 $z\in G$ 的严格凸组合；支撑函数非负且在 $x$ 为零，便也在 $g$ 为零。使用(186.9)，$M$ 成为全局暴露面；186.2重新供应 $P_M$。每次 $\dim\operatorname{aff}M<\dim\operatorname{aff}F$，故有限次下降必到 $G$。这同时证明 $G$ 本身闭且暴露，不把这些性质偷偷加在下降起点。其正投影再由186.2供应；空面按前条约定。一般下降工具只作证明中的中间步骤，新增接合是186.2支付其全部原正收回前件。$\square$

### 186.4 更短的候选与全部有限理论

**定义 186.4（三复制精确零删除候选）。** 完整保留185.6的强实全有限原背景，包括全部张量幂、原锥及原严格正乘法单位、每个有限 min/max 分块、整个原基与全对偶菜单、原正置换及逆、规范重括号和标量层。只在整个原 $K_3$ 要求实际 L2及186.1的全纯 $\mathsf{RJ}_{\rm exact}$，记为 $\mathsf Q_{\rm exact\,rej}$。实际 L2亦可继续由逐实际面的局部中心三角形供应。既不输入二点球暴露或 $\mathsf{PL}$，也不输入非零数值互易、谱分解、全局投影或自对偶。只删自身的正核条件明写保留。

**定理 186.5（原单点约束重建全有限复层级）。** 在186.4的精确背景中，$\mathsf Q_{\rm exact\,rej}$ 当且仅当存在固定整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使全部有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{186.10}
$$

在单系统 $d>1$ 的原域，实际 L2与全纯 $\mathsf{RJ}_{\rm exact}$ 同样等价于185.5的完整复 PSD 表示。几何上的更大结构是由原正收回及其正核、正像共同描述的全部实际面；不是先指定复子空间格再给原面贴标签。

证明。先在整个三复制原域用186.2—186.3，得到全部实际面暴露，特别得到 $\mathsf E_2$。184.6给全 $\mathsf Z_2$ 与 least，185.3现在合法供应全部原实际 AD及球内精确公式；178.2给 NC。于是精确消费185.7及其178.6/XIII162.16的共同坐标传播，得到(186.10)，不逐层另选同构。单系统直接消费185.5。

反向在标准复矩阵模型取 $a$ 为秩一迹一投影，$Q_a(X)=(I-a)X(I-a)$。184.10已核全部原零菜单共同保持。若 $X\succeq0$ 且 $Q_a(X)=0$，则 $X^{1/2}(I-a)=0$，所以 $\operatorname{ran}X\subseteq\operatorname{ran}a$，即 $X=\lambda a$、$\lambda\ge0$；反向显然。因此正核精确为所需纯射线。这里没有把其完整实线性核误写成该射线。

重建后，在相应有限层的同一表示 $\Theta_N=\theta^{\otimes N}$ 下，对该层(186.3)中的原正交族，$s_I$ 对应支持投影 $P_I=\sum_{i\in I}\Theta_N(p_i)$，$T_I$ 对应 $X\mapsto(I-P_I)X(I-P_I)$，其互补对应 $X\mapsto P_IXP_I$。一般 $T_I+T_J\ne\operatorname{id}$，球内横向相干项不是一个正补映射能相减取出的独立正块。双侧正互补不能改成恒等分解。

若取三个两两原正交纯点 $a,b,c$，原同一完整族中的 $s=e_a+e_b+e_c\le u$ 及其互补删除先供应 $\{s=1\}$ 的原正投影；取得表示后，这整个面恰为复三维支持的完整 PSD 面，归一仿射维数八。三颗两两球和三种原读数此时属于同一九维实锥，不能用分别可达的三份局部坐标替代这个共同实现。单系统没有三元正交族时该条件陈述为空；三复制完整表示的支持维数 $n^3\ge8$ 则包含这样的三元族。

完整理论字典继续逐项复用185.7：原纯点、混态及全效应配对给复射线、密度矩阵和Born读数；有限单位分解给数学PVM/POVM；同一张量幂给纠缠与偏迹。原过程只有在全部有限旁观者保正及全输入质量预算下才对应CP-TNI分支，有限族的总预算再给仪器；实际事件饱和、指定锐中性更新、原连续可逆时间群及钟、能量和 $\hbar$ 标定仍各自独立。本候选的数学复合不自动宣布对应原装置或接续可用。$\square$

### 186.5 丢失精确核后的后果与完整白话

**命题 186.6（真正保留的非退化成本）。** 去掉(186.1)而只保留全纯 RJ时，186.2中对 $b\in H_I$ 能得到的只是 $e_b(T_Ib)=u(T_Ib)=1$，不能据此推出 $T_Ib=b$。这会中断原正像等式及后面的正延拓。若某个纯点 $a$ 的删除映射还删除另一个纯点 $b$，则 $e_a(a)=e_a(b)=1$；在实际 L2下，整个实际球 $B_{ab}$ 都被 $Q_a$ 删除。

证明。184.6给 $uQ_a=u-e_a$，严格正性给 $Q_ab=0\Longleftrightarrow e_a(b)=1$。若 $a\ne b$ 同在该一值面，该实际面包含最小实际球 $B_{ab}$，故 $e_a=1$ 于整球，$uQ_a=0$ 于整球，再由正性和严格正的 $u$ 得 $Q_a|_{\operatorname{cone}B_{ab}}=0$。其几何对径也满足 $T_a(a^-_{B_{ab}})=1$，所以该球的原对径零关系完全失败。全纯 RJ及实际 L2是否已经能排除这种情形，仍为 open；本条没有构造满足二者全部前件的此类模型。

保留精确核而去掉实际 L2仍有185.8的 $\ell_4$ 对照：其 $Q_a$ 正核恰为 $\mathbb R_{\ge0}a$，因为Hölder等号及严格凸性使 $t-\ell_s(x)=0$ 的正输入只有该射线。但原二点面不是欧氏三球，故不能省略球形前件。此处两个反事实分别定位原点对 $a,b$ 与局部几何的职责，不以单锥对照冒称全有限独立性。$\square$

**命题 186.7（定义前端、归属与完整白话）。** 在全纯 RJ的背景下，本章把185的“每颗二点球原暴露”换成更直接的“每张删除映射在正锥中只删除自己的纯射线”。实际 L2下前者经185.2供应后者，后者经186.2—186.3供应全部实际面暴露，故两个完整候选同域等价。简化发生在原单点删除与另一个原正元素之间的关系语言；本章没有证明独立物理前件数量减少，亦未证明共同映射的存在或精确核条件从裸几何内生。

证明与归属。186.2—186.3的承重推导为 repo-derived接合：原正交删除的共同保持先产生原面正像与对偶正像，再把相对支撑沿同一原正收回延拓，有限下降使实际面暴露。最小确认的正对偶生成、完整确认族与正交预算全部直接复用[Q186L]，不以新增定理重报；非零数值互易及自对偶没有被当作这些中间结论的前件。正投影、完整双侧quasicomplementarity及其面序接口来自[Q184AS]；有限维支持、齐次化和面维数下降只是接合证明内部的成熟凸几何工具。单系统分类与全有限同坐标传播继续归185.5、185.7及其原来源，不主张新分类、文献优先权或穷尽检索。

白话上，还是保留全部准备、测试和有限复合，只在整个三份系统检查。任取两个纯准备，它们撑起一颗三维球；对每个纯点，存在同一个删除映射，所有本来对它读零的测试都完整保留，而且它只把自己的那条正射线删成零。先把彼此正交的点放进同一张完整确认表，依次删除其中一组，其他确认读数不会被改动。面里每个纯点仍被自己的尺认成一；只删自身的条件让这次输出只能是它本人，于是合成映射真把整个原面收回并固定。现在面里的支撑测试可以沿这个收回映射放回原空间，再加上圈住大面的测试，得到圈住小面的同一张正测试。面维数只能有限次下降，所有实际面因而都能被圈出，不必再额外要求二点球可暴露。球内真实输出随后被锁在自己的对径，三点共同支持和全部有限层级由已有重建接成同一套复矩阵理论。若一个删除按钮还把另一个纯点抹掉，它会把两点之间整颗球一起抹掉，关键一步就断了；目前仍须明写排除这一点，不能把这项成本藏进“内生”二字。$\square$

[Q186L]: ../../../Library/QuantumStates/mullerududec2012selfduality.md "Positive dual generation and one common complete frame；该节不需要非零数值互易。"

## 追加锚（本行以下为增补区）

## 187. 删除时保持原可区分准备，预算与精确核随后产生

### 187.1 同一映射保持二元关系的两侧

**定义 187.1（原可区分关系与双侧保持删除）。** 完整采用186.1的有限维实原域：$C\subset V$ 闭、尖、生成，$u$ 在非零正元严格为正，$K=C\cap\{u=1\}$，$P=\operatorname{ext}K$，原效应为整个 $[0,u]$，$\dim V>1$。先不输入实际 L2、least、面暴露、投影或非零数值互易。只用这些原对象定义

$$
a\mathrel{\#}b
\quad\Longleftrightarrow\quad
\exists f\in[0,u],\qquad f(a)=1,\quad f(b)=0
\qquad(a,b\in P).
\tag{187.1}
$$

该二元关系由原菜单的存在量词定义，未指定实现该测试的实际设备。取 $u-f$ 说明它对称；它不含自反对。

对每个 $a\in P$，要求存在同一个实线性 $Q_a:V\to V$，满足

$$
\boxed{\quad
\begin{gathered}
Q_a(C)\subseteq C,\qquad Q_aa=0,\\
a\mathrel{\#}b\ \Longrightarrow\ Q_ab=b\qquad(b\in P),\\
hQ_a=h\qquad(h\in C^*,\ h(a)=0).
\end{gathered}
\quad}
\tag{187.2}
$$

称为全纯双侧保持删除。这里“同一个”量化整个原输入域：一侧是原纯准备的固定，另一侧是原正测试对全部输入的读数固定。未输入 $uQ_a\le u$、精确正核、幂等、纯输出或任何复矩阵坐标。全部纯标签的共同约束不可改为每个标签各选部分测试或部分准备。

### 187.2 最大输出点把局部保持变成全输入预算

**定理 187.2（可区分准备的质量约束已足够给全预算）。** 固定一个原纯点 $a$。若实线性 $Q$ 正、$Qa=0$，并且

$$
a\mathrel{\#}b\ \Longrightarrow\ u(Qb)\le1\qquad(b\in P),
\tag{187.3}
$$

则 $uQ\le u$ 于整个 $C$。特别地，(187.2)的原准备固定已经推出质量不增；这一步不使用零测试保持、least、谱分解或 L2。

证明。令 $q=uQ\in C^*$。若 $q=0$，结论直接成立。否则紧底给正最大值 $M=\max_Kq>0$。最大面非空、紧，取其中一个原纯点 $b$。由于 $q(a)=0$，原效应

$$
f=u-\frac qM\in[0,u],\qquad f(a)=1,\qquad f(b)=0
\tag{187.4}
$$

使 $a\mathrel{\#}b$。于是 $M=q(b)=u(Qb)\le1$。故 $q\le u$ 于 $K$，齐次化即得整个 $C$ 上的预算。若使用更强的 $Qb=b$，非零分支直接给 $M=1$。最大点及测试都来自同一个 $Q$，没有把分别可达的最大值拼成共同实现。$\square$

### 187.3 不先给精确核也能构造全部原面

**定理 187.3（双侧保持删除给全部实际面暴露及精确正核）。** 在187.1的整个原域，全纯(187.2)推出全部原实际面闭且暴露，各有186.2的完整双侧 P-projection。对原先给定的每张 $Q_a$，都有

$$
uQ_a\le u,\qquad
C\cap\ker Q_a=\mathbb R_{\ge0}a.
\tag{187.5}
$$

因此，全纯(187.2)与186.1的全纯 $\mathsf{RJ}_{\rm exact}$ 等价，且该等价在加入 L2以前成立。此处的结论仍是正核，不是整个实线性核。

证明。187.2先给全部 $uQ_a\le u$，所以这些原映射现已满足184.5的完整 RJ。直接消费184.6：

$$
e_a=u-uQ_a=\min\mathcal F_a\in[0,u],\qquad
Q_a^2=Q_a,\qquad e_aQ_a=0.
\tag{187.6}
$$

此后才有

$$
a\mathrel{\#}b\quad\Longleftrightarrow\quad e_a(b)=0.
\tag{187.7}
$$

若左侧由 $f$ 见证，least 给 $0\le e_a(b)\le f(b)=0$；反向直接取原效应 $e_a$。故(187.2)在这里支付 $Q_ab=b$ 对整个原零面 $D_a=K\cap\ker e_a$ 成立：先固定该紧面的全部原纯点，再用其有限纯凸分解。没有以该固定性质预先推导 least。

接着直接复用[Q186L]仅凭全 least取得的零互反、正对偶正交分解、正交预算及完整确认族。对任一原完整族 $p_1,\ldots,p_r$、指标集 $I$，采用186.2的同一 $s_I,H_I,H_J,\mathcal Z_I,T_I$。186.2中不依赖 Sharp的质量与对偶像计算仍给

$$
uT_I=u-s_I,\qquad
T_I(C)\subseteq\operatorname{cone}H_I,\qquad
T_I^*(C^*)=\mathcal Z_I,\qquad T_I^2=T_I.
\tag{187.8}
$$

关键的原准备等式现在直接支付。若 $b\in H_I$ 是原纯点，非负项求和为零给 $e_{p_i}(b)=0$ 对每个 $i\in I$ 成立。(187.7)使 $p_i\mathrel{\#}b$，所以每个原因子都固定 $b$，并非仅保持它的确认概率：

$$
Q_{p_i}b=b\ (i\in I),\qquad
T_Ib=b,\qquad
T_I(C)=\operatorname{cone}H_I.
\tag{187.9}
$$

这完全替换186.2原来消费精确核的那一步。任意原暴露面仍由同一个正泛函分解得到某个 $H_I$，故每个原暴露面已有固定其整个锥的正收回。直接使用186.3证明中的有限维下降工具：相对支撑沿该正收回延拓为 $k_F+h_FP_F$，使包含指定实际面的暴露容纳面严格降维，有限次后就是原实际面。因此全部实际面闭且暴露，包括每个纯单点。取单独暴露 $a$ 的原确认尺 $f_a$，(187.6)的 least 性给 $e_a\le f_a$，从而

$$
\{x\in K:e_a(x)=1\}=\{a\},\qquad
C\cap\ker Q_a=\mathbb R_{\ge0}a.
\tag{187.10}
$$

第二式使用 $uQ_a=u-e_a$ 及 $u$ 在非零正输出上的严格正性。至此已取得全纯 $\mathsf{RJ}_{\rm exact}$，可以完整消费186.2的原/对偶四条 quasicomplementarity、收缩范数和固定正交族内的顺序独立；未预用它们来取得(187.9)。

反向，给全纯 $\mathsf{RJ}_{\rm exact}$。186.2取 $I=\{a\}$ 的原删除因子，已证明 $Q_a$ 固定整个 $D_a$。既有 least 再给(187.7)，所以它固定全部原可区分纯准备，并已具有(187.2)其余各项。两方向均适用于同一整族原映射，不用分别更换代表。$\square$

### 187.4 更短的前端及同一套有限复理论

**定义 187.4（三复制双侧保持候选）。** 完整保留186.4的强实全有限背景：全部 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成原锥与严格正乘法单位、每个有限分块的 min/max 界、整个原归一底和全对偶效应、原正置换及逆、规范重括号与标量层。只在整个原 $K_3$ 要求实际 L2以及对全部原纯点的(187.2)，记为 $\mathsf Q_{\rm neutral\,rej}$。L2仍指每个不同原纯对的真正最小实际面为仿射实心三球；不把暴露性塞进它的定义。

定量的全输入质量预算和精确正核不再列为前件，由同一原二元准备保持关系推得。正线性共同映射的存在、删点、全部零测试保持、全部可区分纯准备保持，以及 L2仍明确保留。这一全局等价前端不证明独立物理假设数已经减少，亦不把零测试保持与原准备保持混成同一句同义重述。

**定理 187.5（双侧二元保持重建全部有限复层级）。** 在187.4的精确背景下，

$$
\mathsf Q_{\rm neutral\,rej}
\quad\Longleftrightarrow\quad
\exists n\ge2\ \exists\theta:V\overset\sim\longrightarrow\operatorname{Herm}_n(\mathbb C),\quad
\forall N\ge0:\quad
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{187.11}
$$

证明。只在整个原三复制域使用187.2—187.3，先得到完整 $\mathsf{RJ}_{\rm exact}$，再直接消费186.5。依赖次序为原二元准备保持给预算，预算与零测试保持给 least，全部原准备固定给原面正收回，有限维下降给全部面暴露，实际 L2随后给球内对径及既有重建。共同坐标仍是同一个 $\theta$，不是每层独立选取的同构。

反向，在标准复 PSD 层对每个秩一迹一 $a$ 取 $Q_a(X)=(I-a)X(I-a)$。原 $a\mathrel{\#}b$ 恰表示正交纯射线：若 $0\le H\le I$ 且 $\operatorname{Tr}(Ha)=1$、$\operatorname{Tr}(Hb)=0$，则 $H$ 在 $a$ 的射线上为一、在 $b$ 的射线上为零，故两射线正交；正交时取 $H=a$。因此 $Q_ab=b$。正性、删点及全部零测试共同保持按184.10复用，完整背景与 L2按186.5复用。

更大几何结构仍是同一原空间中的面、正核、正像与对偶面，而非预送的复子空间格。在完整原正交族里取三个原纯点，逐因子删除其余标签先取得同一个原支持面的正投影；重建后，在相应有限层 $\Theta_N=\theta^{\otimes N}$ 下，它就是完整复三能级支持面，归一仿射维数八。三个二点球在这一共同面中相接，不把三份分别选取的坐标冒充共同实现。$\square$

完整量子理论字典按186.5的同一对应读取：

| 原对象或附加条件 | 得到的既有量子对象及边界 |
| --- | --- |
| 整个原正锥、归一底及其全部纯点 | PSD锥、全部密度矩阵与复纯射线 |
| 全原效应及同一配对 | $0\le H\le I$ 与 $\operatorname{Tr}(H\rho)$ 的Born读数；纯对为重叠模平方 |
| 同一原完整确认族及有限单位分解 | 数学PVM/POVM；全部实际测量可用性另需事件饱和 |
| 全部有限原张量层和乘法单位 | 同一 $\theta$ 下的复张量、纠缠与偏迹 |
| 原过程对全部有限旁观者保正，且有全输入质量预算 | 数学CP-TNI及Choi/Kraus；分支族还须共同总预算才给仪器 |
| 指定锐中性更新合同 | 相应Lüders更新；数学面投影不自动供应实际接续或装置 |
| 给定连续保锥保单位的可逆一参数群 | 酉共轭及生成元；物理钟、能量与 $\hbar$ 标定继续分别给定 |

### 187.5 反着看：只保持测试会漏掉输出质量

**命题 187.6（零测试共同保持本身不约束给定删除映射的预算）。** 在整个标准复有限层级中，固定任意非标量层、任意纯 $a$ 及 $\kappa>0$。令 $P_a=I-a$，定义

$$
R_a(X)=P_aXP_a+\kappa\operatorname{Tr}(P_aX)a.
\tag{187.12}
$$

同一 $R_a$ 正、消去 $a$，幂等且正核精确为 $\mathbb R_{\ge0}a$，并完整保持全部在 $a$ 上读零的原正测试；但它不满足(187.2)的原可区分准备固定，也不是质量不增映射。此例保留标准层级的实际 L2，定位的是给定映射预算的缺口。

证明。对 $X\succeq0$，(187.12)两项都正，且 $R_aa=0$。若 $h(X)=\operatorname{Tr}(HX)$、$H\succeq0$、$h(a)=0$，则 $Ha=aH=0$，故 $H=P_aHP_a$。于是

$$
hR_a(X)=\operatorname{Tr}(HP_aXP_a)
+\kappa\operatorname{Tr}(P_aX)\operatorname{Tr}(Ha)=h(X)
\tag{187.13}
$$

对整个实输入空间成立。再作用一次 $R_a$ 会消去追加的 $a$ 项而恢复相同输出，故 $R_a^2=R_a$。若正输入的 $R_aX=0$，两项正性先给 $P_aXP_a=0$，PSD支持公式遂给 $X=\lambda a$、$\lambda\ge0$；反向显然。因此幂等和精确正核也没有补回缺少的预算。取任意 $b$ 与 $a$ 正交的纯点；它们由原效应 $a$ 确定区分，但

$$
R_ab=b+\kappa a,\qquad u(R_ab)=1+\kappa>1.
\tag{187.14}
$$

因此仅保持所有排除 $a$ 的测试，仍容许把额外质量放回这些测试全部看不见的 $a$ 方向。(187.2)的原准备固定排除的正是这类遗漏。该例不否定存在另一张合规的压缩映射，也不满足含TNI的裸 RJ，故不冒充“L2加全纯 RJ不能推出Sharp”的反模型。后一个推导仍为 open。$\square$

**命题 187.7（归属、未付桥与完整白话）。** 新接合是187.2的最大输出点测试，以及187.3用原可区分准备逐因子固定真正目标面，从而在不输入预算或精确核的前端调用既有全部面重建。最小确认、正泛函分解、完整族、双侧P-projection、正收回下降及分类尾部分别直接复用184.6、[Q186L]、186.2—186.5及其原来源；不重报它们为新分类。最大面取纯点、正泛函缩放、PSD支持计算均为成熟证明工具。[Q187JP]定义3.1的Alfsen–Shultz compression预先要求normalized，定义3.5的F-compression亦在(F1)输入 $J(1)\in[0,1]$；引理4.3说明相应dual neutrality与完整固定面之间的关系。本章沿这一成熟neutrality与compression概念路线组织接口，预算先由原完美区分关系取得，再复用186的面构造，不把该文的预给normalized冒充这里的推导。这里的归属为repo-derived接合，不申领文献优先权或穷尽检索。

原准备固定与零测试固定目前都承担明确的不同步骤，未证明前者由后者或裸L2自动给出；也未证明共同正映射的存在从裸定义内生。187.6已区分两类保持对这张原映射的作用，但不充当完整前件的独立性分类。全局等价允许改用更直观的前端，不等于用等价改名计数出更少独立公理。

白话上，仍把所有准备、测试和有限复合放在同一个系统里，只检查整个三份系统。每两个不同纯准备撑起一颗实际三球；删掉一个纯点时，要求同一个正线性动作有两种保持：能与它确定区分的纯准备原样留下，所有本来排除它的测试也保持全部读数。现在不用另外规定输出质量不能增加：找这张映射输出质量最大的准备，如果最大值为正，就能用它自己的输出质量造一张原测试，把它与被删点确定区分；它因此必须原样留下，最大输出质量便只能是一。已有最小确认随后把选定的一组两两可区分纯准备扩展为同一张完整正交表，依次删除一组标签时，目标面里的每个纯准备都被每个因子原样保留，整张面就有了真正的正收回。面内的支撑测试沿收回放回原空间，有限降维使所有实际面都能被圈出，也就能单独认出每个纯点；删除动作只删自身，成为结果。球内对径、同一正交表中三个纯准备的完整三能级支持，以及全部有限层级再由已有重建接成同一套复量子理论。反过来看，只保留测试读数仍能偷偷往被删方向添质量，因为那些测试全都看不见该方向；保留可区分准备正是堵住这处遗漏。两侧保持和共同映射的存在仍须明写，不能把它们藏进“内生”一词。$\square$

[Q187JP]: https://arxiv.org/html/2102.01628v1 "Jenčová–Pulmannová, Geometric and algebraic aspects of spectrality in order unit spaces: A comparison；定义3.1、3.5及引理4.3。"

## 追加锚（本行以下为增补区）

## 188. 只保持原可区分准备，零测试保持随后产生

### 188.1 只保留准备之间的一项删除约束

**定义 188.1（原准备保持删除）。** 完整保留187.1的有限维实原域，原关系 $a\mathrel{\#}b$ 仍由(187.1)的整个原效应区间定义。对每个原纯点 $a$，只要求存在同一个实线性 $Q_a:V\to V$，满足

$$
\boxed{\quad
Q_a(C)\subseteq C,\qquad Q_aa=0,\qquad
 a\mathrel{\#}b\ \Longrightarrow\ Q_ab=b\quad(b\in P).
\quad}
\tag{188.1}
$$

不输入对偶零测试保持、预算、least、幂等、精确正核或面暴露。该条件只约束同一个原正映射在两个纯准备上的作用；$\#$ 的见证可因点对不同而不同，不要求先有同一张测量确认全部点对。

**命题 188.2（已有预算与全混态零封闭的直接供应）。** 全纯(188.1)使每张原 $Q_a$ 质量不增，且给整个原域的 $\mathsf Z_2$ 与 NC。置

$$
e_a=u-uQ_a\in\mathcal F_a,\qquad
N_a=\{b\in P:a\mathrel{\#}b\},\qquad
D_a=\{x\in K:T_a(x)=0\}.
\tag{188.2}
$$

则

$$
D_a=K\cap\ker e_a=\operatorname{conv}N_a=F_K(N_a),
\qquad Q_a|_{\operatorname{cone}D_a}=\operatorname{id}.
\tag{188.3}
$$

此处的 $e_a$ 仅是共同确认者，尚未证明是 least。

证明。预算直接消费187.2，不重证最大输出点论证。于是 $e_a\in[0,u]$ 且 $e_a(a)=1$。每个 $b\in N_a$ 被 $Q_a$ 固定，故 $e_a(b)=0$。这字面支付178.2的第四项，直接取得整个原混态域的 $\mathsf Z_2$、NC及(188.3)的面与凸包等式。固定性由 $N_a$ 的有限凸生成与线性得到。$D_a=\varnothing$ 时锥按 $\{0\}$ 处理。反向 $e_a(b)=0$ 也由原效应 $e_a$ 见证 $a\mathrel{\#}b$，并未使用 least。$\square$

### 188.2 取平均得到原零面的正收回

**引理 188.3（有限维平均工具及其原面用途）。** 在188.1的原域，每个原 $D_a$ 都有同一原空间上的正、质量不增、幂等映射 $P_a$，满足

$$
P_aa=0,\qquad
P_a(C)=\operatorname{cone}D_a,\qquad
P_a|_{\operatorname{cone}D_a}=\operatorname{id}.
\tag{188.4}
$$

不要求原先给定的 $Q_a$ 已幂等，也不把 $P_a$ 认作实际可接续设备。

证明。使用成熟的有限维幂有界算子平均工具，并在本证明中写出所需部分。正性与 $uQ_a\le u$ 使 $Q_a$ 在原基范数中收缩：对任意分解 $v=x-y$、$x,y\in C$，取 $u(Q_ax)+u(Q_ay)\le u(x)+u(y)$，再取基范数下确界。故其全部幂统一有界。

对任意有限维幂有界实线性 $Q$，有

$$
V=\ker(I-Q)\oplus\operatorname{im}(I-Q).
\tag{188.5}
$$

若 $v=(I-Q)w$ 且 $Qv=v$，则 $Q^nw=w-nv$，幂有界迫 $v=0$；再用秩—零化度得直和覆盖。平均

$$
A_L=\frac1L\sum_{j=0}^{L-1}Q^j\qquad(L\ge1)
\tag{188.6}
$$

在固定空间恒等，在 $(I-Q)w$ 处等于 $(w-Q^Lw)/L\to0$。因此 $A_L$ 收敛到固定空间投影 $P$，$P^2=P$、$QP=PQ=P$。对 $Q=Q_a$，每个 $A_L$ 正且质量不增；$C$ 闭使极限 $P_a$ 仍正且质量不增。$A_La=a/L\to0$，故 $P_aa=0$。

若 $x\in C$ 且 $Q_ax=x$，则 $e_a(x)=u(x)-u(Q_ax)=0$，所以 $x\in\operatorname{cone}D_a$。反之188.2已给整个该锥固定。因此 $P_a(C)\subseteq\operatorname{cone}D_a$，并固定其每一点，得到(188.4)。因 $C$ 生成 $V$，还得 $\operatorname{im}P_a=\operatorname{span}(\operatorname{cone}D_a)$，完整线性像亦已确定。这个工具供应原正收回；不供应对偶零测试保持、least或完整双侧P-projection。$\square$

### 188.3 把原约束传进面，再沿极大真面下降

**定理 188.4（准备保持删除使全部实际面正收回且暴露）。** 仅在188.1的整个原域，全部原实际面均闭且暴露，并各有固定其整个锥的正、质量不增收回。此结论不需要 L2、least或对偶零测试保持。

证明。承重接合是把同一个原正收回用于局部全菜单的延拓和原删除映射的限制。设一个已取得的非空原闭面 $F$ 有原正、质量不增收回 $P_F$，$P_F(C)=\operatorname{cone}F$ 且在该锥恒等。令 $V_F=\operatorname{span}(\operatorname{cone}F)$，使用完整局部效应区间 $[0,u_F]$，$u_F=u|_{V_F}$。对任何局部效应 $f_F$，都有

$$
0\le f_FP_F\le uP_F\le u.
\tag{188.7}
$$

因此局部 $a\mathrel{\#_F}b$ 的见证通过同一 $P_F$ 成为原全域见证，而非假设任意面的局部效应免费延拓。$F$ 的全部纯点也是原纯点，所以对每个 $a\in\operatorname{ext}F$，原映射给

$$
R_a^F=P_FQ_a|_{V_F}:V_F\to V_F.
\tag{188.8}
$$

它正、消去 $a$，并固定全部局部 $a\mathrel{\#_F}b$。故完整局部原域再次满足(188.1)，可在该域直接使用188.2—188.3。局部维数一及空零面也由同一公式处理。

下一步直接复用 XIII162.12证明中(162.17)的极大真面极标机制，仅把其 NC供应明确改为188.2。具体地，在 $F$ 内取任一非空极大真面 $H$，不预设它闭。在 $\operatorname{ri}H$ 的一点取 $F$ 的相对支撑函数，它的真暴露零面包含 $H$；极大性迫二者相等，所以 $H$ 闭且相对暴露。取相对正泛函 $h_H$、归一使 $\max_F h_H=1$，再取一个局部原纯最大点 $r$。于是 $h_H\in\mathcal F_r^F$ 且消去整个 $H$，故 $H\subseteq D_r^F$。188.2使 $D_r^F$ 为真面，极大性给

$$
H=D_r^F.
\tag{188.9}
$$

188.3因而供应 $V_F$ 上固定 $\operatorname{cone}H$ 的正TNI收回 $P_H^F$；与 $P_F$ 合成便是整个原空间到 $\operatorname{cone}H$ 的正TNI收回。极标不要求唯一，所取投影也不在此宣称唯一。

现在取任意非空原实际面 $G$，不预设闭。从 $F=K$、$P_F=\operatorname{id}$、$k_F=0$ 开始，其中 $F=K\cap\ker k_F$。若 $G\subsetneq F$，它可包含在 $F$ 的某个极大真面 $H$ 中：先用 $\operatorname{ri}G$ 处的支撑取得真容纳面，再在有限面维数中取最大的真容纳面。上述构造供应 $P_H^FP_F$。同时188.7支付相对支撑 $h_H$ 的正延拓，186.3中的同一公式给

$$
k_H=k_F+h_HP_F\in C^*,\qquad
K\cap\ker k_H=H.
\tag{188.10}
$$

$H$ 包含 $G$，且其仿射维数严格小于 $F$。重复有限次必到 $G$，所以它本身闭、全局暴露，并有原正TNI收回。整个 $K$ 用恒等映射；空面用零映射。证明没有先假定任意实际面暴露、没有先给局部菜单延拓，也没有由 $P_F$ 偷得实际设备可用性。$\square$

### 188.4 实际球效应现在可以延拓

**定理 188.5（原准备删除与实际 L2重建复量子锥）。** 在188.1的原域中，若另给实际 L2，则存在 $m\ge2$ 及保持原单位的实线性同构到整个 $\operatorname{PSD}_m$。并且对原先给定的每张 $Q_a$，零测试保持、least、精确正核和标准压缩公式都是结论。

证明。188.2已给全部原 NC。任取实际二点球 $B$，188.4供应固定整个 $\operatorname{cone}B$ 的原正TNI收回 $P_B$。在该仿射三球的完整局部效应中，对每个球面原纯点 $a$，取球内确认尺 $b_a^B$，在 $a$ 读一、在几何对径 $a_B^-$ 读零。由(188.7)，

$$
f_a^B=b_a^BP_B\in[0,u],\qquad
f_a^B(a)=1,\qquad f_a^B(a_B^-)=0.
\tag{188.11}
$$

于是原全域 $T_a(a_B^-)=0$，即全部实际 AD。到此才字面取得同一完整原域的 L2+NC+AD，直接消费 XIII162.10的既有整锥分类。不把未延拓的球内尺当作原效应，也不把正收回先认作完整AS投影。

重建后仍可追踪原来的给定映射，而非另换代表。用同一表示把 $a$ 写成秩一迹一投影 $p=|\psi\rangle\langle\psi|$。原 $\#$ 恰是纯射线正交，所以 $Q_a$ 固定 $\psi^\perp$ 上全部秩一正元，进而固定该支持上的整个 Hermitian块。对任意 $z\perp\psi$ 及 $t>0$，

$$
\pm\bigl(|\psi\rangle\langle z|+|z\rangle\langle\psi|\bigr)
\preceq t p+t^{-1}|z\rangle\langle z|.
\tag{188.12}
$$

正性、$Q_ap=0$ 及上述固定性给其输出被 $\pm t^{-1}|z\rangle\langle z|$ 夹住。令 $t\to\infty$，闭尖性迫横向项输出为零；用 $iz$ 同样消去虚横向项。原实线性分块于是给

$$
Q_a(X)=(I-p)X(I-p).
\tag{188.13}
$$

所以全部原零测试保持及186.1的精确正核按标准支持公式成立，least按184.6复用。它们在本证明中都位于 AD与分类之后，没有反向承担188.4。

反向，完整标准复锥中的压缩(188.13)正、删去 $p$ 且固定全部与之正交的纯点，满足(188.1)，实际 L2亦成立。$\square$

**定义 188.6（三复制原准备保持候选）。** 保留187.4全部强实全有限背景，包含所有原 $V^{\otimes_{\mathbb R}N}$、闭尖生成锥、严格正乘法单位、每个有限 min/max 分块、全部原基和完整效应、正置换及逆、规范重括号、标量层与 $\dim V>1$。只在整个 $K_3$ 要求实际 L2以及全纯(188.1)，记为 $\mathsf Q_{\rm prep\,rej}$。前端不输入对偶零测试保持、预算、精确核、least或面暴露。

**定理 188.7（同一有限理论及被删除的输入条款）。** 在188.6的精确背景下，$\mathsf Q_{\rm prep\,rej}$ 当且仅当存在同一个 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使所有有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{188.14}
$$

证明。仅在整个原三复制域使用188.2—188.5，取得同域 L2、NC、AD；直接消费 XIII162.16及178.6已核对的全部强域与共同坐标传播接口。反向按188.5及标准全有限背景成立。与187.4相比，保持全部零测试的那条输入约束已由本章推导，不是重新命名；原准备固定、共同正线性映射存在、L2及全有限背景继续明写。裸 L2加全RJ是否自动给原准备固定，仍未由本章证明。

三个原正交纯点的有限提升仍在同一原完整支持面内进行。188.4先供应其实际面的原正收回；取得同一表示后，最小支持为复三维，归一仿射维数八，三颗两两球都在此共同面里。有限层坐标始终是 $\Theta_N=\theta^{\otimes N}$。完整QM字典直接消费187.5的全部条件：全态/全效应配对给Born、纯射线与数学POVM，同一张量层给纠缠和偏迹；全部旁观者保正、全输入预算及族总预算分别承担CP-TNI与仪器。实际事件饱和、指定锐中性更新、连续可逆时间群、钟与能量和 $\hbar$ 标定继续各自独立。平均收回及球内测试延拓没有增加任何原实际控制或免费重置。$\square$

### 188.5 不加球形时，准备保持仍不会自动保持零测试

**命题 188.8（三维原非欧球的全纯反事实）。** 在 $\mathbb R^3$ 取范数

$$
\nu(x,y,z)=\sqrt{x^2+y^2+z^2}+|x|,\qquad
C_\nu=\{(t,v):t\ge\nu(v)\},\qquad u(t,v)=t.
\tag{188.15}
$$

采用整个归一底与全效应。它满足全纯(188.1)，但某张同一原 $Q_a$ 不保持零于 $a$ 的正测试。实际 L2失败；此例只定位球形职责，不冒充全有限强域反模型。

证明。范数底中心对称且严格凸，全部边界点都是原纯点。严格凸性来自欧氏范数的严格三角不等式及 $|x|$ 的凸性；同向不同单位点不存在。原效应写成 $f(t,v)=\alpha t+\ell(v)$ 时，$0\le f\le u$ 等价于 $\|\ell\|_*\le\min(\alpha,1-\alpha)$。若 $f(1,s)=1$、$f(1,r)=0$，两端等号迫 $\alpha=1/2$，$2\ell$ 是在 $s$ 取一的范数支撑；严格凸性使其唯一正负支持点为 $s,-s$，故原 $\#$ 邻点恰为对径。

每个单位 $s$ 任选一个范数支撑 $\ell_s$，定义

$$
Q_s(t,v)=\frac{t-\ell_s(v)}2(1,-s).
\tag{188.16}
$$

$|\ell_s(v)|\le\nu(v)\le t$ 保证正性与TNI，$\ell_s(s)=1$ 给删 $s$ 及固定唯一原可区分纯点 $-s$。故全部标签满足(188.1)。在 $a=(1;0,1,0)$ 处选 $\ell_a(v)=y$，取原正测试 $h(t,x,y,z)=t-x-y$。由 $\nu(v)\ge x+y$ 得 $h\ge0$，且 $h(a)=0$。另取原纯点 $c=(1;1/2,0,0)$，直接算得

$$
h(Q_ac)=1\ne\frac12=h(c).
\tag{188.17}
$$

这个底不是椭球：例如 $x=0$ 的单位方向有多个范数支撑，椭球则处处光滑。严格凸性使任意不同纯对的最小实际面都是整个三维非椭球底，故实际 L2失败。即使已有所有实际面的正TNI收回，球形仍承担188.11的原对径测试供应，不能省略。$\square$

**命题 188.9（归属与完整白话）。** 新承重接合是188.4的遗传步骤：原正TNI收回把局部完整菜单的区分见证带回原空间，使同一原准备删除约束可逐面重用，再由极大真面极标有限下降。预算及零封闭直接复用187.2与178.2；幂有界平均、有限维支持和秩—零化度只作成熟中间工具，coatom极标复用XIII162.12证明的(162.17)，支撑延拓复用186.3。分类与全有限共同坐标尾部归XIII162.10、162.16及178.6；不申领新分类、文献优先权或穷尽检索。188.5末尾的给定映射唯一性是标准PSD支持和两维正块夹逼的应用。原映射的数学存在、正性和原准备固定仍为前件，未从裸逻辑赚得。

白话上，只保留全部原准备、全部测试和有限复合，在整个三份系统检查：每两个不同纯准备撑起一颗实际三球；每个纯点都有同一个正线性删除动作，删掉自己，并把所有能与自己确定区分的纯准备原样留下。先不要求它保持任何测试。最大输出点证明先迫总质量不能增加；没被改变的可区分准备能共用一张原确认尺，组成一个真正的零面。把删除动作反复作用后取平均，得到固定整张零面的正收回。现在到某张已经收回的面里做同样的事：面内的测试先沿收回放回原空间，因此面内能区分的点在原系统也能区分，原删除条件确实传了进去。每个极大真面都能由一个纯极标这样收回，面维数只能有限次下降，所有实际面于是都有原正收回。球里确认一个端点、排除其对径的尺，现在可以沿球的收回变成原测试，对径关系不再额外输入。已有重建把这些球和三点共同支持接成同一套复矩阵及全部有限张量层级；回看原删除动作，它也只能是标准压缩，所以全部零测试读数保持成为结果。若小面是有尖法向的非欧球，准备都能原样保留，零测试仍会改变，188.17直接显示了这一点；因此球形、共同映射和原准备保持仍各有职责，不能一并藏进“内生”二字。$\square$

## 追加锚（本行以下为增补区）
