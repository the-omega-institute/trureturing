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

**定义 177.2（一个目标的中心三项关系）。** 对固定 $p\in\partial B$，$\mathsf R_F(p)$ 表示：每个由至多三个不同纯标签组成的中心配方，都满足

$$
\begin{gathered}
1\le r\le3,\quad a_i>0,\quad\sum_i a_i=1,\quad
q_i\in\partial B,\quad\sum_i a_iq_i=0\\
\Longrightarrow\qquad
\sum_i a_iT_{q_i}^F(p)=T_p^F(0).
\end{gathered}
\tag{177.2}
$$

零权先删除，重复标签先合并。右侧是同一确认定义对中心的读数，不另指定一个概率常数。关系把“各标签分别确认目标，再平均”与“目标直接确认中心”相接；它不是预设 $T_q^F$ 对任意混合为仿射。

**定理 177.3（中心配方精确刻画一条欧氏直和轴）。** 在定义177.1的域中，$\mathsf R_F(p)$ 当且仅当存在实线性泛函 $b_p$，满足 $b_p(p)=1$，并且

$$
N(x)^2=b_p(x)^2+N\bigl(x-b_p(x)p\bigr)^2
\qquad(x\in W).
\tag{177.3}
$$

此时 $W=\mathbb Rp\oplus_2\ker b_p$，且中心关系对任意有限项配方都成立。欧氏直和轴是既有 Banach 空间概念；本条所推导的是它与原始完整确认菜单的两、三项中心关系的等价。

证明。完整确认集的计算复用 [VI，101.2的完整效应式及其证明][Q177VI] 中仅使用中心对称凸体的部分。精确参数是附着于本面自身的锥 $C_F=\{(t,x):t\ge N(x)\}$、单位 $u_F(t,x)=t$、基 $\{(1,x):x\in B\}$；其整个 proper 区间恰是本面的全部仿射效应。该计算不消费101.1的参考互反，其原证明在中心对称性得到后直接逐参数计算。它给出

$$
T_q^F(x)=\tfrac12\left(1+\min_{j\in J(q)}j(x)\right),\qquad
T_q^F(0)=\tfrac12.
\tag{177.4}
$$

在光滑严格凸范数模型中，唯一支持函数的相应公式见 [N177，§7，式(5)，印刷页7][Q177N]；该文定理7.1在其光滑前件下用全部转移概率互反刻画 pre-Hilbert 空间。本证明保留可能多值的 $J(q)$，不用光滑性，也不假设全部目标间的互反。

现假设 $\mathsf R_F(p)$。把配方取成 $q,-q$ 各半，使用 $J(-q)=-J(q)$，得到

$$
\min_{j\in J(q)}j(p)=\max_{j\in J(q)}j(p).
\tag{177.5}
$$

令这个共同值为 $h_p(q)$。它是奇函数，且 $|h_p(q)|\le1$、$h_p(p)=1$。定义 $L_p(0)=0$，并对 $x\ne0$ 定义

$$
L_p(x)=N(x)h_p\bigl(x/N(x)\bigr).
\tag{177.6}
$$

它实齐次且 $|L_p(x)|\le N(x)$。若 $x,y,x+y$ 均非零，取三个单位标签

$$
\frac{x}{N(x)},\quad\frac{y}{N(y)},\quad
-\frac{x+y}{N(x+y)}
$$

及与 $N(x),N(y),N(x+y)$ 成比例的正权，便是中心配方。标签重合时合并仍属于(177.2)；应用(177.4)—(177.6)给 $L_p(x)+L_p(y)=L_p(x+y)$。若有零向量，或 $x+y=0$，结论分别由零值或奇性成立。因此 $b_p:=L_p$ 是有界实线性泛函，$b_p(p)=1$。

为从读数得到平方范数，令 $H(x)=N(x)^2/2$。直接复用 VI101.4证明中(101.6)的范数平方次梯度公式，按因子 $1/2$ 缩放，得到

$$
\partial H(x)=N(x)J\bigl(x/N(x)\bigr)\quad(x\ne0),
\qquad \partial H(0)=\{0\}.
\tag{177.7}
$$

这条公式只要求有限维范数，不要求VI的端点互反。沿直线的方向导数表示同样复用其证明所引 Rockafellar 定理。

由(177.5)，每个 $s\in\partial H(x)$ 都满足 $s(p)=b_p(x)$，包括 $x=0$。凸函数沿 $p$ 的左右导数分别是这个紧次梯度集上的最小值和最大值，因此二者相同。对任意实 $t$，

$$
\frac{\mathrm d}{\mathrm dt}H(x+tp)=b_p(x)+t,
\qquad
H(x+tp)=H(x)+t b_p(x)+t^2/2.
\tag{177.8}
$$

右端导数连续，积分在所有实区间都有效。取 $t=-b_p(x)$ 即得(177.3)。这一推导没有将全体支持函数先验替换成单值微分。

反之设(177.3)。在 $x=tp+z$、$z\in\ker b_p$ 的坐标中，$H(x)=t^2/2+N(z)^2/2$，所以每个 $s\in\partial H(x)$ 在 $p$ 上取值 $t=b_p(x)$。由(177.7)，对单位 $q$ 的所有 $j\in J(q)$ 都有 $j(p)=b_p(q)$。于是 $T_q^F(p)=(1+b_p(q))/2$，而任何有限中心配方的加权 $b_p$ 值为零，给出(177.2)及其任意有限项版本。$\square$

**定理 177.4（三维面的两目标闭合）。** 在定义177.1的三维域中，存在两个中心化方向独立的纯目标 $p_1,p_2$ 满足 $\mathsf R_F(p_1),\mathsf R_F(p_2)$，当且仅当 $F$ 仿射同构于整个闭 Euclidean 三球。

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

**定义 177.6（完整原生候选 $\mathsf Q_{\rm center}$）。** 采用 [VII，定义102.1][Q177VII] 的同一全有限强分块实层级：$V$ 实有限维且 $\dim V>1$，$W_N=V^{\otimes_{\mathbb R}N}$；每层 $C_N$ 闭、尖、生成，$u_N=u^{\otimes N}$ 严格正；每个有限分块均满足原 min/max 界，全部原置换正且逆正，重括号为规范恒等识别，保留标量对象。全基、全纯点、整个对偶和 proper 区间均按 VII102.1取得。不给定复数、矩阵载体、矩阵秩或指定纠缠准备。

只在整个三份基 $K_3$ 上附加下列关系。面均为包含给定点的最小实际凸面，$F(\varnothing)=\varnothing$。

1. 对每个不同 $p,q\in P_3$，整个 $F(p,q)$ 紧、仿射维数三、中心对称且严格凸。以其自身完整仿射菜单定义177.1的读数。在其中心，存在两个纯目标，中心化后的方向独立，二者均满足177.2。这里三个标签与三个物理份数是不同的两个计数。
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

证明。177.4把第一项精确变成整个 $K_3$ 上的 L2；第二、三项就是同一原域的 TC、NC。XIII160.5的参数取 $V'=W_3,C'=C_3,u'=u_3$，全部纯点、全局菜单和实际面均保持原样。闭、尖、生成与严格正性由强域给出。故该既有重建定理给出一个保单位的整锥同构

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

**命题 177.9（几何简化、反事实边界与文献范围）。** 完整候选把复矩阵载体和外供二元秩几何，换成原实凸体的中心、至多三标签配方与两个独立目标的确认关系；局部内积由这些定义间关系重建。其余几何合同为实际三维二元面、TC及全局NC，强域的尖性、生成性和严格正单位仍是前件。

证明。177.3的配方桥与177.4的有限参考应用没有使用复数、矩阵秩、环境 Euclidean 度量、光滑支持函数或纯态可逆传递。它们从两条可检测的欧氏轴得到整个三维面；177.7才通过已有整锥分类识别复数及全有限产品。在最终坐标中，二元面的纯边界为 $S^2$，所有有限纯点整体为 $\mathbb{CP}^{n^N-1}$，二元球是整个正 Hermitian 锥及其张量层级的实际支持面。不是把整个高维外接球面都认成纯态。

若删第三标签或第二方向，177.5的光滑非椭球给出明确局部反例。若保留局部球而删全局NC，[XIII160.7][Q177XIII] 的平衡商是满足 L2、TC 却存在真实邻点面塌缩的单锥控制；其每个球也满足177.4的中心关系。该控制没有给出全部有限复合，不用它主张完整强域中的独立性。TC仍是独立保留的合同；本章没有证明它可由局部配方推出，也没有另给删TC的全有限反模型。

与176.10比较，所去掉的是外供复载体、普通秩一族及迹配对；所保留或新支付的是强实层级、实际面三维性、中心对称严格凸性及TC、NC。二者模型域不同，不能宣称在176的同一弱域上免费减假设，也不宣称全局最短公理数。所有约束也没有变成无前提真理：模型定义给出对象和操作范围，候选约束这些定义之间的相容关系。

文献范围如下。Niestegge [N177][Q177N] §7式(5)、定理7.1及定理9.2分别供应光滑模型的支持函数转移公式、完整互反的 Hilbert 刻画及相应状态空间对应；它们不被另列为本章新结果。欧氏直和方向的概念与结构属于既有 $L^2$-summand 理论；仓内余维一闭合直接复用 VI101.4—101.5，相关书目为 Aizpuru–García-Pacheco, *L²-summand vectors in Banach spaces*, Proc. AMS 134, 2109–2115, DOI [10.1090/S0002-9939-06-08243-8][Q177A]；本章不以尚未核对的该文定理作为证明前提。177.3的多值确认集到局部配方判据、177.4在本候选中的有限目标应用和177.7的参数接合是本章纸面推导；不主张已证明文献优先权。XIII160.5、VII102.4与102.11及其量子字典明确作为既有供应复用。$\square$

**命题 177.10（完整白话候选）。** 在能任意有限复合的实概率关系空间里，取整个三份系统。任意两个纯准备撑起的实际小面都只有三个仿射方向，中心对称且没有平边。在每个小面选两条独立纯方向：不论用至多三个纯标签怎样调出中心，各标签反过来确认这条目标方向的平均代价，都必须等于目标直接确认中心的代价；两条方向都如此。不同小面在共同纯点处的切方向按177.14相容，而全局上与某纯点互不响应的所有邻点，即使一起生成实际面，也不能把它吞进去。这个候选在177.7列明的供应范围内恰好重建全部有限复量子层级。

证明与图景。只看一对对径标签，能逼所有把中心读数压到最低的确认尺，在目标方向上口径一致，却看不出横向空间有没有变形；再放入第三个标签，三角形闭合就让这个读数必须线性。一条目标方向因此变成一条满足勾股分解的轴，但旁边仍能藏一块非欧氏平面。第二条独立目标方向再锁住一条轴，三维里只剩一条横向直线，已无处藏曲折的范数，整个小面便是一颗球。球与球还须能沿共同端点拼接，且不能把原本不同的整体关系压成同一点：切方向相容支付拼接，全局零邻点不吞回自身排除塌缩。已有整锥定理遂把整个三份对象识别成复量子锥，其完整确认关系再经实际复合推广到所有有限份数。最终画面是许多两条纯线撑起的三维球，嵌在同一个复射影纯态几何和正锥层级中。这里球的度量、复数和一维矩阵线不再预送；三维性、概率复合合同、拼接与非塌缩仍明写在候选里，具体事件、测后选择与时间另有177.8的条件。$\square$

[Q177N]: https://arxiv.org/pdf/2208.07135v1
[Q177A]: https://doi.org/10.1090/S0002-9939-06-08243-8
[Q177XIII]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md
[Q177VII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q177VI]: QUANTUM_ORIGIN_INTRINSIC_POLAR_QUOTIENT_AND_NONCOLLAPSE_VI.md

## 追加锚（本行以下为增补区）
