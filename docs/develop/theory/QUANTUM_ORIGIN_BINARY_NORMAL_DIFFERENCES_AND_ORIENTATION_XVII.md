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

白话上，只保留全部原准备、全部测试和有限复合，在整个三份系统检查：每两个不同纯准备撑起一颗实际三球；每个纯点都有同一个正线性删除动作，删掉自己，并把所有能与自己确定区分的纯准备原样留下。先不要求它保持任何测试。最大输出点证明先迫总质量不能增加；没被改变的可区分准备能共用一张原确认尺，组成一个真正的零面。把删除动作反复作用后取平均，得到固定整张零面的正收回。现在到某张已经收回的面里做同样的事：面内的测试先沿收回放回原空间，因此面内能区分的点在原系统也能区分，原删除条件确实传了进去。每个极大真面都能由一个纯极标这样收回，面维数只能有限次下降，所有实际面于是都有原正收回。球里确认一个端点、排除其对径的尺，现在可以沿球的收回变成原测试，对径关系不再额外输入。已有重建把这些球和三点共同支持接成同一套复矩阵及全部有限张量层级；回看原删除动作，它也只能是标准压缩，所以全部零测试读数保持成为结果。若小面是有尖法向的非欧球，所有与被删点可区分的纯准备仍能原样保留，零测试仍会改变，188.17直接显示了这一点；因此球形、共同映射和原准备保持仍各有职责，不能一并藏进“内生”二字。$\square$

## 追加锚（本行以下为增补区）

## 189. 只保留可区分准备的射线，共同质量比例由球面连通产生

### 189.1 不预先指定存活准备的长度

**定义 189.1（原射线保持删除）。** 使用188.1的完整有限维实原域，$\dim V>1$，原纯点集 $P$、整个原效应菜单及原二元关系 $\#$ 全部不变。对每个 $a\in P$，只要求存在同一个实线性 $Q_a:V\to V$，满足

$$
\boxed{\quad
Q_a(C)\subseteq C,\qquad Q_aa=0,\qquad
 a\mathrel{\#}b\ \Longrightarrow\ Q_ab\in\mathbb R_{>0}b
 \quad(b\in P).
\quad}
\tag{189.1}
$$

存活的每个原纯准备只须保持自己的正射线，未预给各自质量比例相等或等于一。$Q_a$ 的原正标度属于这个存在条件的可选择代表，不将数学代表的重新归一化当作实际设备概率的任意更改。未输入预算、least、对偶零测试保持、幂等或精确正核。

### 189.2 最大面的球面把有限个本征值接成一个

**定理 189.2（单标签共同质量比例）。** 在上述完整原域与实际 L2 下，固定一个 $a\in P$。若同一实线性 $Q$ 对全部 $b\in N_a$ 满足

$$
Qb=\lambda_b b,\qquad \lambda_b>0,
\qquad N_a=\{b\in P:a\mathrel{\#}b\},
\tag{189.2}
$$

则 $N_a\ne\varnothing$，并存在唯一 $\lambda_a>0$，使全部 $\lambda_b=\lambda_a$。系数相等不使用 $Q$ 的正性、$Qa=0$、NC、$\mathsf Z_2$、预算、least、对偶保持或其他标签的映射。

证明。先说明邻点非空，不把原纯点暴露性当作前提。非单点紧凸底中的纯点 $a$ 位于相对边界。相对支撑定理给在 $K$ 上非恒零的非负仿射函数、零于 $a$；沿单位超平面齐次延拓，得到 $h\in C^*$、$h(a)=0$ 及 $M=\max_Kh>0$。最大面有一个原纯点 $b$，效应 $u-h/M$ 确认 $a$ 并在 $b$ 读零，所以 $b\in N_a$。

对任意这样的正泛函 $h$，令

$$
F_h=\{x\in K:h(x)=M\},\qquad M=\max_Kh>0,
\qquad h(a)=0.
\tag{189.3}
$$

$u-h/M\in[0,u]$ 使 $F_h$ 的全部纯点都属于 $N_a$。任取其中不同纯点 $b,c$，实际最小面 $B=F_K(b,c)$ 包含在 $F_h$。实际 L2 使 $B$ 是整颗仿射三球，其全部纯点组成连通球面 $S^2$，且因 $B$ 是实际面，这些点也是原纯点。

在该球面，$\lambda(p)=u(Qp)$ 连续，(189.2)又使它只取 $Q$ 的有限个实特征值。连通集到有限集的连续映射恒定，所以 $\lambda_b=\lambda_c$。最大面只有一个纯点时结论直接成立；一般由紧凸底的有限纯凸生成，得到一个 $\lambda(F_h)>0$，满足

$$
Qx=\lambda(F_h)x\qquad(x\in F_h).
\tag{189.4}
$$

关键是连接不同最大面。任取 $b,c\in N_a$，用原完整菜单选 $f_b,f_c$，使它们在 $a$ 读一、分别在 $b,c$ 读零。置

$$
\begin{gathered}
h_b=u-f_b,\quad h_c=u-f_c,\qquad
h_t=(1-t)h_b+th_c,\quad 0\le t\le1,\\
M_t=\max_Kh_t,\qquad F_t=\{x\in K:h_t(x)=M_t\}.
\end{gathered}
\tag{189.5}
$$

这些正泛函都零于 $a$，且 $M_t\ge\max\{1-t,t\}\ge1/2$。上一步为每个 $F_t$ 给一个正实特征值 $\lambda_t$，$Qx=\lambda_tx$ 对全部 $x\in F_t$ 成立。

下面的紧性步骤不要求原纯点集闭。对 $Q$ 的每个正实特征值 $\lambda$，令 $T_\lambda=\{t:\lambda_t=\lambda\}$。若 $t_j\to t$ 且 $t_j\in T_\lambda$，任选 $x_j\in F_{t_j}$；紧性给子列 $x_j\to x\in K$。因为 $0\le h_b,h_c\le u$，有 $|M_t-M_s|\le|t-s|$，故极限 $x\in F_t$。由连续线性得到 $Qx=\lambda x$，而(189.4)给 $Qx=\lambda_t x$。$u(x)=1$ 迫 $\lambda=\lambda_t$。每个 $T_\lambda$ 因而闭合；有限个互不相交闭集覆盖连通区间 $[0,1]$，只有一个非空。因此 $\lambda_t$ 恒定。端点 $b\in F_0,c\in F_1$ 给

$$
\lambda_b=\lambda_0=\lambda_1=\lambda_c.
\tag{189.6}
$$

邻点非空给共同正系数的存在及唯一性。有限谱、紧性和球面连通都是本证明的成熟中间工具；没有先假定 $N_a$ 本身连通、闭或共同可确认。$\square$

### 189.3 归一代表接入准备保持重建

**定理 189.3（内在归一代表及原映射的准确结论）。** 全纯(189.1)与实际 L2 下，每个原 $Q_a$ 有唯一的正标度归一代表

$$
\widehat Q_a=\lambda_a^{-1}Q_a,\qquad
\lambda_a=\max_{x\in K}u(Q_ax)>0,
\tag{189.7}
$$

使它精确满足188.1的原准备固定条件。因此取得188.4的全部实际面正TNI收回和暴露，并由188.5取得同原单位的完整复PSD表示。在该表示中，对每张原先给定的 $Q_a$，准确公式为

$$
\begin{gathered}
Q_a(X)=\lambda_a(I-p_a)X(I-p_a),\qquad
\widehat Q_a(X)=(I-p_a)X(I-p_a),\\
hQ_a=\lambda_a h,\qquad h\widehat Q_a=h
\quad(h\in C^*,\ h(a)=0).
\end{gathered}
\tag{189.8}
$$

预算、幂等、least及精确正核的188.5结论对归一代表成立；不宣称每张未经归一的原 $Q_a$ 质量不增或幂等。

证明。189.2先给每个标签的共同 $\lambda_a>0$。除以它保持正性及删点，并固定全部原 $N_a$，所以字面满足188.1。此时才消费187.2：$u\widehat Q_a\le u$，且因某个 $b\in N_a$ 被固定，$\max_Ku\widehat Q_a=1$，从而共同系数正是(189.7)的内在最大质量。它不是先输入的预算，且不需要选择某个特殊邻点来定义规范代表。188.2—188.5的全标签推导现在直接适用。重建后对归一代表使用188.13，再乘回原标度，得到(189.8)。

例如在标准复锥取 $Q_a(X)=2(I-p_a)X(I-p_a)$，原映射仍满足(189.1)，但在正交纯输入处质量为二，且原零测试读数乘二。故不能把归一代表的预算与读数保持冒领为未经归一原映射的性质。实际输入输出概率若已指定，重新缩放会改变设备；此处只从数学存在类中选规范代表。$\square$

**定义 189.4（三复制射线删除候选）。** 完整保留188.6的强实全有限背景：全部原 $V^{\otimes_{\mathbb R}N}$、闭尖生成锥、严格正乘法单位、每个有限 min/max 分块、整个原基与全效应、正置换及逆、规范重括号、标量层和 $\dim V>1$。只在整个原 $K_3$ 要求实际 L2 与全纯(189.1)，记为 $\mathsf Q_{\rm ray\,rej}$。每个标签只需存在一条正算子射线 $[Q_a]=\{cQ_a:c>0\}$；同一代表对全部原可区分纯准备保持各自正射线。

**定理 189.5（同一全有限复理论与射线几何）。** 在189.4的精确背景下，$\mathsf Q_{\rm ray\,rej}$ 当且仅当存在同一个 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使全部有限 $N\ge0$ 满足188.14。

证明。仅在整个原三复制域使用189.2—189.3，各标签取得同一原空间中的归一代表，直接达到188.6的完整候选；消费188.7即可。反向用标准压缩或其任意正倍数。有限层坐标仍是同一个 $\theta^{\otimes N}$，不另给各层选择方向。

这个前端只记录可区分纯射线在删除方向下不改变，存活长度的一致性由最大面插值和有限谱推出。它与188.6在同一背景上等价，简化在于删去输入中的逐点数值归一约束；不据此申领独立经验假设数严格减少，也没有删除正线性共同映射存在、全原菜单、实际 L2 或全有限背景。

重建后的简洁几何仍是复射影纯点、复子空间支持面与其正交压缩。三个两两原正交纯点在同一复三维支持面内，归一面仿射维数八；三个二点球是该共同面内的面，未将三颗独立球任意拼装。原 $\#$ 对应正交，归一算子射线对应唯一标准压缩；非零Born读数由完整原态/效应配对恢复，不由单纯零邻接表假装给定。QM字典沿用188.7及187.5的精确条件：数学态、效应、POVM、纠缠与偏迹由同一表示供应；CP、全输入TNI及仪器分别要求全部旁观者保正、输入预算和分支族总预算。实际事件饱和、指定锐中性更新、连续可逆时间群、钟与能量及 $\hbar$ 标定仍各自保留。$\square$

### 189.4 两项不能删去的关系职责

**命题 189.6（失去球面连通或允许全灭时的反事实）。** 不输入实际 L2 时，即使保留整个强实全有限背景与全纯射线删除，共同系数也不必成立。另在实际 L2 的单锥域，若将(189.1)的严格正射线改为允许零输出，候选可不满足全纯 $\mathsf Z_2$，因而不能按本证明重建。

证明。第一项用标准经典有限层级 $V=\mathbb R^3$、$C_N=\mathbb R_{\ge0}^{3^N}$、单位为坐标和，使用全部准备与效应。此为成熟的单纯形复合中间实例：各分块 min/max 均为同一正正交锥，置换、重括号与标量层满足189.4的背景。在每个纯标签 $e_i$ 选对角正映射，删去第 $i$ 坐标，在其余坐标取正但不全相等的对角系数。原 $N_{e_i}$ 恰为全部其余基纯点，故全标签(189.1)成立，而共同系数失败。例如 $Q=\operatorname{diag}(0,1,2)$ 对 $e_2,e_3$ 的比例分别为一、二。任意不同纯对的实际面却是线段；其纯边界不连通，L2失败，189.2的球面连接步骤正是在这里失效。

第二项直接消费178.4及XII159的平衡商族，$m\ge3$。它保留完整原菜单与实际 L2、AD，但 $\mathsf Z_2$ 失败。令每个标签的 $Q_a=0$，便正、删点，并满足允许零比例的弱化射线条件。故严格存活不能换成非负比例；这一结论只是在现有单锥族中的反事实，不冒充满足强全有限背景的反模型。$\square$

**命题 189.7（数学归属与完整白话）。** 189.2的新增接合是在原完整效应区间插值两张零于同一标签的测试，用其最大面内实际三球的连通纯边界统一本征值，再以紧性沿测试路径统一不同最大面的本征值。有限维算子的有限谱、紧凸生成、相对支撑及连通集性质只作成熟中间工具；归一后全部面、分类与有限共同坐标直接归188、XIII162及178.6，不申领新分类或文献优先权。

白话上，保留全部原准备、测试和有限复合，只在整个三份系统检查：任意两个不同纯准备撑起一颗实际三球；每个纯点有同一个正线性删除方向，把自己删成零，并让所有能与自己确定区分的纯准备仍沿原来的射线出去，先不规定各自出去多长。拿两张排除被删点的测试，慢慢把一张混成另一张，每一刻最亮的那张面里仍全是可区分准备。面里任意两颗纯点之间有完整三球，球面是连着的，而同一有限维线性映射只有有限种本征值，因而这一整面不能各点各选长度比例。测试连续混合时，紧性又使这个比例不能突然跳走，最终所有存活准备只能共用一个正比例。用它统一归一，便得到188的原样保留删除；平均、逐面收回和球内测试延拓随后把对径关系接回原系统，已有重建给同一套复矩阵及所有有限张量层级。原来的未归一映射是标准压缩的正倍数，数学存在类可以选规范代表，真实设备的概率却不能任意改标度。经典线段的纯端点是断开的，能给不同端点不同倍数；若允许全部删成零，单锥平衡商也能通过弱化的删除条件，因此三球、同一线性映射和严格存活仍各有明确职责。$\square$

## 追加锚（本行以下为增补区）

## 190. 原准备与原测试的有限正配对，删除映射作为结论

### 190.1 先约束关系的关系

**定义 190.1（有限正配对一致性）。** 保留188.1的完整原域：有限维实空间 $V$、闭尖生成锥 $C$、严格正单位 $u$、整个紧底 $K$、全部原纯点 $P=\operatorname{ext}K$ 和整个效应区间 $[0,u]$，置 $d=\dim V>1$。原二元关系及零邻点仍为

$$
a\mathrel{\#}b\ \Longleftrightarrow\
\exists f\in[0,u]\quad f(a)=1,\ f(b)=0,
\qquad N_a=\{b\in P:a\mathrel{\#}b\}.
\tag{190.1}
$$

固定原纯点 $a$。对所有 $0\le k\le d^2$、$0\le r\le d$，原纯点 $p_i$、零邻点 $b_j\in N_a$、原效应 $f_i\in[0,u]$、系数 $t_i\ge0$ 和任意实代数对偶元 $g_0,g_j\in V^*$，要求

$$
\boxed{\quad
\sum_{i=1}^k t_i p_i\otimes f_i
 =a\otimes g_0+\sum_{j=1}^r b_j\otimes g_j
\quad\Longrightarrow\quad
\sum_{j=1}^r g_j(b_j)\ge0.
\quad}
\tag{190.2}
$$

两侧相等是在同一原 $V\otimes_{\mathbb R}V^*$ 中的精确相等。空和允许为零。$g_j$ 可有符号，只是原测试的实线性表达式，不作为负概率事件。此张量记一条准备和一条读数的配对关系，不预认作复合系统的态；其算子配对方向为 $\langle x\otimes h,Q\rangle=h(Qx)$。前端没有 $Q_a$、局部删除 $\delta_a$、$\mathsf Z_2$、NC、暴露面或线性独立性输入。

### 190.2 有限关系自行产生删除方向

**定理 190.2（原有限配对与正删除的精确等价）。** 在190.1的原域，固定 $a$，(190.2)当且仅当存在原实线性映射 $Q:V\to V$，满足

$$
Q(C)\subseteq C,\qquad Qa=0,\qquad Qb=b\quad(b\in N_a).
\tag{190.3}
$$

证明。若有这样的 $Q$，以它收缩(190.2)的张量等式，左侧为非负数 $\sum_i t_i f_i(Qp_i)$，右侧为 $\sum_j g_j(b_j)$，必要性成立。

反向先让空正和排除隐藏的线性冲突。置 $W=\operatorname{span}N_a$。若 $a\in W$，可选至多 $d$ 个线性独立邻点，使 $a=\sum_j c_jb_j$。取 $k=0$、$g_0=u$、$g_j=-c_ju$，得到零张量等式，但右侧读数为 $-\sum_jc_j=-u(a)=-1$，违背(190.2)。所以

$$
a\notin W,\qquad S=\mathbb Ra\oplus W,
\qquad \delta(a)=0,\quad\delta|_W=I
\tag{190.4}
$$

是良定义的证明内构造。取 $N_a$ 的一组基 $b_1,\ldots,b_m$，此时 $m\le d-1$。前端保留 $r\le d$ 是为了此前排除 $W=V$ 时也不漏检。

关键是 $S$ 不需先有零面或 $\mathsf Z_2$ 就已包含原内点。令 $e=a+\sum_{j=1}^m b_j\in C$。若 $e$ 不在 $\operatorname{int}C$，支撑分离给非零 $h\in C^*$、$h(e)=0$。各正加项都被它消去，故 $h(a)=0$ 且 $h$ 消去整个 $W$。因 $C$ 生成，$M=\max_Kh>0$。在真实最大面取一个原纯最大点 $b$；原全菜单中的 $u-h/M$ 确认 $a$ 并排除 $b$，所以 $b\in N_a$。这与 $h|_W=0$、$h(b)=M$ 矛盾。因此

$$
e\in S\cap\operatorname{int}C.
\tag{190.5}
$$

这里的纯最大点存在由有限维紧凸生成给出，不要求原纯集闭。

余下把成熟正锥对偶工具用于这个已内生的 $S$。记 $\mathcal P=\{Q\in\operatorname{End}V:Q(C)\subseteq C\}$、$\rho(Q)=Q|_S$。其限制像 $\rho(\mathcal P)$ 是闭凸锥。具体地，若 $\rho(Q_n)\to R$，则 $Q_ne$ 有界。对每个固定基向量 $v$，内点性给 $-te\le_Cv\le_Cte$，正性给 $-tQ_ne\le_CQ_nv\le_CtQ_ne$。由基范数定义，$\|Q_nv\|_K\le t\,u(Q_ne)$，所以 $Q_n$ 算子有界。收敛子列的极限仍正且限制为 $R$。此处没有用一般线性锥像必闭的错误断言。

正算子锥的成熟对偶公式是精确有限生成

$$
\mathcal P^*
 =\operatorname{cone}\{x\otimes h:x\in C,\ h\in C^*\}.
\tag{190.6}
$$

按C183所引Gritzmann–Klee–Tam引理2.1复用其秩一生成；这里说明不遗漏闭包的理由。选 $\eta\in\operatorname{int}C^*$，把非零 $x,h$ 分别归一到紧底 $\eta(x)=1$、$h(e)=1$。归一秩一张量的凸包紧，线性泛函 $L(x\otimes h)=\eta(x)h(e)$ 在该凸包恒为一，故其锥闭。与每个正算子配对非负的双锥关系遂给(190.6)。

若 $\delta$ 无正延拓，闭锥分离给 $\ell\in\operatorname{Hom}(S,V)^*$，在 $\rho(\mathcal P)$ 上非负且 $\ell(\delta)<0$。限制映射的对偶是在输入因子上的包含，因而

$$
Z=\rho^*\ell\in\mathcal P^*\cap(S\otimes V^*),\qquad
\langle Z,\delta\rangle<0.
\tag{190.7}
$$

先按(190.6)取有限秩一正分解，再逐个正输入作原纯点的有限分解，逐个非零正泛函按 $\max_Kh$ 归一成原效应。于是 $Z$ 已有有限个原纯点—效应正配对的精确表示。最后在 $d^2$ 维张量空间对这批有限生成元用锥Carathéodory，删去冗余项，得到

$$
Z=\sum_{i=1}^k t_ip_i\otimes f_i,\qquad k\le d^2.
\tag{190.8}
$$

不要求原纯点集紧，不取纯点的极限，也不把近似证书冒充精确等式。另一方面，沿(190.4)的原基展开同一个总张量，有

$$
Z=a\otimes g_0+\sum_{j=1}^m b_j\otimes g_j,\qquad
\langle Z,\delta\rangle=\sum_{j=1}^m g_j(b_j)<0.
\tag{190.9}
$$

(190.8)—(190.9)正是(190.2)禁止的有限关系，矛盾。所以 $\delta$ 有正延拓，它对全部 $N_a$ 恒等，给(190.3)。总张量属于 $S\otimes V^*$ 即可；没有把(190.8)的每个 $p_i$ 偷限在 $S$ 内。$\square$

### 190.3 零面与被删点已经撑住内点，原删除本身就是投影

**定理 190.3（直接收回，不必先平均）。** 若整个原域满足全标签(190.2)，则每张满足(190.3)的原 $Q_a$ 已经满足

$$
Q_a^2=Q_a,\qquad Q_a(C)=\operatorname{cone}D_a,\qquad
D_a=\operatorname{conv}N_a=K\cap\ker(u-uQ_a).
\tag{190.10}
$$

这里没有输入 L2，也不要求先换成另一张平均映射。

证明。由190.2取得全标签188.1，直接消费187.2与178.2，得到188.2—188.3的预算、共同确认和原零暴露面 $D_a$，且 $Q_a$ 固定整个 $\operatorname{cone}D_a$。$d>1$ 时邻点非空，复用189.2证明开头的原边界支撑论证。

任取非零 $z\in\operatorname{ri}(\operatorname{cone}D_a)$。有

$$
a+z\in\operatorname{int}C.
\tag{190.11}
$$

否则取非零 $h\ge0$ 消去 $a+z$，便同时消去 $a,z$。相对内点性使它消去整个 $\operatorname{cone}D_a$；而在 $h$ 的真实最大面取原纯点 $b$，$u-h/\max_Kh$ 又使 $b\in N_a\subset D_a$，矛盾。

对任何 $x\in C$，内点性给某个 $t>0$ 使 $x\le_Ct(a+z)$。同一原 $Q_a$ 的正性与固定性给

$$
0\le_CQ_ax\le_Ctz.
\tag{190.12}
$$

因 $\operatorname{cone}D_a$ 是原实际面锥，面遗传性迫 $Q_ax\in\operatorname{cone}D_a$。它已经固定该锥，故正像恰为该锥；$C$ 生成 $V$ 又给完整幂等性。本证明加强188.3对原给定映射的结论，188.3的平均构造仍正确。188.4的局部菜单延拓与有限面下降现在可以直接用这张原投影，188.5的球内尺延拓随后供应AD。投影是数学结构，不据此认定实际设备可任意接续。$\square$

### 190.4 一个完整候选与原量子公理的条件字典

**定义 190.4（三复制有限配对候选）。** 完整保留188.6的强实全有限背景：原 $V^{\otimes_{\mathbb R}N}$、各层闭尖生成锥与严格正乘法单位、每个有限 min/max 分块、全部原准备与完整效应、正置换及逆、规范重括号、标量层和 $\dim V>1$。只在整个 $K_3$ 要求实际L2及全标签(190.2)，记为 $\mathsf Q_{\rm pair}$。实际L2的含义仍是每两个不同原纯点生成的整个最小实际面为实心仿射三球。配对计数中的 $d$ 在此取 $\dim(V^{\otimes_{\mathbb R}3})$，不是单份维数。

**定理 190.5（同一全有限复理论）。** 在190.4的精确背景下，$\mathsf Q_{\rm pair}$ 当且仅当存在同一个 $n\ge2$ 和同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使全部有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{190.13}
$$

证明。只在整个原三复制域用190.2，得到188.6要求的全部原正删除。190.3说明其零面几何已经是指定补方向的正收回；188.4逐面下降，188.5把实际二点球内效应沿收回延拓，取得同域NC和AD。直接消费188.7所核对的XIII162.10、162.16与178.6共同坐标接口，给(190.13)。反向用标准正交压缩满足190.3，再由190.2的必要性支付全部有限配对关系；标准复锥满足实际L2与原强全有限背景。$\square$

这里得到的简洁几何是：原二元可区分关系指定零邻点；它们的有限正配对不允许删去 $a$ 项后产生负数，遂迫一张指定补方向的正投影。加入原实际球形后，几何成为复射影纯点、复子空间支持面及正交压缩。三个两两原正交纯点在同一个复三维支持内，其归一面仿射维数八，三颗二点球都在这同一实际面内；这是真正的三点共同有限提升。(190.8)的 $d^2$ 只是证书项数界，不是三点定理。

现有量子公理的对应沿187.5和188.7，保留各项条件：

| 原量子结构 | 本候选中的推导与必要范围 |
| --- | --- |
| 密度算子、纯射线、锐效应 | 原完整锥/底/效应经同一 $\theta$ 成为PSD、迹一态、$[0,I]$ 与秩一纯射线；支持面给投影 |
| Born规则与数学POVM | 原配对在对偶坐标为 $\operatorname{Tr}(\rho E)$；有限效应族和为 $u$ 才对应和为 $I$ 的POVM |
| 有限复合、纠缠、偏迹 | (190.13)固定全部层级的同一 $\theta^{\otimes N}$；乘法单位及边缘给标准偏迹 |
| CP-TNI映射与仪器 | 给定线性变换须对全部有限旁观者保正，并逐输入质量不增；分支总和质量不增给数学次仪器，保质量给完整数学仪器 |
| 锐中性更新 | 原删除投影成为 $X\mapsto(I-p)X(I-p)$；把指定投影当作实际锐事件更新仍需相应操作合同 |
| 酉时间演化、Schrödinger方程 | 连续、保锥、保单位的可逆实一参数群及其物理时间解释仍须输入，钟、能量与 $\hbar$ 标定继续独立 |

全效应菜单不自动让每个数学仪器成为实际设备；有限维重建也不自动供应无限维normal实现。dev的NormalMomentFamily与NormalL1Realization仍按它们自己的连续矩族、紧性及正常延拓合同使用，未作此处有限分类的免费推论。

### 190.5 不遵守有限关系，哪里会出现负读数

**命题 190.6（实际球与单标签零封闭仍能漏过的原配对冲突）。** 178.4及XII159的平衡商族保留实际L2、AD和完整原菜单；其中存在一个满足单标签 $\mathsf Z_2$ 的纯点，却在(190.2)中出现 $k=1$、负读数 $-7/9$ 的精确原证书。该族不满足全标签 $\mathsf Z_2$，不作为强全有限反模型。

证明。复用该族 $H=\operatorname{diag}(I_m,-I_m)$、$m\ge3$，$\pi:\operatorname{Herm}_{2m}(\mathbb C)\to\operatorname{Herm}_{2m}(\mathbb C)/\mathbb RH$、$C=\pi(\operatorname{PSD}_{2m})$、$u=\operatorname{Tr}$。原效应为 $0\le E\le I$、$\operatorname{Tr}(EH)=0$ 的配对。用正负正交基 $e_i,f_i$，置

$$
\begin{gathered}
v=(e_1+f_1)/\sqrt2,\qquad z=Hv=(e_1-f_1)/\sqrt2,\\
a=\pi(P_v),\qquad r=(2v+z)/\sqrt5,\qquad p_s=\pi(P_s),\\
H_R=\sum_{i=2}^m(P_{e_i}-P_{f_i}),\qquad Y=P_z-2H_R.
\end{gathered}
\tag{190.14}
$$

$P_v$ 是原效应，确认 $a$ 且排除全部 $p_s$、$s\perp v$。反向若原效应在 $v$ 读一，$0\le E\le I$ 使 $Ev=v$，其零纯点必在 $v^\perp$。故 $N_a=\{p_s:s\perp v\}$，零混态也恰为这些原纯点的凸包；按178.2，单标签 $\mathsf Z_2$ 成立。

原商中的真实准备回路为

$$
5p_r+2\sum_{i=2}^m p_{e_i}
 =4a+p_z+2\sum_{i=2}^m p_{f_i}.
\tag{190.15}
$$

它来自 $5P_r=4P_v+Y+2H$。取 $w=v-z/2+e_2$，有 $w^*Hw=0$、$\|w\|^2=9/4$；因此 $E=4ww^*/9$ 满足 $0\le E\le I$、$\operatorname{Tr}(EH)=0$，给原效应 $f(\pi X)=\operatorname{Tr}(EX)$。将(190.15)与这同一 $f$ 配对成张量等式，得到

$$
5p_r\otimes f
 =a\otimes4f+p_z\otimes f
 +2\sum_{i=2}^m p_{f_i}\otimes f
 -2\sum_{i=2}^m p_{e_i}\otimes f.
\tag{190.16}
$$

全部 $a$ 以外的右侧准备都在 $N_a$，且 $r_{\rm count}=2m-1\le d=4m^2-1$。去掉 $a$ 项后，右侧总读数为

$$
f(p_z)+2\sum_{i=2}^m f(p_{f_i})-2\sum_{i=2}^m f(p_{e_i})
 =\frac19-\frac89=-\frac79<0.
\tag{190.17}
$$

若存在正删除，左侧必为非负的 $5f(Q_ap_r)$，矛盾。只在 $S=\mathbb Ra+\operatorname{span}N_a$ 定义的线性删除确会要求 $\delta(p_r)=\pi Y/5$，其这一次归一测试读数为 $-7/45$；它与(190.17)的五倍读数不同。此例把遗漏定位为原准备与原测试的联合约束失败，没有仅凭球内几何或一个标签的零凸性就许诺全域正延拓。$\square$

**命题 190.7（简化的准确含义、归属与完整白话）。** 本章的前端只用原准备、原测试及它们的有限线性关系，外部正删除存在量词被移入结论；190.2在不预给 $\mathsf Z_2$、$\delta$ 或 $a\notin\operatorname{span}N_a$ 时，先由空正和与原最大测试自行建立相应接口。190.3又以原零面和被删点共同撑住内点，直接识别每张原删除为正投影，省去平均步骤。这是原有关系上的repo-derived接合。

正算子对偶、有限维分离、紧凸生成及Carathéodory均为成熟工具；(190.6)归[Q190GKT]引理2.1及C183已有归属，不申领这些定理、重建分类或文献优先权。该对偶等价不是独立经验假设数减少的证明，也未证明(190.2)由裸全标签 $\mathsf Z_2$ 加实际L2自动推出。简化在原始对象表和直接投影几何，有限张量检验仍是一项明确的联合正性要求，不能用“内生”掩去。球形与强全有限背景也继续明写；实际量子操作和时间演化仍按190.5后的条件字典。

白话上，保留系统本来的全部准备、测试和有限复合，只在整个三份系统检查两件事：任意两个不同纯准备撑起一颗实际三球；挑一个纯点，把若干“准备配测试”的正项写成它自己那一项加上可与它确定区分的准备项，去掉它自己后，剩下的总配对不能变成负数。这里先不放进任何删除机器。若被删点已经藏在那些可区分准备的线性关系里，一个空正和就会算出负一，条件先排除这种自相矛盾。原全测试菜单又保证被删点连同这些邻点能撑住一个内点；因此，假如找不到统一的正删除，有限维分离一定能抓到至多 $d^2$ 个原正配对，给出违反规则的精确负证书。没有这种证书，删除便作为结论出现。它固定的零面加上被删点已经撑住内点，正性不容任何输出逃离这张零面，所以这张删除本来就是投影，不必反复平均。沿实际面下降并把球内的尺放回原空间后，已有重建把二点球和三点共同支持接成同一套复矩阵、Born配对及全部有限张量层级。反过来看，平衡商里一条真实准备回路通过原测试会留下负九分之七的总读数，正删除绝不能实现它；单标签的零面和球形正是漏掉了这一联合关系。这个候选把操作的存在改写为原关系不能互相抵触，尚未把这条一致性要求从更少的独立前提赚得。$\square$

[Q190GKT]: https://doi.org/10.1016/0024-3795(93)00364-6 "Gritzmann–Klee–Tam, Cross-positive matrices revisited, Linear Algebra and its Applications 223–224 (1995), 285–305；引理2.1的正算子对偶秩一生成。"

## 追加锚（本行以下为增补区）

## 191. 固定目标的二元互反产生欧氏轴，两条轴支付实际三球

### 191.1 只交换两个比较端点

**定义 191.1（固定目标二元互反）。** 在177.1的有限维中心对称严格凸紧体中，保留本面自身的完整仿射效应菜单。中心平移为零，记其内在单位球为 $B$、范数为 $N$、单位边界为 $S$。对 $p\in S$，定义

$$
\mathsf R_F(p):\quad T_p^F(q)=T_q^F(p)\quad(q\in S).
\tag{191.1}
$$

这里 $S=\operatorname{ext}B$，量词遍历整个本面纯边界；比较是同一状态—效应配对的两个端点互换，没有输入任何两次测量的时间次序、仪器或接续更新。没有另行要求 $\mathsf R_F(-p)$、光滑性、三标签中心配方或独立的对径穷尽关系。

**定理 191.2（一个互反目标精确是一条欧氏直和轴）。** 在191.1的域中，$\mathsf R_F(p)$ 当且仅当存在实线性 $b_p$，满足

$$
\begin{gathered}
b_p(p)=1,\\
N(x)^2=b_p(x)^2+N\bigl(x-b_p(x)p\bigr)^2
\quad(x\in W).
\end{gathered}
\tag{191.2}
$$

因此它与177.2的 $\mathsf\Delta_F(p)$ 等价。任一条件成立时，$J(p)=\{b_p\}$，且

$$
\begin{gathered}
j(p)=b_p(q)\quad(q\in S,\ j\in J(q)),\\
T_p^F(q)=T_q^F(p)=\frac{1+b_p(q)}2,\qquad
T_{-p}^F(q)=T_q^F(-p)=\frac{1-b_p(q)}2.
\end{gathered}
\tag{191.3}
$$

证明。直接复用177.1及(177.4)的完整确认公式，置

$$
m_p(x)=\min_{j\in J(p)}j(x),\qquad
M_p(x)=\max_{j\in J(p)}j(x).
\tag{191.4}
$$

由(191.1)先得 $m_p(q)=m_q(p)$。再将同一输入量词用于 $-q$，使用 $J(-q)=-J(q)$，得到

$$
m_p(q)=m_q(p),\qquad M_p(q)=M_q(p)\quad(q\in S).
\tag{191.5}
$$

有限维有限凸函数的稠密可微定理给出范数的光滑非零方向稠密；具体复用[Q191R]例9.14的局部Lipschitz性及定理9.60的稠密可微结论。径向归一后，$J(q)$ 为单点的 $q$ 在 $S$ 中稠密。这里只调用这一成熟凸分析工具，不把稠密可微当成新增公理。在这些 $q$ 上，(191.5)迫 $m_p(q)=M_p(q)$。任取 $j_1,j_2\in J(p)$，它们在这个稠密集上的读数相同；线性连续性与齐次性给它们在整个 $W$ 相同。因此

$$
J(p)=\{b_p\},\qquad b_p(p)=1,\qquad N^*(b_p)=1.
\tag{191.6}
$$

再代回(191.5)，任意 $q$ 的全部 $j\in J(q)$ 在 $p$ 上都取 $b_p(q)$，并非只为每个 $q$ 选择一个合适法向。

令 $H(x)=N(x)^2/2$，使用177.3证明已采用的次梯度公式(177.5)：$x\ne0$ 时，$\partial H(x)=N(x)J(x/N(x))$，而 $\partial H(0)=\{0\}$。故

$$
s(p)=b_p(x)\quad(x\in W,\ s\in\partial H(x)).
\tag{191.7}
$$

有限凸函数的左右方向导数是相应次梯度读数的最小值、最大值；(191.7)使二者相等。固定 $x$，一元函数 $h(t)=H(x+tp)$ 于是处处可微，且

$$
h'(t)=b_p(x)+t,\qquad
H(x+tp)=H(x)+tb_p(x)+\frac{t^2}{2}.
\tag{191.8}
$$

取 $t=-b_p(x)$ 即得(191.2)。反向直接使用177.3证明中对该分解所得的全部法向读数关系，以及177.4证明开头对单条轴所得的 $J(p)=\{b_p\}$。代入完整确认公式即得(191.3)及(191.1)。与 $\mathsf\Delta_F(p)$ 的等价由177.3供应。没有重证两轴闭合，也没有把仅在多面体极点上的关系替代整个边界量词。$\square$

### 191.2 两个独立目标的局部闭合与反事实

**定理 191.3（实际二元面上的两个互反目标）。** 设有限维紧凸基 $K$ 的每个不同原纯对均生成中心对称、仿射维数三的实际最小面。在每一个这样的面 $F$ 中，下列条件等价：

1. $F$ 仿射同构于整个闭 Euclidean 三球。
2. 存在 $a,b\in\operatorname{ext}K\cap F$，满足 $a\ne b$、$T_a^F(b)>0$、$\mathsf R_F(a)$ 及 $\mathsf R_F(b)$。

证明。177.5a先给每个实际 $F$ 紧且严格凸，其整个相对边界正是原纯点 $\operatorname{ext}K\cap F$；且 $a\ne b$ 与 $T_a^F(b)>0$ 恰好排除相同及对径方向。191.2给两条中心方向独立的欧氏直和轴，字面支付177.4的两个 $\mathsf\Delta$ 前件，直接得到第一项。反向球内的完整确认值为 $(1+G(p,q))/2$，任选两个独立方向即可。$\square$

**命题 191.4（一条轴或单侧比较均不足）。** 在中心对称严格凸三维紧体类中，一个互反目标不足以迫使椭球；即使有两个独立目标，把(191.1)弱化为 $T_p^F(q)\le T_q^F(p)$ 也不足。

证明。第一项直接使用177.5的 $\mathbb R\oplus_2\ell_4^2$ 范数球及191.2；该例的一条欧氏轴给一个互反目标，横向平面仍非欧氏。

第二项复用188.8的同一非椭球范数体 $N(x,y,z)=\sqrt{x^2+y^2+z^2}+|x|$，不另申领该范数实例。取两个单位目标 $p_2=e_2,p_3=e_3$。对单位 $q=(x,y,z)$，令 $r=\|q\|_2=1-|x|>0$，$q_2=y,q_3=z$。在目标处

$$
J(p_i)=\{p_i^*+\lambda e_1^*:|\lambda|\le1\},\qquad i=2,3.
\tag{191.9}
$$

当 $x\ne0$，$J(q)$ 是梯度 $q/r+\operatorname{sgn}(x)e_1^*$ 的单点集，所以

$$
\begin{aligned}
T_{p_i}^F(q)&=\frac{1+q_i-|x|}{2},&
T_q^F(p_i)&=\frac{1+q_i/r}{2},\\
T_q^F(p_i)-T_{p_i}^F(q)
&=\frac{|x|}{2}\left(1+\frac{q_i}{r}\right)\ge0.
\end{aligned}
\tag{191.10}
$$

当 $x=0$，$r=1$，$J(q)=\{q+\lambda e_1^*:|\lambda|\le1\}$，两读数相等。故两个独立目标均满足全部单侧比较；在 $q=(1/2,0,0)$ 上，两者读数分别为 $1/4$ 与 $1/2$，互反严格失败。188.8已给该体严格凸且非椭球。这些反事实只定位局部范数体判据，不冒充完整强实复合背景的反模型。$\square$

### 191.3 接入射线删除的完整有限理论

**定义 191.5（三复制二元互反与射线删除候选）。** 完整采用189.4的原全有限强实背景：有限维实 $V$、$\dim V>1$、$W_N=V^{\otimes_{\mathbb R}N}$、各层闭尖生成 $C_N$、严格正乘法单位 $u_N=u^{\otimes N}$、每个有限分块的原 min/max 张量包含、原正置换及逆、规范重括号与标量层。归一基 $K_N=C_N\cap\{u_N=1\}$、纯点 $P_N=\operatorname{ext}K_N$ 及完整效应 $[0,u_N]$ 均不换域。只在整个 $K_3$ 要求：

1. 每个不同 $s,t\in P_3$ 的实际最小面 $F(s,t)$ 中心对称、仿射维数三；每张这样的 $F$ 有191.3第二项的两个独立互反目标，其比较使用本面完整内禀仿射菜单。
2. 对每个 $a\in P_3$，存在同一个原实线性 $Q_a:W_3\to W_3$，满足

$$
\begin{gathered}
Q_a(C_3)\subseteq C_3,\qquad Q_aa=0,\\
a\mathrel{\#}b\quad\Longrightarrow\quad
Q_ab\in\mathbb R_{>0}b\quad(b\in P_3),\\
a\mathrel{\#}b\quad\Longleftrightarrow\quad
\exists e\in[0,u_3]:\ e(a)=1,\ e(b)=0.
\end{gathered}
\tag{191.11}
$$

记合取为 $\mathsf Q_{\rm binary\,ray}$。局部比较不预设它的效应能延拓为原全域效应；删除中的 $\#$ 始终是整个原菜单的关系。映射的存在、正线性、同一映射对全部可区分原纯准备严格保持射线仍是前件。未预给复数、内积、矩阵秩、指定纠缠准备、球面度量、预算或每点存活长度。

**定理 191.6（同原坐标的全有限复量子重建）。** 在191.5的准确背景下，$\mathsf Q_{\rm binary\,ray}$ 当且仅当存在同一个整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\quad(N\ge0).
\tag{191.12}
$$

证明。第一项的全原纯对量词先支付177.5a，再由191.2—191.3得到同一 $K_3$ 上的全部实际 L2。第二项字面是189.1；因此此时才达到189.4的完整候选，直接调用189.5得到(191.12)。其内部供应顺序保持为：189.2使各标签的存活比例一致，189.3选规范代表；188.4给原实际面的正质量不增收回与局部全菜单延拓；188.5才得原对径关系 AD，并消费同域 L2+NC+AD 的整锥分类；188.7再通过既有强实接口传播同一 $\theta$ 到全部有限层。没有附加177.6路线的 TC 或把不同版本的供应混用，也没有在菜单延拓之前用局部 $\#$ 偷换原关系。

反向在完整复量子层级中，两个不同纯点的实际最小面是其复二维支持上的完整三球，完整确认互反给全部目标的(191.1)。取标准压缩的任意正倍数满足(191.11)。两方向都保留原 $V,C_N,u_N$ 及所有张量分块。$\square$

**命题 191.7（几何、QM字典及独立物理前件）。** 在191.6的全部前件下，纯点、面、态与测试在同一表示中的对应为

$$
\begin{gathered}
K_N\leftrightarrow\{\rho\succeq0:\operatorname{Tr}\rho=1\},\qquad
P_N\leftrightarrow\{|\psi\rangle\langle\psi|:\|\psi\|=1\},\\
[0,u_N]\leftrightarrow\{E:0\preceq E\preceq I\},\qquad
e(x)=\operatorname{Tr}(E\rho),\\
T_p(q)=|\langle\psi_p,\psi_q\rangle|^2.
\end{gathered}
\tag{191.13}
$$

证明。直接消费189.5、188.7及187.5的原QM字典，并以迹配对实现原对偶。最小确认值的末式由秩一确认者和PSD支持公式给出。局部191.3的球是复射影纯点空间中一条复射影直线的混态凸包；三个两两正交纯点位于同一个复三维支持，其归一面仿射维数八，三个二点球是该共同面内的面。

每张给定 $Q_a$ 仍仅由189.3取得 $Q_a=\lambda_a\widehat Q_a$、$\lambda_a>0$，规范代表为正交压缩；不把原映射的任意正标度认作设备概率的自由更改。所有有限旁观者下保正、全输入质量预算和分支族总预算分别供应CP、TNI和数学仪器；实际事件饱和、指定锐中性测后更新及连续可逆保单位时间群仍分别需要自己的前件。时钟、能量与 $\hbar$ 的物理标定没有由(191.1)推出。交换比较端点也没有推出任意测量的接续可交换。$\square$

**命题 191.8（归属与完整白话候选）。** 191.2的承重接合是：同一目标对 $q,-q$ 的最小确认互反同时给出支持读数的最小值与最大值互反，稠密光滑方向先迫目标法向唯一，再迫所有方向的全部法向在该目标上读数一致，最后通过单方向次梯度积分取得勾股分解。稠密可微、次梯度公式与一元积分是成熟凸分析工具；轴的几何类型是既有 $L^2$-summand vector。[Q191N]第7节公式(5)及定理7.1处理光滑严格凸范数模型的全原子互反与pre-Hilbert几何；[Q191A]定理3.2已在光滑实Banach空间中给出固定目标的对偶映射读数对称与 $L^2$-summand vector的等价刻画，正是191.2的光滑特例。这里新增的是有限维、无需预设光滑性的完整最小确认菜单桥梁及其接合；没有用两文替代该非光滑证明，也不主张文献优先权或穷尽检索。两轴闭合归177.4，实际面正则性归177.5a，射线归一、全局面和分类传播归189与188。

证明。191.2给出所述接合，191.3及191.6给出其准确消费者。因而可把完整候选说成：保留全部原准备、全部测试和有限复合，只在整个三份系统检查；每两个不同纯准备撑起一张实际三维中心对称小面；在每张小面中，能找到两个不相同、也不互为对径的纯目标，每个目标和这张面上任何纯点交换比较两端，最低确认读数都完全相同；另外，每个纯点都有同一个正线性删除方向，删掉自己，让所有能与自己确定区分的纯准备仍沿原射线严格存活。一个互反目标把一条轴的平方长度锁成勾股形式，三维内两个独立目标把整张小面锁成三球；删除关系再把各张小面的测试接回同一原系统，已有重建给同一套复矩阵和全部有限张量层级。球的度量和各点存活长度由关系推出，中心对称、三维、完整复合背景与共同正映射存在仍明确保留。

这把177的三标签中心配方改成只含两个比较端点的等价判据，也把189直接输入的实际 L2换成由比较关系推出的结论；它没有减少每个固定目标必须遍历整个纯边界的量词，不据较短表述宣称独立经验公理数严格下降。$\square$

[Q191N]: https://arxiv.org/abs/2208.07135v1 "Niestegge, Non-symmetric transition probability，第7节公式(5)及定理7.1。"
[Q191A]: https://doi.org/10.1090/S0002-9939-06-08243-8 "Aizpuru–García-Pacheco, L²-summand vectors in Banach spaces, Proc. Amer. Math. Soc. 134, 2109–2115，定理3.2。"
[Q191R]: https://sites.math.washington.edu/~rtr/papers/rtr169-VarAnalysis-RockWets.pdf "Rockafellar–Wets, Variational Analysis，例9.14及定理9.60。"

## 追加锚（本行以下为增补区）

## 192. 一个互反目标产生中心，两目标关系接入有限正配对

### 192.1 先不给中心的完整确认关系

**定义 192.1（无中心的局部域）。** 设 $K$ 是有限维实仿射空间内仿射维数 $d\ge2$ 的严格凸紧体，所有内部、边界均相对于 $\operatorname{aff}K$。保留全部纯点 $S=\operatorname{ext}K=\partial K$ 和全部内禀仿射效应

$$
\begin{aligned}
\mathcal E(K)&=\{e:K\to[0,1]:e\text{ 仿射}\},\\
\mathcal E_p&=\{e\in\mathcal E(K):e(p)=1\},\qquad
T_p(x)=\min_{e\in\mathcal E_p}e(x),\\
\mathsf R_K(p)&:\quad T_p(q)=T_q(p)\quad(q\in S).
\end{aligned}
\tag{192.1}
$$

这里未给中心、范数、内积或光滑性。两个目标的关系只写 $p\ne s$ 和 $T_p(s)>0$；后者等价于不存在完整菜单中的 $e$ 同时满足 $e(p)=1,e(s)=0$，取补效应可见这种不可确定区分是对称的。

**引理 192.2（支持确认与近点缺口）。** 在192.1的域中，完整效应及每个确认菜单紧，所有 $T_p$ 连续且有共同 Lipschitz 界。暂选辅助 Euclidean 坐标，记

$$
h(n)=\max_{x\in K}n(x),\quad w(n)=h(n)+h(-n),\quad
\mathcal N(q)=\{n:\|n\|=1,\ n(q)=h(n)\}.
\tag{192.2}
$$

则

$$
T_q(x)=\min_{n\in\mathcal N(q)}
\frac{n(x)+h(-n)}{w(n)},\qquad
1-T_q(p)=o(\|q-p\|)\quad(q\in\partial K,\ q\to p).
\tag{192.3}
$$

证明。$K$ 包含某个辅助球 $B(x_0,\rho)$。若 $e=b+\ell\in\mathcal E(K)$，比较球上对径点得 $\|\ell\|\le1/(2\rho)$；$e(x_0)\in[0,1]$ 又界住常数项。效应菜单在有限维仿射函数空间中闭有界，故紧；确认菜单闭、非空，最小值取得，公共斜率界给连续性。

非恒定确认 $e(q)=1$ 的最小值若为 $m$，则 $(e-m)/(1-m)$ 仍确认 $q$ 且逐点不大于 $e$。归一后的确认正是(192.3)的支持效应；常数确认 $1$ 不降低最小值。每个单位方向满足 $w(n)\ge2\rho$，故只需证明

$$
\sup_{n\in\mathcal N(q)}n(q-p)=o(\|q-p\|).
\tag{192.4}
$$

否则取 $q_j\to p$、$n_j\in\mathcal N(q_j)$ 及 $\varepsilon>0$，使 $n_j(q_j-p)\ge\varepsilon\|q_j-p\|$。抽子列使 $n_j\to n$。支持函数连续性给 $n(p)=h(n)$，所以 $n(q_j-p)\le0$，而

$$
0\le\frac{n_j(q_j-p)}{\|q_j-p\|}
\le\|n_j-n\|\longrightarrow0,
\tag{192.5}
$$

矛盾。小量结论本身不要求严格凸或光滑。$\square$

### 192.2 一个互反目标的切平面与中心

**定理 192.3（一个固定目标赚得中心）。** 在192.1的域中，若 $\mathsf R_K(p)$，则 $p$ 有唯一支持超平面，$T_p$ 是同一归一仿射支持效应 $e_p$。令 $a$ 为 $e_p$ 的唯一最小点，则 $c=(p+a)/2$ 是 $K$ 的对称中心。中心化后的 $p-c$ 因而满足191.2的欧氏轴分解。

证明。先任选一个在 $p$ 取一、最小值零的非恒定仿射支持效应 $e$。对趋向 $p$ 的边界点 $q$，互反与192.2给

$$
0\le1-e(q)\le1-T_p(q)=1-T_q(p)=o(\|q-p\|).
\tag{192.6}
$$

取从 $p$ 严格指向一个内接球的方向为竖直方向。$p$ 附近的下边界可写为 $q=(y,f(y))$、$p=(0,0)$，其中 $f$ 在零点邻域有限、凸且局部 Lipschitz。具体地，$p$ 与内接球的凸包给出向内圆锥，保证投影定义域包含零点邻域；内方向与支持超平面横截，故所选支持面写为 $t=b(y)$，且

$$
e(y,t)=1-\gamma(t-b(y)),\qquad\gamma>0.
\tag{192.7}
$$

由局部 Lipschitz 性，$\|(y,f(y))\|=O(\|y\|)$。将图像代入(192.6)得 $f(y)-b(y)=o(\|y\|)$，所以 $f$ 在零点可微且导数为 $b$，支持超平面唯一。任何确认效应由同一支持方向给出，恰为 $m+(1-m)e_p$、$0\le m\le1$；故 $T_p=e_p$ 于整个 $K$。唯一的是统一最小确认，不是整个确认菜单。

严格凸性使 $e_p$ 的最小点 $a$ 唯一，且开弦 $(p,a)$ 位于内部。现在才取 $c=(p+a)/2$ 为原点，作仿射坐标变换，使

$$
p=(0,1),\quad a=(0,-1),\quad e_p(y,z)=(1+z)/2.
\tag{192.8}
$$

这只是坐标选择，尚未断言 $c$ 为中心。严格凸性使每个非零法向 $n$ 的支持点 $q(n)$ 唯一；支持函数因此在 $n\ne0$ 可微，导数为 $q(n)$。可直接核对：支持点的紧性与唯一性给 $q(n_j)\to q(n)$；两个极值不等式夹住 $h(n+v)-h(n)-v(q(n))$ 为 $o(\|v\|)$。这里没有假设边界点的法向唯一。

归一支持效应 $e_n(x)=(n(x)+h(-n))/w(n)$ 确认 $q(n)$，而 $1-e_n$ 确认 $q(-n)$。分别使用互反，有

$$
e_n(p)\ge T_{q(n)}(p)=e_p(q(n)),\qquad
1-e_n(p)\ge T_{q(-n)}(p)=e_p(q(-n)).
\tag{192.9}
$$

相加得 $z(q(n))+z(q(-n))\le0$。固定非零横向法向 $u$，定义 $\beta_u(t)=h(u,t)-h(-u,-t)$，于是

$$
\beta_u'(t)=z(q(u,t))+z(q(-u,-t))\le0.
\tag{192.10}
$$

另一方面，$p,a$ 是 $z$ 的唯一最大点与最小点，故

$$
h(u,t)-|t|\longrightarrow0\quad(t\to\pm\infty).
\tag{192.11}
$$

例如 $t\to+\infty$，支持点 $q_t=(y_t,z_t)$ 趋向 $p$：比较 $q_t$ 与 $p$ 的极值读数并除以 $t$，任意聚点必须满足 $z=1$，严格凸性使其只能为 $p$。再有 $0\le h(u,t)-t\le u(y_t)\to0$。负无穷方向对 $a$ 同理。因此 $\beta_u$ 在正负无穷两端都趋零；它单调不增，只能恒零。$u=0$ 时直接有 $h(0,t)=|t|$。于是所有法向满足 $h(n)=h(-n)$，支持函数决定紧凸体，给 $K=-K$。

所得中心即 $c$。在这个已赚得的中心域中，$\mathsf R_K(p)$ 字面支付191.1，直接调用191.2取得欧氏直和轴，无须重证其积分分解。辅助 Euclidean 标尺只用于有限维紧性、极限与微分，没有进入候选的原始结构。$\square$

### 192.3 实际三维面不需预送中心

**引理 192.4（原紧域内的实际面正则性）。** 设 $\Omega$ 为有限维紧凸基，且每个不同原纯对的实际最小面均有仿射维数三。那么每个这样的面紧、严格凸，其整个相对边界恰为原纯点与该面的交集；此结论不需中心对称。

证明。对任意非空实际面 $F$，取 $x\in\operatorname{ri}F$。若 $y\in\Omega\cap\operatorname{aff}F$，可取小 $\varepsilon>0$ 使 $z=x+\varepsilon(x-y)\in F$。等式 $x=\varepsilon y/(1+\varepsilon)+z/(1+\varepsilon)$ 和面性质迫 $y\in F$。故 $F=\Omega\cap\operatorname{aff}F$，有限维仿射包闭，$F$ 因而紧。余下复用177.5a证明的严格凸步骤：非平凡边界线段给维数至多二的紧真支撑面 $G$，其两个不同极点也是原纯点，却生成包含于 $G$ 的实际面，与全原纯对三维量词矛盾。实际面极点性质给最后的边界等式。这里只复用不消费中心的证明段。$\square$

**定理 192.5（无中心的两目标三球判据）。** 在192.4的域中，每张实际二元面 $F$ 是仿射三球，当且仅当其中存在两个原纯目标 $p\ne s$，满足 $T_p^F(s)>0$、$\mathsf R_F(p)$、$\mathsf R_F(s)$。所有比较均用本面完整内禀菜单。

证明。192.4先给严格凸紧体域，192.3从一个互反目标给中心。此时复用177.5a证明最后一段的局部支持计算：在已知严格凸的中心体中，$T_p^F(s)=0$ 当且仅当 $s=2c-p$。因而 $p\ne s$ 和 $T_p^F(s)>0$ 排除相同与对径，给两个独立中心方向；191.2及177.4直接给三球，不要求其他实际面先有中心。反向由完整球的确认公式直接成立。三维一个目标不足的局部反例仍为191.4的 $\mathbb R\oplus_2\ell_4^2$；没有把局部反例冒充全有限层级的反模型。$\square$

**命题 192.6（紧性不能从裸互反补回）。** 若不保留原紧凸域，三维、全部原纯对的三维最小面及全纯互反仍允许非中心对称的凸态集。

证明。令 $K=\overline B^3\setminus\{n\}$，其中 $n$ 是 Euclidean 单位球面上一点。删去极点后集合仍凸，纯点为 $S^2\setminus\{n\}$，且仍由它们凸生成。任意不同纯对的中点在内部，实际最小面为整个 $K$。$K$ 在闭球中稠密，完整仿射效应菜单与闭球完全相同，所以剩余全部纯对满足 $T_p(q)=(1+p\cdot q)/2=T_q(p)$。但 $K$ 不闭、不紧；若有中心，其闭包也以它为中心，只能是零，而 $-n\in K,n\notin K$，矛盾。这只检验删除紧性的局部扩域，不改变192.1及原强全有限背景。$\square$

### 192.4 两种原关系组成一个完整有限候选

**定义 192.7（三复制互反—正配对候选）。** 完整保留190.4的强实全有限背景：$\dim V>1$、原 $W_N=V^{\otimes_{\mathbb R}N}$、各层闭尖生成 $C_N$、严格正乘法单位 $u_N=u^{\otimes N}$、全部原准备与完整效应、每个有限 min/max 分块、正置换及逆、规范重括号及标量层。只在整个 $K_3=C_3\cap\{u_3=1\}$ 要求：

1. 每个不同原纯对的实际最小面仿射维数三；每张这样的面满足192.5的两个目标条件。
2. 对每个原纯点 $a$，保留190.1的原全域 $\#$、$N_a$ 及有限正配对关系(190.2)，其中 $d=\dim W_3$、$k\le d^2$、$r\le d$，包括空和、任意有符号 $g_j\in W_3^*$ 和全部原效应。

记此合取为 $\mathsf Q_{\rm reciprocal\,pair}$。局部菜单不预认作原可实施效应；第二项始终使用整个原系统的菜单。前端没有中心、球度量、复数、矩阵秩、删除映射或投影存在量词；强全有限背景、完整菜单、三维和有限配对一致性仍是明列条件。

**定理 192.8（同原域的全有限复量子理论）。** 在192.7的准确背景下，$\mathsf Q_{\rm reciprocal\,pair}$ 当且仅当存在同一个整数 $n\ge2$ 及同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(N\ge0).
\tag{192.12}
$$

证明。第一项依次由192.4、192.3、192.5供应整个原 $K_3$ 的实际 L2；第二项就是同一域的全标签(190.2)。此时才精确达到190.4，直接调用190.5。190.2先从有限关系产生同一个原正删除，190.3识别它为指定零面的投影，188.4才延拓局部全菜单，188.5及既有分类传播支付共同坐标；没有偷用未延拓的局部效应定义原 $\#$，没有额外加入 TC 或 AHS projectivity。反向标准复层级中每张二元实际面为三球，所有目标互反；标准压缩按190.2必要性供应有限关系。$\square$

**命题 192.9（量子字典、几何与简化边界）。** 在192.8的全部前件下，原态、效应与配对依次为迹一PSD、$[0,I]$ 及 $\operatorname{Tr}(\rho E)$；纯点为单位向量射线，最低确认为 $|\langle\psi_p,\psi_q\rangle|^2$。有限原效应分解给数学POVM，全部原张量层及边缘给标准复合与偏迹。实际二点面是 $\mathbb{CP}^1$ 的混态三球；三个两两原正交纯点在同一复三维支持中生成仿射维数八的面，三颗二点球是这同一大面内的实际面。三个标签的共同支持与三份物理复制是不同计数。

证明。静态字典直接消费190.5后的条件表及191.7，几何由同一复矩阵支持对应给出。过程仍逐项保留：所有有限旁观者保正才给CP，全输入质量预算及分支总预算才给TNI/TP和数学仪器；实际事件饱和、指定锐中性更新及连续可逆保单位时间群仍须各自条件，钟、能量和 $\hbar$ 标定也没有由互反推出。

相对于191的局部两目标入口，本章删除了中心对称前件，没有增加互反目标数，也没有加强为全纯对互反；192.3证明中心由剩余局部条件推出。相对于190的完整候选，本章用无中心的二元读数判据支付原实际 L2，有限配对关系继续保留。没有由此申领整套物理公理的独立性或最小性，也没有把交换比较端点变成任意接续测量可交换。$\square$

**命题 192.10（承重归属与完整白话）。** 新接合是192.3：从一个未给中心、未给光滑的严格凸紧体中的固定目标互反，先以近点缺口取得目标光滑，再以两端趋零的支持函数差之单调性取得中心。中心后的轴分解归191.2及其注明的 $L^2$-summand先例，两轴闭合归177.4，有限正配对及完整量子重建归190。支持函数、有限凸函数局部图像与紧性是成熟凸分析工具。[Q192N]定理9.2及其后总结已覆盖光滑严格凸紧体的全纯互反到Hilbert球，定理7.1及[Q191A]定理3.2已覆盖注明的光滑赋范空间路线；本章不把这些已知情形重报为新定理。固定一个目标产生光滑和中心的自含桥梁是这里的repo-derived增量，未据有界文献检索申领优先权。

证明。192.2—192.3给新增接合，192.4—192.8核对其实际消费者。完整候选可以说成：保留原系统的全部准备、全部测试和全部有限复合，只在整个三份系统检查；每两个不同纯准备撑起一张实际三维小面，每张面上能找到两个不同且不能确定区分的纯目标，让每个目标与这张外壳上任何纯点交换确认比较的两端，最低读数都不变；另外，原准备配原测试的有限正和若能写成某纯点自身项加上其可区分邻点项，删去自身项后总配对不能变负。第一位目标先把自身的棱角排掉，再使两张平行支持面的偏差成为两端归零的单调量，物体自己的中心因而出现；第二位目标补足独立勾股方向，三维小面只能成为三球。有限正配对再产生统一删除与零面投影，把小面上的尺接回同一原系统，已有重建给同一套复矩阵、Born配对及全部有限张量层。中心和删除不再预送，三维、全边界两目标量词、完整复合及有限关系一致性仍明确保留。$\square$

[Q192N]: https://arxiv.org/abs/2208.07135v1 "Niestegge, Non-symmetric transition probability，定理9.1、9.2及其后总结；光滑严格凸紧体的全互反范围。"

## 追加锚（本行以下为增补区）

## 193. 商核的谱宽度、共同二元测试与最坏区分损失

**定义 193.1（矩阵商中的原二元读数）。** 取 $D\ge2$、实线性子空间 $L\subset\operatorname{Herm}_D(\mathbb C)$，假定每个 $X\in L$ 均迹零。令 $\pi:\operatorname{Herm}_D\to\operatorname{Herm}_D/L$、$C=\pi(\operatorname{PSD}_D)$、$u\pi=\operatorname{Tr}$。商态为 $p_v=\pi P_v$，其中 $v$ 为单位向量、$P_v=vv^*$。完整商效应恰为

$$
\mathcal E_L=L^\perp\cap[0,I],\qquad
T_v(p_z)=\min_{E\in\mathcal E_L,\ Ev=v}z^*Ez.
\tag{193.1}
$$

常数效应 $I$ 保证最小化域非空。定义原向量正交对的共同区分条件

$$
\mathsf A(L):\quad
\forall v\perp w\quad\exists E\in\mathcal E_L:
Ev=v,\quad Ew=0.
\tag{193.2}
$$

向量均取单位长度。此定义先于商像的纯性；只有另已证明全部 $p_v$ 恰为原纯点，且 $\pi$ 在每个二维复支持态集上限制为到相应原二元实际面的仿射同构、将正交射线送到几何对径时，才将它识别为原实际面对径零关系 AD。对 $0\ne X\in L$，记

$$
a(X)=\lambda_{\max}(X)>0,\quad b(X)=-\lambda_{\min}(X)>0,
\quad t(X)=\operatorname{Tr}X_+=\operatorname{Tr}X_-.
\tag{193.3}
$$

$X_\pm$ 均为正半定谱部。迹零、非零保证上述严格正性。以下所有矩阵、正性和范数属于这个明确给出的矩阵模型，不以它们为任意原系统预设坐标。

**定理 193.2（谱宽度恰好控制同一个合法二元测试）。** 在193.1下，下列三项等价：

1. $\mathsf A(L)$；
2. 每个 $X\in L$ 满足 $\operatorname{Tr}X_+\ge\lambda_{\max}(X)-\lambda_{\min}(X)$；
3. 所有单位向量 $v,z$ 满足 $T_v(p_z)=|v^*z|^2$。

等价的核条件是

$$
\boxed{\quad\|X\|_1\ge2\bigl(\lambda_{\max}(X)-\lambda_{\min}(X)\bigr)
\qquad(X\in L).\quad}
\tag{193.4}
$$

证明。固定 $v\perp w$，置 $Q=I-P_v-P_w$。满足 $0\le E\le I$、$Ev=v$、$Ew=0$ 的矩阵恰为 $E=P_v+B$、$0\le B\le Q$。对迹零 Hermitian $X$，写 $h=v^*Xv$、$a=\lambda_{\max}X$、$b=-\lambda_{\min}X$、$t=\operatorname{Tr}X_+$。成熟的余维一 Cauchy 交错界给任意余维一压缩 $A'$：

$$
\operatorname{Tr}(A')_+\ge\operatorname{Tr}A_+-\max(\lambda_{\max}A,0),\qquad
\operatorname{Tr}(A')_-\ge\operatorname{Tr}A_--\max(-\lambda_{\min}A,0).
\tag{193.5}
$$

先将 $X$ 压到 $v^\perp$，得矩阵 $Y$，其迹为 $-h$，因而 $\operatorname{Tr}Y_- =\operatorname{Tr}Y_++h\ge t-a+h$。再删去 $w$，并用 $\lambda_{\min}Y\ge-b$，得

$$
\operatorname{Tr}(QXQ)_-\ge t-a-b+h,
\qquad
\min_{P_v\le E\le I-P_w}\operatorname{Tr}(EX)
=h-\operatorname{Tr}(QXQ)_-\le a+b-t.
\tag{193.6}
$$

压缩谱部只在 $\operatorname{ran}Q$ 上计；零维压缩允许。取 $v,w$ 分别为 $X$ 的最大、最小谱向量便达到等号，所以

$$
\sup_{v\perp w}\ \min_{P_v\le E\le I-P_w}\operatorname{Tr}(EX)
=a+b-t.
\tag{193.7}
$$

固定一对 $v,w$，将整个紧凸区间 $\{E:P_v\le E\le I-P_w\}$ 送到 $L^*$，映射为 $E\mapsto[X\mapsto\operatorname{Tr}(EX)]$。它的像包含零，当且仅当对每个 $X\in L$，该区间的最小配对不大于零；若零在像外，紧凸严格分离给一个所有配对均严格为正的 $X$。这里 $-X$ 也属于 $L$，故一个方向的条件已含另一方向。于是(193.7)证明1与2等价。这一步得到同一个 $E$ 同时消去整个 $L$，没有把各个方向分别可行拼成共同可行。

任意确认 $v$ 的正收缩满足 $E\ge P_v$，故 $T_v(p_z)\ge|v^*z|^2$。若1成立，把 $z$ 写在 $\operatorname{span}\{v,w\}$ 中，取相应共同测试，达到这个下界；$z$ 平行 $v$ 时直接成立。故1推出3。3对正交 $v,w$ 给最小值零，紧性保证达到，正性使 $w^*Ew=0$ 等价于 $Ew=0$，故3推出1。$\square$

**定义 193.3（最差原二元区分能力）。** 定义

$$
\kappa(L)=\min_{v\perp w}\ \max_{E\in\mathcal E_L}
\operatorname{Tr}\bigl(E(P_v-P_w)\bigr)\in[0,1].
\tag{193.8}
$$

最大值允许同一测试的两个结果互换，因为 $I-E\in\mathcal E_L$。若两种准备等先验且数学二结果测量为 $\{E,I-E\}$，其最优平均错误为该对比度的 $(1-\text{对比度})/2$；因此最难正交对的最优错误为 $(1-\kappa(L))/2$。这只是已给准备及测试模型中的统计量。

**定理 193.4（共同菜单的精确损失公式）。** 若 $L\ne\{0\}$，则

$$
\boxed{\quad
\kappa(L)=\min\left\{1,\ \min_{0\ne X\in L}
\frac{t(X)-\min(a(X),b(X))}{\max(a(X),b(X))}\right\}.
\quad}
\tag{193.9}
$$

右侧齐次比值的最小值可在 $\max(a,b)=1$ 的紧集上取得。若 $L=\{0\}$，则 $\kappa(L)=1$。特别地，$\kappa(L)=1$ 恰为193.2；若谱条件失效，可选最优核方向，其两端谱向量给出达到全局最坏值的一对原正交向量。

证明。令 $\Delta=P_v-P_w$。由于 $I\in L^\perp$、$\operatorname{Tr}\Delta=0$，置 $A=2E-I$，成熟的迹范数／算子范数商对偶给

$$
\max_{E\in\mathcal E_L}\operatorname{Tr}(E\Delta)
=\frac12\max_{\substack{A\in L^\perp\\\|A\|_\infty\le1}}\operatorname{Tr}(A\Delta)
=\frac12\min_{X\in L}\|\Delta+X\|_1.
\tag{193.10}
$$

有限维 Hahn–Banach 商范数对偶亦直接给最后等式。基范数与全效应对偶归[Q193LPW]，不是新增对偶定理。

对固定 $X\ne0$，Hermitian 特征值重排的迹范数下界给

$$
\min_{v\perp w}\frac12\|X+P_v-P_w\|_1
=t+1-\min(a,1)-\min(b,1).
\tag{193.11}
$$

具体地，把 $P_v$ 放在最小谱方向，把 $P_w$ 放在最大谱方向便达到；下界是成熟的特征值扰动不等式 $\sum_j|\lambda_j(A)-\lambda_j(B)|\le\|A-B\|_1$，取 $B=P_w-P_v$，特征值按同一顺序列出。这是谱重排工具的应用，不另申领该不等式。

联合最小化中的 $v,w,X$ 可交换次序，因为它们都是最小化。沿每条核射线 $rX$，需最小化

$$
f(r)=rt+1-\min(ra,1)-\min(rb,1),\qquad r\ge0.
\tag{193.12}
$$

设 $a\ge b$。在 $[0,1/a]$、$[1/a,1/b]$、$[1/b,\infty)$ 上斜率依次为 $t-a-b$、$t-b$、$t$。后两者非负，因为 $t\ge a\ge b$。故 $t\ge a+b$ 时最小值为1，否则在 $r=1/a$ 取 $(t-b)/a$。交换正负谱处理 $b\ge a$，即得(193.9)。非零 $L$ 的算子范数单位球面紧，且 $t\ge\max(a,b)$，所以比值连续、非负并达到最小值。若总值小于1，选最优核方向及上述极谱对，同时达到联合最小值。$\square$

**定理 193.5（单核中纯互反不能与对径零分离）。** 令 $L=\mathbb RH$、$0\ne H=H^*$、$\operatorname{Tr}H=0$，并用193.1的完整菜单。则下列条件等价：全原向量对的 $T_v(p_z)=T_z(p_v)$、全原向量对 Born 公式、$\mathsf A(L)$、$t(H)\ge a(H)+b(H)$。若另已支付193.1注明的纯点及实际面对应，这也是全原纯互反、全纯 Born 与 AD 在该单核商类中的等价。此断言没有推广到任意多维核的“纯互反推出 AD”。

证明。193.2给后三项等价，Born 公式给互反。反之设 $a+b>t$，取极谱单位向量 $v_+,v_-$，置

$$
z=\frac{\sqrt b\,v_++\sqrt a\,v_-}{\sqrt{a+b}},
\qquad z^*Hz=0,\qquad s=\frac{a+b-t}{b}\in(0,1].
\tag{193.13}
$$

$P_z$ 是合法效应，所以 $T_z(p_{v_+})=b/(a+b)$。任意确认 $v_+$ 的 $E$ 在该向量上为单位、与其余方向的交叉项为零；其余负谱方向最多补偿 $t-b$，故 $\operatorname{Tr}(EH)=0$ 迫 $v_-^*Ev_-\ge s$。等号由

$$
E=P_{v_+}+sP_{v_-}+P_{\mathcal H_-\cap v_-^\perp}
\tag{193.14}
$$

达到。因此

$$
T_{v_+}(p_z)=\frac b{a+b}+\frac a{a+b}\frac{a+b-t}{b}
>\frac b{a+b}=T_z(p_{v_+}),
\tag{193.15}
$$

互反失败。这是同一原菜单中的两个达到效应。$\square$

**定理 193.6（平衡方向与任意复迹零矩阵的共同中性基）。** 设 $m\ge2$、$H=\operatorname{diag}(I_m,-I_m)$，$M\in M_{2m}(\mathbb C)$ 满足 $\operatorname{Tr}M=0$，不要求 $M$ Hermitian。那么存在正交单位基 $(z_j)_{j=1}^{2m}$，同时满足

$$
z_j^*Hz_j=0,\qquad z_j^*Mz_j=0\quad(1\le j\le2m).
\tag{193.16}
$$

证明。先给所需的酉迹抵消。对任意 $B,C\in M_m(\mathbb C)$，置 $p(U)=\operatorname{Tr}(BU)$、$q(U)=\operatorname{Tr}(U^*C)$。若 $B=V\Sigma W^*$ 为奇异值分解，取对角全零的循环置换矩阵 $Q$，则 $U_p=WQV^*$ 满足 $p(U_p)=\operatorname{Tr}(\Sigma Q)=0$；$m\ge2$ 正用在 $Q$ 的存在。由于 $q(U)=\overline{\operatorname{Tr}(C^*U)}$，同理有 $U_q$ 使 $q(U_q)=0$。酉群 $U(m)$ 路径连通，连续实函数 $|p(U)|-|q(U)|$ 在这两点分别非正、非负，所以某个 $U_0$ 满足 $|p(U_0)|=|q(U_0)|$。两者皆零时完成；否则选相位 $e^{2i\theta}=-q(U_0)/p(U_0)$。对 $U=e^{i\theta}U_0$ 得

$$
\operatorname{Tr}(BU+U^*C)=e^{i\theta}p(U_0)+e^{-i\theta}q(U_0)=0.
\tag{193.17}
$$

按 $H$ 的正负扇区写 $M=\begin{pmatrix}A&B\\C&D\end{pmatrix}$，取(193.17)的 $U$，令

$$
T_\pm=\frac1{\sqrt2}\binom{I_m}{\pm U},\qquad
M_\pm=T_\pm^*MT_\pm
=\frac12(A+U^*DU\pm BU\pm U^*C).
\tag{193.18}
$$

有 $T_\pm^*T_\pm=I_m$、$T_+^*T_-=0$、$T_\pm^*HT_\pm=0$。两个像因而是正交互补的整平面中性子空间，且 $\operatorname{Tr}M_\pm=0$。

此时直接使用单个复迹零矩阵可酉零对角化的经典结论，见[Q193GA] Lemma 1 的有限维部分。其所需论证是：Toeplitz–Hausdorff 数值域凸性及对角元平均为零，给一个零期望单位向量；删去它后的压缩仍迹零，逐维继续即得完整零对角基。将 $M_+$、$M_-$ 的两组基分别经 $T_+$、$T_-$ 送回，$H$ 的整平面中性不被这些内部换基破坏，故得到(193.16)。经典单矩阵零对角化不是本条的新内容；接合在于(193.17)—(193.18)先保证两块同时中性且压缩迹零。$\square$

**定理 193.7（任意有限层的共同合法投影区分）。** 设 $m\ge2$，$S=H^\perp\subset\operatorname{Herm}_{2m}$，并定义

$$
\pi:\operatorname{Herm}_{2m}\to\operatorname{Herm}_{2m}/\mathbb RH,
\qquad L_N=\ker\pi^{\otimes N},\qquad L_N^\perp=S^{\otimes N}.
\tag{193.19}
$$

那么每个有限 $N\ge1$、每对正交单位向量 $v,w\in(\mathbb C^{2m})^{\otimes N}$，都存在同一个正交投影

$$
\boxed{\quad E=E^*=E^2\in S^{\otimes N},\qquad Ev=v,\quad Ew=0.\quad}
\tag{193.20}
$$

因此全部这些层满足193.2的谱条件、$\kappa(L_N)=1$，且对任意单位 $v,z$ 的完整原菜单最低值为 $|v^*z|^2$。

证明。$L_N^\perp=S^{\otimes N}$ 由 $\operatorname{Herm}_{2m}=\mathbb RH\oplus S$ 的正交张量展开给出，正是165.2的空间恒等式。证明(193.20)时允许正交向量未归一化。若 $v=0$ 取 $E=0$；若 $v\ne0,w=0$ 取 $E=I$，其中 $I\in S^{\otimes N}$。

当 $N=1$ 且二者非零，令 $M=|v\rangle\langle w|$，它的迹为 $w^*v=0$。193.6给共同中性基 $(z_j)$，于是 $P_{z_j}\in S$，且 $(z_j^*v)(w^*z_j)=0$。令 $J=\{j:z_j^*v\ne0\}$，则 $E=\sum_{j\in J}P_{z_j}$ 是 $S$ 中确认 $v$、消去 $w$ 的投影。

对 $N\ge2$，假定结论对 $N-1$ 成立。令

$$
M=\operatorname{Tr}_{2,\ldots,N}(|v\rangle\langle w|),\qquad
v_j=(z_j^*\otimes I)v,\quad w_j=(z_j^*\otimes I)w,
\tag{193.21}
$$

其中 $(z_j)$ 由193.6作用于这个迹零 $M$ 取得。按偏迹定义，$w_j^*v_j=z_j^*Mz_j=0$。对每个分支用归纳假设，含上述零向量分支，取得 $E_j\in S^{\otimes(N-1)}$。置

$$
E=\sum_jP_{z_j}\otimes E_j.
\tag{193.22}
$$

第一因子投影两两正交，所以 $E^*=E$、$E^2=E$；每个张量项属于 $S^{\otimes N}$。向量展开 $v=\sum_jz_j\otimes v_j$、$w=\sum_jz_j\otimes w_j$ 给 $Ev=v$、$Ew=0$。所有分支被拼成同一个完整原合法效应。由193.2和193.4得其余结论。

这个条件重叠归零及逐方递归的证明骨架归 Walgate 等[Q193W]及[Q193GA] Theorem 2、§III；标准递归未要求本地投影处于 $H^\perp$，新增支付是193.6。这里仅构造完整商菜单内的数学效应；未据递归形式授予商理论中的实际自适应仪器或控制操作。$\square$

**命题 193.8（精确阈值、旧不平衡商与全有限反模型）。** 对193.7的平衡族，全部原向量正交对区分的阈值恰为 $m\ge2$。对 XIV165 原来取定的 $m\ge3$，在其完整强全有限背景中，对每个有限 $N$ 同时有

$$
\boxed{\quad\mathrm{L2}_N+\mathrm{TC}_N+\mathrm{AD}_N
+\text{全部原纯点 Born 最低值与互反},\qquad\neg\mathrm{NC}_N.\quad}
\tag{193.23}
$$

原混合零闭合也在各层失败。若另取 $m\ge4$，全部有限层还满足原 L3；固定任意有限支持预算 $r$ 时，取 $m\ge\max\{3,r+1\}$，165.5的该预算继续成立。故增加任意固定有限的实际小面预算、甚至加入全有限层纯 Born 读数，仍不能删除共同混合零约束。

证明。$m\ge2$ 的正向由193.7。若 $m=1$，$X=H\otimes P_e^{\otimes(N-1)}\in L_N$ 只有非零谱 $1,-1$，正谱迹1而谱直径2，193.2必要性在每层排除区分；此阈值只涉及原向量条件，不把 $m=1$ 的商像预认作165的纯点几何。

$m\ge3$ 时，165.2已给强全有限背景和完整效应，165.4—165.5已给各层全部原纯点、二维支持实际面的仿射同构与正交对径对应，所以193.7给真正的原 AD、全纯 Born 与纯互反。165.6给各层原零邻点的有限混合 $y$ 满足 $T_a(y)>0$ 且其实际生成面为整个 $K_N$；这同时违反混合零凸性及 NC。其余小面量词原样消费165.5，不将 $m\ge3$ 的 L2 范围错报为 L3 范围。

非量子性也由实维数直接读出：固定 $\dim V=(2m)^2-1$，严格落在相邻平方 $(2m-1)^2$ 与 $(2m)^2$ 之间，不存在 $\operatorname{Herm}_n(\mathbb C)$ 的同维有序同构。这个模型没有满足192.7的有限正配对条件。

另外，对 XII159.11 的旧 $H=\operatorname{diag}(7,1,1,1,-7,-1,-1,-1)$，$a=b=7,t=10$，193.4给 $\kappa=3/7$、最难正交对最优错误 $2/7$。193.5取 $v_+=e_1$、$v_-=e_5$、$z=(e_1+e_5)/\sqrt2$，给 $T_{v_+}(p_z)=11/14$、$T_z(p_{v_+})=1/2$。该已有不平衡商不能供应全纯互反且非 AD 的反模型。$\square$

**命题 193.9（完整候选的逻辑位置与几何边界）。** 完整候选仍为192.7，量子理论仍精确由192.8—192.9给出。193.2将矩阵商类中的原二元确认关系压成一个齐次谱不等式；193.7—193.8表明这个条件甚至能在同一个强全有限反模型中处处成立，而共同混合零闭合仍失败。因此它不支付192.7的有限正配对关系，也不独立生成原矩阵表示。

证明。193.23的全部性质在同一固定 $V$、同一系列 $\pi^{\otimes N}\operatorname{PSD}$ 及其完整原菜单中实现，包含每层所有纠缠原纯点；并非分别成立的单层模型。它因而精确加强165的反模型性质：若从192.7的第二项只保留全有限层原纯互反、对径零或全纯 Born 最低值，193.8仍满足这些替代读数，却没有所需共同混合零闭合。由192.8，192.7的有限正配对在该模型中不成立，故这种替换不能给同原域的完整复量子结论。

几何上，(193.10)说明商后二元对比度是原秩二差 $P_v-P_w$ 到核 $L$ 的迹范数距离的一半；(193.4)恰好禁止所有这样的正交纯弦被商缩短。但是保持这些弦长没有保持混合邻点的共同零面。这个描述消费明确矩阵模型的迹范数，未将它称为已从裸关系内生的新度量。完整192.7仍由两目标互反取得实际三球，再由有限正配对取得统一正删除与原菜单延拓，192.8才给同一 $\theta$ 的全部有限复矩阵锥。相应态、效应、Born 配对、POVM 与复合字典原样保留192.9；过程公理和实际操作仍各守其条件。$\square$

**命题 193.10（工具归属与完整白话）。** 交错、紧凸分离、商范数对偶、Hermitian 谱重排及单复矩阵零对角化均为成熟工具。基范数／全效应对偶归[Q193LPW]，纯态统计识别的核／惯性背景归 XIV165 所引[Q193CHST]；后者不承担零错误区分的谱质量条件。单复矩阵零对角化归[Q193GA] Lemma 1 所列经典结论，二正交纯态的条件重叠归零与逐方递归归[Q193W]、[Q193GA]。本章的 repo-derived 接合是193.2的共同原菜单谱判据、193.4的最坏对比度公式、193.5的单核互反分类，以及193.6的平衡中性基和它在193.7—193.8中的全有限层消费者；不申领历史优先权，已有平衡商、经典递归或既有重构不另计为新内容。

证明。193.2—193.9给推导与适用边界。完整白话是：一个大空间可以压掉某些“看不见的方向”，却仍让任意两种纯准备之间的最低确认读数都和量子力学完全相同；这甚至能在全部有限复合中一起做到。办法是先把每次比较的重叠信息分到两张互补平面，让两张平面都对被删方向中性，再在里面选一组使条件重叠归零的基，逐层拼成同一把合法测试尺。谱判据说明这些被删方向为何不缩短任何正交纯弦。但两点之间总能各找一把好尺，不等于所有零邻点能共用一把尺：分别读零的准备混起来，仍会读出正数。因而回溯完整量子公理时，真正不能丢的是“这些关系能在同一个原系统里共同实现”的约束。完整候选继续用三维实际面上的两目标互反和有限正配对表达它；前者产生小球，后者把小球的尺接成共同删除与正延拓，才由既有定理给全部有限复矩阵理论。本章把纯点读数路线能走到哪里、在哪一步不足，给成了同一个全有限反模型的定理。$\square$

[Q193LPW]: https://arxiv.org/pdf/1703.03392v2 "L. Lami, C. Palazuelos, A. Winter, Ultimate data hiding in quantum mechanics and beyond；§II.A Definition 2、Lemma 3，基范数与全效应对偶。"
[Q193CHST]: https://arxiv.org/pdf/1411.0828v2 "C. Carmeli, T. Heinosaari, J. Schultz, A. Toigo, Expanding the Principle of Local Distinguishability；§§II—V，纯态统计识别、核、压缩与惯性，不作零错误区分谱条件的来源。"
[Q193W]: https://arxiv.org/pdf/quant-ph/0007098 "J. Walgate, A. J. Short, L. Hardy, V. Vedral, Local Distinguishability of Multipartite Orthogonal Quantum States，PRL85 (2000), 4972—4975；条件重叠与逐方递归，不含平衡中性限制。"
[Q193GA]: https://arxiv.org/pdf/2601.20074 "I. George, M. A. Alhejji, Local Distinguishability of Multipartite Orthogonal Quantum States: Generalized and Simplified；Lemma1的经典单复矩阵零对角化与Theorem2、§III的标准递归，不含H中性限制。"

## 追加锚（本行以下为增补区）

## 194. 截面正性看不见的四项回路，按未定方向压缩完整候选

### 194.1 空和、单项与整个截面的准确区别

**定义 194.1（原截面与收缩）。** 保留190.1的同一有限维原域 $V,C,u,K,P,[0,u]$，$d=\dim V>1$，以及完整原二元关系 $\#$。对原纯点 $a$ 置

$$
W_a=\operatorname{span}N_a,\qquad
S_a=\mathbb Ra+W_a,\qquad
s_a=\dim S_a,\qquad c_a=d-s_a.
\tag{194.1}
$$

当 $a\notin W_a$ 时，定义唯一的代数删除及其张量收缩

$$
\delta_a(ta+w)=w\quad(w\in W_a),\qquad
\Lambda_a(s\otimes f)=f(\delta_as).
\tag{194.2}
$$

这里 $\delta_a$ 的定义域仅为 $S_a$，没有输入正性或全域延拓。张量 $x\otimes f$ 仍按190.1只表示准备与读数的代数配对。

**定理 194.2（三种检验的精确含义）。** 固定 $a$。190.2式的全部空正和检验当且仅当 $a\notin W_a$。在此条件下，全部 $k\le1$ 检验当且仅当

$$
\delta_ap\in C\quad(p\in P\cap S_a).
\tag{194.3}
$$

另一方面，整个截面正性

$$
\mathsf{LP}_a:\quad\delta_a(C\cap S_a)\subseteq C
\tag{194.4}
$$

当且仅当190.2式在所有正项共用同一个原效应、且 $k\le d$ 时成立。若另有 $C\cap S_a=\operatorname{cone}(P\cap S_a)$，则(194.3)推出(194.4)；这里给出的是一条充分桥梁。

证明。若 $a\in W_a$，190.2证明中的至多 $d$ 个原邻点和空和证书给读数 $-1$。反向在 $a\notin W_a$ 时，右侧任一表示的读数恰为其总张量的 $\Lambda_a$，故零张量读数为零。

记 $\pi_a:V\to V/S_a$ 为商映射。非零单项 $tp\otimes f$ 属于 $S_a\otimes V^*$ 当且仅当 $p\in S_a$，因为 $t>0,f\ne0$ 时 $\pi_a(p)\otimes f=0$ 迫 $\pi_a(p)=0$。其读数就是 $tf(\delta_ap)$。完整原效应生成 $C^*$：非零 $h\in C^*$ 除以 $\max_Kh$ 就在 $[0,u]$ 中。因此所有原效应读数非负等价于落在闭锥 $C$。每个 $S_a$ 内总张量都能沿 $a$ 和一组原邻点基展开，右侧所需邻点数不超过 $d-1$，故没有遗漏原表示量词。

若所有效应都是同一个 $f\ne0$，总张量为 $x\otimes f$，其中 $x=\sum_i t_ip_i\in C$；它属于 $S_a\otimes V^*$ 当且仅当 $x\in S_a$，读数为 $f(\delta_ax)$。任意 $x\in C$ 有有限原纯分解，锥Carathéodory可将输入项数压到 $d$，所以这恰好检查整个 $C\cap S_a$。零效应不贡献读数。最后一项由线性与锥生成立即成立；没有从原单项量词自行取得这个额外生成等式。$\square$

### 194.2 整个截面保正之后，三项仍不增加共同延拓约束

**定理 194.3（低秩与三项自动性）。** 设 $S\subseteq V$，实线性 $\delta:S\to V$ 满足 $\delta(C\cap S)\subseteq C$。将张量 $\mathcal T\in S\otimes V^*$ 看作从 $V$ 到 $S$ 的算子，收缩记为 $\Lambda_\delta$。若 $\mathcal T(C)\subseteq C$ 且普通算子秩不超过二，则

$$
\Lambda_\delta(\mathcal T)\ge0.
\tag{194.5}
$$

若 $\mathcal T=\sum_{i=1}^k x_i\otimes f_i$，$x_i\in C,f_i\in C^*$ 且 $k\le3$，同一结论成立。因此，满足 $\mathsf{LP}_a$ 的标签通过190.2式的全部 $k\le3$ 检验；其负证书若存在，至少有四个正项、普通张量秩至少三。

证明。置 $E=\operatorname{ran}\mathcal T\subseteq S$。因 $C$ 生成 $V$，$\mathcal T(C)-\mathcal T(C)=E$，所以 $C\cap E$ 是 $E$ 中的闭尖生成锥。维数至多二的这种锥为单纯锥。取其线性无关极射线生成元 $e_1,\ldots,e_r$，$r\le2$，沿此基展开

$$
\mathcal T=\sum_{j=1}^r e_j\otimes\ell_j.
\tag{194.6}
$$

$\mathcal T(C)\subseteq C\cap E$ 使各坐标泛函 $\ell_j\in C^*$；而 $e_j\in C\cap S$，故 $\ell_j(\delta e_j)\ge0$，相加给(194.5)。秩零时收缩为零。

正项数至多三时，只剩 $k=3$、普通秩为三尚未覆盖。此时三个输入因子与三个对偶因子分别线性无关，故 $\operatorname{ran}\mathcal T=\operatorname{span}\{x_1,x_2,x_3\}\subseteq S$。每个 $x_i\in C\cap S$，逐项 $f_i(\delta x_i)\ge0$ 即可。这里普通张量秩、正纯分解长度和实际可辨frame长度是不同的计数。$\square$

### 194.3 一个实际三球补面中的最小四项障碍

**命题 194.4（同一原六维域的精确障碍）。** 存在一个满足190.1原域的六维锥及原纯标签 $a$，使 $a\notin W_a$、$\mathsf{LP}_a$ 成立，$\operatorname{conv}N_a$ 是实际闭三球面，但全域正删除不存在。该标签的最小负证书恰有四个正纯张量项，最小普通秩恰为三，读数可取 $1-\sqrt2$。该模型不满足全标签空和条件或全局实际L2。

证明。取 $V=\mathbb R^6$，坐标为 $(\alpha,\tau,x,y,r,z)$，对应坐标泛函为 $A,T,X,Y,R,Z$，单位 $u=A+T$。令 $c=1/\sqrt2$，并置

$$
\begin{aligned}
D&=\{(0,\tau,x,y,r,0):\tau\ge\sqrt{x^2+y^2+r^2}\},\\
a&=(1,0,0,0,0,0),\\
v_\varepsilon&=(1,\tfrac12,\varepsilon c,0,0,1),\\
w_\eta&=(1,\tfrac12,0,\eta c,0,-1),\qquad\varepsilon,\eta\in\{+1,-1\},\\
C&=\operatorname{cone}\bigl(D\cup\{a,v_+,v_-,w_+,w_-\}\bigr),
\qquad B=D\cap\{T=1\}.
\end{aligned}
\tag{194.7}
$$

整个归一底为 $K=\operatorname{conv}(B\cup\{a,\frac23v_+,\frac23v_-,\frac23w_+,\frac23w_-\})$。该紧凸集位于 $u=1$，其锥闭；所有非零生成方向满足 $A,T\ge0$ 且 $u>0$，故 $C$ 尖、$u$ 严格正。$D,a,v_+$ 张成 $V$，故 $C$ 生成。$D=C\cap\ker A$ 是面，$B$ 是实际闭三球面。

全部原纯点恰为

$$
P=\operatorname{ext}B\ \cup\{a,p_+,p_-,q_+,q_-\},
\qquad p_\varepsilon=\tfrac23v_\varepsilon,\quad q_\eta=\tfrac23w_\eta.
\tag{194.8}
$$

球面纯点由面性质保持极端，$a$ 由 $T=0$ 隔离。若以生成元正表示 $v_\varepsilon$，令 $v$ 项总系数为 $s$、$w$ 项总系数为 $t$、$a$ 系数为 $\lambda$；比较 $Z,A$ 得 $s-t=1$、$s+t+\lambda=1$，迫 $t=\lambda=0,s=1$。再比较 $T$ 排除非零 $D$ 项，比较 $X$ 排除另一条 $v$ 射线。$w_\eta$ 同理。紧生成集的凸包不产生这些生成集之外的新极点，证明(194.8)。

定义四个原球面纯点

$$
b_{\varepsilon\eta}=(0,1,\varepsilon c,\eta c,0,0),\qquad
v_\varepsilon+w_\eta=2a+b_{\varepsilon\eta}.
\tag{194.9}
$$

原效应 $A\in[0,u]$ 确认 $a$ 且排除全部球面点。反向若原效应 $f(a)=1$，置 $h=u-f\ge0$，则 $h(a)=0$，(194.9)给 $h(v_\varepsilon)+h(w_\eta)=h(b_{\varepsilon\eta})\le1$。所以 $f(p_\varepsilon),f(q_\eta)\ge1/3$，其余四个纯点不属于 $N_a$。由此

$$
N_a=\operatorname{ext}B,\qquad W_a=\operatorname{span}D,\qquad S_a=\{Z=0\}.
\tag{194.10}
$$

若非负生成和的 $Z$ 坐标为零，$v$ 项和 $w$ 项总系数相等。将两组系数非负配对，逐对应用(194.9)，就有

$$
C\cap S_a=\mathbb R_+a+D,\qquad
\delta_a(\alpha,\tau,x,y,r,0)=(0,\tau,x,y,r,0).
\tag{194.11}
$$

故整个截面保正，且在截面上质量不增。假如全域正 $Q$ 杀掉 $a$ 并固定全部 $N_a$，(194.9)迫 $Qv_\varepsilon+Qw_\eta=b_{\varepsilon\eta}$。右侧是 $C$ 的极射线，故固定 $\varepsilon$、改变 $\eta$ 时，$Qv_\varepsilon$ 必落在两条不同极射线的交中，只能为零。随后同一 $Qw_\eta$ 又须等于两个不同的 $b_{+\eta},b_{-\eta}$，矛盾。

精确负证书使用完整原效应

$$
H=\tfrac14A+\tfrac12T,\qquad
f_\varepsilon=H-\tfrac\varepsilon2X,\qquad
h_\eta=H-\tfrac\eta2Y.
\tag{194.12}
$$

在 $D$ 上，$f_\varepsilon=(T-\varepsilon X)/2\in[0,T]$，$h_\eta$ 同理；在 $a$ 上两者为 $1/4$；在 $v_\sigma$ 上分别为 $(1-\varepsilon\sigma c)/2,1/2$，在 $w_\rho$ 上分别为 $1/2,(1-\eta\rho c)/2$。这些值均介于零和对应 $u$ 值之间，故确是原全域效应。以 $e_\tau,e_x,e_y$ 表示相应坐标向量，令

$$
\begin{aligned}
\mathcal T
&=\sum_\varepsilon v_\varepsilon\otimes f_\varepsilon
  +\sum_\eta w_\eta\otimes h_\eta\\
&=(4a+2e_\tau)\otimes H-c\,e_x\otimes X-c\,e_y\otimes Y,\\
g_0&=4H,\qquad
g_{\varepsilon\eta}=\tfrac12H-\tfrac\varepsilon4X-\tfrac\eta4Y.
\end{aligned}
\tag{194.13}
$$

四个正输入以原纯点表示时系数均为 $3/2$。直接展开得

$$
\mathcal T=a\otimes g_0+\sum_{\varepsilon,\eta}b_{\varepsilon\eta}\otimes g_{\varepsilon\eta},\qquad
\sum_{\varepsilon,\eta}g_{\varepsilon\eta}(b_{\varepsilon\eta})
=4(\tfrac14-\tfrac c2)=1-\sqrt2<0.
\tag{194.14}
$$

右侧邻点数 $4\le d=6$。194.3和(194.11)排除全部至多三项负证书，也排除普通秩至多二的负证书；(194.13)两组三个因子分别线性无关，普通秩为三。所以两种最小性均已支付。

最后明确原域范围。令 $b_N=(0,1,0,0,1,0)$、$b_S=(0,1,0,0,-1,0)$。原正泛函 $T-R$ 的零面锥恰为 $\operatorname{cone}\{a,b_N\}$，故 $F_K(a,b_N)=[a,b_N]$ 为线段，全局实际L2失败。原效应 $T$、$(T+R)/2$、$(T+R)/2-Z/4$、$(T+R)/2+Z/4$ 分别确认 $b_N$ 并排除 $a,b_S,p_\pm,q_\pm$；其原效应合法性逐生成元由(194.7)核对。又有

$$
b_N=v_++v_-+w_++w_- -4a-b_S\in\operatorname{span}N_{b_N}.
\tag{194.15}
$$

因此全标签空和条件也失败。本例只反驳“单标签整个截面保正且补面为实际三球就能全域正延拓”，没有构造强全有限层级或全标签L2反模型。$\square$

**命题 194.5（全局实际L2排除这个矩形拼法）。** 在任意原紧凸域中，不能同时保留实际三球面 $B$、外部原纯点 $a\notin B$、194.9的四个不同球面点及原纯射线关系，并使全部不同原纯对的实际最小面都是三球。

证明。将(194.9)归一，有 $(p_\varepsilon+q_\eta)/2=(2a+b_{\varepsilon\eta})/3$。面遗传性使 $p_\varepsilon$ 属于 $F(a,b_{\varepsilon+})\cap F(a,b_{\varepsilon-})$。两颗实际三球都含不同原纯点 $a,p_\varepsilon$，故都含 $F(a,p_\varepsilon)$；三球没有非单点真面，三者只能相等。这一共同球面又含 $B$ 中两个不同原纯点 $b_{\varepsilon+},b_{\varepsilon-}$，故含整个实际面 $B$。$B$ 是该球的非单点面，只能等于该球，与 $a\notin B$ 矛盾。该排除只覆盖指定的矩形关系，不据此排除一切四项秩三障碍。$\square$

### 194.4 只检查不能再拆的闭合配对回路

**定义 194.6（商中的原始正回路）。** 固定 $a$，取非零原效应 $f_i$、原纯点 $p_i$，记 $z_i=\pi_a(p_i)\otimes f_i$。一个原始正回路是正系数 $t_i>0$ 满足 $\sum_i t_iz_i=0$，且没有真子集支持非零非负零关系。$z_i=0$ 时允许单项回路；它恰对应 $p_i\in S_a$。

**定理 194.7（未定方向的精确充分界）。** 在190.1的同一原域，对每个标签 $a$，以下三项等价：

1. 存在190.3式的同一个全域正删除。
2. 保留全部空正和检验，并只对194.6的原始正回路检查190.2式。
3. 保留全部空正和检验，并只对 $k\le d(d-s_a)+1$ 检查190.2式。

原始正回路的项数自动不超过 $d(d-s_a)+1$；若该回路的效应线性跨度为 $q$，还有 $k\le c_aq+1$。还可用统一界 $k\le(d-1)^2$ 代替190.1的 $d^2$，而不增加任何模型前件。统一界与全标签L2类中的最优性均未断言。

证明。先由空和取得 $a\notin W_a$，从而 $\delta_a,\Lambda_a$ 良定义。任取有限非负零关系 $\sum_i t_iz_i=0$，删去零系数；在其支持内选一个支持极小的非负零关系 $v$，沿它减去 $\lambda v$，其中 $\lambda=\min_{v_i>0}t_i/v_i$。余系数仍非负且至少去掉一个指标。有限归纳将原系数向量分成原始正回路的非负和。各回路的原正张量都属于 $S_a\otimes V^*$，故收缩线性保证：若总张量收缩为负，至少一条原始回路收缩为负。其右侧沿 $a$ 与原邻点基展开，仍符合 $r\le d$，没有要求每个正输入单独属于 $S_a$。

原始回路的生成元关系空间是一维：若核中另有独立向量，从全正关系沿该方向移动到非负系数的边界，就得到真子集上的非负零关系，矛盾。因此其 $k$ 个商生成元的秩为 $k-1$，而商张量空间维数为 $c_ad$，故 $k\le c_ad+1$；把对偶因子限于该回路效应的实际跨度，便给 $k\le c_aq+1$。这证明只查第2项或第3项都能排除任何有限负证书；190.2即供应第1项。反向由正删除收缩原关系给非负数。

194.4的证书在这个实际跨度界取等：$c_a=1$，四个效应张成 $\operatorname{span}\{H,X,Y\}$，$q=3$；商中唯一关系是 $f_++f_-=h_++h_-$，所有系数严格正，没有真子回路，故 $k=c_aq+1=4$。这里的取等仅针对这个单标签模型及其效应跨度，不声称原全维界或全局L2类的锐性。

同一界还有直接的锥Carathéodory证明，可核对没有把正项误限在 $S_a$。任选 $\delta_a$ 的实线性延拓 $D_0$，对每个原正配对置

$$
\zeta(p,f)=\bigl(\pi_a(p)\otimes f,\ f(D_0p)\bigr)
\in\bigl((V/S_a)\otimes V^*\bigr)\oplus\mathbb R.
\tag{194.16}
$$

负证书经正缩放给 $(0,-1)$ 的有限锥表示；在 $c_ad+1$ 维空间用成熟锥Carathéodory，只保留至多该数量的原生成元。第一坐标仍为零使新总张量属于 $S_a\otimes V^*$，第二坐标保留负收缩，任意选取的 $D_0$ 没有成为额外正性前件。

$d>1$ 时每个原纯点都有原零邻点：取在 $a$ 为零的非零正支持泛函 $h$，在其原纯最大点 $b$ 处用 $u-h/\max_Kh$ 确认 $a$、排除 $b$。所以空和通过后 $s_a\ge2$，遂有 $c_ad+1\le d(d-2)+1=(d-1)^2<d^2$。全域条件的强弱等价已证；减少的是必须显式量化的检验；原纯点与效应菜单仍可无限，回路长度有界不将它们变为有限枚举，也不给独立经验前提数减少或检验成本的界。$\square$

### 194.5 完整候选、几何与量子对应

**定义 194.8（三复制原始回路候选）。** 完整保留192.7的强实全有限背景和第一项无中心两目标条件：原 $W_N=V^{\otimes_{\mathbb R}N}$、全部 $C_N,u_N=u^{\otimes N}$、闭尖生成与严格正单位、全部原态及全效应、每个有限min/max分块、正置换及逆、规范重括号、标量层；在整个原 $K_3$ 中，每个不同原纯对生成三维实际最小面，每面有192.5的两个不同、不能确定区分的互反目标。将192.7第二项替换为：对每个原纯 $a$ 保留全部空正和，并仅对194.6的原始正回路要求190.2式的非负读数。可等价改成 $k\le d(d-s_a)+1$ 或统一 $k\le(d-1)^2$，其中 $d=\dim W_3$。记此候选为 $\mathsf Q_{\rm circuit}$。

**定理 194.9（同一全有限量子理论与简化范围）。** 在194.8的精确背景下，$\mathsf Q_{\rm circuit}$ 当且仅当存在同一个 $n\ge2$ 和同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使所有有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{194.17}
$$

证明。194.7在同一整个原 $K_3$ 中恢复192.7第二项，192.8直接给(194.17)。反向原标准压缩支付190.2式，因而支付其原始回路子族。两目标、实际三维与强全有限背景均保留原量词，没有把局部内禀菜单用于定义原 $N_a$。

在重建后的任一矩阵层，记矩阵大小为 $D$、$a=P_v$。则 $W_a=\operatorname{Herm}(v^\perp)$，$S_a$ 是 $\mathbb Cv\oplus v^\perp$ 的块对角空间，故 $d=D^2$、$s_a=1+(D-1)^2$、$c_a=2(D-1)$。新界为 $2D^2(D-1)+1$，原界为 $D^4$；商中未定方向恰是被删射线与其补空间之间的相干方向。这是重建后的维数解释，不在重建前预送矩阵大小。

192.9的条件字典逐项保留：原态与原全效应成为迹一PSD和 $[0,I]$，配对成为Born迹，有限效应族总和为单位才成为数学POVM；同一个全有限张量坐标供应复合与偏迹。全部有限旁观者保正、全输入质量预算及分支总预算分别承担CP、TNI/TP与数学仪器；实际操作实现、指定锐事件更新、连续可逆时间群、物理钟、能量和 $\hbar$ 标定仍须各自前件。几何仍是复射影纯点、复支持面及正交压缩，三个两两原正交纯点在同一复三维支持内给仿射维数八的共同面，三颗二点球是其中的实际面。

194.3—194.5在整个截面保正的前提下，将局部到整体的剩余问题准确留在四项以上、秩三以上的联合关系，并排除一个最简单的实际球矩形拼法；它们没有证明全标签实际L2加单项检验足够，也没有证明全标签实际L2加整个截面正性足够。194.7则在不等待这两条未证桥梁时，实质缩小原候选的检验子族。$\square$

**命题 194.10（承重归属与完整白话）。** 单纯锥的低维结构、有限凸生成、锥Carathéodory及有限线性关系的支持消元是成熟工具。正核回路分解是[Müller–Regensburger，arXiv:1512.00267v2，定理3、命题5](https://arxiv.org/abs/1512.00267v2)在 $\ker B\cap\mathbb R_+^k$ 上的特例，其中 $B$ 为有限商生成元矩阵；194.3将它们用于原准备—读数配对，194.4给出指定删除形状的同原六维最小证书，194.5核对其与全局实际L2的冲突，194.7把商方向回路界接回190的正删除等价，构成本章的repo-derived接合。不申领正映射延拓理论、凸分析工具、既有重建或文献优先权。正算子对偶的文献前置仍按[Q190GKT]的注明范围复用。

证明。相应推导分别在194.3—194.9。完整候选可说成：保留全部原准备、测试和有限复合，在整个三份系统中，每对纯准备仍撑起三维小面，每面两个不能确定区分的目标对整张纯外壳的确认比较交换端点不变；再挑一个待删纯点，把它和能与它确定区分的邻点共同张成一张截面，只检查那些离开截面又恰好闭合、并且不能拆成更小正回路的“准备配测试”关系，删去自身项后总读数不能负。空回路先排除自身已经藏在邻点线性关系中的冲突。单项只看原来就在截面里的纯点；连整个截面都保正时，三项以内仍看不见更深的错位，六维例子的四项回路正好留下 $1-\sqrt2$。这个例子缺少全局二点三球拼接，而那种最简单矩形又确被全局三球排除，所以不能拿它否定完整量子候选。对其余回路不用无限枚举全部长关系：每条正闭环都能拆成原始闭环，长度由截面外尚未指定的方向数控制；任何负总账必在其中一条短闭环出现。没有这种负闭环，统一正删除才作为结论出现，既有重建随后给Born配对和全部有限复张量层。这里省掉的是冗余长检验；“交换两个比较端点”依旧没有变成“任意接续测量可交换”。$\square$

## 追加锚（本行以下为增补区）

## 195. 邻点投影的实张成：三点切向闭合把共同正性压成线性不回卷

### 195.1 原二元关系与纯线性约束

**定义 195.1（完整原域与 LIN）。** 设 $V$ 是非零有限维实向量空间，$C\subset V$ 是闭、尖、生成的凸锥，$u\in V^*$ 在 $C\setminus\{0\}$ 严格正。保留紧底 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$ 和全部原效应 $\mathcal E=[0,u]_{C^*}$。$F_K(A)$ 始终是包含 $A$ 的实际最小面，含空面与整个 $K$。定义

$$
\begin{gathered}
a\mathrel\# b\quad\Longleftrightarrow\quad
\exists e\in\mathcal E:\ e(a)=1,\ e(b)=0,\qquad a,b\in P,\\
N_a=\{b\in P:a\mathrel\# b\},\quad
W_a=\operatorname{span}_{\mathbb R}N_a,\\
\mathrm{LIN}(a):\quad a\notin W_a,\qquad
\mathrm{LIN}:\quad\forall a\in P,\ \mathrm{LIN}(a).
\end{gathered}
\tag{195.1}
$$

取补效应表明 $\#$ 对称。这里的张成允许任意实系数，并不是凸包，也不预给邻点共同为零的效应。NC 仍指 $a\notin F_K(N_a)$ 对所有 $a$ 成立。

L2 仍要求每个不同纯对的整个实际面 $B(a,b)=F_K(a,b)$ 仿射同构于闭 Euclidean 三球。对 $p\ne y$，$\tau_p(y)$ 是这个球的纯边界在 $p$ 处的二维实仿射切方向；它由球内仿射结构唯一决定，不用原空间的预给内积。TC 是同一层内的三点相容关系

$$
\tau_p(y)\subseteq\tau_p(a)+\tau_p(b)
\quad\bigl(a\ne b,\ p\notin B(a,b),\ y\in P\cap B(a,b)\bigr).
\tag{195.2}
$$

定义160.2已给这个切方向的坐标无关性。本章的单锥候选为 $\mathrm{L2+TC+LIN}$；不在此前件中放入 AD、正删除、最小确认者或复矩阵坐标。

### 195.2 从向量张成加强为秩一投影的实张成

**定理 195.2（实际邻点的完整实张成）。** 设同一个满射实线性映射满足

$$
\Psi:\operatorname{Herm}_n(\mathbb C)\twoheadrightarrow V,
\quad\Psi(\operatorname{PSD}_n)=C,\quad u\Psi=\operatorname{Tr},
\quad p_v=\Psi(P_v),\quad\mathcal N=\ker\Psi.
\tag{195.3}
$$

假设 $[v]\mapsto p_v$ 是到全部原 $P$ 的同胚，且支持维数至多二的限制是到对应实际面张成的序同构，准确如命题160.4。对每个单位 $v$，有

$$
\begin{aligned}
\operatorname{span}_{\mathbb R}\{P_w:p_w\in N_{p_v},\ \|w\|=1\}
 &=\operatorname{Herm}(v^\perp),\\
W_{p_v}&=\Psi\operatorname{Herm}(v^\perp).
\end{aligned}
\tag{195.4}
$$

矩阵空间右端按零延拓嵌入 $\operatorname{Herm}_n$。此结论不要求 AD；尤其没有预设每个 $w\perp v$ 都是原邻点。

证明。完整原菜单的准确拉回是 $\mathcal N^\perp\cap[0,I]$。任意原见证 $A$ 满足 $Av=v,Aw=0$，故 $w\perp v$；这先给第一行的包含方向。$n=1$ 时两边都是零，以下设 $H=v^\perp\ne0$。

复用 XII159.8 的压缩空间

$$
\mathscr M_v=\{Q_vZQ_v|_H:Z\in\mathcal N\},\quad
\mathscr L_v=\mathscr M_v^\perp,\quad Q_v=I-P_v.
\tag{195.5}
$$

该引理的前件正是(195.3)及实际小面，并不需要 AD：每个非零压缩核元有至少两个正与两个负本征值，$\mathscr L_v$ 含正定元。XII159.9 的证明于是给出正定 $B\in\mathscr L_v$，其最大本征值 $\lambda$ 单重，单位本征向量记 $w$；并给出实线性满射

$$
A\longmapsto(\lambda I-B|_{w^\perp})^{-1}P_{w^\perp}Aw
\quad\text{从 }\mathscr L_v\text{ 到 }w^\perp.
\tag{195.6}
$$

因此对每个 $z\in w^\perp$，存在该证明中的归一化、固定相位扰动曲线

$$
w_z(t)=w+tz+o(t),
\tag{195.7}
$$

它在充分小的正负 $t$ 上都是某个正定 $\mathscr L_v$ 元素的最大本征向量。每个这样的最大本征向量 $s$ 都是真正的原邻点：若对应正定元为 $B_s$、最大本征值为 $\lambda_s$，则 XII159.30 的

$$
A_s=I-\widehat B_s/\lambda_s
\in\mathcal N^\perp\cap[0,I],\qquad A_sv=v,\quad A_ss=0
\tag{195.8}
$$

逐个供应原见证，$\widehat B_s$ 为在 $\mathbb Cv$ 上补零的矩阵。不同 $s$ 可以用不同见证。

现在令 $T\in\operatorname{Herm}(H)$ 与全部这些邻点投影迹正交。在基点有 $w^*Tw=0$，沿(195.7)的一阶项给

$$
2\operatorname{Re}(z^*Tw)=0\quad(z\in w^\perp).
\tag{195.9}
$$

实方向包括 $z$ 及 $iz$，故 $Tw=0$。再用同一恒等式 $w_z(t)^*Tw_z(t)=0$，此时所有含 $w$ 的交叉项已经严格为零，除以 $t^2$ 并取极限得 $z^*Tz=0$ 对全部 $z\in w^\perp$ 成立。复极化给 $T|_{w^\perp}=0$，结合 $Tw=0$ 得 $T=0$。有限维迹配对非退化，故这些投影的实张成就是整个 $\operatorname{Herm}(H)$。$\dim H=1$ 时单个投影已张成该一维实空间。最后应用同一个 $\Psi$ 得第二行。

XII159.9 已证明向量的复张成；这里增加的是二阶读数迫使投影实张成，既不把两种张成混同，也不需要增加全局光滑结构或开片假设。$\square$

### 195.3 一个标签检测本征方向，全部标签排除整个核

**定理 195.3（点态线性塌缩的精确谱字典）。** 在195.2的同一商中，对每个单位 $v$，

$$
\begin{aligned}
\neg\mathrm{LIN}(p_v)
&\Longleftrightarrow
\exists Z\in\mathcal N,\ \exists\lambda\in\mathbb R\setminus\{0\}:\ Zv=\lambda v,\\
p_v\notin F_K(N_{p_v})
&\Longleftrightarrow
v^*Zv=0\quad\text{对每个 }Z\in\mathcal N.
\end{aligned}
\tag{195.10}
$$

因而全标签 LIN、全标签 NC 与 $\mathcal N=0$ 等价；单个标签的 LIN 则不要求 $v^*Zv=0$。

证明。由195.4，$p_v\in W_{p_v}$ 当且仅当某个 $Y\in\operatorname{Herm}(v^\perp)$ 满足 $\Psi Y=\Psi P_v$。此时 $Z=P_v-Y\in\mathcal N$ 且 $Zv=v$。反向若 $Zv=\lambda v$、$\lambda\ne0$，Hermitian 性给

$$
Z=\lambda P_v+Q_vZQ_v,\qquad
p_v=-\lambda^{-1}\Psi(Q_vZQ_v)\in W_{p_v}.
\tag{195.11}
$$

第二行直接复用 XII159.10 的实际面二分：若某个 $v^*Zv\ne0$，整个邻点生成面就是 $K$；若全部为零，它是 $\Psi\mathcal D(v^\perp)$，且排除 $p_v$。每个非零 Hermitian 核元都有非零本征值，故全标签 LIN 由第一行迫核为零。核为零时第二行给全标签 NC，并由第一行给全标签 LIN；全标签 NC 排核亦是159.10的结论。这里从未用 AD 把全部正交纯点免费放进邻点集。$\square$

**定理 195.4（L2、TC 与线性不回卷的完整单锥重建）。** 在195.1的全部原域上，以下两项等价：

1. L2、TC、全标签 LIN 成立。
2. 存在有限 $n\ge1$ 和同一个实线性同构 $\Phi:\operatorname{Herm}_n(\mathbb C)\to V$，使 $\Phi(\operatorname{PSD}_n)=C$、$u\Phi=\operatorname{Tr}$。

此时 AD、NC、完整混输入 Born 最低值及原菜单中的 least 确认者均为结论。

证明。命题160.4只用 L2+TC，已供应195.2所需的归一化共同商和全部实际小面；195.2—195.3从 LIN 排除它的全部核，取 $\Phi=\Psi$。这一步复用成熟 cap 分类的原接口，不把共同矩阵商当作新增前提。反向矩阵锥的 L2 与 TC 由160.5的反向供应；若 $a=P_v$，其每个原邻点 $P_w$ 都有 $w\perp v$，迹配对 $X\mapsto\operatorname{Tr}(P_vX)$ 在邻点张成上为零、在 $a$ 上为一，故 LIN。原单位与整个菜单均由同一个同构保持。

核为零后，原效应恰为 $0\preceq E\preceq I$；$P_v$ 是确认 $p_v$ 的 least 效应，因此对任意 $X\succeq0$，包括零与任意非负质量，

$$
\min_{\substack{0\preceq E\preceq I\\Ev=v}}\operatorname{Tr}(EX)
=\operatorname{Tr}(P_vX)=v^*Xv.
\tag{195.12}
$$

正交对由这个原效应直接区分，给 AD；邻点实际面是 $\Phi\mathcal D(v^\perp)$，给 NC。它们属于结论，未用于取得(195.4)。$\square$

### 195.4 单正配对与完整正删除的点态边界

**定义 195.5（有限正配对的截断）。** 在195.1的原域，固定 $a\in P$，记 $d=\dim V$。沿190.1，$\mathrm{FC}_1(a)$ 要求下列蕴涵对 $k=0,1$、$r\le d$ 成立；$\mathrm{FC}(a)$ 则要求所有 $k\le d^2$：

$$
\sum_{i=1}^k t_i p_i\otimes f_i
=a\otimes g_0+\sum_{j=1}^r b_j\otimes g_j
\quad\Longrightarrow\quad
\sum_{j=1}^r g_j(b_j)\ge0.
\tag{195.13}
$$

这里 $t_i\ge0$、$p_i\in P$、$f_i\in\mathcal E$、$b_j\in N_a$，而 $g_0,g_j\in V^*$ 任意有符号；空和也在量词中。

**定理 195.6（单标签三层条件及其精确缺项）。** 在195.2的归一化商域中，

$$
\mathrm{FC}_1(p_v)\quad\Longleftrightarrow\quad
\mathrm{FC}(p_v)\quad\Longleftrightarrow\quad
Zv=0\quad(Z\in\mathcal N).
\tag{195.14}
$$

相比195.10，完整正删除排除的不只是非零本征方向或非零对角读数，也排除所有核元在该方向的横向分量。

证明。$\dim V=1$ 时原纯点集是单点，(195.3)的纯点同胚迫 $n=1$，迹归一化迫 $\mathcal N=0$；此时 $N_a=\varnothing$，$S_a=\mathbb Ra$，$\delta_a=0$，FC$_1$ 与 FC 都成立。以下设 $\dim V>1$，直接复用194.2的准确归约：全部空正和恰等价 LIN；在此条件下，$S_a=\mathbb Ra\oplus W_a$ 上良定义 $\delta_aa=0$、$\delta_a|_{W_a}=I$，且 $\mathrm{FC}_1(a)$ 恰等价于

$$
\delta_a(P\cap S_a)\subseteq C.
\tag{195.16}
$$

该归约保留所有原纯点、完整效应、至多 $d$ 个原邻点及有符号读数；它没有将原纯截面正性升级为整个 $C\cap S_a$ 上的正性或全域正延拓。本定理新增的是共同矩阵商域中的精确充要条件。

现进入同一个商，置 $a=p_v$。由195.4，$W_a=\Psi\operatorname{Herm}(v^\perp)$。若 $\mathrm{FC}_1(a)$ 成立而某 $Z\in\mathcal N$ 有 $b=Q_vZv\ne0$，取

$$
\begin{gathered}
w=b/\|b\|,\quad q=(v+sw)/\sqrt{1+s^2},\quad s>0,\\
t=\frac{s}{(1+s^2)\|b\|},\qquad
\alpha=\frac1{1+s^2}-t\,v^*Zv,\qquad
Y=P_q-\alpha P_v-tZ.
\end{gathered}
\tag{195.17}
$$

$Yv=0$，故 $Y\in\operatorname{Herm}(v^\perp)$，并有 $p_q=\alpha a+\Psi Y\in S_a$。令 $q'=(sv-w)/\sqrt{1+s^2}$，则 $P_q+P_{q'}=P_v+P_w$。$c=p_w\in W_a$，所以 $p_{q'}=a+c-p_q\in S_a$，且

$$
\delta_ap_q+\delta_ap_{q'}=c.
\tag{195.18}
$$

(195.16)使左侧两项都在 $C$。$c$ 是原纯射线，其两项各为非负倍数；可写 $\delta_ap_q=\beta c$，$0\le\beta\le1$。于是 $p_q=\gamma a+\beta c$，原单位给 $\gamma+\beta=1$，所以 $p_q$ 位于 $a,c$ 的凸线段。这与它是不同于两端的原纯点矛盾。这里不需要 $c$ 本身是原邻点；它属于已证的邻点实张成就足够。

因此全部 $Q_vZv=0$。若某 $v^*Zv\ne0$，$v$ 便是该核元的非零本征向量，由195.10违反 LIN。故全部 $Zv=0$。反向若全部 $Zv=0$，标准压缩 $R_v(X)=Q_vXQ_v$ 满足 $R_vZ=Z$ 对所有核元成立，因而下降为同一个原正映射 $Q_a$，杀掉 $a$ 并逐点固定全部原邻点。对(195.13)施加 $Q_a\otimes\operatorname{id}$ 后收缩，左侧为 $\sum_it_if_i(Q_ap_i)\ge0$，故完整 FC 成立。完整 FC 蕴涵其截断，证明闭合。$\square$

**命题 195.7（两个严格的点态分离与全标签边界）。** 在193的平衡单核商中取 $m\ge3$、$H=\operatorname{diag}(I_m,-I_m)$，写正负基为 $e_i,f_i$。则

$$
\begin{array}{c|ccc}
v&\mathrm{LIN}(p_v)&p_v\notin F_K(N_{p_v})&\mathrm{FC}_1(p_v)\\ \hline
(\sqrt3e_1+f_1)/2&\text{成立}&\text{不成立}&\text{不成立}\\
(e_1+f_1)/\sqrt2&\text{成立}&\text{成立}&\text{不成立}
\end{array}
\tag{195.19}
$$

这些是同一个完整原菜单、实际 L2+TC+AD 模型中的单标签分离，不是全标签 LIN 的反模型。

证明。该商的原域、实际小面及 TC 由 XIV165 给出，AD由193.7给出，所以195.2适用。两个向量都不是 $H$ 的本征向量；第一行有 $v^*Hv=1/2$，第二行有 $v^*Hv=0$，但两者都有 $Hv\ne0$。分别代入195.10和195.14即得表格。第二行也对应190.6已有的一个正配对负证书，不重新申领该实例。

同一模型在 $a=p_{e_1}$ 上确实违反 LIN，因为真实准备关系为

$$
p_{e_1}=\sum_{i=1}^m p_{f_i}-\sum_{i=2}^m p_{e_i}.
\tag{195.20}
$$

右侧各点都与 $e_1$ 正交，且由原 AD 给出真正的原邻点。这不是凸分解，而是原纯点与其可排除准备的有符号线性混同。全标签条件正是要排除所有这样的混同，不能只选一个通过检查的标签。$\square$

### 195.5 只在整个三复制域检查的完整候选

**定义 195.8（三复制切向—线性候选）。** 完整采用162.15的强实全有限背景：$\dim V>1$，$W_N=V^{\otimes_{\mathbb R}N}$，各层 $C_N$ 为闭尖生成凸锥，严格正乘法单位 $u_N=u^{\otimes N}$，全部原准备、纯点和完整效应，所有有限分块的原 min/max 张量包含，所有位置置换及逆在整个锥上为正，规范重括号与标量层。只在整个 $K_3=C_3\cap\{u_3=1\}$ 要求

$$
\mathsf Q_{\rm tangent\,linear}
:=\mathrm{L2}_3+\mathrm{TC}_3+\mathrm{LIN}_3.
\tag{195.21}
$$

三个条件均量化全部原纯点，含纠缠纯点。TC 是同一层内的三点切向关系；三复制则指检查整个原三份复合，这两个“三”不混用。

**定理 195.9（一个共同坐标下的全有限复量子理论）。** 在195.8的准确背景中，$\mathsf Q_{\rm tangent\,linear}$ 当且仅当存在同一个整数 $n\ge2$ 和同一个实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}
\quad\text{对每个有限 }N\ge0.
\tag{195.22}
$$

证明。195.4先只用于整个 $(W_3,C_3,u_3)$，给出该锥的同原单位复矩阵表示，以及同一个原域的 L2+NC+AD。此时才支付162.16的 $\mathsf R_3$；直接调用其已证的 pure-spectator 实际面、共同复方向与全有限传播尾部，得到同一个 $\theta$ 的(195.22)，不另立各层无关坐标。反向标准矩阵锥在整个三复制层满足195.4的三个条件。$\dim V>1$ 排除 $n=1$；标量层取空张量约定。$\square$

**命题 195.10（几何与熟悉量子公理的条件字典）。** 在195.9的全部前件下，令 $\Theta_N=\theta^{\otimes N}$。既有162.9及192.9的字典可在同一原对象上直接复用：

| 结构或公理 | 对应结论及其前件 |
| --- | --- |
| Hilbert 空间、纯态、叠加和混态 | $\mathcal H_N=(\mathbb C^n)^{\otimes N}$；全部原纯点为 $\mathbb{CP}^{n^N-1}$，全部原归一态为迹一 PSD，纯态射线的复线性叠加包含在该空间中 |
| Born 概率、全效应和观测量 | 原配对为 $e(x)=\operatorname{Tr}(E\Theta_Nx)$，全部原效应恰为 $0\le E\le I$；同一个 least 确认者给全部混输入的(195.12)，纯点值为 $|\langle v,w\rangle|^2$；Hermitian 谱分解给数学 PVM，有限单位正分解给数学 POVM |
| 复合、纠缠与约化 | 原产品、位置置换和括号对应通常复张量，原边缘 $\operatorname{id}\otimes u$ 对应偏迹；每层包含全部纠缠态 |
| 过程、分支、通道和仪器 | 另要求原线性映射在每个有限旁观者下保持整个原正锥，恰对应 CP；全输入质量不增或保持分别给 Kraus 的 $\sum K_i^*K_i\le I$ 或 $=I$；这些数学分支的有限保质量族组成仪器 |
| 理想锐中性测后更新 | 另给投影效应及逐点固定其读一原纯态的正分支，才由既有中性定理得到 $X\mapsto PXP$ |
| 连续可逆动力学 | 另给连续、保原锥和原单位的实参数群，才推出 $X\mapsto e^{-itH}Xe^{itH}$，$H=H^*$ 唯一到标量；纯态的相应酉提升给 Schrödinger 形式，物理时间、能量与 $\hbar$ 的标定仍需其对应输入 |

证明。195.22正是162.16所得共同表示，所列各行直接使用其后162.9的同域字典，未重证已有过程分类。几何上，二点实际三球是复射影直线 $\mathbb{CP}^1\cong S^2$ 的混态凸包；三条独立纯射线的共同面是复三维支持的 $\mathcal D_3$，仿射维数八。TC把小球的切向关系接进同一个 Hermitian Veronesean 商；LIN再迫这个嵌入没有隐藏核。作为数学映射，195.6的正压缩也随表示存在；它与POVM的存在均不额外宣告每个数学分支或测试族都已由某个实际设备实现。$\square$

### 195.6 简化范围与完整白话

**命题 195.11（空正和的消费者及保留的几何义务）。** 在 L2+TC 的原域中，全标签 LIN、全标签 NC、全标签 $\mathrm{FC}_1$ 与全标签 FC 等价，并由它们重建195.4。因而190.2的全部 $k\ge1$ 正配对在这个入口可作为后果；只保留其 $k=0$ 部分即足够。这个结论没有删除 TC，也不证明裸 L2+AD+LIN 的重建。

证明。$\dim V=1$ 的单点情形中，全部条件直接成立。$\dim V>1$ 时，194.2给空正和恰为 LIN。195.3先使全标签 LIN 排核，195.6再给全部标签的完整 FC。反向 FC 蕴涵空正和，NC 与核为零的等价由195.3供应。强全有限背景下只需在 $K_3$ 应用这些同域等价，再由195.9传播。

194.7—194.9已将192.7的有限正配对缩到原始正回路，长度由商中未定方向控制。在 L2+TC 入口，本候选再将这些非空回路也移入结论，只用原邻点的纯线性独立性表达不回卷；其代价是显式保留 TC 的三点切向闭合。正删除在这些候选中都作为结论。每张二元实际三球仍可由192.5的两个互反目标支付。上述完整候选在同一强背景中都等价于完整复量子层级，但这不证明独立经验公理条数严格减少，更不把 TC 自动从裸二元关系中赚得。

承重新增是195.2的投影实张成、195.10与195.14的点态谱边界，以及它们对线性不回卷的完整重建消费者，属 repo-derived 接合。Hermitian 扰动、谱分解、极化及双对偶性为成熟工具；扰动的具体条件与实满射直接复用 XII159.8—159.9，射影分类通过160.4复用[Q195SV]的 Theorem2.4，全有限传播及过程字典归162.16及162.9。不申领新的 cap 分类、历史优先权或严格最小公理数。

完整白话是：保留系统本来的全部准备、测试和有限复合，只看整个三份系统。任意两个不同纯准备撑起一颗实际三球；从第三个纯点看向这颗球，球上所有比较的切方向，都得装进看向两个端点的那四个方向里；再要求每个纯点都不能由那些能与它确定区分的纯准备，哪怕带正负号，也线性拼回自己。前两条先把小球接成同一个复几何的投影，但还允许压掉看不见的方向。新的桥梁说明，实际可区分邻点虽然未必已经填满所有正交纯点，它们的秩一矩阵却能撑满整个正交矩阵空间；沿原有曲线的一阶读数先消掉交叉项，二阶读数再消掉剩余缺口。若还藏着任何被压掉的方向，取它的一个非零本征方向，就会把对应纯点写成这些邻点的带符号组合，违反第三条。因此投影不能再压掉东西，同一套复矩阵、Born概率和全部有限复合随之恢复。正删除成为结果，动力学与实际过程则在各自明确的过程条件下接上。$\square$

[Q195SV]: https://cage.ugent.be/~hvm/artikels/204.pdf "Schillewaert–Van Maldeghem, Hermitian Veronesean Caps；§2.3的H1—H3、Theorem2.4及§3.3的有限指数供应，经XIII160.3—160.4使用。"

## 追加锚（本行以下为增补区）

## 196. 两条邻方向的共同读数已足够，最短失败由单纯商给出

### 196.1 单纯邻锥把截面正性接成全域正性

**定义 196.1（指定原邻锥）。** 保留190.1的整个原域 $V,C,u,K,P,[0,u]$、原二元关系 $\#$，以及194.1的 $W_a,S_a,s_a,c_a$。记 $w_a=\dim W_a$、$d=\dim V>1$。空正和检验通过后 $a\notin W_a$，因而 $s_a=w_a+1$、$c_a=d-w_a-1$；仍只在 $S_a$ 上定义 $\delta_a(ta+w)=w$，并置

$$
J_a=C\cap W_a,\qquad
\mathsf{LP}_a:\ \delta_a(C\cap S_a)\subseteq C.
\tag{196.1}
$$

$J_a$ 是 $W_a$ 中的闭尖生成锥，因为原邻点属于它并张成 $W_a$。称它单纯，是指它由 $w_a$ 条线性无关极射线生成；没有预给这些射线的原可操作性。

**定理 196.2（原邻锥的单纯延拓桥）。** 固定通过空和检验的原纯标签 $a$。

1. 若 $w_a=1$，则原全域正删除自动存在，不需非空正和检验。
2. 若 $J_a$ 单纯，则原全域正删除存在当且仅当 $\mathsf{LP}_a$。无正删除时，有至多 $c_a+1$ 个原纯输入、共用同一个原效应的负证书。
3. 若 $w_a=2$，则 $N_a=\{b_1,b_2\}$、$J_a=\operatorname{cone}\{b_1,b_2\}$，第2项自动适用，其负证书至多有 $d-2$ 项。

证明。$w_a=1$ 时归一化使 $N_a=\{b\}$。按原关系取 $e\in[0,u]$，$e(a)=1,e(b)=0$，则

$$
Qx=(u-e)(x)b
\tag{196.2}
$$

在整个原锥上正，且 $Qa=0,Qb=b$。

设单纯邻锥的生成元为 $v_1,\ldots,v_{w_a}$。若 $\mathsf{LP}_a$，将指定删除写成 $\delta_as=\sum_j\ell_j(s)v_j$。其正像属于 $J_a$，故每个坐标泛函 $\ell_j$ 在 $C\cap S_a$ 上非负。190.2证明已在同一原域中给出 $S_a\cap\operatorname{int}C\ne\varnothing$，不以正删除存在为前件。成熟的标量正 Hahn–Banach 延拓（[Paulsen–Tomforde，arXiv:0712.2613v4，定理2.14、推论2.15](https://arxiv.org/abs/0712.2613v4)）为每个 $\ell_j$ 供应 $H_j\in C^*$：其中 $S_a$ 包含内点序单位，恰支付所引推论的子空间条件。因此 $Qx=\sum_jH_j(x)v_j$ 是全域正延拓，杀掉 $a$ 并固定全部原邻点。反向限制任一原正删除即给 $\mathsf{LP}_a$。

这个成熟工具只涉及标量：任选 $e\in S_a\cap\operatorname{int}C$，对正泛函 $\ell$ 定义

$$
p(x)=\inf\{\ell(s):s\in S_a,\ s-x\in C\}.
\tag{196.3}
$$

序界 $-Me\le_Cx\le_CMe$ 同时给可行点与有限下界 $-M\ell(e)$。$p$ 次线性，且 $p|_{S_a}=\ell$。实 Hahn–Banach 给 $H|_{S_a}=\ell,H\le p$；$x\in C$ 时 $p(-x)\le0$，故 $H(x)\ge0$。没有使用一般向量值正延拓定理。

若单纯邻锥情形无正删除，取 $x\in C\cap S_a$，$\delta_ax\notin C$。闭锥分离并按 $\max_K$ 归一，给原效应 $f$ 使 $f(\delta_ax)<0$。将 $x$ 有限分解为原纯输入。任选代数延拓 $D_0:V\to V$，在这些输入的向量

$$
\bigl(\pi_a(p_i),f(D_0p_i)\bigr)\in(V/S_a)\oplus\mathbb R
\tag{196.4}
$$

上应用锥 Carathéodory，保留零商分量和负读数，只需至多 $c_a+1$ 个输入，仍共用原效应 $f$。沿 $a$ 及原邻点基展开给190.2允许的右侧，$r\le w_a\le d$。

$w_a=2$ 时归一邻点位于仿射线 $W_a\cap\{u=1\}$。三个不同原纯点不能共线；张成维数二遂使邻点恰有两个。若 $K\cap W_a$ 在线段 $[b_1,b_2]$ 外还有点，一个原纯端点就成为严格凸组合，矛盾。因此 $K\cap W_a=[b_1,b_2]$，单纯性和 $c_a+1=d-2$ 均成立。$\square$

### 196.2 分支短检验与精确达到界的原多面体

**定理 196.3（更短的充分预算）。** 在190.1原域，每个标签的原正删除存在等价于全部空正和检验以及 $k\le B_a$ 的190.2检验。空和失败时条件直接判否；通过后取

$$
B_a=
\begin{cases}
0,&w_a=1,\\
c_a+1=d-2,&w_a=2,\\
c_ad+1=d(d-w_a-1)+1,&w_a\ge3.
\end{cases}
\tag{196.5}
$$

若已知 $J_a$ 单纯，还可将相应分支换成至多 $c_a+1$ 项的共同效应检验。对全部原域统一可取

$$
U(d)=
\begin{cases}
0,&d=2,\\
1,&d=3,\\
2,&d=4,\\
d^2-4d+1,&d\ge5.
\end{cases}
\tag{196.6}
$$

证明。$w_a=1,2$ 由196.2，$w_a\ge3$ 由194.7。正删除的收缩又供应任意长度检验，故各分支是等价。194.7已证原邻点非空；空和通过后 $1\le w_a\le d-1$。$w_a\ge3$ 时 $c_a\le d-4$，$w_a=2$ 时预算为 $d-2$。逐维取可存在分支的最大值：$d=2$ 只有第一分支；$d=3$ 的第二分支给一；$d=4$ 的第二、第三分支分别给二、一；$d\ge5$ 时 $d(d-4)+1\ge d-2$。这给(196.6)，且总有 $U(d)<(d-1)^2$。除下项给出的固定标签情形外，不断言最优性。$\square$

**命题 196.4（共同效应仍可需要 $d-2$ 个原纯输入）。** 对任意整数 $c\ge0$，有维数 $d=c+3$ 的完整原域与原纯标签 $a$，其 $w_a=2,c_a=c$，全部 $k\le c$ 检验通过，但一条 $k=c+1=d-2$ 的共同效应原始回路读数为 $-1/4$。故196.2第三项在固定标签类中精确。

证明。置 $m=c+1$、$\alpha=1/(2m)$、$\beta=1/(4m)$，在 $\mathbb R^3\oplus\mathbb R^c$ 的坐标 $(t,x,y,z)$ 中取

$$
\begin{aligned}
a&=(1,0,0,0),& b_1&=(1,1,0,0),& b_2&=(1,0,1,0),\\
p_i&=(1,\alpha,-\beta,v_i),&
q&=(1,\alpha,-\beta,0),&u&=t.
\end{aligned}
\tag{196.7}
$$

$c\ge1$ 时令 $v_i=e_i$（$1\le i\le c$）、$v_m=-\sum_{i=1}^ce_i$；$c=0$ 时只有 $v_1=0$。取整个 $K=\operatorname{conv}\{a,b_1,b_2,p_1,\ldots,p_m\}$、$C=\operatorname{cone}K$ 和全效应 $[0,u]$。生成元张成全空间，$K$ 紧且在 $u=1$，所以闭尖生成和严格正单位条件齐备。

$t-x-y,x,y$ 分别唯一暴露 $a,b_1,b_2$。$c\ge1$ 时 $z_i$ 暴露 $p_i$、$-\sum z_i$ 暴露 $p_m$；$c=0$ 时 $-y$ 暴露 $p_1$。故所列顶点恰为全部原纯点。效应 $e_0=t-x-y$ 在 $a$ 为一，在 $b_1,b_2$ 为零，在每个 $p_i$ 为 $1-\alpha+\beta\in[0,1]$，故两端点属于 $N_a$。

对任意原效应 $e(a)=1$，记 $B=e(b_1),H=e(b_2)\in[0,1]$。由

$$
\sum_{i=1}^mp_i=mq,\qquad
q=(1-\alpha+\beta)a+\alpha b_1-\beta b_2
\tag{196.8}
$$

得 $e(q)=1-\alpha+\beta+\alpha B-\beta H\ge1-\alpha$。所以 $\sum_ie(p_i)\ge m-1/2$；其余 $m-1$ 项各至多一，逐项 $e(p_i)\ge1/2$。因此 $N_a=\{b_1,b_2\}$、$W_a=\operatorname{span}\{b_1,b_2\}$、$S_a=\{z=0\}$，全部空和通过。

$c\ge1$ 时，$v_1,\ldots,v_m$ 的任意至多 $c$ 个不同列线性无关。$k\le c$ 的原检验最多涉及 $c$ 个不同截面外纯点。按这些点合并效应因子，商约束成为 $\sum_i v_i\otimes F_i=0$，线性无关迫每个 $F_i=0$。余项只有 $a,b_1,b_2$，删除收缩均非负。$c=0$ 的较短检验只有已经通过的空和。这核对了全部更短检验，没有预限每个输入在 $S_a$。

取原效应 $f=t-x$，它在 $a,b_2$ 为一，在 $b_1$ 为零，在 $p_i$ 为 $1-\alpha$，在整个原域合法。准确证书为

$$
\begin{aligned}
\sum_{i=1}^mp_i\otimes f
&=a\otimes\bigl[m(1-\alpha+\beta)f\bigr]
 +b_1\otimes(m\alpha f)+b_2\otimes(-m\beta f),\\
m\alpha f(b_1)-m\beta f(b_2)&=-m\beta=-\tfrac14.
\end{aligned}
\tag{196.9}
$$

商列 $v_i\otimes f$ 秩为 $c$，唯一正关系为全部等系数，故是原始回路并达到 $k=c+1$。$c=1$ 给 $d=4$ 的显式五顶点模型：$p_\pm=(1,1/4,-1/8,\pm1)$，全部单项通过，二项读数负；$c=0$ 给 $d=3$ 的单项失败。因此 $U(3)=1,U(4)=2$ 在无实际L2的固定标签类中不能下降。

证书总张量为 $mq\otimes f$，普通秩一，却需 $m$ 个原纯输入；纯分解长度与普通秩不同。它直接违反 $\mathsf{LP}_a$：$q\in K\cap S_a$ 而 $f(\delta_aq)=-\beta<0$，不反驳196.2。零暴露面 $K\cap\ker e_0=[b_1,b_2]$ 是实际线段，实际L2失败。没有提供全标签缩短检验、强全有限层级或物理实现的反模型。$\square$

### 196.3 完整候选、几何及量子对应

**定义 196.5（三复制分支短关系候选）。** 完整保留194.8的强实全有限背景及第一项：全部原 $V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正乘积单位、原全态全效应、每个有限min/max分块、正置换及逆、规范重括号与标量层；在整个原 $K_3$，每个不同原纯对生成三维实际最小面，每面有192.5的两个不同且不能确定区分的互反目标。第二项改为：对每个原纯标签保留空正和，并只检查(196.5)预算内的190.2原正配对关系。等价地统一检查 $k\le U(d)$，$d=\dim(V^{\otimes_{\mathbb R}3})$，右侧仍允许任意有符号原对偶和至多 $d$ 个原邻点。记为 $\mathsf Q_{\rm short}$。

**定理 196.6（同一完整量子对应）。** 在196.5的准确背景下，$\mathsf Q_{\rm short}$ 当且仅当存在同一个 $n\ge2$ 及实线性同构 $\theta:V\to\operatorname{Herm}_n(\mathbb C)$，使全部有限 $N\ge0$ 满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{196.10}
$$

证明。196.3在整个原 $K_3$ 恢复全部原正删除，194.7遂恢复194.8的回路条件，194.9给(196.10)。反向标准正交压缩满足全部原有限配对检验。192.9及194.9的条件字典保留：态、全效应和配对成为迹一PSD、$[0,I]$ 及Born迹，纯点为复射影射线，实际二点面为三球；共同有限张量层供应复合与偏迹。全部有限旁观者保正、全输入与分支总预算分别承担CP、TNI/TP和数学仪器；实际更新、连续时间群、物理钟、能量及 $\hbar$ 标定仍须各自条件。

在矩阵大小 $D$ 层，$W_a=\operatorname{Herm}(a^\perp)$。$D=2$ 时其维数一，该标签的正删除由(196.2)自动供应；$D\ge3$ 时其正锥为 $\operatorname{PSD}_{D-1}$，不是单纯锥。三份检验所在的实际矩阵大小为 $D=n^3\ge8$，不据单份qubit的自动性删除三份域的联合条件。减少的是显式关系长度上界，未减少背景、独立经验前件或无限菜单的枚举成本。未增加TC时，全标签实际L2加单项、或加全部 $\mathsf{LP}_a$ 的充分性仍未由本章证明。

195.4—195.11已在明确增加TC的入口，用全标签空正和排除共同商核，并将非空正配对全部移入结论。本章的196.2—196.4适用于一般原域，不要求实际L2或TC；196.5的完整候选也不预设TC，而保留196.3的短正配对。两种入口在各自准确的强全有限背景中都接到同一复量子层级，不将较短预算重报为TC已被删除，也不重复195的切向重建。$\square$

**命题 196.7（归属与完整白话）。** 标量正 Hahn–Banach、单纯锥坐标与锥 Carathéodory为成熟中间工具；196.2将它们接到指定原邻关系，196.3给分支预算，196.4给同一原全菜单中精确达到 $d-2$ 的族。新增是这些指定接口与锐例的接合，不申领正延拓理论、已有量子重建或文献优先权。

证明。196.2—196.6给完整推导。白话上，仍保留全部原准备、测试和有限复合，只在整个原三份系统中检查：每对纯准备撑起三维小面，每面两位不同而不能确定区分的目标与整张纯外壳交换确认比较的两端，最低读数都不变；全部空正和先排除一颗纯点已经藏进自身可区分邻点的有符号线性关系中的冲突，再选一颗待删纯点，问能与它确定区分的邻点共同留下几条方向。只剩一条时，原区分测试直接给统一删除；只剩两条时，留下的部分是单纯锥，每条坐标的非负读数都能延拓到原全域，所以只需检查同一把尺下的准备正和。更大的非单纯邻锥才可能留下截面保正而共同延拓失败的障碍，仍用短正回路检查。显式的单纯商说明，同一把尺也可能必须同时放入 $d-2$ 颗原纯准备才看见负读数，不能把总张量秩一误读成只需一颗纯准备。这样保留完整量子对应，又去掉冗余长检验；比较端点互换仍未变成任意测量接续可交换。$\square$

## 追加锚（本行以下为增补区）

## 197. 每线命中与纯准备的单侧系数

### 197.1 原二元关系、实际面与有向商

**定义 197.1（命中与纯系数条件）。** 完整保留 XIII160.1 的原域：非零有限维实空间 $V$，闭、尖、生成凸锥 $C$，在非零正元上严格正的原单位 $u$，整个紧底 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$ 及整个原效应区间 $\mathcal E=[0,u]_{C^*}$。记 $d=\dim V$，$F_K(A)$ 是包含 $A$ 的最小实际面；空集生成空面。定义

$$
\begin{gathered}
a\#b\quad\Longleftrightarrow\quad
\exists e\in\mathcal E:\ e(a)=1,\ e(b)=0,\\
N_a=\{b\in P:a\#b\},\qquad
W_a=\operatorname{span}_{\mathbb R}N_a,\qquad
S_a=\mathbb Ra+W_a,\\
\mathrm{Hit}(a):\quad
N_a\cap F_K(p,q)\ne\varnothing
\quad\text{对所有不同的 }p,q\in P,\\
\mathrm{SP}(a):\quad
p\in P,\ \lambda\in\mathbb R,\ p-\lambda a\in W_a
\quad\Longrightarrow\quad\lambda\ge0.
\end{gathered}
\tag{197.1}
$$

补效应使 $\#$ 对称，无自反性由读数一与零不同给出。Hit 只用纯点和原实际面，不预先指定球、对径、混态零凸性或共同确认者。若另给 L2，每个不同纯对的实际面就是整颗仿射三维闭球，Hit 便是 $N_a$ 命中每条纯点线；该线是球的整个纯边界。

SP 只检查原纯准备的线性关系。其有限写法是：对任意 $0\le r\le d$、原 $b_1,\ldots,b_r\in N_a$、实数 $c_j,\lambda$ 和原 $p\in P$，

$$
p=\lambda a+\sum_{j=1}^r c_jb_j
\quad\Longrightarrow\quad\lambda\ge0.
\tag{197.2}
$$

$r=0$ 保留空和；邻点系数允许任意正负号。有限写法与(197.1)等价，因为任一 $W_a$ 向量可用至多 $\dim W_a\le d$ 个原邻点展开。它没有量化准备—效应张量、正删除或局部效应的全域延拓。

**定理 197.2（有向商的准确几何）。** SP$(a)$ 蕴涵 $\mathrm{LIN}(a):a\notin W_a$。在 LIN 下，令 $\pi_a:V\to V/W_a$ 为原线性商，则 SP$(a)$ 等价于

$$
\pi_a(P)\cap\{-t\pi_a(a):t>0\}=\varnothing.
\tag{197.3}
$$

同样，它等价于 $S_a=\mathbb Ra\oplus W_a$ 上的唯一线性系数函数

$$
\alpha_a(ta+w)=t
\quad\text{在 }P\cap S_a\text{ 上非负}.
\tag{197.4}
$$

证明。若 $a\in W_a$，取 $p=a,\lambda=-1$，有 $p-\lambda a=2a\in W_a$，违反 SP。故商中的 $\pi_a(a)$ 非零，目标系数唯一。等式 $p-\lambda a\in W_a$ 恰为 $\pi_a(p)=\lambda\pi_a(a)$，从而给(197.3)；同一唯一系数就是(197.4)。这是197.1的几何读法，不另外申领有限基抽取或商空间的新定理。$\square$

### 197.2 命中实际面使截面仍由原纯点生成

**定理 197.3（命中集的截面极点桥）。** 固定 $a\in P$，只假设 Hit$(a)$，不假设 L2。对每个包含 $N_a$ 的实线性子空间 $S\le V$，有

$$
\operatorname{ext}(K\cap S)=P\cap S,\qquad
K\cap S=\operatorname{conv}(P\cap S),\qquad
C\cap S=\operatorname{cone}(P\cap S).
\tag{197.5}
$$

空截面时凸包取空集，正锥生成取含零的有限非负和。这里没有预设原纯点集闭或最小实际面闭。

证明。设 $x\in\operatorname{ext}(K\cap S)$ 却不是原纯点。有限维紧凸生成使 $x$ 有原纯点的有限凸分解；非纯性使至少两个不同的原纯点 $p,q$ 以正系数出现。每个含 $x$ 的实际面都含这些分解点，故它们都属于最小实际面 $F_K(x)$。于是

$$
F_K(p,q)\subseteq F_K(x).
\tag{197.6}
$$

Hit 给一个 $b\in N_a\cap F_K(p,q)$。由于 $N_a\subseteq S$，有 $b\in S\cap F_K(x)$；$b$ 原纯而 $x$ 非纯，故 $b\ne x$。点 $x$ 位于其最小面的相对内部，因而存在 $\varepsilon>0$ 使

$$
y=x+\varepsilon(x-b)\in F_K(x),\qquad
x=\frac{\varepsilon}{1+\varepsilon}b+
\frac1{1+\varepsilon}y.
\tag{197.7}
$$

$y$ 也属于 $S$，且 $b,x,y$ 不同，矛盾于截面极点性。这个延伸只在最小面的相对内部进行，无需将该面替成其闭包。反向，原极点落在截面内便仍是截面极点。对紧凸集 $K\cap S$ 再用有限维极点生成给第二式；任何非零 $c\in C\cap S$ 都按原严格正单位写成 $c=u(c)k$、$k\in K\cap S$，给第三式。

有限维紧凸生成、最小面的相对内部及支撑分离是成熟凸几何工具，参见 [Q197R, §§11,18]；本条新增的接合是 Hit 排除线性截面中的新极点。它不是一般线性截面自动保持原极点的断言。$\square$

### 197.3 从纯系数到原共同正支撑

**定理 197.4（逐标签纯系数与不塌缩等价）。** 在197.1的同一完整原域中，NC$(a)$ 总蕴涵 SP$(a)$。若另给 Hit$(a)$，则

$$
\boxed{\quad
\mathrm{SP}(a)\quad\Longleftrightarrow\quad
\mathrm{NC}(a):a\notin F_K(N_a).
\quad}
\tag{197.8}
$$

在 Hit$(a)$ 下，它们还等价于 LIN$(a)$ 加上 $\alpha_a\ge0$ 于整个 $C\cap S_a$。等价只要求该标签的命中；没有用其他标签的 SP。

证明。SP 先由197.2给 LIN，故 $\alpha_a$ 良定义。SP 恰使它在 $P\cap S_a$ 非负。197.3用于 $S=S_a$，遂给

$$
\alpha_a(C\cap S_a)\subseteq\mathbb R_+.
\tag{197.9}
$$

若 $z\in W_a\cap\operatorname{int}C$，充分小的 $\varepsilon>0$ 使 $z-\varepsilon a\in C\cap S_a$，其 $\alpha_a$ 值却为 $-\varepsilon$，矛盾。因此

$$
W_a\cap\operatorname{int}C=\varnothing.
\tag{197.10}
$$

分离实线性子空间 $W_a$ 与开凸集 $\operatorname{int}C$，取得非零 $g\in V^*$，满足 $g|_{W_a}=0$ 且 $g\ge0$ 于 $\operatorname{int}C$。原锥闭且生成，故 $\overline{\operatorname{int}C}=C$，所以 $g\in C^*\setminus\{0\}$。这一标准分离步骤没有假设 $C+W_a$ 闭或正延拓定理。

此时直接调用 XIII160.10 的全称严格性：完整原菜单使每个消去 $N_a$ 的非零正泛函都满足 $g(a)>0$，并给 NC$(a)$。该供应的关键不是令 $g/g(a)$ 自动 proper；它取 $g$ 的原纯最大点和原单位归一化，再以补效应排除 $g(a)=0$。这里准确使用其正支撑结论，不提前声称共同确认或 least。

反向，NC 由同一160.10供应 $g\in C^*\setminus\{0\}$、$g|_{W_a}=0$、$g(a)>0$。若原纯点 $p=\lambda a+w$，则

$$
\lambda=g(p)/g(a)\ge0.
\tag{197.11}
$$

这给 SP，且不需要 Hit。对整个 $C\cap S_a$ 同样成立，故给最后的等价。$\square$

**命题 197.5（不遵守时的两类有限后果）。** 在 Hit$(a)$ 下，NC$(a)$ 失败当且仅当 SP$(a)$ 失败。其失败可按两类区分：

1. $a\in W_a$，即旧的线性回卷；此时 $p=a,\lambda=-1$ 已是 SP 负证书。
2. $a\notin W_a$，但存在不同于 $a$ 的原纯点 $p$ 及 $\lambda<0$，使 $p-\lambda a\in W_a$。

第二类仍有至多 $d-1$ 个原邻点的有符号展开。只给 LIN 排除第一类；本命题没有证明全标签 LIN 也排除第二类。

证明。197.4先给失败的等价和负证书的存在。若 LIN 成立，系数唯一且 $\alpha_a(a)=1$，负系数的 $p$ 不能等于 $a$；又 $\dim W_a\le d-1$，取其中原邻点基即得有限界。

还可从原混态内部直接看到第二类。若 NC 失败，160.10排除任何非零正泛函消去 $W_a$，由前段分离的逆否有 $z\in W_a\cap\operatorname{int}C$。取 $x=z-\varepsilon a\in C\cap S_a$，$\alpha_a(x)=-\varepsilon$。197.3将 $x$ 写成原纯点的有限非负和；至少一个原纯项必须有负 $\alpha_a$，它就是所需 $p$。负系数不是测试给出的负概率，而是原准备之间确实成立、却翻转目标方向的线性关系。$\square$

### 197.4 不经切向闭合的完整几何候选

**定理 197.6（单系统的命中—单侧候选）。** 在197.1的原域上，下列等价：

$$
\boxed{\quad
\mathrm{L2}+\forall a\in P\,[\mathrm{Hit}(a)+\mathrm{SP}(a)]
\quad\Longleftrightarrow\quad
\exists n\ge1,\ \theta:V\overset\sim\longrightarrow
\operatorname{Herm}_n(\mathbb C):
\ \theta(C)=\operatorname{PSD}_n,\quad u=\operatorname{Tr}\circ\theta.
\quad}
\tag{197.12}
$$

所有对象都沿同一个原实线性同构运输。左侧没有 TC、全混态零凸性、正删除或预给的矩阵商。

证明。197.4先给全标签 NC。L2+Hit 给 AD：取任何实际二元球 $B$ 和球内纯点 $a$，Hit 给 $b\in N_a\cap B$。原区分效应在整个 $B$ 上取值于 $[0,1]$，于 $a,b$ 达到一、零。三球上非恒定仿射函数的最大、最小点唯一且互为对径，故 $b$ 正是 $a$ 的几何对径。这个步骤只使用179.3证明中的球内极值部分，无需其混态零凸性前件。于是准确达到 XIII162.10 的 L2+NC+AD，直接复用其完整单系统分类。

反向，在完整复矩阵底中，$a=P_v$ 的原邻点恰为 $P_w$、$w\perp v$。任意二点实际球的复二维支持 $U$ 满足 $\dim(U\cap v^\perp)\ge1$，给 Hit，包括球外的 $a$。原正泛函 $X\mapsto\operatorname{Tr}(P_vX)$ 消去全部 $N_a$ 且在 $a$ 取一，故由(197.11)给 SP；实际二点底为三球，给 L2。$n=1$ 时 $K$ 单点，Hit 与 L2 为空量词，$N_a=\varnothing$，SP 直接成立。$\square$

**定义 197.7（三复制候选的全部背景）。** 完整采用 XIII162.15 的强实全有限背景：对每个有限 $N\ge1$，原空间 $W_N=V^{\otimes_{\mathbb R}N}$，原锥 $C_N$ 闭、尖、生成，严格正乘法单位 $u_N=u^{\otimes N}$；每层保留全部原纯点和完整效应。对所有分块 $a+b=N$ 有原 min/max 张量包含，全部位置置换及其逆在整个锥上正，两个括号使用同一原规范识别，并保留标量层。只在整个三复制底要求

$$
\mathsf Q_{\rm incidence,sign}
:=\mathrm{L2}_3+
\forall a\in P_3\,[\mathrm{Hit}_3(a)+\mathrm{SP}_3(a)].
\tag{197.13}
$$

量词包括所有纠缠纯点、所有实际二点面及全部原线性准备关系。球的仿射三维与检查整个三复制系统是两种不同的“三”。

**定理 197.8（共同复几何及所有有限层）。** 在197.7的精确背景下，$\mathsf Q_{\rm incidence,sign}$ 当且仅当存在同一个整数 $n\ge1$ 和同一个实线性同构 $\theta:V\overset\sim\longrightarrow\operatorname{Herm}_n(\mathbb C)$，使对每个有限 $N\ge0$，

$$
\Theta_N=\theta^{\otimes N},\qquad
\Theta_N(C_N)=\operatorname{PSD}_{n^N},\qquad
u_N=\operatorname{Tr}\circ\Theta_N.
\tag{197.14}
$$

证明。197.6只先用于整个 $(W_3,C_3,u_3)$，从三复制候选取得同域的 L2+NC+AD。此时才调用162.16的 $\mathsf R_3$ 入口；其 pure-spectator 实际面、共同复方向及全有限传播供应同一个 $\theta$ 的(197.14)。反向在每个标准复矩阵层使用197.6的矩阵反向。标量层取空张量，$n=1$ 包括所有一维层；$\dim V>1$ 时必有 $n\ge2$。没有另行分类各层后直接宣告坐标相同。$\square$

### 197.5 局部更弱的条件及其准确边界

**命题 197.9（SP 不等于单项正删除）。** 在195.7的旧平衡单核商 $H=\operatorname{diag}(I_m,-I_m)$、$m\ge3$ 中，令

$$
v=(e_1+f_1)/\sqrt2,\qquad
w=(e_1-f_1)/\sqrt2,\qquad a=p_v.
\tag{197.15}
$$

这个同原完整菜单模型保留 L2、TC、AD 及所有标签的 Hit；在标签 $a$ 上 SP 成立而 $\mathrm{FC}_1(a)$ 失败。它是既有模型的点态分离应用，不是全标签 SP 或全标签 LIN 的反模型。

证明。193.7给全原 AD，原纯点及二点实际面对应由 XIV165 的商模型供应；复二维支持与 $v^\perp$ 必有交，故全标签 Hit。$v^*Hv=0$，所以矩阵 $P_v$ 是原合法效应，其消去全部原邻点且在 $a$ 取一；(197.11)给 SP。更明确地，旧商关系给

$$
p_{e_1}-\frac12a
=\frac12p_w+
\frac12\sum_{i=2}^m(p_{f_i}-p_{e_i})\in W_a.
\tag{197.16}
$$

右侧每个原纯点都与 $v$ 正交，原 AD 使其确为原邻点。另一方面 $E=P_{f_1}+P_{e_2}$ 满足 $0\le E\le I$ 且 $\operatorname{Tr}(EH)=0$，是同一个完整原菜单中的效应，而

$$
E\!\left(p_{e_1}-\frac12a\right)=-\frac14.
\tag{197.17}
$$

194.2的 $\mathrm{FC}_1(a)$ 正规形要求 $\delta_a(P\cap S_a)\subseteq C$，其中 $\delta_a p=p-\alpha_a(p)a$；(197.16)的目标系数为 $1/2$，(197.17)排除这个删除像的正性。因此 $\mathrm{FC}_1(a)$ 失败，与195.7第二行一致。SP 约束的是目标系数非负，FC$_1$ 约束的是删去目标后的余项为正，两个条件不能互换。$\square$

### 197.6 熟悉量子公理的条件字典与更简结构

**命题 197.10（量子字典及三种关系的分工）。** 在197.8的全部前件下，完整量子字典由同一个 $\Theta_N$ 给出：

| 熟悉结构 | 由新候选得到的对应及保留的条件 |
| --- | --- |
| Hilbert 空间、纯态、叠加、混态 | $\mathcal H_N=(\mathbb C^n)^{\otimes N}$；全部原纯点为 $\mathbb{CP}^{n^N-1}$，全部原归一态为迹一 PSD；复线性叠加在该 Hilbert 空间中取射线 |
| Born、效应、测量 | 原配对为 $e(x)=\operatorname{Tr}(E\Theta_Nx)$，整个原效应区间恰为 $0\le E\le I$；同一 least 确认者在纯输入读 $|\langle v,w\rangle|^2$，并在全部混输入线性延拓；Hermitian 谱与单位正分解分别给数学 PVM、POVM |
| 复合、纠缠、约化 | 同一个 $\theta$ 保持原产品、位置置换、括号及原单位；原边缘对应偏迹，各层含全部纠缠态 |
| 分支、通道、仪器 | 另要求原线性映射在每个有限旁观者下保持整个正锥，才恰得 CP；全输入质量不增或保持给 Kraus 预算，保质量的有限分支族给数学仪器 |
| 理想锐中性更新 | 另给投影效应和逐点固定其读一原纯态的正分支，才得 $X\mapsto PXP$ |
| 连续可逆动力学 | 另给连续、保原锥和原单位的实参数群，才得 $X\mapsto e^{-itH}Xe^{itH}$；物理时间、能量与 $\hbar$ 的标定另需经验对应 |

证明。197.14是162.16的相同结论，表中全部对应及附加条件直接消费162.9的字典，未重证已有过程分类，也未把每个数学效应、分支或测试族的存在宣告成实际设备的完备实现。

新入口的几何只分三种关系：L2 固定每个二点实际面的形状；Hit 要求每个纯标签的原邻点集合命中每条纯点线；SP 固定由原邻点线性张成所作商中的目标半轴方向。它先在原线性截面上排除新极点，再使目标系数具有原正支撑，最后消费既有复几何分类。重建后，纯点线就是 $\mathbb{CP}^1\cong S^2$，$N_a$ 是复射影正交超平面。在任意固定的第 $N$ 层置 $D=n^N$，以下各原对象沿 $\Theta_N$ 运输至 $\operatorname{Herm}_D(\mathbb C)$；若 $a=P_v$，则

$$
W_a=\operatorname{Herm}(v^\perp),\qquad
S_a=\mathbb RP_v\oplus\operatorname{Herm}(v^\perp),\qquad
\alpha_a(X)=\operatorname{Tr}(P_vX)\quad(X\in S_a).
\tag{197.18}
$$

$W_a$ 在该层的原实余维为 $2D-1$，$S_a$ 的余维为 $2D-2$；入口三复制层取 $D=n^3$。$D>1$ 时，“纯点超平面”不是原实空间里的余维一超平面；$D=1$ 时 $N_a$ 为空、$W_a=0$、$S_a=\operatorname{Herm}_1(\mathbb C)$。商图不提前把纯点线当普通实直线。相较195的入口，这里不输入 TC 或切方向；新增的纯生成桥让原纯系数的单侧性已经足够。不过没有证明 Hit+SP 由裸全标签 LIN 导出，亦没有证明独立公理数严格减少。

196.2从删除余项的截面正性得到全域正删除，保留其明确的邻锥单纯前件；197.4借助197.3从原纯系数的单侧性得到该系数在整个截面上非负，不要求邻锥单纯，也未供应删除余项的全域正延拓。两条桥处理不同的正性，不能互相替代。

承重新增197.3与197.4是原实际面命中、截面纯生成和纯系数符号之间的 repo-derived 接合。197.2的有限线性代数、分离、最小面相对内部及紧凸生成是成熟工具；原正支撑严格性归160.10，完整分类、全有限传播与量子字典归162.10、162.16及162.9。旧平衡商仅用于197.9的点态边界，不申领新反模型或文献优先权。$\square$

**命题 197.11（完整白话与尚未消去的条件）。** 197.7的候选可以完整表述为：保留系统本来的全部准备、测试和任意有限复合，只在整个三份系统上查看三件事。任意两个不同纯准备撑起一颗实际三球；对任意目标纯准备，所有能与它确定区分的纯准备，必须碰到每颗这样的球；把这些可区分准备的线性张成压成零后，任何原纯准备都不能落到目标的反向半轴。这些条件约束同一批原定义之间的关系，不另外输入 Hilbert 空间、Born 公式、正删除或切向闭合。

证明及图景。若线性截面里冒出一个并非原纯的新极点，它原本属于一个含不同纯点的实际面。命中律会从这个面中找出一个仍在截面内的原邻点；沿这点穿过新极点再走一点，便得到截面内的一条真线段，否定极点性。因此截面没有夹生的新尖角，全部混态都由原纯点填满。纯点不许反向，便使整个截面的目标系数非负。若邻点张成还能穿入整个正锥内部，轻轻减掉一点目标仍会留下正准备，却得到负系数，发生矛盾；所以它必须留在原锥边界的一侧。原完整测试随后供应一张同时消去全部邻点的正支撑；球上的一与零将相交邻点钉成对径，已有重建把这些小球接成同一复射影几何和全部有限复矩阵层。Born 和复张量由此得到，过程与时间各在197.10列明的条件下接上。

这里的内生化，是把新候选写成原准备、原效应、实际面及原线性关系的相容约束；没有把所选原概率载体与这三条约束宣称成无前提真理。若想再只留 LIN，必须证明它同时禁止197.5第二类的纯准备负系数；这一联合命题尚未在当前推导中成立。$\square$

[Q197R]: https://doi.org/10.1515/9781400873173 "R. T. Rockafellar, Convex Analysis；§§11,18的有限维分离、面与相对内部工具，沿用XIII160.10的工具归属。"

## 追加锚（本行以下为增补区）

## 198. 邻点是纯配置的平坦集，整纯域是二维丛的单点紧化

### 198.1 去掉符号，只检查邻张成中有没有额外纯点

**定义 198.1（原纯配置中的平坦条件）。** 保留197.1的完整有限维原域及全部记号。L2 仍表示每个不同原纯对的最小实际面是整颗仿射三维闭球。记 $B(p,q)=F_K(p,q)$，其纯点线为 $\ell_B=P\cap B=\partial_{\rm rel}B$。不同纯点唯一确定该线：三球的非空真面只有单点。置

$$
\mathrm{Flat}(a):\qquad
P\cap W_a=N_a,\qquad W_a=\operatorname{span}_{\mathbb R}N_a.
\tag{198.1}
$$

这是原向量配置 $P\subset V$ 的线性拟阵平坦集条件：邻点集合已经包含其线性张成里的全部原纯点。它不选择商半轴、系数符号、正泛函或内积。有限维写法是：原纯点 $p$ 若是至多 $\dim W_a$ 个原邻点的实线性组合，则 $a\#p$；空和也保留。若 $N_a=\varnothing$，则 $W_a=0$，因 $u(p)=1$ 而 Flat 自动成立。

**引理 198.2（单标签的连续对径投影）。** 在 L2 与固定标签 Hit$(a)$ 下，有唯一连续映射

$$
\beta_a:P\setminus\{a\}\longrightarrow N_a,
\qquad
\beta_a(p)=a\text{ 在 }B(a,p)\text{ 内的对径点}.
\tag{198.2}
$$

它固定 $N_a$；每个不含 $a$ 的实际二点球的纯点线连续嵌入 $N_a$。

证明。Hit 给 $b\in N_a\cap B(a,p)$。原效应在球上取值于 $[0,1]$，在 $a,b$ 读一、零；球上非恒定仿射函数的两个极值点唯一且对径。因此这个 $b$ 唯一。反向，若 $p\in N_a$，同一极值论证给 $\beta_a(p)=p$。

连续性不能预设实际面映射连续。暂选辅助 Euclidean 坐标。若 $p_j\to p\ne a$，写

$$
B(a,p_j)=c_j+A_j\overline{\mathbb B}^{,3},
\qquad \|A_j\|\le\tfrac12\operatorname{diam}K.
\tag{198.3}
$$

因为 $c_j\pm A_js\in K$，上界成立；球心也在紧 $K$ 中。任一子列可再取 $c_j\to c,A_j\to A$，极限椭球 $Q=c+A\overline{\mathbb B}^{,3}\subset K$ 含不同的原纯点 $a,p$。它们也是 $Q$ 的极点；正秩椭球严格凸，所以 $(a+p)/2\in\operatorname{ri}Q$。包含此中点的原面 $B(a,p)$ 必含整个 $Q$：对任意 $y\in Q$，从 $y$ 穿过中点可在 $Q$ 内再延长一点，随后用面性。这里允许 $A$ 降至秩一或二。

记 $b_j=2c_j-a$，选原见证 $e_j(a)=1,e_j(b_j)=0$。完整效应区间紧，故可再取 $e_j\to e\in\mathcal E$。极限 $b=2c-a\in Q\subset B(a,p)$ 满足 $e(a)=1,e(b)=0$，球极值唯一性迫使 $b=\beta_a(p)$。每个聚点都相同，给连续性；未预设 $P$ 闭。

最后，若球 $D$ 不含 $a$，不同 $p,q\in\ell_D$ 有同一个像 $b$，则 $B(a,b)$ 含 $p,q$，必等于 $D$，矛盾。连续单射从紧 $S^2$ 到 Hausdorff 空间是嵌入。$\square$

**定理 198.3（额外纯零点与负弧等价）。** 在 L2 与 Hit$(a)$ 下，

$$
\boxed{\quad
\mathrm{Flat}(a)\quad\Longleftrightarrow\quad
\mathrm{SP}(a)\quad\Longleftrightarrow\quad
\mathrm{NC}(a).
\quad}
\tag{198.4}
$$

前一个等价实际上只使用 Hit 在过 $a$ 的实际二点球上的部分；后一个等价消费197.4的全线命中。

证明。若 $a\in W_a$，则 $a\notin N_a$ 使 Flat 失败；$a=(-1)a+2a$ 使 SP 失败。下设 $a\notin W_a$，令 $\alpha_a(ta+w)=t$ 是 $S_a=\mathbb Ra\oplus W_a$ 上的唯一系数函数。

若 SP 失败，取 $p\in P\cap S_a$ 满足 $\alpha_a(p)<0$，再取 $b=\beta_a(p)\in N_a$。三个球面点 $a,b,p$ 不共线，且 $a,b$ 对径；其仿射平面截出一张经过球心的完整椭圆盘 $D\subset B(a,p)\cap S_a$。圆周全部是原纯点。$\alpha_a$ 在 $a,b,p$ 读 $1,0,<0$，所以零直线穿过圆盘内部，除 $b$ 外还与圆周相交于第二点 $d$。于是 $d\in P\cap W_a$；但球中能与 $a$ 原确定区分的纯点只有其对径 $b$，故 $d\notin N_a$，Flat 失败。

反向，若 $d\in(P\cap W_a)\setminus N_a$，令 $b=\beta_a(d)$。$a,b,d$ 的中心圆盘仍包含于 $S_a$。$\alpha_a$ 在不同圆周点 $b,d$ 为零、在 $a$ 为一；弦 $bd$ 另一侧的非空开圆弧上必为负。任取该弧上的原纯点就违反 SP。最后直接应用197.4。$\square$

**命题 198.4（三个实方向内的完整失败证书）。** 在198.3中 LIN 成立但 Flat 失败时，上述圆盘的三维线性张成内可选坐标，使原盘锥及其强制系数为

$$
\begin{gathered}
t\ge\sqrt{x^2+z^2},\qquad
a=(1,0,1),\quad b=(1,0,-1),\\
\alpha_a(t,x,z)=\frac{t+z}{2}+\kappa x,
\qquad \kappa\ne0.
\end{gathered}
\tag{198.5}
$$

原纯圆周上的最小值与第二零点分别是

$$
\frac{1-\sqrt{1+4\kappa^2}}2<0,\qquad
d=\left(1,\frac{-4\kappa}{1+4\kappa^2},
                \frac{4\kappa^2-1}{1+4\kappa^2}\right).
\tag{198.6}
$$

证明。中心椭圆盘经仿射圆化后取 $u=t$，把对径放在 $z$ 轴，$\alpha_a(a)=1,\alpha_a(b)=0$ 给(198.5)。若 $\kappa=0$，零线只在 $b$ 与圆相切，不会有第二纯零点。最小化 $1/2+\kappa x+z/2$ 于 $x^2+z^2=1$ 给第一式；将所列 $d$ 代入圆方程及 $\alpha_a=0$ 给第二式。该负值是原线性准备关系的系数，不能称原测试读出的负概率；任一消去 $W_a$、在 $a$ 取一的代数延拓都受它约束。$\square$

### 198.2 从全线命中到连续的整体纯几何

**定理 198.5（全命中使原纯域紧）。** 在197.1的原域中，若每个原纯标签都满足 Hit，则 $P$ 闭且紧。此结论不要求 L2、LIN、SP 或 NC。

证明。设 $a_j\in P$ 趋于 $x\in K$，而 $x$ 非纯。有限维紧凸生成给 $x$ 的有限纯分解；面性将各纯项留在 $F_K(x)$ 中，故其中可选不同 $p,q\in P$。Hit$(a_j)$ 给

$$
b_j\in N_{a_j}\cap F_K(p,q)\subset F_K(x),
\qquad e_j(a_j)=1,\quad e_j(b_j)=0.
\tag{198.7}
$$

完整原效应区间紧，抽取 $e_j\to e$，得 $e(x)=1$。原读一面 $\{e=1\}\cap K$ 包含 $F_K(x)$，所以 $e(b_j)=1$。但有限维效应收敛在紧 $K$ 上一致，$e_j(b_j)=0$ 矛盾。故极限仍纯。这里没有假设最小面本身闭。$\square$

**定理 198.6（整个实际球及其内禀度量连续）。** 在 L2 与全标签 Hit 下，非对角原纯对的映射

$$
(p,q)\longmapsto B(p,q)
\tag{198.8}
$$

按 Hausdorff 距离连续。球心、三维方向空间及确定该椭球的内禀正定二次型连续；原 $\#$ 闭，$a\mapsto N_a$ 是非空紧集族的 Hausdorff 连续映射。后两项限于 $K$ 非单点时。

证明。设不同纯对 $(p_j,q_j)\to(p,q)$，$p\ne q$，照(198.3)抽取极限椭球 $Q=c+A\overline{\mathbb B}^{,3}$。198.2中的中点论证给 $Q\subset B(p,q)$。每个 $s\in S^2$ 满足 $c_j+A_js\in P$；198.5给 $c+As\in P$。若 $\operatorname{rank}A<3$，则 $A(S^2)=A(\overline{\mathbb B}^{,3})$，所以整个 $Q$ 都纯，与 $p,q\in Q$ 不同矛盾。故 $\operatorname{rank}A=3$，且 $\partial Q\subset P\cap B(p,q)=\partial B(p,q)$。

这个嵌入 $S^2\hookrightarrow S^2$ 由不变域及紧性满射，故 $Q=B(p,q)$。每个聚限相同，给整球连续。球的中心、方向和椭球二次型由该球唯一决定；亦可由 $A_jA_j^{\mathsf T}$ 及其在三维像上的逆看出连续性。不变域在这里按 [Hatcher, AT, 2B.3–4][Q198AT] 使用。

若 $a_j\#b_j$ 且纯对趋于 $(a,b)$，原见证效应的紧性给 $a\#b$，故闭图。各 $N_a$ 非空且紧。上半连续由闭图与 $P$ 紧给出；对任意 $b\in N_a$ 及 $a_j\to a$，最终 $a_j\ne b$，而 $\beta_{a_j}(b)$ 是 $B(a_j,b)$ 的对径点，由球心连续而趋于 $b$，给下半连续。$\square$

**定理 198.7（从一个纯点展开的二维实丛）。** 在 L2、全标签 Hit 与非单点背景下，固定任意 $a\in P$。对每个 $b\in N_a$，记 $B(a,b)$ 的方向空间为 $E_b$，中心 $m_b=(a+b)/2$，$d_b=(b-a)/2$。以唯一正定二次型 $q_b$ 将该球写成 $m_b+\{x\in E_b:q_b(x)\le1\}$。置

$$
T_b=\{z\in E_b:\langle z,d_b\rangle_{q_b}=0\},
\qquad \mathscr T_a=\coprod_{b\in N_a}T_b.
\tag{198.9}
$$

则 $\mathscr T_a\to N_a$ 是平凡环境实丛中的连续秩二子丛，且有保持零截面的同胚

$$
P\setminus\{a\}\cong\operatorname{Tot}(\mathscr T_a),
\qquad N_a\longleftrightarrow\text{零截面},
\qquad
P\cong\operatorname{Th}(\mathscr T_a).
\tag{198.10}
$$

特别地，$P\setminus\{a\}$ 强形变收缩到 $N_a$。这里是二维**实**向量丛，不预送复结构或原仿射对称群。

证明。198.6使 $E_b,q_b,d_b$ 连续，且 $q_b(d_b)=1$，故(198.9)是连续的二维核子丛。每个 $p\ne a$ 对应唯一 $b=\beta_a(p)$，位于球 $B(a,b)$ 的纯边界。写 $p=m_b+x$、$t=\langle x,d_b\rangle_{q_b}$，从 $a$ 作立体投影给

$$
z=\frac{2(x-td_b)}{1+t}\in T_b.
\tag{198.11}
$$

$t=-1$ 仅对应被删去的 $a$。反向，对 $z\in T_b$ 令 $r=q_b(z)/4$，则

$$
p=m_b+\frac{(1-r)d_b+z}{1+r}.
\tag{198.12}
$$

直接代入得 $q_b(p-m_b)=1$，而 $p\ne a$，其对径邻点正是 $b$。两式互逆且连续；$z=0$ 恰对应 $b$。纤维缩放 $(b,z)\mapsto(b,(1-s)z)$ 给强形变收缩。198.5使 $P$ 紧；$a$ 在任一过它的纯球面上非孤立，所以 $P$ 是 $P\setminus\{a\}$ 的单点紧化。对紧底上的实向量丛，单点紧化等于盘丛把整个球丛压成一点的 Thom 空间，使用 [Hatcher, VBKT, §4.1][Q198VB]；由此给最后一式。$\square$

### 198.3 一个标签的临界维数及其不应越过的范围

**定理 198.8（非整球邻空间至少四维，达到下界即自动正支撑）。** 仅假设 L2 与固定标签 Hit$(a)$。若 $K$ 非单点且不是整颗三球，则

$$
w_a:=\dim W_a\ge4.
\tag{198.13}
$$

若 $w_a=4$，则 $H_a=K\cap W_a$ 是一颗实际二点面球，$N_a=\partial_{\rm rel}H_a$，且该标签满足 NC、SP 和 Flat。单点域的 $w_a=0$；整三球的 $w_a=1$，也满足这三项。

证明。若所有二点球都含 $a$，取一颗球 $B$。假如有原纯点 $r\notin B$，取 $q\in\ell_B\setminus\{a\}$，则 $B(r,q)$ 与 $B$ 共含不同纯点 $a,q$，所以相等，矛盾。故纯点全在 $B$，紧凸生成给 $K=B$。因此非整球时存在不含 $a$ 的实际球 $D$。

198.2给嵌入 $S^2\cong\ell_D\hookrightarrow N_a$。因为归一化邻点张成 $W_a$，截面 $H_a$ 的仿射维数为 $w_a-1$；其所有邻点仍是极点，因而位于相对边界。$w_a\le3$ 时，不可能把 $S^2$ 连续嵌入一维凸体边界或二维凸体边界 $S^1$；后者亦可嵌入 $\mathbb R^2$，由不变域否定紧 $S^2$ 到 $\mathbb R^2$ 的连续单射。因此 $w_a\ge4$。

若 $w_a=4$，$\partial_{\rm rel}H_a\cong S^2$。上述嵌入由不变域及紧性占满边界，所以 $N_a=\partial_{\rm rel}H_a$。边界全是原纯点，使 $H_a$ 严格凸。取不同 $b,c\in N_a$，中点位于 $\operatorname{ri}H_a$；面性使实际球 $B(b,c)$ 包含整个 $H_a$。两者仿射维数均三，而 $H_a=K\cap\operatorname{aff}H_a$，故两者相等。$a$ 不在此面，否则也是其边界原纯点，即 $a\in N_a$，矛盾。于是 $F_K(N_a)=H_a$ 排除 $a$，给 NC；198.3给其余等价。单点和整球分支直接由原定义及球极值给出。$\square$

**推论 198.9（低维标签的自动支付与受限分类）。** 在 L2+全标签 Hit 下，只有 $w_a\ge5$ 的标签还需要额外输入 Flat 或 SP。并且

$$
\mathrm{L2}+\forall a\in P\,[\mathrm{Hit}(a),\ w_a\le4]
\quad\Longleftrightarrow\quad
\text{完整保单位复 }\operatorname{PSD}_n,\quad 1\le n\le3.
\tag{198.14}
$$

证明。198.8逐标签给 NC，直接消费 XIII162.10 的 L2+AD+NC 分类；AD 由197.6的球内命中论证供应。标准 $\operatorname{PSD}_n$ 的 $W_{P_v}=\operatorname{Herm}(v^\perp)$，故 $w_a=(n-1)^2$，给 $n\le3$ 与反向。

这个受限维数条件不能放进整个非平凡三复制底充当普适量子候选：197.7的强实背景使其空间维数为整数立方 $(\dim V)^3$，而(198.14)只容许维数 $1,4,9$。非平凡整数立方不在其中。这是受限分类的边界，不是否定完整候选。单标签达到 $w_a=4$ 在198.8中只用于该标签结论，本条没有由此声称整个原锥已被识别。$\square$

### 198.4 不选择方向的完整候选与量子字典

**定义 198.10（三复制的命中—平坦候选）。** 保留197.7的全部强实全有限背景、原单位、全部准备与完整菜单，只在整个原三复制底要求

$$
\boxed{\qquad
\mathsf Q_{\rm incidence,flat}
:=\mathrm{L2}_3+
\forall a\in P_3\,[\mathrm{Hit}_3(a)+\mathrm{Flat}_3(a)].
\qquad}
\tag{198.15}
$$

**定理 198.11（同一个坐标的所有有限复量子层）。** 在198.10背景中，候选(198.15)当且仅当存在同一个 $n\ge1$ 和同一个实线性同构 $\theta:V\overset\sim\longrightarrow\operatorname{Herm}_n(\mathbb C)$，使对每个有限 $N\ge0$，

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{n^N},
\qquad u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{198.16}
$$

证明。198.3在整个 $K_3$ 逐标签将 Flat 与 SP 互换，得到与197.13完全相同的候选，随后直接消费197.8。反向同理。按198.9，也可只在 $w_a\ge5$ 的标签输入 Flat，低维标签自动满足；没有因此证明实际三复制量子域的检查成本严格下降。

197.10的同一坐标字典完整保留：

| 原定义或另外条件 | 所得量子对象及精确范围 |
| --- | --- |
| 全部归一态、原纯点、实际二点球 | 迹一 PSD、$\mathbb{CP}^{n^N-1}$、复二维支持上的完整 Bloch 三球 |
| 全效应区间及原配对 | $0\le E\le I$ 与 $\operatorname{Tr}(E\rho)$；最低纯确认读数在纯输入上为 Born 平方模；总和为单位的有限效应族才给数学 POVM |
| 强全有限背景及同一个 $\theta$ | 同一复张量乘积、全部纠缠态、正置换、重括号及偏迹 |
| 全部有限旁观者下保正的原线性分支 | CP；另给全输入质量预算才给 TNI/TP，保总质量的有限分支族才给数学仪器 |
| 指定锐效应及逐点固定读一纯态的正分支 | 在197.10的锐中性条件下给 $X\mapsto PXP$ |
| 连续、保锥保单位的实参数可逆群 | 酉共轭的一参数形式；物理钟、能量及 $\hbar$ 的标定仍要经验对应 |

前三行是静态与复合重建；后三行各保留所列过程输入。数学效应、分支或测试族的存在不等于实际设备的实现完备性。

更大结构现在有两个准确层次。重建前，$N_a$ 是原纯向量配置中的平坦集，并命中每条纯点线；全命中另使整纯域等于其邻集上一个二维实丛的 Thom 空间。重建后，$N_a=\mathbb{CP}^{D-2}$，$P=\mathbb{CP}^{D-1}$，$D=n^N>1$；删去一点留下以该正交超平面为底的二维实丛，逐纤维正是 $\mathbb{CP}^1\setminus\{a\}$。这既没有把原实线性张成误认作复射影直线，也没有从单纯连续性提前推出正性、TC 或复线性结构。

相较197，新的简化是删去纯系数符号和目标商半轴，改为只查看“原邻点张成是否产生额外原纯点”。198.3证明这项改写保持完整重建能力；未证明独立经验前件的数目减少。更弱的全标签 LIN 只禁每个 $a$ 自己落进 $W_a$，尚未在当前推导中排除别的额外纯点；(198.6)精确标出了还需消去的局部障碍。$\square$

**命题 198.12（完整白话、反事实与工具归属）。** 候选(198.15)可以完整表述为：保留系统原有的全部准备、测试和任意有限复合，在整个三份系统上只看三件事。每两个不同纯准备撑起一颗实际三球；每个目标的全部可区分纯准备都碰到每颗这样的球；这些可区分准备的线性张成里，不能再冒出一个并不可区分的原纯准备。

证明及图景。最后一条若失败，先分清是否连目标自己也卷进了邻张成。若已卷入，$a=(-1)a+2a$ 直接给反向系数，不能再用两个不同纯点的球。若目标没有卷入，就把那个额外纯点与目标放进同一颗实际球，再找到目标的对径邻点。三点撑出一张过球心的圆盘；邻张成在圆周上已吞进对径点和另一个纯点，于是割出一条弦。弦的另一侧必出现反向的目标系数。反过来，在目标没有卷入的分支中，只要出现负系数，这张圆盘就一定交出第二个原纯零点。因此不需要先告诉理论哪边是正：只要求邻集在线性张成后不长出额外纯点，正支撑便由197.4内生。已有重建再把二点球接成同一复射影几何，并把全部有限层接成同一复矩阵张量理论；Born、混态和复合随之对应，过程和时间按198.11的额外条件接入。

整体画面也可在重建前直接看见：从一个纯点向其余所有纯点看，每个点落在一颗经过它的球上，球的另一端是唯一邻点。把每颗球删掉这一个共同端点，就摊成一张二维实平面；这些平面随邻点连续拼合，最后把所有远处压回同一点，恢复整个纯域。这个图景约束原定义之间的关系，不把所选概率载体与相容条件宣称成无前提宇宙定律。

198.3、198.5–8是原实际面、完整效应、纯配置和连续球丛之间的 repo-derived 接合，不申领文献优先权。圆盘极值、椭球紧性及拟阵平坦集是成熟工具；不变域按 [AT, 2B.3–4][Q198AT]，向量丛的盘/球商与单点紧化按 [VBKT, §4.1][Q198VB]，均只作为新桥内部的既有工具。正支撑、复分类、全有限传播及过程条件分别复用197.4、197.6、197.8与197.10；198.11没有另立已有分类的证明。$\square$

[Q198AT]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology, §2.B, Theorem 2B.3 and Corollary 2B.4：不变域及紧同维流形嵌入的满射性。"
[Q198VB]: https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf "Allen Hatcher, Vector Bundles and K-Theory, §4.1 Thom Spaces：紧底丛的Thom空间是总空间的单点紧化。"

## 追加锚（本行以下为增补区）

## 199. 一张四维邻屏已确定整个三能级系统

**定义 199.1（单标签临界候选）。** 保留197.1的完整原锥、原单位、全部纯准备及整个原效应区间，仍以198.1的实际球 $B(p,q)$ 和纯点线 $\ell_B$ 表示 L2 几何。只要求

$$
\mathsf Q_{\rm one,4}:=\mathrm{L2}
+\exists a\in P:\quad
\mathrm{Hit}(a),\qquad \dim W_a=4.
\tag{199.1}
$$

维数是原实线性张成维数。另给不读取线性张成的几何写法：

$$
\mathsf Q_{\rm one,screen}:=\mathrm{L2}
+\exists a,b,c\in P:\quad
b\ne c,\quad B(b,c)\subsetneq K,\quad
N_a\subset B(b,c),\quad\mathrm{Hit}(a).
\tag{199.1a}
$$

它只要求一个标签的全部邻点容纳在同一颗真实际二点球内，并命中每条线。两个写法在199.2中证明等价。除了所选标签，其他标签的命中、Flat、SP、NC及共同确认者都不预给。这是三能级单系统候选；它不替代198.15的任意大小全有限候选。

**定理 199.2（一张邻屏迫成实际射影平面）。** 在199.1下，$H=K\cap W_a$ 是实际二点球，$N_a=\ell_H$，且 $a\notin H$。每两条不同纯点线恰交一点；全部非空真面恰为纯单点与实际二点球。因此原面格是射影平面的子空间格；纯点空间 $P$ 与球线空间 $\mathcal L$ 紧、连通，定秩的 join、meet 连续。

证明。先核对两个入口。若(199.1a)成立，$N_a\subset B(b,c)$ 使 $w_a\le4$；真二点球排除单点和整三球，198.8使 $w_a\ge4$，所以得到(199.1)。反向，198.8从(199.1)给真实际球 $H=K\cap W_a$ 及 $N_a=\ell_H$，任选其中不同纯点 $b,c$ 即给(199.1a)。以下使用这个 $H$，不调用其他标签的命中。若实际球 $D$ 不含 $a$，198.2给连续单射

$$
\beta_a:\ell_D\longrightarrow\ell_H,
\qquad S^2\longrightarrow S^2.
\tag{199.2}
$$

不变域与紧性使它满射。故 $D$ 命中每条过 $a$ 的纯点线：任意该线都写成 $\ell_{B(a,b)}$，$b\in\ell_H$，而(199.2)的逆像就在它与 $D$ 的交中。两条过 $a$ 的线本已相交。因此每条线都遇到每条过 $a$ 的线。

还需把这一结论传到普通中心。固定纯点 $x$ 及不经 $x$ 的球线 $L$。若相关连接线 $B(x,p)$ 都与 $L$ 唯一相交，则透视 $p\mapsto\ell_{B(x,p)}\cap\ell_L$ 连续：对 $p_j\to p\ne x$，交点在紧 $\ell_L$ 内取聚点；198.2证明中的椭球中点论证仅用 L2，就把聚点放入 $B(x,p)$。唯一交点锁定极限；这里没有预设 $P$ 闭或整个面映射连续。

假设两条线 $D,E$ 不交。若其中一条经过 $a$，前段已给矛盾；故取 $x\in\ell_D$ 时 $x\ne a$。选一条经过 $a$ 且不经 $x$ 的线 $L$；它存在，否则所有过 $a$ 的线都等于 $B(a,x)$，将全部纯点及 $K$ 压成一球，与198.8给出的真球 $H$ 矛盾。从 $x$ 将 $\ell_E$ 透视到 $\ell_L$，前段给连续性，二点定线给单射。这个 $S^2\to S^2$ 又是满射。取 $y=D\cap L$，便有 $p\in E$ 的连接线 $B(x,p)$ 经过 $y$，所以等于 $D$，违反 $D\cap E=\varnothing$。于是任两线相交；不同线至多有一个公共纯点。

若一个实际面含非共线三纯点，则它包含两条相交线。对这两线之外任意纯点 $z$，取第一线上异于交点的 $y$；线 $zy$ 与第二线交于 $t$，$y\ne t$，故整个 $B(y,t)$ 包含于该面，特别包含 $z$。因此该面包含全部 $P$，等于 $K$。任何非空面中的点都有原纯点有限分解，面性将纯项留在该面内，遂知所有真非点面只能是一条球。$K$ 不是整球，故有非共线三点；每线有无穷多点，在三角形两边取内部纯线点，再在它们的连接线上避开三边，即得非退化四边形。这准确给出射影平面及其完整子空间格，因而该面格模且不可约。

到此才应用 [Labardini-Fragoso–Neumann-Coto–Takane, Lemmas 2–3][Q199LF]：模面格的各定秩面集在 Hausdorff 拓扑下紧；不可约且非严格凸时，全部原极点是紧连通拓扑射影空间，定秩 join、meet 连续。这里的秩零面是原纯单点，秩一面是原实际球，故同时供应 $P$ 与 $\mathcal L$，没有提前假设面格模律。每两条线经过公共纯点，该点的线束由一条不过该点的球面连续参数化，故 $\mathcal L$ 也连通。这些是已发表工具，不另立紧性分类。$\square$

**定理 199.3（单标签候选的完整三能级等价）。** 在上述完整原域中，

$$
\boxed{\quad
\mathsf Q_{\rm one,screen}
\quad\Longleftrightarrow\quad\mathsf Q_{\rm one,4}
\quad\Longleftrightarrow\quad
\exists\theta:V\overset\sim\longrightarrow\operatorname{Herm}_3(\mathbb C):
\quad\theta(C)=\operatorname{PSD}_3,\qquad
u=\operatorname{Tr}\circ\theta.
\quad}
\tag{199.3}
$$

特别地，左侧已推出其他所有标签的 Hit、NC、SP 与 Flat，以及 $\dim V=9$；无需另给它们。

证明。先在199.2的原几何中，对每颗实际球 $B$ 取非零正支撑 $h$ 消去 $B$。它存在于球的相对内点处；因 $B$ 是 coatom，所得真零面正好是 $B$。原纯最大点 $r$ 满足 $M=h(r)=\max_Kh>0$，所以 $h/M$ 是真正的原效应，给 $\ell_B\subset N_r$。若还有 $c\in N_r\setminus\ell_B$，线 $B(r,c)$ 与 $B$ 的纯交点 $d$ 也在 $N_r$，却与 $c$ 不同；两者同为球 $B(r,c)$ 内 $r$ 的原邻点，违反对径唯一性。因此

$$
N_r=\ell_B.
\tag{199.4}
$$

这样的 $r$ 唯一。若 $N_r=N_s=\ell_B$ 且 $r\ne s$，线 $B(r,s)$ 与 $B$ 的交点 $d$ 同时原邻于 $r,s$；对称性使两者同为 $d$ 的球内对径，矛盾。由此取得单值根点映射

$$
\rho:\mathcal L\longrightarrow P,\qquad
N_{\rho(B)}=\ell_B.
\tag{199.5}
$$

它是单射。它也连续：若 $B_j\to B$，紧 $P$ 使根点有聚点 $r$；原完整效应的紧性给 $\#$ 闭图，而 [同文 Lemma 4(b)][Q199LF] 使 $\ell_{B_j}\to\ell_B$。所以 $\ell_B\subset N_r$，前述球内对径论证再给等号，唯一性迫 $r=\rho(B)$。不需要连续选择支撑 $h$。

接着只核对不变域的维数前件。对任一固定球线 $L_\infty$，取其上不同纯点 $q_1,q_2$，并取分别经过 $q_1,q_2$、不等于 $L_\infty$ 的轴线 $A_1,A_2$。纯点 $p\notin\ell_{L_\infty}$ 的两条方向线 $B(p,q_1)$、$B(p,q_2)$，分别与 $A_2,A_1$ 交于不在无穷线上的点。两交点给同胚

$$
P\setminus\ell_{L_\infty}
\cong(\ell_{A_2}\setminus\{q_2\})
\times(\ell_{A_1}\setminus\{q_1\})
\cong\mathbb R^4.
\tag{199.6}
$$

逆映射将两条方向线取交；199.2的定秩 join、meet 保证双向连续。每个纯点都在某条线之外，所以这些开图覆盖 $P$。类似地，固定纯点 $q$ 及两条不同过 $q$ 线，不经 $q$ 的线由它与这两条线的交点唯一且连续地坐标化为 $\mathbb R^2\times\mathbb R^2$。它们是 $\mathcal L$ 的开图，并覆盖全部线。因此 $P$ 与 $\mathcal L$ 都是紧四维流形；$P$ 连通。

不变域使连续单射 $\rho$ 的像在 $P$ 中开，紧性使其闭；像非空，故 $\rho$ 满射。于是每个原纯点 $p$ 的邻集都是某颗原实际球的纯边界，且 $p$ 不在该球内。故全 NC 成立；每两线相交又给全 Hit，球内一零极值给全 AD。到此才精确满足 XIII162.10 的 L2+NC+AD，直接消费该既有分类。所得复矩阵大小满足 $(n-1)^2=w_a=4$，所以 $n=3$，给(199.3)。

反向，在完整三能级模型中，$a=P_v$ 的邻点是 $v^\perp$ 中的全部纯射线，张成 $\operatorname{Herm}(v^\perp)$，实维数四；任意复二维支持与 $v^\perp$ 非零相交，给 Hit。实际二点面是三球，给 L2。$\square$

**推论 199.4（普适入口的严格邻维下界）。** 在197.7的强实全有限背景中，若 $m=\dim V>1$，则整个三复制域满足

$$
\mathrm{L2}_3+\mathrm{Hit}_3(a)
\quad\Longrightarrow\quad\dim W_a\ge5.
\tag{199.7}
$$

证明。三复制空间维数是 $m^3$。单点与整三球分别要求维数一与四，均不可能；198.8给 $w_a\ge4$。若等于四，199.3又迫整个三复制空间维数九，仍非非平凡整数立方。因此只能 $w_a\ge5$。这加强198.9的范围说明：非平凡三复制量子入口没有可由四维临界分支省去的标签，不能把该分支的自动支付宣称成实际检查成本下降。$\square$

**命题 199.5（量子对应、反事实与完整白话）。** 在全域 L2 下，(199.1a)只追加一个标签的命中与邻集容纳条件，就在其声明范围内给完整三能级静态理论：

| 原关系或对象 | 同一个 $\theta$ 下的对应与边界 |
| --- | --- |
| 纯点与实际球线 | $\mathbb{CP}^2$ 与其中的 $\mathbb{CP}^1$；根点将每条复射影线送到其正交纯点 |
| 原态、全效应、原配对 | 全部三阶迹一 PSD、$0\le E\le I$ 与 Born 迹配对；最低纯确认读数在纯输入上为平方模 |
| 有限效应族与数学测量 | 总和为单位才给 POVM，正交投影分解给 PVM；数学存在没有额外保证设备实现 |
| 复合、分支、时间 | 单系统结论未给原多系统锥；全有限传播仍须198.10–11的完整背景与入口，CP、质量预算、指定锐中性、连续群和经验标定仍各保留其条件 |

证明及图景。仍要求每两个不同纯准备撑起一颗实际三球。挑一个目标，把它的全部可区分纯准备容纳在同一颗真二点球内，并要求它们碰到每条纯点线。这些邻点便恰好只张成四个原实方向，且占满该球的整张二球面，成为一张真实的邻屏。每颗外部球投向这张屏幕，连续且不重叠；同维紧球面不容只占半张屏幕，故必须铺满。再从普通纯点投影一次，原来可能错开的球线就被迫相遇，实际面组成一张射影平面。每张球面还被原正测试从外面托住；测试达到最大值的纯点与整张球面确定区分，球内唯一对径使这个根点唯一。根点从线空间连续且不重叠地进入纯点空间；两边都是紧四维空间，便不能留下未被命中的纯点。因此全部标签都得到真正的邻面，不再单独输入它们的不塌缩，已有分类将这整个结构识别成复三能级系统。

反过来看，若某目标没有得到邻面，在上述完整背景中就必有(199.1)某项失效：只要 L2 和该标签 Hit 保留，它的邻张成便不能仍为四维。若只知邻维至少五，球外球面嵌入邻域并不再由同维不变域迫成满射；本证明没有排除这时的高维全 LIN 缺口。这是准确的推导断点，没有声称三项前提全局独立。维数也要分别读：二点面仿射三维，整个归一底仿射八维，纯域是实四维的复射影平面。三个非共线纯点的共同支持是重建后的复三维支持，不与局部 Bloch 球的实三维混用。

199.2从单标签原命中取得整个实际射影面格、199.3从原支撑根点取得全标签 NC，是 repo-derived 接合；不申领文献优先权。模面格紧性、连续透视及射影平面坐标是成熟工具：[Q199LF] 的 Lemmas 2–4 及 Theorem 1 的证明明确供应相应接口，前件在199.2中先行赚得；不变域使用 [Q198AT]。复锥分类与菜单字典直接复用 XIII162.10–11，不把拓扑或保面同胚冒充保原单位的线性序同构。$\square$

[Q199LF]: https://arxiv.org/pdf/0903.0643v1 "D. Labardini-Fragoso, M. Neumann-Coto, M. Takane, Cones and convex bodies with modular face lattices：Lemmas 2–4、Theorem 1及其证明；此处只复用模不可约面格的紧性、关联连续性与坐标工具。"

## 追加锚（本行以下为增补区）

## 200. 一点的局部平面邻域与三线接合

**定义 200.1（单点过球候选）。** 保留197.1的完整原域、全部原准备与原效应，以及198.1的实际 L2。定义 $\mathrm{Star}(a)$ 为：对每个 $p\in P\setminus\{a\}$，有 $N_a\cap B(a,p)\ne\varnothing$。只要求

$$
\mathsf Q_{\rm one,surface}:=\mathrm{L2}+\exists a\in P:\quad N_a\ne\varnothing,\quad\mathrm{Star}(a),\quad N_a\text{ 在原子集拓扑中局部同胚于 }\mathbb R^2.
$$

Hausdorff性与第二可数性继承自有限维 $V$；连通、紧、定向、球面拓扑、实际邻面及邻张成维数均不预给。Star只命中过 $a$ 的实际球，不输入其他球的命中。候选仍限于三能级单系统。

**定理 200.2（局部平面入口的完整三能级等价）。** 在200.1的完整原域中，$\mathsf Q_{\rm one,surface}$ 当且仅当存在实线性同构 $\theta:V\overset\sim\longrightarrow\operatorname{Herm}_3(\mathbb C)$，满足 $\theta(C)=\operatorname{PSD}_3$、$u=\operatorname{Tr}\circ\theta$。正向还给全部标签的 Hit、NC、SP、Flat，以及 $\dim W_p=4$。

证明。198.2的证明中，邻点的存在、唯一、投影连续及球外单射只使用过 $a$ 的球命中；以Star代入同一证明，得到连续满射 $\beta_a:P\setminus\{a\}\to N_a$，且固定 $N_a$。这里复用该证明的局部接口，不在尚未取得全Hit时调用其较强陈述。任意两个不同的非 $a$ 纯点在它们自己的纯球面上可由避开至多一点 $a$ 的路径连接，所以 $P\setminus\{a\}$ 及其像 $N_a$ 路径连通。非空局部二维条件排除单点域及整三球，后者的 $N_a$ 仅为一个对径点。198.8证明首段仅用L2的论证遂给不经 $a$ 的实际球 $D$。连续嵌入 $\beta_a|_{\ell_D}:S^2\hookrightarrow N_a$ 的像由不变域开、由紧性闭；连通性迫其满射。因此 $N_a\cong S^2$，紧性与可定向性成为结论。

对每个不经 $a$ 的球重复同一开闭论证，便知每条线都遇每条过 $a$ 的线。199.2中从普通中心向一条过 $a$ 的线作透视的证明，只再使用二点定线、L2的椭球中点极限及这项命中；照该段第二次 $S^2\to S^2$ 不变域论证，取得任两不同纯点线恰交一点。199.2随后纯面性的论证又给：全部非空真面只有纯单点与实际球；这些球都是coatom，且存在真球。本段不需要该条末尾的模面格紧性结论。

对每个实际球 $B$，复用199.3首段的原支撑构造：取消去 $B$ 的非零正支撑 $h$，coatom使其真零面正是 $B$；取原纯最大点 $r$，以 $M=\max_Kh>0$ 归一，$h/M$ 属于原完整效应区间，故 $\ell_B\subset N_r$。若 $c\in N_r\setminus\ell_B$，线 $B(r,c)$ 与 $B$ 的交点又是 $r$ 的邻点且不同于 $c$，违反球内对径唯一性。因此每条球线有一个根点 $r$，满足 $N_r=\ell_B$。此处只用紧底 $K$，不先用 $P$ 紧，也不需要连续选择支撑。

现在固定任意 $p\in P$，选两条不同的过 $p$ 线 $L,M$，分别选根点 $r,s$。它们存在，否则所有纯点都在一颗球中；$N_r=\ell_L\ne\ell_M=N_s$ 使 $r\ne s$。再取 $D=B(r,s)$ 的根点 $t$，对称性给 $t\in N_r\cap N_s=\ell_L\cap\ell_M=\{p\}$。所以 $t=p$、$N_p=\ell_D$；无自邻性排除 $p\in D$，取得全NC。这只选择三个根点，不要求根点唯一、连续或定义全局根点函数。真面穷尽使面高度至多三；直接消费XIII162.13得到 $n=3$ 的完整原锥、原单位表示。任两线相交给全Hit，198.3给SP、Flat，199.3的矩阵邻支持计算给 $\dim W_p=4$。反向，在完整三能级模型中 $N_a=\mathbb{CP}^1\cong S^2$，每颗过 $a$ 的复二维支持都有唯一正交纯点，给Star；实际球给L2。$\square$

**命题 200.3（反事实与简化范围）。** 在完整原域和L2下，若一个满足Star的目标没有得到实际邻面，则其非空邻集不能处处局部像平面。单点、整三球和高秩复量子域分别说明非空、局部二维及单系统范围的作用。

证明。首句是200.2的逆否结论。标量纯域使空邻集的Star空真，故非空不能省略；整三球虽满足Star，邻集是单点。完整 $n\ge4$ 模型也满足Star，但 $N_a=\mathbb{CP}^{n-2}$ 的实维数是 $2n-4\ge4$；球面嵌入不再由同维不变域迫满射。相对199.1，本候选不读取原张成，也不先将邻点容纳于一颗实际球，且命中只检查过所选目标的球；两次透视之后，三线接合替代根点连续性与四维流形满射步骤。没有据此声称独立前件数减少。裸全LIN到Flat的高邻维缺口仍不由此解决；在197.7的强实全有限背景中，整个非平凡三复制域不能满足本候选，否则维数同时为九和非平凡整数立方。$\square$

**命题 200.4（量子字典、更大结构与完整白话）。** 200.2的同一个 $\theta$ 将原纯域、原实际球、全部归一态、完整效应及原配对分别识别为 $\mathbb{CP}^2$、其中的 $\mathbb{CP}^1$、三阶迹一PSD、$0\le E\le I$ 与 $\operatorname{Tr}(E\rho)$。有限效应族只有总和为单位时才给POVM；全有限复合及过程仍须各自条件。

证明及图景。静态对应直接复用199.5及XIII162.10–11，不重复分类。所得邻集是实际复射影线，纯域是复射影平面：局部实二维邻域迫整张球面，三条球线的接合再使任一纯点成为一张邻面的根点。整个归一底实仿射八维，纯域实四维，二点面实仿射三维，三颗非共线纯点的共同复支持三维。任意大小全有限重建可用198.10–11的命中—平坦入口；另一个纯准备入口是[第XVIII卷199.3–4](QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md)的半转准备候选：必须保留其定义199.3的全部两项，包括每面仿射三维及两个不同、局部不能确定区分的互反目标，再给全标签半转一致性、总不同支持至多 $\dim W_3+1$，并使用整个三复制域及全部强实背景；这些前件不能由本单系统判据自动取得。CP仍要求全部有限旁观者下保正，TNI/TP要求全输入质量预算，指定锐更新、连续可逆时间群和经验标定仍各保留199.5与198.11所列条件。

白话说，保留系统原有的全部准备和测试，每两个不同纯准备撑起一颗真正的三球。挑一个至少有一个可区分纯邻点的目标，只要求每颗从它出发的球都有一个能与它确定区分的对径邻点，而且这些邻点每处都像一小片平面；不先告诉理论它们是哪颗球，也不先指定四个线性方向。从目标看出去，每张不经过它的球面都连续、不重叠地投到邻域；二维球面不能只铺其中一块，于是铺满整张邻域。再换普通中心投影，所有球线便被迫相遇。每颗球由原正测试托住，测试的纯最大点就是整张球的根点；对任意目标，取两条经过它的线，再连接它们的根点，第三条线的根点只能是原目标。因此每颗纯点都自动得到真正的邻面，已有重建把整个结构识别成复三能级系统，给出混态、Born配对和数学测量；复合、过程和物理时钟继续按各自条件接入。

本条的Star局部接口、邻集局部平面到实际球线关联、三线根点接合是repo-derived推导，不申领文献优先权。不变域是[AT, 2B.3–4][Q198AT]的成熟工具；球投影、原支撑及实际低面分类分别复用198.2、199.2–3和XIII162.13，不把纯拓扑同胚冒充原线性锥表示。$\square$

**推论 200.5（只看二元关系之间是否相遇）。** 在197.1的完整原域中，200.2的三能级表示还等价于：L2成立，至少存在一颗真二点面球，而且任意两颗实际二点面球相交。后一个条件只比较两条由纯点对生成的关系，不输入原邻集、张成维数或流形结构。

证明。两个实际面相交时，其交面含原纯点；不同球的交面只能是一个纯点。故任两球线相交，直接接200.2证明中从真面穷尽、原支撑到三线根点的后半，再用XIII162.13；该后半不使用Star或局部平面输入。反向，复三维空间的任意两个复二维支持必非零相交，且二点支持面为真球。因此这也给同一完整候选的白话：每对纯点撑起真三球关系，至少一颗球还不是整个系统，而任意两颗这样的球总有共同准备。球关系不能彼此错开；原测试与三线接合随之找回每颗纯点的正交邻面，重建整个三能级锥及Born配对。范围与过程条件仍按200.3–4。$\square$

## 追加锚（本行以下为增补区）
