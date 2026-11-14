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

**Definition 176.1 (positive differences and self-testing).** Keep the entire weak all-finite domain of Definition 175.1, including the actual complex Hermitian tensor carriers, complete trace duals, every minimum/maximum partition, scalar object, positive actual permutations and their inverses, and canonical reassociation. Keep exactly its ternary condition $\mathsf T$ in (175.2). For a closed convex cone $K\subseteq E_d=\operatorname{Herm}_d(\mathbb C)$ define

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

The complete candidate is

$$
\mathsf Q_+:=\mathsf A_+(C_2)\wedge\mathsf I(C_2)\wedge\mathsf T.
\tag{176.2}
$$

Only positive ordinary rank-one differences are tested in $\mathsf A_+$. The negative differences in $\mathsf A$ are omitted, and no nonzero binary readout or Bell resource is designated. Both the ordinary complex rank-one family and the positive-definite trace identification remain supplied geometry. In particular $\mathsf I$ is not a claim that preparation and test types have already been intrinsically identified without a pairing.

### 176.2 What the positive half actually controls

**Theorem 176.2 (the exact one-sided classification).** For every $d\ge1$ and every closed convex cone $K\subseteq E_d$,

$$
\mathsf A_+(K)
\quad\Longleftrightarrow\quad
\bigl(\operatorname{PSD}_d\subseteq K\bigr)
\ \text{or}\
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
\mathsf Q_+\quad&\Longleftrightarrow\quad
C_N=\operatorname{PSD}_{n^N}\text{ for every finite }N\ge0.
\end{aligned}
\tag{176.8}
$$

**Proof.** Corollary 176.3 and Lemma 176.4 give the first forward implication. Binary PSD and the all-zero nonempty hierarchy each satisfy both binary relations, giving its converse.

The nonzero primal dyad in $\mathsf T$ excludes the all-zero hierarchy; no separate $\mathsf N(C_2)$ is needed. Thus $\mathsf Q_+$ gives $C_2=\operatorname{PSD}$. It now supplies $\mathsf Q_{\mathrm A}$ by Theorem 175.3, so Theorem 175.4 with precisely the unchanged $\mathsf T$ gives every finite PSD equality. Its suppliers first recover $C_1=\varepsilon\operatorname{PSD}_n$ and signed properness; the positive odd-level dyad selects $\varepsilon=+1$; its three flattening ranks then pay the full hypotheses of XIII166.12. No rank requirement is used to exclude the zero hierarchy, whereas all three remain in the propagation step. Conversely the standard PSD hierarchy satisfies both binary relations and has the full-rank GHZ seed used in Theorem 175.4. $\square$

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

### 176.5 Quantum correspondence, geometric economy and the remaining bridge

**Corollary 176.8 (the inherited full finite theory).** Under $\mathsf Q_+$, every conclusion and every separate realization condition of Corollary 175.5 applies in the original coordinates.

**Proof and correspondence.** Theorem 176.5 supplies its exact cone hypothesis. Whole trace-one cones give all density states and rank-one pure states; complete proper intervals and all unit decompositions give all POVMs and the Born pairing; the actual joint cones give tensor composition and partial traces; positivity with every original finite spectator gives the rectangular CP/Choi/Kraus dictionary, with the whole-input TNI/TP budgets for mathematical instruments. The corresponding Watrous suppliers and scalar and zero-branch conventions are precisely those reused in 175.5, rather than new proofs of those standard results.

For two distinct pure states inside one resulting matrix block, the minimal normalized face is a real three-ball, and the full pure locus at level $N$ is $\mathbb{CP}^{n^N-1}$. The larger object containing these binary balls is the entire positive Hermitian cone with its finite tensor hierarchy. Event saturation, a specified sharp nondisturbing update for Lüders, and a supplied continuous order-automorphism group for Hamiltonian time retain the distinct assumptions of 175.5. No physical clock or value of $\hbar$ is obtained. $\square$

**Proposition 176.9 (what has and has not become simpler).** Relative to $\mathsf Q_{\mathrm A}\wedge\mathsf T$, the candidate (176.2) deletes the negative rank-one difference tests and the independent nonzero-readout premise, at the cost of the preparation–test inclusion $\mathsf I(C_2)$. Neither candidate implies a claim of a globally minimal axiom set.

**Proof and source scope.** Theorem 176.2 identifies exactly the extra cones admitted by the positive half. Theorem 176.6 shows that this loss survives every finite composite requirement, strict trace positivity, nonzero readout and the original ternary seed. Thus these standing structures cannot silently replace $\mathsf I$. Corollary 176.3 and Lemma 176.4 show precisely how one inclusion and self-composition repair it, and why the seed itself now pays the nonzero condition. On the fixed all-finite domain both complete candidates are equivalent to the same full PSD hierarchy, by Theorems 175.4 and 176.5. This is an alternative allocation of assumptions, not a strict weakening there or a shortest-description theorem.

Moreau's decomposition and nonexpansiveness are the literature inputs at [printed pp.281–282][Q175M]. The one-family argument, hierarchy collapse, and product-block-positive control are paper deductions on the stated carriers; the separable/block-positive polar pairing follows directly from their definitions in (176.9)–(176.10). No general literature priority is claimed. The all-finite propagation and standard quantum dictionary are the explicitly credited existing suppliers above.

The external complex carrier, positive rank-one family and trace identification have not been reconstructed from native zero relations. Proposition 175.7 still rules out the particular native-extreme-ray replacement that makes the constraint automatic. The already established one-interior-reference comparison criterion in the [Pinelis source-context note][Q176P] is a distinct intrinsic route, with its full VII102.4 B1–B3 hypotheses; it is not a consequence of the positive half or a newly established result here. A bridge deleting the supplied rank geometry remains unproved. These statements are paper mathematics, not Lean-kernel certification. $\square$

**命题 176.10（完整白话候选）。** 在175.1给定的复矩阵关系空间里，候选可以说成：任何两份原准备，用同一把迹标尺比较都不能给负数；一份准备与一个原测试互不响应时，如果两者之差恰好是一条正向的一维线，它们就不能各留一块。再保留那颗三个切口都非乘积、至少一条腿铺满本地维数的正三体种子。这些条件恰好给出176.5的全部有限量子锥。

**证明与图景。** 把任意正向一维线分成锥内最近部分和对偶法向部分，第二条关系使整片相连的一维线只能统一留下或统一落空。留下时，量子正锥已全部在里面；第一条关系又让每份准备都能充当非负测试，于是把外面多出的部分挡掉。落空时，二体锥只能朝负面；但一份对象和自己复合总会产生正的平方方向，所以这种二体选择迫使每个非空层都归零。三体种子让整体不能归零，再选定一体的正朝向，并按已有有限传播展开所有层。若删掉第一条关系，“对所有单腿乘积方向都非负”的大锥便能混进来：它装着量子态，也装着有负本征值的对象；两份准备照迹标尺甚至会读出负数。这说明缺的正是准备与测试之间的那条包含关系。所得局部画面仍是两条纯线撑起一颗三维球，整体是相容的有限量子锥层级；正向一维线和迹标尺本身仍是给定地基，具体测后更新与时间保留176.8的额外条件。$\square$

[Q176P]: https://github.com/the-omega-institute/trureturing/blob/1888fc22e76ba8b59fb974ef5db8f5e1b23904f1/Library/Convexity/pinelis2012extremepoints.md

## 追加锚（本行以下为增补区）
