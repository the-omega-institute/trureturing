---
bibkey: janottagogolinbarrettbrunner2011polygon
authors: Peter Janotta, Christian Gogolin, Jonathan Barrett, and Nicolas Brunner
year: 2011
title: Limits on non-local correlations from the structure of the local state space
doi: 10.48550/arXiv.1012.1215
url: https://arxiv.org/abs/1012.1215v3
claim: Regular polygon state spaces have an explicit full effect polytope; for odd polygons it includes both the vertex-aligned effects and all their unit complements.
strata_touched: []
license: citation-only
triage: anchor
---

# Unrestricted regular polygon states and effects

Source DOI: 10.48550/arXiv.1012.1215.
Cited version: https://arxiv.org/abs/1012.1215v3.

Section 3.1, PDF p. 7, equation (5) gives every normalized state vertex,
with radius $r_n=\sqrt{\sec(\pi/n)}$, and (6) gives the unit effect.
For odd $n$, (8) and the following paragraph specify the entire effect
polytope as the convex hull of zero, the unit, every displayed effect
and every unit complement. The complements are essential to the full
proper-effect interval.

The coordinate pullback and comparison application are in
[the application below](#odd-polygons-reciprocal-comparisons-original-faces-and-extension-budgets).
That local application does not use the paper's composite-state or
non-local-correlation assumptions and conclusions.


## Odd polygons: reciprocal comparisons, original faces and extension budgets

### 1. The original carrier and the full effect interval

Use the same comparison domains as
[Definition 109.1](../../docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md#1091-只用原态与原效应的附加关系).
For every odd integer $n=2m+1\ge5$, indices below are taken modulo $n$. Put

$$
\begin{gathered}
V=\mathbb R^2\oplus\mathbb R,\qquad
v_j=(\cos(2\pi j/n),\sin(2\pi j/n)),\qquad p_j=(v_j,1),\\
K=\operatorname{conv}\{p_0,\ldots,p_{n-1}\},\qquad
C=\operatorname{cone}K=\{tx:t\ge0,\ x\in K\},\qquad u(z,t)=t,\\
P=\operatorname{ext}K=\{p_0,\ldots,p_{n-1}\},\qquad
C^*=\{f\in V^*:f(y)\ge0\text{ for all }y\in C\},\\
\mathcal E=[0,u]_{C^*}=\{f\in V^*:0\le f\le u\text{ on }C\},\\
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(p\in P,\ x\in K),\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
$$

Here $K$ is the entire normalized base, $P$ contains every original pure
state, and every minimum ranges over the entire original confirming-effect
set. Let $H(p,q)$ be the smallest face of the original $K$ containing $p,q$.
The conditions under comparison are

$$
\begin{aligned}
\mathrm{EB}_{\ge1}:&\quad
\forall p\in P\ \exists d_p\ge1:\quad
D_p\simeq_{\rm aff}\overline B^{d_p},\\
\mathrm{PR}:&\quad \forall p,q\in P:\quad T_p(q)=T_q(p),\\
\mathrm{Pair}_{\perp}:&\quad
\forall p,q\in P:\quad T_p(q)=0\ \Longrightarrow\ H(p,q)\ne K,
\end{aligned}
$$

where $\overline B^d$ is the entire closed Euclidean unit ball in
$\mathbb R^d$. The first condition explicitly permits $d_p=1$.

**Carrier and attainment.** $K$ is compact and has nonempty relative interior
in $\{u=1\}$. Its cone is closed: in a convergent sequence $t_kx_k$, the
last coordinates $t_k$ converge, and compactness supplies a convergent
subsequence of $x_k\in K$. Every nonzero vector of $C$ has positive last
coordinate. Hence $C$ is pointed, $u$ is strictly positive on
$C\setminus\{0\}$, and the full affine span of $K$ makes $C$ generating
in $V$. The base $C\cap\{u=1\}$ is exactly $K$.

Each affine function on this base uniquely homogenizes to a linear
functional on $V$. Thus $\mathcal E$ consists of all affine functions
whose values on all of $K$ lie in $[0,1]$. Values at three affinely
independent vertices determine such a function and bound its coefficients;
the inequalities at all vertices are closed. Consequently $\mathcal E$
is compact. Each $F_p$ is a nonempty closed subset, since $u\in F_p$,
and every displayed minimum is attained.

Put $\delta=\pi/n$ and $c=\cos\delta$. The complete effect polytope is

$$
a_j(z,t)=\frac{v_j\cdot z+ct}{1+c},\qquad
\mathcal E=\operatorname{conv}\{0,u,a_j,u-a_j:0\le j<n\}.
\tag{OP1}
$$

This is the unrestricted polygon model in
[Janotta–Gogolin–Barrett–Brunner, §3.1, PDF p. 7, (5), (6), (8) and the following text](#unrestricted-regular-polygon-states-and-effects).
In their coordinates $\omega_j=(r_nv_j,1)$ with
$r_n=\sqrt{\sec\delta}$. The invertible map
$L(z,t)=(r_nz,t)$ sends $K$ onto their entire normalized state polygon
and preserves $u$. Their odd-polygon effect acts as

$$
e_j(Z,t)=\frac{r_nv_j\cdot Z+t}{1+r_n^2},\qquad
e_j\circ L(z,t)=\frac{r_n^2v_j\cdot z+t}{1+r_n^2}=a_j(z,t).
$$

Pullback by $L$ is therefore a bijection of the full positive cones and
full unit intervals, including both $0,u$ and all complements; no effect
budget is changed. Reindexing the paper's vertices cyclically has no
mathematical effect. [Takakura, §2.2, PDF pp. 4–6 and Figure 1(b)](takakura2020polygonentropy.md)
gives the same complete effect space and the distinguishability of a vertex
from every point on its opposite edge. These local state/effect facts use
neither the first paper's assumptions about composite non-local
correlations nor the second paper's thermodynamic assumptions or entropy
conclusion.

### 2. Exact confirming sets and complete exclusion edges

**Proposition.** For every $i$ and every $x\in K$,

$$
\begin{aligned}
F_{p_i}&=\operatorname{conv}\{u,a_i,u-a_{i+m},u-a_{i+m+1}\},\\
T_{p_i}(x)&=\min\{1,a_i(x),1-a_{i+m}(x),1-a_{i+m+1}(x)\},\\
D_{p_i}&=[p_{i+m},p_{i+m+1}]\simeq_{\rm aff}\overline B^1.
\end{aligned}
\tag{OP2}
$$

**Proof.** For all $i,j$,

$$
a_j(p_i)=\frac{\cos(2\pi(i-j)/n)+c}{1+c}.
$$

This equals one exactly when $j=i$, and equals zero exactly when
$j=i+m$ or $j=i+m+1$. Indeed the smallest cosine among these odd-polygon
directions is $-c$, attained precisely at those two indices. All generators
in (OP1) take values in $[0,1]$ at $p_i$. A convex combination can take value
one there only if all its positive-weight generators do so. The saturating
generators are exactly the four listed in (OP2), which proves the formula
for the entire $F_{p_i}$. Minimizing evaluation over their convex hull gives
the formula for $T_{p_i}$ at every normalized state.

The nonnegative affine function $a_i$ vanishes exactly on the opposite edge
$[p_{i+m},p_{i+m+1}]$, because its zero-valued vertices are precisely those
two. Similarly $u-a_j$ vanishes only at $p_j$, since $a_j=1$ only at that
vertex. The zero set of the displayed minimum is the union of those three
zero sets; the constant one contributes none. This union is exactly the
opposite closed edge. This proves both inclusions for the whole $D_{p_i}$,
including its mixed points. ∎

### 3. Reflection reciprocity and failure of the original pair-face condition

**Proposition.** Every odd polygon above satisfies
$\mathrm{EB}_{\ge1}+\mathrm{PR}$, but for every pure zero pair one has

$$
\forall p,q\in P:\quad
T_p(q)=0\ \Longrightarrow\ H(p,q)=K.
\tag{OP3}
$$

**Proof.** For any indices $i,j$, reflection in the planar axis with angle
$(i+j)\pi/n$, extended by the identity on the last coordinate, gives a linear
involution $R$ satisfying

$$
Rp_s=p_{i+j-s},\qquad R(C)=C,\qquad u\circ R=u,\qquad
Rp_i=p_j,\quad Rp_j=p_i.
$$

Thus $f\mapsto f\circ R$ is a bijection of the entire $\mathcal E$ and
carries $F_{p_i}$ onto $F_{p_j}$. It follows that

$$
T_{p_j}(p_i)
=\min_{f\in F_{p_i}}(f\circ R)(p_i)
=\min_{f\in F_{p_i}}f(p_j)
=T_{p_i}(p_j).
$$

This holds for every pair of pure states, including identical endpoints.
Equation (OP2) gives $\mathrm{EB}_{\ge1}$ for every pure state.
If $T_{p_i}(p_j)=0$, (OP2) gives $j=i+m$ or $j=i+m+1$.
Since $m\ge2$, these vertices are nonadjacent to $p_i$. The nonempty proper
faces of a convex polygon are its vertices and edges, so no proper face
contains this pair. Hence its smallest original face is $K$. In addition,
every point of the open connecting segment $(p_i,p_j)$ lies in
$\operatorname{ri}K$: a boundary point on that segment would have a supporting
line, whose affine supporting functional would then attain its extremal value
at both endpoints, putting them in one proper face. ∎

Consequently $\mathrm{EB}_{\ge1}+\mathrm{PR}$ does not imply
$\mathrm{Pair}_{\perp}$ on the specified full original domain. The reflection
proves symmetry of numerical endpoint comparisons; it supplies no state-update
rule and makes no assertion about exchanging sequential measurements.
All exclusion balls in this family have dimension one. This counterexample
does not settle a version requiring $d_p\ge2$, an entire three-ball exclusion
set, or the separate three-ball reconstruction target.

### 4. A convex exclusion set has a common original zero confirmer

**Proposition.** On any finite-dimensional carrier with the compact full
interval and attained minima above, fix $p\in P$. If $D_p$ is nonempty and
convex, there is one actual member $a\in F_p$ such that

$$
D_p=K\cap\ker a,\qquad a(p)=1.
\tag{OP4}
$$

In particular $D_p$ is an exposed proper face of the original $K$.

**Proof.** Choose $x_0,\ldots,x_d\in D_p$ affinely spanning
$\operatorname{aff}D_p$. Their average $\bar x$ belongs to $D_p$ by
convexity. Attainment gives $a\in F_p$ with $a(\bar x)=0$.
All $a(x_j)\ge0$, so their zero average forces each to be zero.
Affinity then makes $a$ vanish on $\operatorname{aff}D_p$, hence on all of
$D_p$. Conversely $x\in K\cap\ker a$ implies
$0\le T_p(x)\le a(x)=0$. The set is nonempty and is a minimizing face
of the nonnegative affine function $a$; it is proper because $a(p)=1$. ∎

This common confirmer need not be least on the full original cone and
does not give every proper effect on $D_p$ an extension in $[0,u]$.
It also does not put $p$ and a pure $q\in D_p$ together in a proper face.
In the polygons, any positive functional vanishing at both such $p,q$
vanishes at their midpoint in $\operatorname{ri}K$, hence on all of $K$:
an affine nonnegative function with an interior zero has zero linear part
on the affine hull and is identically zero there. Since $K$ spans $V$,
the functional is zero. Thus it cannot expose a proper face containing
the pair.

### 5. The pentagon violates finite-mixture consistency

Let $n=5$ and $\varphi=(1+\sqrt5)/2$, so $\varphi^2=\varphi+1$.
The full confirming set (OP2) gives the following values at all five pure
states:

| Effect or comparison | $p_0$ | $p_1$ | $p_2$ | $p_3$ | $p_4$ |
| --- | --- | --- | --- | --- | --- |
| $u$ | $1$ | $1$ | $1$ | $1$ | $1$ |
| $a_0$ | $1$ | $\varphi^{-1}$ | $0$ | $0$ | $\varphi^{-1}$ |
| $u-a_2$ | $1$ | $\varphi^{-2}$ | $0$ | $\varphi^{-2}$ | $1$ |
| $u-a_3$ | $1$ | $1$ | $\varphi^{-2}$ | $0$ | $\varphi^{-2}$ |
| $T_{p_0}$ | $1$ | $\varphi^{-2}$ | $0$ | $0$ | $\varphi^{-2}$ |

These evaluations follow by substituting $c=\cos(\pi/5)=\varphi/2$
in (OP1). The same coordinates give

$$
\begin{aligned}
p_2-p_0&=\varphi(p_1-p_0)+(p_4-p_0),\\
p_3-p_0&=\varphi(p_4-p_0)+(p_1-p_0).
\end{aligned}
\tag{OP5}
$$

For example, substitute
$\cos(2\pi/5)=(\varphi-1)/2$,
$\cos(4\pi/5)=-\varphi/2$ and
$\sin(2\pi/5)=\varphi\sin(\pi/5)$ into the first identity;
reflection fixing $p_0$ and exchanging $p_1,p_4$ gives the second.
The first identity yields two finite pure preparations of exactly the
same normalized state:

$$
x=\frac{p_2+\varphi p_0}{1+\varphi}
 =\frac{\varphi p_1+p_4}{1+\varphi}.
$$

Nevertheless their comparison averages against $p_0$ are

$$
\frac{T_{p_0}(p_2)+\varphi T_{p_0}(p_0)}{1+\varphi}
=\varphi^{-1},\qquad
\frac{\varphi T_{p_0}(p_1)+T_{p_0}(p_4)}{1+\varphi}
=\varphi^{-2}.
\tag{OP6}
$$

The values are unequal. Thus the [original finite-mixture condition (9)](../QuantumStates/mullerududec2012selfduality.md#an-intrinsic-binary-comparison-and-its-consistency-condition), required
for every fixed pure $p$ and every equality between finite normalized
pure preparations, fails. [Principle S](../QuantumStates/mullerududec2012selfduality.md#carrier-and-the-retained-condition) retains this condition in addition
to reciprocity. The pentagon therefore does not satisfy S and is no
counterexample to S or to quantum theory; it separates the retained
mixture requirement from pure endpoint reciprocity.

### 6. The sharp positive-extension budget is the golden ratio

**Proposition.** In this same pentagon, $D_{p_3}=[p_0,p_1]$. Let $h$ be the
unique affine function on that entire edge with $h(p_0)=0$, $h(p_1)=1$;
it is a proper face effect since $0\le h\le1$ there. Then

$$
\min_{\substack{\ell\in C^*\\ \ell|_{D_{p_3}}=h}}
\ \max_{x\in K}\ell(x)=\varphi>1.
\tag{OP7}
$$

**Proof.** The vectors $p_0,p_1,p_4$ form a basis of $V$. Hence every linear
extension of $h$ is uniquely specified by $s=\ell(p_4)\in\mathbb R$,
and every real $s$ gives one such extension. Applying (OP5), its values
at $p_0,\ldots,p_4$ are exactly

$$
\bigl(0,\ 1,\ \varphi+s,\ 1+\varphi s,\ s\bigr).
\tag{OP8}
$$

Since these vertices generate the whole cone, positivity on $C$ is
equivalent to nonnegativity of all five entries, which is equivalent to
$s\ge0$. A linear functional attains its maximum over $K$ at a vertex.
For every positive extension that maximum is at least
$\ell(p_2)=\varphi+s\ge\varphi$. Choosing $s=0$ gives a positive
extension with values $(0,1,\varphi,1,0)$ and maximum exactly $\varphi$.
This proves both the lower bound and attainment. ∎

Positive linear extensions therefore exist, but none lies in the original
proper-effect interval $[0,u]$: the least possible whole-base upper bound
is $\varphi u$, strictly exceeding $u$. Bare affine extension or a positive
Hahn–Banach extension cannot supply the missing original unit budget.

The polygon carrier and full effect set are **literature-attested** through
the two linked source notes. Equations (OP2)–(OP8) are the explicit
**repo-derived application** to the original comparison, mixture and
extension-budget questions, with the elementary proofs given here.
This application makes no literature-novelty, new-axiom or physical-origin
claim; its conclusions are ordinary finite-dimensional convex mathematics.

白话说，一个角能排除整条对边；但从对边挑一个端点，与原角连线，线段内部却穿过
多边形内部，所以这两个点没有共同真面。交换比较的两端仍然公平，读数完全互易；
可同一混合态换一种纯态准备后，把每个纯分量各自优化得到的比较读数再取平均，
所得数值并不相同；这不涉及普通仿射效应的概率，后者在这里每个模型中都与准备
分解无关。面上的合法读数延到全域，最小正延拓预算又是 $\varphi$，超过原单位一。
端点互惠、有限混合一致性和原单位内的延拓是不同条件，不能用其中一个替掉另外
两个，也不能把这条一维排除边当成完整三球的结论。
