---
bibkey: pinelis2012extremepoints
authors: Iosif Pinelis
year: 2012
title: "On the extreme points of moments sets"
doi: null
url: https://arxiv.org/abs/1204.0249v1
claim: "Finite-support extreme-point results for moment sets; Theorem 1 and Corollary 4 provide general background for the finite-support reduction used in this repository's one-interior-reference comparison application."
strata_touched: []
license: citation-only
triage: anchor
---

# Extreme points of moments sets and a one-reference comparison application

The cited paper, *On the extreme points of moments sets*, gives relevant general
finite-support background in Theorem 1 and Corollary 4 for the support reduction below.
The exact one-interior-reference comparison criterion, its reciprocal least-confirmation
conclusion, and the quantum substitution are repository-derived paper exposition. They
are not attributed to Pinelis, are not a novelty or fewer-axioms claim, and introduce no
Lean declaration. This companion presents the comparison application alongside the
[Müller–Ududec source-context note](../QuantumStates/mullerududec2012selfduality.md).

## Appendix: one interior reference and the finite-support cap

Keep the same nonzero finite-dimensional real ordered carrier $(A,C,u)$, the entire compact base
$K=C\cap\{u=1\}$, its pure set $P=\operatorname{ext}K$, and the full proper-effect interval
$\mathcal E=[0,u]_{C^*}$. For $p\in P$ put

$$
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(x\in K).
\tag{18}
$$

The minimum is attained on this finite-dimensional compact effect set, as in the existing Chapter 77
carrier. No closedness of $P$, continuity of $q\mapsto T_q(p)$, or measure on an infinite pure set is used.
Fix one reference $m\in\operatorname{relint}K$. Define $D_m$ by requiring that, for every target $p\in P$,

$$
\sum_{i=1}^r a_iT_{q_i}(p)
\tag{19}
$$

has the same value for every finite decomposition
$m=\sum_{i=1}^r a_iq_i$ with pairwise distinct $q_i\in P$, $a_i>0$ and $\sum_i a_i=1$.
The common value is not prescribed. Let $D_m^{\le d}$ be the same condition restricted to $r\le d$, where
$d=\dim_{\mathbb R}A$; it still quantifies every choice of labels, every positive recipe and every target.
The full preparation law is

$$
S:\qquad
T_p\!\left(\sum_i a_iq_i\right)=\sum_i a_iT_{q_i}(p)
\quad\text{for every }p\in P,\ q_i\in P,\ a_i\ge0,\ \sum_i a_i=1,
\text{ including zero weights and repeated labels.}
\tag{20}
$$

Thus the exact one-reference conclusion is

$$
D_m^{\le d}\ \Longleftrightarrow\ D_m\ \Longleftrightarrow\ S
\ \Longleftrightarrow\ \text{reciprocal whole-cone least proper confirmation}.
\tag{21}
$$

Under these equivalent conditions, the common value in (19) is $T_p(m)$ for each target $p$. The full law
$S$ makes every $T_p$ affine on the whole normalized base, while (22) gives reciprocity as a conclusion rather
than an extra comparison premise.

The last equivalence is the existing full-mixture/circuit-balance result on this same full carrier: its
intermediate condition is balance of every finite minimal-support pure relation, and it constructs effects
$e_p\in F_p$ satisfying

$$
e_p\le f\text{ on }C\quad(f\in F_p),\qquad e_p(q)=e_q(p)\quad(p,q\in P).
\tag{22}
$$

It is the result recorded in the existing [`full_mixture_iff_circuit_balance`](../../Blueprint/D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.md)
statement; this application does not re-prove that carrier theorem.

### Why one interior reference controls all finite relations

Fix a target $p$ and a finite signed pure relation

$$
\sum_i c_iq_i=0,\qquad q_i\in P.
\tag{23}
$$

Applying $u$ gives $\sum_i c_i=0$. Write $c_i=c_i^+-c_i^-$ and
$s=\sum_i c_i^+=\sum_i c_i^-$. If $s=0$ there is nothing to prove. Otherwise

$$
x=\frac1s\sum_i c_i^+q_i=\frac1s\sum_i c_i^-q_i\in K.
\tag{24}
$$

Since $m$ is relative interior, some $t\in(0,1)$ has
$y=(m-tx)/(1-t)\in K$. Choose any finite pure decomposition of $y$ and append it to the two
decompositions

$$
m=t\sum_i\frac{c_i^+}{s}q_i+(1-t)y
 =t\sum_i\frac{c_i^-}{s}q_i+(1-t)y.
\tag{25}
$$

After merging repeated labels, $D_m$ makes the two values in (19) equal. The common decomposition of $y$
cancels, leaving

$$
\sum_i c_iT_{q_i}(p)=0.
\tag{26}
$$

Thus one interior reference balances every finite signed relation, including relations with arbitrary support.
The existing circuit-balance equivalence then gives $S$ and (22). Conversely, $S$ applied to two decompositions
of $m$ is exactly $D_m$, so (23)--(26) are the interior-reference bridge needed for the equivalence.

### Why the cap is $d$ and why it suffices

Suppose a recipe $m=\sum_{i=1}^r a_iq_i$ has distinct labels, positive weights and $r>d$. Because all $q_i$
lie in the affine hyperplane $u=1$ of the $d$-dimensional space $A$, they are affinely dependent: there is a
nonzero $\lambda$ with

$$
\sum_i\lambda_i=0,\qquad \sum_i\lambda_iq_i=0.
\tag{27}
$$

The signs of $\lambda$ are mixed. Choose the largest steps $t_+,t_->0$ for which
$a+t_+\lambda$ and $a-t_-\lambda$ remain nonnegative; each step deletes at least one label. With
$\theta=t_-/(t_++t_-)$,

$$
a=\theta(a+t_+\lambda)+(1-\theta)(a-t_-\lambda),
\tag{28}
$$

and both new weight vectors still represent $m$. If $V(a)=\sum_i a_iT_{q_i}(p)$, then
$V(a)=\theta V(a+t_+\lambda)+(1-\theta)V(a-t_-\lambda)$. Induction on the support reduces every recipe to a
convex combination of recipes with at most $d$ distinct positive labels. Hence $D_m^{\le d}$ makes all
recipes have one common value and gives $D_m$.

The number $d$ is the ambient $\dim_{\mathbb R}A$. Since $C$ is generating and each nonzero $c\in C$
equals $u(c)(c/u(c))$ with $c/u(c)\in K$, we have $\operatorname{span}_{\mathbb R}K=A$. Together with
$K\subseteq\{u=1\}$ this gives $\operatorname{aff}K=\{u=1\}$ and $\operatorname{affdim}K=d-1$.
Thus the cap is exactly the affine dimension plus one on this full carrier. It is a sufficient bound;
universal minimality of the test cap is not asserted. In a classical direct-sum cone with $d$ rays, the
barycentre needs all $d$ pure labels, but that simplex already satisfies $S$: this controls representation
size only and does not show that a smaller cap fails to imply $S$. The quantifier is still infinite in
general: all pure labels, targets and recipes of the allowed support are tested, not a finite test list.

### Boundary control and the geometric picture

The interior hypothesis cannot be dropped. In the square $K=[0,1]^2$ with vertices
$a=(0,0),b=(1,0),c=(0,1),d=(1,1)$ and the full affine effect interval, each pairwise value is
$T_p(q)=\delta_{pq}$. At the edge reference $m=(a+b)/2$, every pure decomposition uses only $a,b$ with
weights $1/2,1/2$, so $D_m$ holds trivially. Yet

$$
\frac{a+d}{2}=\frac{b+c}{2},\qquad
\frac{T_a(a)+T_d(a)}2=\frac12\ne0=\frac{T_b(a)+T_c(a)}2,
\tag{29}
$$

so $S$ fails. At a vertex the reference test is even more vacuous. The role of $m\in\operatorname{relint}K$
is geometric: a sufficiently small amount of any $x\in K$ can be removed from $m$, leaving a common remainder
$y\in K$; the two sides of every relation can therefore be inserted into the same reference decomposition.
The support cap is a separate affine-dependence fact: a large recipe is a convex combination of lower-support
recipes. Together they turn one reference into all finite relations without topology on the pure locus.

### Conditional three-copy substitution

Apply the criterion to the **entire** $P_3$ and $\mathcal E_3$ of [VII Definition 102.1](../../docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md):
all finite $W_N=V^{\otimes_{\mathbb R}N}$, the closed pointed generating cones, strict units, whole bases and
pure sets, the complete proper intervals, min/max composite bounds, product pairing, permutations and
rebracketing are retained. At three copies, replace the $S_3$ premise by the single capped condition

$$
D_{m_3}^{\le d_3}\quad\text{for one }m_3\in\operatorname{relint}K_3,\qquad
d_3=\dim_{\mathbb R}W_3.
\tag{30}
$$

By (21), (30) is exactly $S_3$ on the unchanged $P_3/\mathcal E_3$ carrier. Only after this replacement is
made do we invoke the existing [B1--B3 interfaces of VII Convention 102.4](../../docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md): B1 applies $S_q$ to the whole
$q=1,2,3$ carriers and supplies the reciprocal-least, self-dual EJA geometry; B2 supplies the actual
$(W_1,W_1,W_2)$, $(W_2,W_1,W_3)$ and $(W_1,W_2,W_3)$ products, units, pairings and local tomography; B3
requires one common $W_2$, the identity rebracketing on $W_3$, positivity of the original $\tau_{12}$ on all
$C_3$, and the product calibrations. [Theorem 102.11](../../docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md) then gives the fixed-coordinate all-finite conclusion

$$
\theta^{\otimes N}(C_N)=\bigoplus_{s\in I^N}\operatorname{Herm}_+(\mathcal H_s),
\qquad A=\bigoplus_{i\in I}M_{n_i}(\mathbb C),
\tag{31}
$$

with the existing state/effect/Born, finite-POVM and CP/Kraus dictionary and its stated source, budget and
event contracts. Classical centres and direct sums remain in scope; the pure geometry is the disjoint union
$\bigsqcup_{s\in I^N}\mathbb{CP}^{D_s-1}$, $D_s=\prod_tn_{s_t}$. In the aligned single-block model of
XIII [Definition 166.1](../../docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md), $V=\operatorname{Herm}_n(\mathbb C)$ and
$W_3=\operatorname{Herm}_{n^3}(\mathbb C)$, so $d_3=n^6$ and

$$
m_3=I_{n^3}/n^3\in\operatorname{relint}K_3.
\tag{32}
$$

The interiority in (32) follows from the finite-projector argument in [VIII §124.6, proof of Theorem 124.6](../../docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md#1246-归一匹配锥的闭性原极性与严格夹逼):
local rank-one projectors span $\operatorname{Herm}_n$ and sum to $(2n-1)I$. Their tensorized positive
identity decomposition, together with iterated minimum inclusion, gives (32) without assuming higher-copy
PSD. Thus the exact aligned test
uses at most $n^6$ distinct positive pure labels. The criterion itself selects neither the complex field nor
the dimension, and it does not supply actual instruments, Lüders updates, a physical clock, a Hamiltonian,
$\hbar$, or commutativity of successive updates; endpoint reciprocity is a static exchange of arguments.
The existing XIII full-support GME route at 166.12 is a separate supplied seed result; this comparison
application neither constructs nor replaces that seed.

For orientation, the finite-support step is standard convex geometry; [Pinelis, *On the extreme points of
moments sets*](https://arxiv.org/abs/1204.0249v1), Theorem 1 and Corollary 4, is relevant general finite-support background, not the source of
the exact comparison criterion above. The exact criterion is the carrier-level application just proved and
the existing full-mixture/circuit theorem supplies its least-confirmation conclusion.

白话说：选一个真正位于整个状态基内部的参考态 $m$，任何有限纯态关系都能以很小的共同份额塞进
两种 $m$ 的分解，剩下同一个混态，所以参考分解值相等就逼出这条关系的比较值平衡；超过实空间维数
的配方又能沿仿射依赖拆成更少标签的配方。于是“一个内点、每个目标、最多 $d$ 个不同纯标签”的
检查与原来所有有限混合检查完全等价。把它放到完整三份量子载体时，$m_3=I/n^3$ 的内点性和
$d_3=n^6$ 来自已有几何，再在 B1--B3 的全部复合条件下调用既有全有限层级定理；它保留经典中心、
直和、Born/POVM/CP 字典及实际来源合同，也没有把静态端点互换变成测量次序、仪器或动力学的公理。
