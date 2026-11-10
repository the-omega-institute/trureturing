---
bibkey: niestegge2023transition
authors: G. Niestegge
year: 2023
title: Quantum transition probability
doi: 10.48550/arXiv.2312.13213
url: https://arxiv.org/abs/2312.13213v2
claim: Proper least confirmation and reciprocal pure-state comparisons admit a finite-dimensional bridge to signed spectrality and self-duality, using the source's proper-effect peeling method.
strata_touched: []
license: citation-only
triage: anchor
---

# Reciprocal least confirmation and the spectrality bridge

[Niestegge, arXiv:2312.13213v2](https://arxiv.org/pdf/2312.13213v2),
Lemma 3(iv), Lemma 5 and Theorem 2(i), give a maximal-value subtraction
argument, joint orthogonal families and spectrality on an order-unit space
with Axioms 1–2 and the proper-effect property $(*)$. Theorem 3 adds
symmetric transition probabilities to obtain a positive definite
self-dualizing inner product. Axiom 1 requires each minimal nonzero extreme
effect to have exactly one normalized state accepting it with certainty;
Axiom 2 requires every pure state to arise from such an effect.

The derivation below is a finite-dimensional premise bridge for the
project's least confirming effects. It uses that subtraction method and
spells out the state–effect and unique-saturation interfaces. It is a
mathematical exposition, not a claim that the cited classification or this
whole bridge has been formalized in Lean. The repository theorem
`D5.S3.Quantum.Foundation.LeastConfirmationGeneration.positive_dual_generation`
proves positive-dual generation, the length bound and the proper-frame bound
under an explicit attained-positive-maximum interface. The remaining
compact-base, state–effect and signed-state bridges below are not
formalized by that theorem.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2312.13213
- Version: https://arxiv.org/abs/2312.13213v2
- Proper-effect Lemma 3(iv), Lemma 5, Theorem 2(i), and Theorem 3.

## Carrier and the retained condition

Use [Definition 26.1 of the quantum-origin volume](../../docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md).
Thus $A$ is a nonzero finite-dimensional real vector space, $C$ is a
closed pointed generating cone, and $u$ is strictly positive on
$C\setminus\{0\}$. The normalized base $K=\{x\in C:u(x)=1\}$ is compact.
Write $P=\operatorname{ext}K$. Every effect in the full interval $[0,u]$
is allowed. Order between functionals means order in the dual cone $C^*$.

Retain precisely Principle S:

$$
e_p\in[0,u],\qquad e_p(p)=1,\qquad
e_p\le f\quad(f\in[0,u],\ f(p)=1),
\tag{1}
$$

$$
e_p(q)=e_q(p)\qquad(p,q\in P).
\tag{2}
$$

Leastness in (1) means below every proper confirming effect. It is not
merely minimality, an arbitrary selected test, or leastness among all
positive functionals. No inner product, reversible group, signed frame
spectrality or unique-saturation assumption is supplied.

Ordinary finite-dimensional convex decomposition gives
$K=\operatorname{conv}P$, $C=\operatorname{cone}P$ and
$\operatorname{span}P=A$. These decompositions have no joint
distinguishability requirement. Compactness also makes $u$ an order unit
for $C^*$: every $g\in A^*$ satisfies $-tu\le g\le tu$ for some $t\ge0$.
In particular $C^*$ spans $A^*$.

## An intrinsic binary comparison and its consistency condition

The proper-effect interval is defined by the carrier. For pure $p$ and
arbitrary normalized $x$, define

$$
T_p(x)=\inf\{f(x):f\in[0,u],\ f(p)=1\}.
$$

This is the least possible false acceptance of $x$ by a test which
certainly accepts $p$. A pointwise infimum need not itself be one effect.
On this finite-dimensional carrier, the following requirements for each
fixed pure $p$ are equivalent:

1. $T_p$ is affine on normalized mixtures.
2. There is one least proper effect confirming $p$.
3. Every finite relation between pure-state preparations is preserved:

$$
\sum_i\lambda_iq_i=\sum_j\mu_jr_j
\quad\Longrightarrow\quad
\sum_i\lambda_iT_p(q_i)=\sum_j\mu_jT_p(r_j),
\qquad
\lambda_i,\mu_j\ge0,\quad\sum_i\lambda_i=\sum_j\mu_j=1.
\tag{9}
$$

To prove the nontrivial direction, define $e_p(x)$ by the average of
$T_p$ over any finite pure-state preparation of $x$. Such preparations
exist by compact finite-dimensional convex geometry, and (9) makes the
definition independent of the preparation. Combining preparations proves
affinity. Its values lie in $[0,1]$, and $e_p(p)=1$. An affine function on
$K$ extends to its relative affine hull, and homogenization gives a
linear proper effect on $A$. For every confirming effect $f$, the
inequality $T_p(q)\le f(q)$ on pure $q$ gives $e_p\le f$ on all of $K$,
hence on $C$. Thus $e_p$ is least and equals $T_p$ everywhere. Conversely,
a least confirming effect realizes the infimum and preserves all mixture
relations by affinity.

Consequently S can be expressed using the carrier-defined comparison:
exchanging its two pure endpoints preserves its value, and replacing a
normalized state by another pure preparation of the same state preserves
the average comparison. This is an equivalent expression of leastness
and reciprocity, not a further deletion of an independent condition.
The substantive reduction in the subsequent argument is the removal of
the separate signed-spectrality input.

For the square $K=[0,1]^2$, its four vertices have
$T_p(q)=\delta_{pq}$, just as four classical pure states do. Nevertheless,
writing $a=(0,0)$, $b=(1,0)$, $c=(0,1)$, $d=(1,1)$ gives
$(a+d)/2=(b+c)/2$, while the proposed comparison average against $a$ is
$1/2$ on the first preparation and zero on the second. Hence the table
does not preserve the actual square's mixture relations, and no least
confirming effect exists at $a$. This is the square obstruction discussed
in the cited source's Section 3, expressed with the proper-effect domain;
it is not claimed as a new counterexample. Numerical endpoint symmetry
alone does not provide a common effect.

The first endpoint must remain pure in this infimum definition. A proper
effect attaining one at a relative interior state is constant one, so
extending the definition to mixed first endpoints does not produce the
symmetric bilinear pairing derived below. That pairing is an extension
of pure comparisons, with a different meaning at mixed first endpoints.

## Positive dual generation and one common complete frame

Even without (2), leastness implies reciprocal zero readings. If
$e_p(q)=0$, then $u-e_p$ confirms $q$, so $e_q\le u-e_p$ and
$e_q(p)=0$. Exchanging the roles gives the converse.

For $0\ne f\in C^*$, let $M=\max_K f$. This maximum is positive and is
attained at a pure state $p$: the maximizing set is a nonempty compact
face. The rescaled functional $f/M$ belongs to $[0,u]$ and confirms $p$.
Consequently

$$
f_1=f-Me_p\in C^*,\qquad f_1(p)=0.
\tag{3}
$$

Repeat (3) on a nonzero residual. Each new confirming effect vanishes on
every previously chosen pure state, because it is bounded above by a
positive multiple of a residual which vanishes there. Reciprocal zero
readings give the reverse vanishing. The resulting evaluations are
$e_{p_i}(p_j)=\delta_{ij}$. The chosen states are linearly independent, so
after at most $\dim A$ subtractions the residual is exactly zero. Thus

$$
C^*=\operatorname{cone}\{e_p:p\in P\}.
\tag{4}
$$

The zero functional uses an empty decomposition. Neither (2) nor signed
spectrality is needed for (4).

For a finite family with $e_{p_i}(p_j)=\delta_{ij}$, induction using (1)
gives $\sum_i e_{p_i}\le u$: the remaining proper effect confirms the next
state. If $h=u-\sum_i e_{p_i}\ne0$, maximize $h$ at a pure $q$ and put
$M=\max_K h>0$. Leastness gives $e_q\le h/M$, so $e_q(p_i)=0$ and hence
$e_{p_i}(q)=0$. Therefore $M=h(q)=1$. Subtracting $e_q$ preserves a
positive residual. Linear independence again forces finite termination.
Every such family therefore extends to a common complete frame:

$$
e_{p_i}(p_j)=\delta_{ij},\qquad \sum_{i=1}^r e_{p_i}=u.
\tag{5}
$$

The positive decomposition of any $f$ can be completed in this same
frame, with zero coefficients on added members. This supplies an actual
joint effect family under Definition 26.1. It does not replace joint
distinguishability by separately chosen pairwise measurements.

## Reciprocal comparison gives signed spectrality

If $\sum_i a_i p_i=0$, reciprocity gives, for every pure $q$,

$$
\left(\sum_i a_i e_{p_i}\right)(q)
=e_q\left(\sum_i a_i p_i\right)=0.
$$

Since pure states span $A$, the assignment $p\mapsto e_p$ therefore
extends uniquely to a linear map $L:A\to A^*$. By (4), its image contains
$C^*$, which spans $A^*$. It is surjective and hence a linear isomorphism.
Moreover $L(C)=C^*$. Reciprocity makes $B(x,y)=(Lx)(y)$ symmetric; this
alone has not yet established positive definiteness.

Given arbitrary $x\in A$, choose $t\ge0$ with $Lx+tu\in C^*$. Use (3)–(5)
to write, in one and the same complete frame,

$$
Lx+tu=\sum_i\lambda_i e_{p_i},\qquad
u=\sum_i e_{p_i},\qquad \lambda_i\ge0.
$$

Injectivity of $L$ now gives

$$
x=\sum_i(\lambda_i-t)p_i,\qquad
B(x,x)=\sum_i(\lambda_i-t)^2.
\tag{6}
$$

This is the original signed frame condition Sp, derived from S. The
square sum is strictly positive when $x\ne0$. Finally $L(C)=C^*$ gives

$$
C=\{x\in A:B(x,y)\ge0\text{ for every }y\in C\}.
\tag{7}
$$

The order-unit bound for arbitrary dual functionals is essential here.
A spanning family of normalized probes and maximum attainment only for
positive functionals suffice for positive-dual generation, but do not
alone imply that the dual cone spans the full dual space. Compactness and
the full closed-cone carrier supply that extra bridge in (6).

Thus Sp is redundant relative to the stated S on this carrier. This is
a revelation of an existing dependence between written premises; it does
not remove finite dimensionality, convex mixing, full effect availability
or leastness. Theorem 26.2's three norm formulas then apply to their
specified norms, with no identification of the operational base norm with
the self-dualizing inner-product norm.

## Exact interface to the cited theorems

Each $e_p$ is extreme in $[0,u]$: a convex decomposition into proper
effects forces both components to confirm $p$, and leastness forces both
to equal $e_p$. If a pure $q$ satisfies $e_p(q)=1$, reciprocity and
leastness give $e_p=e_q$. Reciprocity then gives identical evaluations of
$p,q$ by every $e_r$. Equation (4) implies these effects span $A^*$, so
$p=q$. Ordinary pure-state convex decomposition extends this to

$$
\{x\in K:e_p(x)=1\}=\{p\}.
\tag{8}
$$

A nonzero extreme proper effect $a$ has $\max_K a=1$: otherwise
$a=M(a/M)+(1-M)0$ with $0<M<1$ is a nontrivial convex decomposition.
Choose a pure $q$ attaining that maximum. If also $a\le e_p$, (8) gives
$q=p$, so $e_p\le a$ and $a=e_p$. Hence the $e_p$ are exactly the minimal
nonzero extreme proper effects.

Taking the source's order-unit space to be $(A^*,C^*,u)$ now supplies
Axiom 1 from (8), Axiom 2 from $p\leftrightarrow e_p$, and proper $(*)$
from (1). The information capacity is at most $\dim A$ by frame linear
independence. The source's Theorems 2–3 therefore have the required
premises. The subtraction technique and its spectral consequences are
existing literature; this note does not claim a new general spectral or
classification theorem.

The domain in v2 §3's displayed $(**)$ is different: it takes an infimum
over all positive affine functionals normalized at one state, with no
upper bound by $u$. The [qubit scope test](mullerududec2012selfduality.md#scope-tests)
shows why proper leastness cannot be substituted into that domain. The
bridge here uses proper $(*)$ and Theorems 2–3, and does not invoke
Theorem 1's passage to $(**)$.

## Face geometry and the projective interface

The same paper derivation supplies the face interface needed by
[Barnum–Barrett–Krumm–Müller, arXiv:1508.03107v2](https://arxiv.org/pdf/1508.03107v2),
Definitions 3.2–3.3, Proposition 3.1 and Theorem 6.1. This is an application
bridge to their projective, symmetric-transition setting, not an additional
Lean result or an assumption of filter purity.

Let $U=L^{-1}u$. Every complete frame sums to $U$. For a nonzero cone
face $F$, choose $x$ in its relative interior and a positive spectral
expansion $x=\sum_{i\in I}\lambda_i a_i$ with every $\lambda_i>0$.
Set $s=\sum_{i\in I}a_i$. Positivity and the face property imply
$a_i\in F$. Bounding the coefficients above and below shows that
$s$ and $x$ generate the same face, so $s$ also lies in the relative
interior of $F$. Completion of the frame gives $0\le s\le U$.

The positive functional $B(U-s,\cdot)$ vanishes on $x$, and hence on
$F$. Conversely, if a pure $q$ has $B(U-s,q)=0$, the proper effect
$B(s,\cdot)$ confirms $q$. Leastness gives $e_q\le B(s,\cdot)$;
self-duality makes this $q\le s$, so $q\in F$. Decomposing positive
vectors into pure rays proves

$$
F=C\cap(U-s)^{\perp_B},\qquad s=P_FU,
\tag{10}
$$

where $P_F$ is the $B$-orthogonal projection onto $\operatorname{span}F$.
In particular every face is exposed, and its unit $s_F=P_FU$ is
independent of the chosen interior point and spectral expansion.

Every $v\in\operatorname{span}F$ has a signed expansion inside $F$.
Indeed, take $t>0$ large enough that $ts_F+v$ is in the relative
interior of $F$. Its nonzero spectral terms belong to $F$ and their
unweighted sum is $s_F$ by (10). Subtracting $ts_F$ gives the claimed
signed expansion in this same face frame. If $B(v,y)\ge0$ for every
$y\in F$, evaluation on its frame members makes all these signed
coefficients nonnegative. Thus $F$ is self-dual in its span. The cone is
perfect in the sense of the cited Definition 3.2.

Consequently $P_F$ is positive: its pairing with each $y\in F$ equals
$B(x,y)\ge0$ for positive $x$, and face self-duality applies. Moreover

$$
u(P_Fx)=B(s_F,x)\le B(U,x)=u(x)\qquad(x\in C).
\tag{11}
$$

The complementary face is $F^\perp=C\cap s_F^{\perp_B}$, with unit
$U-s_F$. To see the unit assertion, any pure state in $F^\perp$ is
orthogonal to the frame used for $s_F$; extend that frame by positive
residual peeling. Its completing states belong to $F^\perp$ and sum
to $U-s_F$. Equation (10) then gives $(F^\perp)^\perp=F$.
The positive projections $P_F,P_{F^\perp}$ have complementary positive
images and kernels. They are self-adjoint under the order identification
$L$, so their duals are complemented as well. Equation (11) gives
normalization contraction. Equality in (11) forces $x\in F$ by (10),
and then $P_Fx=x$. These are mathematical filters with every exposed face
as an image; they give projectivity. The cited Proposition 3.1 identifies
all filters with faces and gives the orthomodular face lattice.

For a face frame, $u(s_F)=B(s_F,s_F)$ is its integer length. Any other
frame in the face can be completed to a face frame by the same residual
argument, so this integer is its capacity, the largest jointly
distinguishable pure-state frame size. None of these steps asserts that
$P_F$ sends every external pure state to zero or a pure ray. That is the
remaining condition analyzed in the
[two-pure-state comparison note](miyaderaimai2007landaupollak.md).

## What this geometry does and does not select

The derived pairing identifies a pure state with its least confirming
effect: the object and its reference test occupy the same real geometry.
Positive dual readings can be separated into jointly distinguishable
directions, and the same complete frame permits signed decompositions.
These statements do not require a supplied reversible symmetry group.

Classical simplices and real, complex and quaternionic Jordan systems
remain examples. The candidate does not by itself select a complex
Hilbert space, a tensor product, an allowed instrument menu, complete
positivity, a clock or a Hamiltonian. Endpoint reciprocity does not make
successive physical measurements commute. The full composition and
process contracts in the [spectral strong-symmetry note](barnumhilgert2019spectral.md#complete-conditional-reconstruction-and-its-remaining-contracts)
remain separate obligations.

In ordinary words: each pure state has one least confirming test which
every other certain confirmation must contain, and two pure states give
the same cross-reading when their roles are exchanged. Repeatedly remove
the direction with the largest positive reading; leastness keeps the
remainder positive, and finite dimension makes the removal stop. The
reciprocal rule lets states and tests share one geometry. Spectral
decomposition is a consequence to derive within that model, while
complex-field selection and physical evolution require further bridges.
