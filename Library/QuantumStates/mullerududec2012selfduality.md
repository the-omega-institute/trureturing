---
bibkey: mullerududec2012selfduality
authors: M. P. Müller and C. Ududec
year: 2012
title: The structure of reversible computation determines the self-duality of quantum theory
doi: 10.1103/PhysRevLett.108.130401
url: https://arxiv.org/abs/1110.3516v2
claim: Compact reversible bit symmetry yields a normalized invariant self-dualizing inner product in finite-dimensional general probabilistic theories.
strata_touched: []
license: citation-only
triage: anchor
---

# Bit symmetry and least proper confirmation effects

Theorem 1 of [arXiv:1110.3516v2](https://arxiv.org/pdf/1110.3516v2),
page 3, gives self-duality from bit symmetry. Its inner product is invariant
under the chosen compact reversible group, nonnegative on positive states,
has squared norm one on pure states, and makes perfectly distinguishable
states orthogonal. Page 2 defines bit symmetry as transitivity on ordered
pairs of perfectly distinguishable pure states. It is a requirement on
available reversible transformations, beyond symmetry of a numerical
comparison function. Odd regular polygons, including the pentagon, satisfy
the source's bit symmetry; this conclusion alone does not classify quantum
state spaces.

## Identification with the project's least proper effects

Use the finite-dimensional ordered carrier of
[the quantum-origin volume, Definition 26.1](../../docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md):
a nonzero real vector space $A$, a closed pointed generating cone $C$,
a strictly positive normalization $u$, the compact base
$K=\{x\in C:u(x)=1\}$, and the full proper-effect interval $[0,u]$.
Suppose the physical reversible group is compact and bit-symmetric. Suppose
also that each pure state $w$ has a **least** proper saturating effect:

$$
e_w\in[0,u],\qquad e_w(w)=1,\qquad
e_w\le f\quad\text{whenever }f\in[0,u],\ f(w)=1.
$$

Least means below every such effect in the dual-cone order; uniqueness of a
minimal element would be a different condition. Reciprocity and frame
spectrality are absent from these assumptions.

Apply the source theorem and call its inner product $B$. For pure $w$ put
$f_w=B(w,\cdot)$. If $s$ is pure, positivity and Cauchy–Schwarz give
$0\le B(w,s)\le1$. Every normalized mixed state is a finite convex
combination of pure states, so the same bound holds on $K$. Rescaling
positive vectors gives $0\le f_w\le u$, and $f_w(w)=1$. Full effect
availability therefore makes $f_w$ an admissible proper saturating effect.
This argument uses ordinary convex decompositions, not spectral
decompositions into distinguishable states; mixed states need not have
squared norm one.

Leastness gives $0\le e_w\le f_w$. By self-duality write
$e_w=B(v,\cdot)$ with $v\in C$, and put $r=w-v\in C$.
Saturation and symmetry give $B(w,r)=0$. Consequently

$$
0=B(w,r)=B(v,r)+B(r,r),\qquad
B(v,r)\ge0,\quad B(r,r)\ge0.
$$

Positive definiteness forces $r=0$. Hence

$$
e_w(x)=B(w,x),\qquad
e_w(s)=B(w,s)=B(s,w)=e_s(w).
$$

The cancellation step needs neither an extreme-ray lemma nor spectrality:
it holds whenever a positive functional is dominated by $B(w,\cdot)$ and
agrees with it at $w$. Pure states span $A$, so $w\mapsto e_w$ determines
this bilinear form and its linear state–effect identification uniquely.
The form is also invariant under the supplied reversible group. If $K$ is
a singleton, the generating assumption makes $A$ one-dimensional;
$B(aw,bw)=ab$ and $e_w=u$ give the conclusion directly.

This is an application of the cited self-duality theorem and elementary
inner-product positivity to the project's specified effect interval. It
does not claim a new general self-duality or transition-probability theorem.
In particular, the entire Müller–Ududec theorem is a literature premise,
not a theorem formalized here in Lean.

## What this removes and what it retains

In Definition 26.1, call least proper saturation alone $S_{\min}$.
The application gives

$$
S_{\min}+\text{compact physical bit symmetry}\ \Longrightarrow\ S.
$$

On this carrier, the [proper-effect spectrality bridge](mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)
derives signed frame spectrality Sp from S by finite positive-dual peeling
and a common-frame shift. Theorem 26.2 then supplies its original three
norm formulas without a separate Sp input. That complete bridge remains
a paper derivation; its positive-dual generation step is formalized under
an explicit maximum-attainment interface. Bit symmetry alone does not
supply the leastness used in that bridge or the all-frame strong symmetry
needed for the cited Jordan classification.
Where the original strong symmetry is retained, it already includes
transitivity on two-element frames. The closure of its reversible group
inside the normalized-base automorphism group is compact and retains that
transitivity; using the closure in a geometric existence proof does not
declare its limit transformations physically callable.

Deleting the written reciprocity equality in that stronger context does
not enlarge the resulting model class. The more direct
[spectral strong-symmetry application](barnumhilgert2019spectral.md)
also makes leastness a consequence after Jordan classification. Neither
observation derives these stronger premises from a bare symmetric binary
function.

## Scope tests

The quantum-origin volume's Theorem 27.1 gives a useful boundary. For
$1<p<\infty$, the cone $C_p=\{(t,x):t\ge\|x\|_p\}$ has least proper
saturating effects and signed Sp. Its displayed reciprocity defect is
nonzero for $p\ne2$. Leastness and signed spectrality alone therefore do
not replace the missing dynamical condition.

Conversely, arbitrary proper saturating effects on an ordinary qubit need
not be reciprocal. For pure projectors $P,Q$ with
$c=\operatorname{Tr}(PQ)\in(0,1)$, choose
$E_P=P+t_P(I-P)$ and $E_Q=Q+t_Q(I-Q)$, where
$t_P,t_Q\in[0,1]$ and $t_P\ne t_Q$. Both effects saturate their own states,
but their cross-evaluations differ by $(t_P-t_Q)(1-c)$. Leastness identifies
the effects; self-duality does not identify an arbitrary assigned readout.

The upper bound in $[0,u]$ is essential to the meaning of this application.
For $P_0=|0\rangle\langle0|$ and
$P_\pm=|\pm\rangle\langle\pm|$, the positive operator $2P_-$ saturates
$P_0$ but evaluates to zero at $P_+$, whereas $P_0$ evaluates to $1/2$.
Thus leastness among proper saturating effects is different from leastness
among all positive saturating functionals. Transition-probability results
using the latter domain require their own hypotheses.

The geometry and reciprocity are compatible with classical simplices and
all simple Euclidean Jordan alternatives. They do not select the complex
field, specify a composite or instrument, or make sequential measurements
commute. The comparison $B(w,s)$ exchanges two endpoints of one relation;
it specifies no order of physical updates.

## Reciprocal least confirmation and the spectrality bridge

Source metadata (citation-only; the derivations below retain their stated attribution and proof boundaries):

- **bibkey**: niestegge2023transition
- **authors**: G. Niestegge
- **year**: 2023
- **title**: Quantum transition probability
- **doi**: 10.48550/arXiv.2312.13213
- **url**: https://arxiv.org/abs/2312.13213v2
- **claim**: Proper least confirmation and reciprocal pure-state comparisons admit a finite-dimensional bridge to signed spectrality and self-duality, using the source's proper-effect peeling method.
- **strata_touched**: []
- **license**: citation-only
- **triage**: anchor

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

### Verified locator

- DOI: https://doi.org/10.48550/arXiv.2312.13213
- Version: https://arxiv.org/abs/2312.13213v2
- Proper-effect Lemma 3(iv), Lemma 5, Theorem 2(i), and Theorem 3.

### Carrier and the retained condition

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

### An intrinsic binary comparison and its consistency condition

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

### Positive dual generation and one common complete frame

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

### Reciprocal comparison gives signed spectrality

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

### Exact interface to the cited theorems

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
upper bound by $u$. The [qubit scope test](../QuantumStates/mullerududec2012selfduality.md#scope-tests)
shows why proper leastness cannot be substituted into that domain. The
bridge here uses proper $(*)$ and Theorems 2–3, and does not invoke
Theorem 1's passage to $(**)$.

### Face geometry and the projective interface

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
distinguishable pure-state frame size. No purity-preservation assumption
has entered the construction of these projections.

### Least confirmation forces face-filter purity

The following maximum argument uses the pairing and positive face
projections just derived. It requires full proper-effect leastness and
does not assume covering, two-state face capacity, or filter purity.
It remains a paper argument, not an additional Lean result. The impurity
quantity below also appears in
[Barnum–Müller–Ududec, arXiv:1403.4147v4](https://arxiv.org/html/1403.4147v4),
Definition 27; no literature priority is asserted for this application.

Write $\|x\|^2=B(x,x)$. Convex decomposition into unit-norm pure states
gives $\|x\|\le u(x)$ for $x\in C$. Strict convexity of squared norm
gives $P=K\cap\{x:\|x\|=1\}$, so $P$ is compact and nonempty.
For every pure $r$, Cauchy–Schwarz yields
$B(x,r)\le\|x\|\le u(x)$. Pure rays generate $C$, and self-duality
therefore gives

$$
x\le_C u(x)U\qquad(x\in C).
\tag{12}
$$

Define $I(x)=u(x)^2-\|x\|^2$ on $C$. It is nonnegative and vanishes
exactly at zero and pure rays. Fix a cone face $F$ and set $Q=P_F$,
$s=QU$. The continuous function $r\mapsto I(Qr)$ attains its maximum
$d\ge0$ at a pure state $p$. Put $z=Qp$, $a=u(z)$ and $g=as-z$.
Equation (12) and positivity of $Q$ imply

$$
g=Q(aU-z)\in F,\qquad B(g,p)=a^2-\|z\|^2=d.
\tag{13}
$$

For pure $r$, use the vector
$v_r=(u(Qr),(\mathrm{Id}-Q)r)$ in the Euclidean direct sum
$\mathbb R\oplus A$. Orthogonality gives

$$
\|v_r\|^2=1+I(Qr),\qquad
\langle v_p,v_r\rangle=B(p+g,r).
\tag{14}
$$

Since $p+g\in C$, Cauchy–Schwarz and maximality of $d$ give

$$
0\le B(p+g,r)
\le\sqrt{1+d}\sqrt{1+I(Qr)}\le1+d,
\tag{15}
$$

with equality at $r=p$. The functional
$f=B(p+g,\cdot)/(1+d)$ consequently belongs to the full interval
$[0,u]$ and confirms $p$. Leastness gives $e_p\le f$. By self-duality,

$$
g-dp\in C.
\tag{16}
$$

If $d>0$, the positive decomposition $g=dp+(g-dp)$ and $g\in F$
force $p\in F$. Hence $Qp=p$, contradicting $d=I(p)=0$. Thus $d=0$,
and every pure input is projected either to zero or to a pure ray.
This includes the zero face and the whole cone. The nonzero carrier
ensures a pure maximizer exists; no division by $u(Qp)$ is needed.

The face/filter bijection from Proposition 3.1 above makes every filter
one of these projections. Projectivity, reciprocal transitions and
filter purity therefore meet the hypotheses of Theorem 16 of
arXiv:1403.4147v4, giving general finite-dimensional Euclidean Jordan
state geometry, including direct sums. This classification is used as
an attributed theorem, not proved anew. Neither strong symmetry nor
purity preservation is a separate input to this paper route from S.
The [two-pure-state comparison note](mullerududec2012selfduality.md#two-pure-states-comparison-bounds-and-jordan-geometry)
spells out the resulting two-state faces and probability bound.

### One preparation-comparison equation

Using the original infimum definition of $T$, S is equivalently written

$$
T_p\!\left(\sum_i\alpha_iq_i\right)
=\sum_i\alpha_i T_{q_i}(p)
\quad\left(p,q_i\in P,\quad\alpha_i\ge0,\quad\sum_i\alpha_i=1\right),
\tag{17}
$$

for every finite preparation. A singleton preparation gives reciprocity.
Substituting that equality into (17) preserves every finite preparation
relation and hence gives mixture affinity as above. Conversely affinity
and reciprocity give (17). The equation combines two consistency
requirements; displaying one equality is not by itself a reduction in
their logical content. The substantive paper reduction is that signed
spectrality and face-filter purity are consequences of S on this carrier.

### What this geometry does and does not select

The derived pairing identifies a pure state with its least confirming
effect: the object and its reference test occupy the same real geometry.
Positive dual readings can be separated into jointly distinguishable
directions, and the same complete frame permits signed decompositions.
The face argument supplies purity-preserving filters and the attributed
Jordan classification. These statements do not require a supplied
reversible symmetry group, and the full chain is not Lean-formalized here.

Classical simplices and real, complex and quaternionic Jordan systems
remain examples. The candidate does not by itself select a complex
Hilbert space, a tensor product, an allowed instrument menu, complete
positivity, a clock or a Hamiltonian. Endpoint reciprocity does not make
successive physical measurements commute. A [composite premise bridge](barnumhilgert2019spectral.md#local-comparison-and-composite-frames)
derives product purity, complete product frames, comparison factorization
and rank multiplication under its positive bilinear state/effect product
contract, including the pairing and unit identities, with S on both
factors and their locally tomographic composite. It also derives
composite simplicity when both local comparison graphs are connected;
for a self-composite, connectedness of its local system suffices.
Compatible products and local tomography remain separate inputs.
Connectedness is needed for the single-sector conclusion; the
self-composite sector argument classifies complex matrix sectors without
assuming connectedness. The process contracts in the
[spectral strong-symmetry note](../QuantumStates/barnumhilgert2019spectral.md#complete-conditional-reconstruction-and-its-remaining-contracts)
remain separate obligations.

In ordinary words: each pure state has one least confirming test which
every other certain confirmation must contain, and two pure states give
the same cross-reading when their roles are exchanged. Repeatedly remove
the direction with the largest positive reading; leastness keeps the
remainder positive, and finite dimension makes the removal stop. The
reciprocal rule lets states and tests share one geometry. Spectral
decomposition is a consequence to derive within that model, while
complex-field selection and physical evolution require further bridges.

## Two pure states, comparison bounds and Jordan geometry

Source metadata (citation-only; the derivations below retain their stated attribution and proof boundaries):

- **bibkey**: miyaderaimai2007landaupollak
- **authors**: T. Miyadera and H. Imai
- **year**: 2007
- **title**: Generalized Landau-Pollak Uncertainty Relation
- **doi**: 10.48550/arXiv.0707.4450
- **url**: https://arxiv.org/abs/0707.4450v3
- **claim**: The weak Landau-Pollak inequality bounds the sum of two projection probabilities by one plus the operator norm of their product.
- **strata_touched**: []
- **license**: citation-only
- **triage**: anchor

[Miyadera–Imai, arXiv:0707.4450v3](https://arxiv.org/pdf/0707.4450v3),
Section 2, equation (1), states the weak Landau–Pollak bound for rank-one
quantum projections. Theorem 2 gives, for arbitrary orthogonal projections
$P,Q$ on a Hilbert space and any density operator $\rho$,

$$
\operatorname{tr}(\rho P)+\operatorname{tr}(\rho Q)
\le 1+\|PQ\|.
$$

For rank-one $P,Q$, $\|PQ\|=\sqrt{\operatorname{tr}(PQ)}$.
The source already assumes Hilbert-space quantum mechanics. Its theorem
therefore cannot establish the same bound in a general ordered model.
The argument below relates this numerical bound to two-state face
geometry in the project's comparison reconstruction. It is a
paper derivation and an application of attributed classification results;
no claim of literature priority or Lean verification is made.

### Carrier, comparison and two-state faces

Use the nonzero finite-dimensional ordered carrier, full proper-effect
interval and Principle S from the
[least-confirmation note](mullerududec2012selfduality.md#carrier-and-the-retained-condition).
For a pure state $p$ and a normalized state $x$, define

$$
T_p(x)=\inf\{f(x):0\le f\le u,\ f(p)=1\}.
$$

S requires that $T_p$ preserve probability mixtures and that
$T_p(q)=T_q(p)$ for pure $p,q$. Mixture preservation is equivalent to
one least proper confirming effect. The first endpoint in this infimum
remains pure. These are conditions on comparisons and preparation
relations, not an assertion that successive measurements commute.

The cited note's paper derivation gives the positive definite pairing
$B$, a vector $U$ with $u=B(U,\cdot)$, signed spectral decompositions in
complete orthonormal pure frames, and projectivity with canonical
orthogonal face projections. Write

$$
\tau(p,q)=T_p(q)=B(p,q),\qquad B(p,p)=1.
$$

A complete frame $(a_i)$ satisfies $\sum_i a_i=U$. Each cone face $F$
has unit $s_F=P_FU$ and capacity
$\operatorname{cap}(F)=u(s_F)=B(s_F,s_F)$, equal to its frame length.
The face lattice is atomic and orthomodular. These supplied bridges
remain paper results, including when used below.

Let $p\vee q$ denote the smallest cone face containing the two pure
rays. The geometric property of interest is

$$
\operatorname{cap}(p\vee q)\le2\qquad(p,q\text{ pure}).
\tag{J2}
$$

It says that the smallest face containing two pure possibilities cannot
contain any three pure states perfectly distinguished by one common
measurement. The triple need not include either original state. This concerns that
entire face; testing only the straight line segment between $p$ and $q$
would be a different, weaker statement. The
[maximum-impurity argument](mullerududec2012selfduality.md#least-confirmation-forces-face-filter-purity)
derives purity of all face projections from S on the stated carrier.
The following construction consequently derives J2 without a separate
two-state or covering assumption. These are paper arguments, not a
formalization of the full chain.

### A capacity-two face from two pure states

For distinct pure $p,q$, put $t=B(p,q)<1$ and
$D=C\cap p^{\perp_B}$. Properness of $e_p$ gives $U-p\in D$;
since $p\perp\operatorname{span}D$, $P_DU=U-p$. Therefore
$u(P_Dq)=1-t>0$. Face-filter purity makes

$$
r=\frac{P_Dq}{1-t}
$$

a pure state in $D$. Orthogonal projection gives $B(q,r)=1-t$.
The vector

$$
w=U-p-r=P_D(U-r)\in C
$$

is orthogonal to $p,q,r$. Positivity follows from $U-r\in C$ and
positivity of $P_D$. The exposed face $H=C\cap w^{\perp_B}$ contains
$p,q,r$, and its unit is $s_H=P_HU=p+r$. Hence its capacity is two,
and $p\vee q\subseteq H$ proves J2. A face of capacity one is a pure
ray, so two distinct pure states in fact generate capacity exactly two.
When $p=q$, the capacity is one. The case $w=0$ is allowed.

If the whole system has capacity three, $u(w)=1$ and
$\|w\|^2=B(w,U-p-r)=u(w)=1$, so $w$ is pure. It is the unique pure
state having zero comparison with both $p$ and $q$. Indeed any such
$h$ lies in $D$ and satisfies
$B(h,r)=B(h,P_Dq)/(1-t)=0$, whence $B(h,w)=1$; unit norms force
$h=w$. Thus $T_w=0$ is a supporting hyperplane containing the entire
line segment $[p,q]$. Distinctness of $p,q$ is essential to uniqueness.

### A three-comparison expression of exactly the same condition

In this geometry, J2 is equivalent to

$$
\tau(p,r)+\tau(q,r)\le1+\sqrt{\tau(p,q)}
\qquad(p,q,r\text{ pure}).
\tag{WLP}
$$

To prove the equivalence, fix $p,q$, put $t=\tau(p,q)$ and take a
positive spectral expansion $p+q=\sum_i\lambda_i a_i$ in a complete
frame. Then

$$
\sum_i\lambda_i=2,\qquad
\sum_i\lambda_i^2=2+2t,
\qquad\lambda_i\ge0.
\tag{1}
$$

Let $M=\max_i\lambda_i$ and label a maximal term by $i=1$.
For any pure $r$, the numbers $B(a_i,r)$ are nonnegative and sum to one.
Their weighted average is $B(p+q,r)$, with value $M$ attained at
$r=a_1$. In particular

$$
M=\max_{r\text{ pure}}[\tau(p,r)+\tau(q,r)]\ge1+t\ge1.
\tag{2}
$$

Equations (1) give

$$
2+2t=M^2+\sum_{i\ge2}\lambda_i^2
\le M^2+(2-M)^2.
$$

Thus S already gives the reverse bound $M\ge1+\sqrt t$. If WLP also
holds, equality forces at most one nonzero coefficient after $\lambda_1$.
The support of $p+q$ is precisely $p\vee q$, so its capacity is at most
two. Conversely J2 permits at most two nonzero spectral terms in (1).
Their values are $1\pm\sqrt t$, giving WLP by (2). This includes $p=q$.

The exact defect can be written without any new primitive objects:

$$
\delta(p,q)=M-1-\sqrt t\ge0,\qquad
\sum_{2\le i<j}\lambda_i\lambda_j
=\delta(p,q)(2\sqrt t+\delta(p,q)).
\tag{3}
$$

Consequently $p\vee q$ has capacity greater than two precisely when
$\delta(p,q)>0$. A maximal spectral state $a_1$ then gives an explicit
third pure state violating WLP in the supplied spectral geometry.
The moment identities alone supply the lower bound; face-filter purity
and the two-state construction supply the upper bound, so in S the
defect is zero. WLP is an equivalent expression of J2 within this
geometry, not an additional independent assumption in the paper route.

### From the two-state condition to purity-preserving filters

The relevant established interface is
[Barnum–Müller–Ududec, arXiv:1403.4147v4](https://arxiv.org/html/1403.4147v4),
Theorem 16: finite-dimensional projectivity, symmetric transition
probabilities and purity-preserving filters characterize formally real
Jordan state spaces. Theorem 17 has additional symmetry assumptions
and is not used here. The equivalence of filter purity and the covering
law in the projective setting is also discussed at the end of its
Section V, with references to Guz's filter theory.

For completeness, the required lattice bridge can be proved in the
present geometry. The covering law says that $F\vee a$ has no strict
intermediate face above $F$ whenever $a$ is an atom outside $F$.
Suppose J2 holds and write $F=d_1\vee\cdots\vee d_k$ using an
orthogonal face frame. Starting with $a_0=a$, successively make the atom
orthogonal to each $d_i$. If it already is, keep it. Otherwise replace it
inside $H_i=d_i\vee a_{i-1}$ by
$a_i=H_i\wedge d_i^\perp$. J2 makes this relative complement an atom.
The case $a_{i-1}=d_i$ is excluded by the invariant
$F\vee a_{i-1}=F\vee a\ne F$.

At every step $d_i\vee a_i=d_i\vee a_{i-1}$. Earlier orthogonality
persists because both generators of $H_i$ lie in each earlier
$d_j^\perp$. The final atom $b$ is orthogonal to $F$ and
$F\vee b=F\vee a$. Orthomodularity gives an interval isomorphism
$[F,F\vee b]\simeq[0,b]$ by intersecting with $F^\perp$; its inverse
is joining with $F$. The latter interval has two elements, proving
covering. Conversely covering makes the join of two distinct atoms
have capacity two, giving J2.

For an arbitrary face $F$ and pure $p$, the support face of its positive
projection obeys the Sasaki formula

$$
\operatorname{face}(P_Fp)=F\wedge(F^\perp\vee p).
\tag{4}
$$

Indeed $B(y,P_Fp)=B(y,p)$ for $y\in F$. The relative orthogonal
complement of the support is therefore $F\wedge p^\perp$; taking its
relative orthogonal complement and using De Morgan's law gives (4).
The support of zero is the zero face. Covering and the interval
isomorphism above make (4) either zero or an atom. Thus all face
projections preserve pure rays. Conversely that preservation makes
$F^\perp\wedge(F\vee p)$ an atom for $p\not\le F$, and
orthomodularity gives $F\vee p=F\vee[F^\perp\wedge(F\vee p)]$.
The same interval argument proves covering.

Proposition 3.1 of
[arXiv:1508.03107v2](https://arxiv.org/pdf/1508.03107v2)
identifies filters uniquely with faces. Hence purity of these canonical
projections supplies exactly the filter hypothesis of Theorem 16.
Within the supplied S geometry this proves the paper-level chain

$$
\mathrm{WLP}\iff\mathrm{J2}\iff\text{covering law}
\iff\text{all filters preserve pure rays}
\iff\text{finite-dimensional Jordan state geometry}.
\tag{5}
$$

The last reverse implication uses the usual positive spectral and
purity-preserving compression properties of Euclidean Jordan algebras.
It includes finite direct sums and classical simplices.

### The two-state picture is a ball

S already makes the normalized base of any capacity-two face a Euclidean
ball. To see this, let $s=s_F$, so $B(s,s)=2$. Every pure $a\in F$
has a complementary pure state $s-a$, giving
$\|a-s/2\|_B^2=1/2$. Each nonzero direction
$v\in\operatorname{span}F\cap s^\perp$ has a signed two-term
face expansion $v=\lambda a-\lambda(s-a)$. Thus every direction reaches
that pure-state sphere. Taking its convex hull gives

$$
K\cap F=\frac{s}{2}+
\left\{v\in\operatorname{span}F\cap s^\perp:
\|v\|_B\le\frac1{\sqrt2}\right\}.
\tag{6}
$$

The one-dimensional ball is a line segment. J2 makes the smallest face
of every two distinct pure states such a ball. This does not force the
whole state space to be a ball or choose a three-dimensional Bloch ball.
If the whole system has capacity three, J2 is equivalent to saying
that every pure-state midpoint $(p+q)/2$ lies on the relative boundary
of $K$: its support is $p\vee q$, and a proper face has smaller
capacity. The construction of $w$ above excludes an interior midpoint
and supplies its unique pure zero-comparison witness when $p\ne q$.
This uses the global face-filter argument, not local ball geometry alone.

### Complete conditional candidate and its scope

On the stated finite-dimensional full-effect carrier, the complete
candidate is S: the carrier-defined comparison preserves mixtures and
exchanging its pure endpoints preserves its value. The
[preparation-comparison equation](mullerududec2012selfduality.md#one-preparation-comparison-equation)
combines these two requirements. The preceding paper bridges and
Theorem 16 give precisely general finite-dimensional Euclidean Jordan
state spaces; their usual trace pairing satisfies S conversely. Filter
purity, J2 and WLP are consequences on this route. The full bridge and
maximum argument remain unformalized in Lean; the positive-dual theorem
alone does not certify this classification.

For the converse, in an EJA's trace representation a primitive idempotent
$p$ represents a pure state. If $0\le a\le U$ and $B(a,p)=1$, then
$U-a$ belongs to the complementary face $p^\perp$. Its positive face
projection fixes $U-a$ and maps $U$ to $U-p$. Applying that projection
to $U-a\le U$ gives $U-a\le U-p$, or $a\ge p$. Thus $p$ is the least
proper confirming effect, and its trace pairing is affine and reciprocal.

This permits classical simplices, real, complex and quaternionic matrix
systems, spin factors, the Albert algebra, and finite direct sums. It
does not supply the composite, tomography and process conditions needed
to select complex quantum mechanics and its allowed instruments.
Existence of mathematical filters does not assert physical availability
of every filter. No clock or Hamiltonian is selected.

In ordinary words: use the least possible false-acceptance probability
as the comparison reading. Comparing after a random pure preparation
gives the same result as reversing each comparison first and then
averaging. In the stated model the paper argument makes a face filter
preserve pure inputs, and makes every two pure states generate a local
ball-shaped face. Those local parts fit into Jordan geometry. This is
an explicit mathematical candidate with the displayed carrier and
effect assumptions, not a claim that all physical measurement orders
commute or that complex quantum dynamics has been reconstructed.

## Appendix: unordered distinguishable-pair transitivity

The preceding application uses the ordered-pair form of the
Müller–Ududec bit-symmetry hypothesis.  The same self-duality conclusion
already follows from the following weaker relation, while the least-effect
condition remains a separate premise.

Let $V$ be a nonzero finite-dimensional real ordered space with closed pointed
generating cone $C$, strictly positive order unit $u$, compact base
$K=C\cap\{u=1\}$, pure-state set $P=\operatorname{ext}K$, and the full
proper-effect interval $[0,u]\subseteq C^*$.  Let $G$ be compact and act
by $u$-preserving cone automorphisms.  Pure $p,q\in P$ are perfectly
distinguishable when a proper effect has readings $1$ and $0$ on them.
Assume that whenever $\{p,q\}$ and $\{p',q'\}$ are distinguishable pure
pairs, some $g\in G$ maps one unordered set to the other.  Write
$d=\operatorname{affdim}K$.

### The local bridge to pure-state transitivity

Assume first that $d\ge2$.  Every pure $p$ has a pure distinguishable
partner.  Indeed, choose a nonconstant affine functional supporting $K$ at
a face containing $p$, and choose a pure point in the opposite minimizing
face.  After affine rescaling, that functional is a proper effect with
readings $1$ and $0$ on the two points.  This uses only compact finite
convex geometry; it does not assume that $P$ is connected.

Fix one distinguishable edge $\{a,b\}$, and put
$$
 O_0=Ga,\qquad O_1=Gb.
$$
The partner property and unordered transitivity give
$P=O_0\cup O_1$.  If the two orbits meet, $G$ is already transitive on
$P$.  Suppose they are disjoint.  Every distinguishable edge then crosses
from $O_0$ to $O_1$; this says nothing about arbitrary cross-orbit pairs.
Let $W$ be the translation space of $\operatorname{aff}K$, and choose an
origin $o\in\operatorname{aff}K$.  For nonzero $\ell\in W^*$, set
$$
 h_i(\ell)=\max_{x\in O_i}\ell(x-o),\qquad D(\ell)=h_0(\ell)-h_1(\ell).
$$
The maxima exist because the orbits are compact.

The function $D$ never vanishes on the dual unit sphere.  If
$h_0(\ell)=h_1(\ell)$, choose pure maximizers $p_i\in O_i$ and a pure
global minimizer $r\in P$.  Since $\ell$ is nonzero and $K$ has full
affine dimension in its affine hull, the maximum exceeds the minimum.
Thus each $p_i,r$ has distinct endpoints and is a distinguishable pair,
because the same affine functional attains its maximum and minimum there.
Whichever orbit contains $r$, one of these edges has both endpoints in that
orbit, contradicting the crossing property.  Since $d\ge2$, the sphere
$S^{d-1}$ is connected, so the nonzero continuous function $D$ has one
constant sign.  If $D>0$, support-function domination gives
$\operatorname{conv}(O_1)\subseteq\operatorname{conv}(O_0)$; if $D<0$, the
reverse inclusion holds.  Either inclusion is impossible: a point of $O_i$
is extreme in $K$, while a point of one orbit lying in the convex hull of
the other would have to equal one of its points.  Thus the disjoint case is
impossible, and unordered transitivity implies ordinary pure transitivity.

This is the only new geometric bridge.  In particular, it does not infer
that every cross-orbit pair is distinguishable, and it does not use a
connectedness assumption on the pure-state set.

### Reusing the self-duality proof

Haar-average a pure state over $G$ to obtain the invariant state $\mu$.
Write $\widehat x=x-u(x)\mu$.  On $\ker u$, choose a $G$-invariant
inner product $Q$, scaled so that
$Q(\widehat p,\widehat p)=1$ for every pure $p$.  Put
$$
 c=\min_{x,y\in K}Q(\widehat x,\widehat y).
$$
Bilinearity lets a minimizer be chosen pure in both variables.  The original
Müller–Ududec argument gives $c<0$, and for each pure $p$ defines
$$
 E_p(x)=\frac{Q(\widehat p,\widehat x)-c\,u(x)}{1-c}.
$$
The bounds $c\le Q(\widehat x,\widehat y)\le1$ show that $E_p$ is a proper
effect and $E_p(p)=1$.  If $Q(\widehat p,\widehat q)=c$, it confirms $p$
and has zero reading at $q$.  The strict inequality $c<0$ can also be seen directly:
if $c=0$, the proper effect $E_p$ would vanish on the Haar average of
its own orbit, while being nonnegative on that orbit and equal to one at
$p$.

A minimizing pure pair is distinguishable.  Unordered transitivity and
$G$-invariance of $Q$ therefore transport its scalar value $c$ to every
distinguishable pure pair, without choosing an orientation.  If arbitrary
states $x,y$ are distinguishable, decompose them into pure states.  The
proper effect witnessing $x,y$ has constant $1$ on every pure summand of
$x$ and constant $0$ on every pure summand of $y$.  Every cross pair is
therefore distinguishable, and ordinary bilinearity gives
$Q(\widehat x,\widehat y)=c$.

The remainder of the cited proof is unchanged.  For an exposed ray
$\mathbb R_+E\subseteq C^*$, choose an exposing $x\in C$, normalize $E$
so its maximum on $K$ is one, and choose a pure maximizer $p$ on the face
where $E$ is one.  That face is distinguishable from $x/u(x)$, hence
$E_p(x)=0$; exposedness makes $E_p$ a positive multiple of $E$.
Straszewicz density then represents every extremal dual ray in this way.
Define
$$
 B(x,y)=\frac{Q(\widehat x,\widehat y)-c\,u(x)u(y)}{1-c}.
$$
This is a normalized, $G$-invariant positive-definite bilinear form and
$E_p=B(p,\mathord\cdot)$.  Every extremal ray of $C^*$ consequently lies
in $C$ under the $B$-identification, while every pure ray of $C$ gives a
positive functional $B(p,\mathord\cdot)$.  Since the two cones are generated
by their extremal rays, $C=C^*$.  This is precisely the original exposed-ray
and Straszewicz completion, applied after the local bridge to pure-state transitivity
rather than by assuming ordered bit symmetry at the outset.

### Least effects remain independent

Suppose, separately, that every pure $p$ has a least proper confirming
effect $e_p$.  Since $E_p$ confirms $p$, leastness gives
$e_p\le E_p=B(p,\mathord\cdot)$.  Self-duality writes
$e_p=B(v,\mathord\cdot)$ with $v\in C$; put $r=p-v\in C$.  Then
$$
 0=B(p,r)=B(v,r)+B(r,r),
$$
and both terms are nonnegative, so positive definiteness gives $r=0$.
Thus $e_p=B(p,\mathord\cdot)$.  Because pure states span $V$, this also
gives uniqueness, the intrinsic comparison $T_p=e_p$, reciprocity, and the
full finite preparation comparison $S$ already used in this note.  The
known odd-regular-polygon examples already show that bit symmetry does not
supply least proper confirmation; the square obstruction above separately
records failure of mixture consistency.

### Exceptional dimensions and controls

For $d=0$, $C$ is a single ray, $K=\{p\}$, and $B(ap,bp)=ab$.  For $d=1$, write
$K=[p,q]$.  In the cone coordinates,
$$
 B(\alpha p+\beta q,\gamma p+\delta q)=\alpha\gamma+\beta\delta,
$$
and the least effects are the two coordinate functionals.  The group need
not exchange the endpoints: even the trivial group satisfies unordered
transitivity on the sole unordered pair, and the displayed $B$ is invariant
under every endpoint permutation.

The weakening of the chosen-group condition is strict.  For the classical
three-state simplex, let $G=C_3$ act by cyclically permuting the vertices.
All distinct pure pairs are distinguishable and form one unordered orbit.
The ordered pairs split into the two cyclic orientations, so $G$ is not
ordered-pair-transitive and contains no endpoint swap.  The least effects are
the coordinate effects and $B$ is their reciprocal dot product.

The result is an elementary extension of the attributed Müller–Ududec proof,
not a new classification.  The self-duality result retains finite
dimensionality, the full proper-effect interval, and compactness, and uses
unordered symmetry without leastness.  The additional intrinsic identification
$T_p=e_p$ separately retains leastness.  The result does not select complex
quantum theory, composites, dynamics, measurement-sequence commutativity, or
physical availability of every mathematical automorphism.  It is a paper
argument and makes no formal-verification claim.

## Appendix: a fixed-half pure–mixed entrance to S

Use the same nonzero finite-dimensional real ordered carrier $(A,C,u)$, entire compact base $K$, pure set
$P=\operatorname{ext}K$, and full effect interval $[0,u]$ as above. The reused results are in
[the quantum-origin volume, Chapters 77–79](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md).
Definition 77.1 and Proposition 77.2 give the nonempty compact sets $F_p=\{f\in[0,u]:f(p)=1\}$ and attained
comparisons $T_p(x)=\min_{f\in F_p}f(x)$, with $T_p(p)=1$ and $K=\operatorname{conv}P$. No closedness of $P$,
exposedness of its points, or actual preparation procedure is assumed. Here S is exactly (17), equivalently
reciprocal **least** proper confirmation, in the dual-cone order on the entire $C$.

**Definition (fixed-half law).** Require just

$$
\mathrm B_{1/2}:\qquad
T_p\!\left(\frac{q+x}{2}\right)
 =\frac{T_q(p)+T_p(x)}2
 \qquad(p,q\in P,\ x\in K).
\tag{FH1}
$$

The remainder $x$ ranges over the original entire base, including mixed states. The fixed half concerns this
comparison law alone.

**Theorem (same-carrier equivalence).** On this carrier,
$\mathrm B_{1/2}\Longleftrightarrow S\Longleftrightarrow\mathrm B_{\rm mix}$ of Definition 77.18, including every
real $t\in[0,1]$ in its last law. Neither reciprocity nor a least confirming effect is an extra premise.

**Proof.** In (FH1) put $x=q$. Then $2T_p(q)=T_q(p)+T_p(q)$, so $T_p(q)=T_q(p)$ for all pure endpoints. Fix $p$ and
any nonempty finite list $q_1,\ldots,q_n\in P$. Form

$$
y_1=q_1,\qquad y_{j+1}=\frac{q_{j+1}+y_j}{2},\qquad
w^{(1)}_1=1,\quad
w^{(j+1)}_i=\tfrac12w^{(j)}_i\ (i\le j),\quad
w^{(j+1)}_{j+1}=\tfrac12.
\tag{FH2}
$$

Every $y_j$ is an original state. These weights are strictly positive and sum to one. Induction using (FH1) and the
just-derived reciprocity gives $y_n=\sum_iw^{(n)}_iq_i$ and $T_p(y_n)=\sum_iw^{(n)}_iT_{q_i}(p)$. Apply Lemma 77.11
directly: this positive-support equality gives

$$
\bigcap_{i=1}^n A_{pq_i}\ne\varnothing,\qquad
A_{pq}=\{f\in F_p:f(q)=T_p(q)\}.
\tag{FH3}
$$

The same lemma now gives (17) for every real probability vector on that support, not just dyadic weights. Its
zero-weight and repeated-label clauses restore those cases; $n=1$ is the reciprocity already obtained. Thus S holds.
For completeness, (FH3) for every finite support and compactness of $F_p$ give $e_p\in\bigcap_{q\in P}A_{pq}$. Each
$A_{pq}$ is closed in $F_p$; the indexing set $P$ need not be closed. For every $f\in F_p$, $e_p(q)\le f(q)$ on $P$,
hence on $C=\operatorname{cone}P$ by linearity. Thus $e_p$ is least, rather than merely minimal, and $T_p=e_p$ on
$K$. If $K$ is a singleton, $F_p=\{u\}$ and all these statements hold directly.

Conversely, assume S and take a finite pure decomposition $x=\sum_i v_i r_i$, supplied by Proposition 77.2. Apply
(17) to $x$ and to $tq+(1-t)x$, using the weights $t,(1-t)v_i$. For every real $0\le t\le1$,

$$
T_p(tq+(1-t)x)
 =tT_q(p)+(1-t)\sum_i v_iT_{r_i}(p)
 =tT_q(p)+(1-t)T_p(x).
\tag{FH4}
$$

This includes $t=0,1$ and gives $\mathrm B_{\rm mix}$, whose $t=1/2$ instance is (FH1). No limiting argument or
closure of pure states is used. ∎

**Binary-tree geometry.** (FH2) is a finite binary tree: each new node joins one pure leaf to the entire previously
formed mixed subtree. Every leaf has positive weight at the root. Lemma 77.11 says that the root equality selects
one effect on the common intersection of all its minimizing faces $A_{pq_i}$ in the same $F_p$. Reweighting moves
within the convex hull of these leaves while that one effect remains minimizing. Compactness joins the finite
intersections into a single least effect for the whole base. This is a statement about one common effect, not
independently chosen optimizers or an asserted order-independence of measurement updates.

**Control (the mixed remainder is essential).** Reuse the $q=3$ strip of equation (77.7) and Theorem 77.7, with its
entire proper-effect interval. All pure binary preparations satisfy $S_2$. Nevertheless, for $p=r_1$, $q=c_3$,
$x=(c_1+c_2)/2$, the exact values are

$$
T_{c_3}(r_1)=T_{r_1}(x)=0,\qquad
T_{r_1}\!\left(\frac{c_3+x}{2}\right)
 =\min\{\tfrac14,\tfrac14,\tfrac12\}=\tfrac14.
\tag{FH5}
$$

Thus the two sides of (FH1) are $1/4$ and $0$. This midpoint is not the uniform column center; the latter has
reading $1/3$. Restricting $x$ to a pure state would miss this failure. The existing finite-arity, free-sum and
circuit results of Chapter 77 retain their original scope.

### Substitution into the complete normalized candidate

**Definition (fixed-half candidate).** Take exactly Definition 79.14, replacing only its comparison entry,
separately for each $X=A,D,E$, by $(\mathrm B_{1/2})_X$ on the same $(X,C_X,u_X,K_X,P_X,[0,u_X])$. Keep every other
predicate and witness of Definitions 79.1–79.2 and 79.14:

- The original real bilinear $L:D\times A\to E$ and real linear $p:E\to D$ both remain positive on their entire
  original cones, including entangled inputs. After the comparison bridge, $u_X=\tau_X$ and $\omega=1_D/\tau_D1_D$.
  Retain $K(a)=pL(\omega,a)$, $M(a,b)=pL(K(a),b)$, $Q(a,b,c)=L(M(a,b),c)$, $J(a)=M(a,1_A)$, $H(d)=L(d,1_A)$,
  $B_1=pH$: the same actual $p$ is used twice. Both real spans $\operatorname{span}_{\mathbb R}M(A,A)=D$ and
  $\operatorname{span}_{\mathbb R}L(D,A)=E$, and full-real $Z:B_1M(a,b)=u_A(a)Jb$ for all $a,b\in A$, remain.
- Retain $D_J:a,b\in C_A,\ \langle a,b\rangle_A=0\Rightarrow Ja\perp Jb$ and
  $D_H:d,d'\in C_D,\ \langle d,d'\rangle_D=0\Rightarrow Hd\perp Hd'$. Alternatively retain exactly 79.14's
  $\mathsf{JG}_3$ generating complete frames and both same-frame zero tables for $J$ and $HF$, with $U=M(1_A,1_A)$
  and $F=P_{U^{-1/2}}M$. The optional single defect is exactly Theorem 78.4, displayed equation (78.5), with
  $H_{\mathrm s}=H$ and its original generating-frame parameters; its quantitative extra hypotheses are not part of
  the exact candidate.
- Fix the original $t,s\in(0,1)$, unrelated to the comparison half. Retain $\Phi(C_A)\subseteq C_A$, $u_A\Phi=u_A$,
  and $\{f\in A^*:f\Phi=f\}=\mathbb R u_A$ over all real functionals. With the original $m_2=u_DM$ and $m_3=u_EQ$,
  retain **both** mass identities

  $$
  \begin{aligned}
  m_2(a,b)&=t\,m_2(\Phi a,b)+(1-t)m_2(a,\Phi b),\\
  m_3(a,b,c)&=st\,m_3(\Phi a,b,c)+s(1-t)m_3(a,\Phi b,c)
   +(1-s)m_3(a,b,\Phi c)
  \end{aligned}
  \tag{FH6}
  $$

  for all original positive $a,b,c$, including zero and unequal masses, and the original anchor
  $u_EL(\omega,1_A/n)=1$, $n=\tau_A1_A$.
- Retain the exact NB or H13 predicate of 79.14: the same qualified original total-trace-one state and the entire
  positive output under its original $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$,
  $T_{\rm raw}(a,c)=L(Ja,c)$. Active means both endpoint ranks are at least two. NB retains strictly positive block
  mass, conditional joint purity and intrinsically mixed margins. H13 retains a strictly negative direction in at
  least one of $\alpha_{ik}\alpha_{ik}^*x-x$, $\beta_{ik}\beta_{ik}^*x-x$ for $x=\pi_{ik}\rho$, with
  $\alpha_{ik}=F(-,c_k)|_{A_i}$, $\beta_{ik}=F(c_i,-)|_{A_k}$, original trace adjoints and unnormalized units. It
  imposes no purity or fixed Schmidt spectrum. Inactive blocks remain arbitrary positive components including zero;
  an empty active set gives the entire state base. The qualified state is not replaced or selected by its output.

**Corollary (identity of actual model classes).** After forgetting just the mathematical witnesses, this candidate
has exactly the actual model class of Theorem 79.15, under the identity correspondence on $(A,D,E,C_X,u_X,L,p)$ and
the same original $\omega$. **Proof.** Apply the theorem above in each original $X$ to recover S before the
least-effect/Jordan geometry bridge or any normalization consumer. All remaining predicates are exactly 79.14, so
Theorem 79.15 applies with the same $t,s,\Phi$, zero/direction witnesses and scalar anchor. Conversely S gives (FH1)
on those same carriers; nothing else is changed. ∎

The resulting Born pairing, specified two- and three-copy tensors and unique readbacks are precisely (79.17),
(79.27). Every process/source prerequisite in §79.8 remains: the same actual event, branch and record,
product-extension law, sufficient actual reference and full joint-cone positivity for CP/Kraus; both budgets (79.28)
and the same complete menu's total TP; positive-mass conditioning, zero-branch records, sequential and
coarse-graining contracts; sharp neutrality for Lüders; and the supplied continuous time-homogeneous reversible
$*$-automorphism group, original clock and units for Hamiltonian evolution. No higher-copy or alternative bracketing
source compatibility is supplied by this substitution.

两两比较的端点互换，只说两个纯态的比较数相同，不等于两次测量交换次序后仍有同一状态更新。这里的对半关系还要求：一端是纯态，另一端可以是原系统中任意已有混态，比较整个混合所得的数必须与先分别比较再平均一致。把有限多个纯态接成二叉树，每个叶子都占正份额，根节点的等式就要求同一个确认效应同时在所有叶子上取到最小值；因此改变成任意实概率权重仍成立。三条带例子说明，只检查两个纯态会漏掉这个共同要求。这个入口删除的是定义 77.18 对混合比例的全量词，全部状态、效应、混合余项以及第 79 章的质量、方向和来源条件仍完整保留；它没有把数学混合或数学见证变成实际可调用的准备与操作。

## Original probability images and the complete comparison interface

This is a literature application to the original preparation, test and process
interface of the current [Theorem 81.8, equation (81.14)](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md#81-对角几何的单个内在投影与完整量子候选),
retaining the exact equivalent [equation (80.14)](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md#80-全框架缺陷的内在上包络与共同原映射修复)
correspondence. The simpler current entrance uses one fixed source-projection
contraction and the unit-fixed mass witness on the same reconstructed models.
The probability-span representation and convex-effect-subalgebra classification
are existing mathematics. The application below supplies their parameter
correspondence, a tetrahedron obstruction to recovering menus from the specified
comparison table, and the descent conditions needed to retain original processes.
The classification, projection/moment and mass results are reused directly.
It is paper mathematics, without a new general theorem, novelty claim or Lean
kernel certification.

### Verified locator

- S. N. Filippov, S. Gudder, T. Heinosaari and L. Leppäjärvi,
  *Operational Restrictions in General Probabilistic Theories*,
  [DOI 10.1007/s10701-020-00352-6](https://doi.org/10.1007/s10701-020-00352-6),
  [arXiv:1912.08538v1](https://arxiv.org/abs/1912.08538v1), Theorem 3,
  pp. 14–15: convex effect subalgebras are intersections with linear subspaces
  containing the unit. Section 2.2, equation (6), defines finite random selection
  and classical post-processing of meters; §§4.4–5 distinguish this simulation
  closure from closure under every bounded effect sum.
- Alexander Wilce, *Symmetry and Composition in Probabilistic Theories*,
  [arXiv:0910.1527v2](https://arxiv.org/abs/0910.1527v2), §2, pp. 3–4:
  the span of the designated probability weights, its generated cone, and
  original outcome evaluations give an abstract state space with designated
  observables. An arbitrary outcome evaluation is not the unit functional.
- Martin Plávala, *General probabilistic theories: An introduction*,
  [arXiv:2103.07469v2](https://arxiv.org/abs/2103.07469v2), Theorem 3.19
  and Proposition 3.20: normalized evaluation representation and its dimension
  shift; §3.7 retains the no-restriction hypothesis separately.
- John Harding and Alex Wilce, *Order-unit spaces and probabilistic models*,
  [arXiv:2603.05682v2](https://arxiv.org/abs/2603.05682v2), §2,
  Examples 2.2(3)–(4) and Remark 2.3(1): original evaluation functionals,
  affine maps and distinct outcomes with equal effect images.
- Peter Janotta and Raymond Lal, *Generalized Probabilistic Theories Without
  the No-Restriction Hypothesis*,
  [arXiv:1302.2632v1](https://arxiv.org/abs/1302.2632v1),
  [DOI 10.1103/PhysRevA.87.052131](https://doi.org/10.1103/PhysRevA.87.052131):
  state and effect restrictions must be distinguished. That DOI belongs to
  arXiv:1302.2632.

### 1. The carrier of the original image

For each $X=A,D,E$, let $\Sigma_X$ be the nonempty set of original
preparation labels and $\mathcal T_X$ the original binary-test labels, with
original probabilities $\pi_X(e,\sigma)\in[0,1]$. Retain their raw menus,
devices, events, records and source/reference labels as additional data.
A supplied unit test $\mathbf1_X$ satisfies
$\pi_X(\mathbf1_X,\sigma)=1$ for every $\sigma$.
Define the **original image**, without taking any completion, by

$$
k_\sigma(e)=\pi_X(e,\sigma),\qquad
K_X=\{k_\sigma:\sigma\in\Sigma_X\}\subseteq\mathbb R^{\mathcal T_X}.
\tag{1}
$$

Require this image itself to be closed under every finite real probability
mixture, compact in the pointwise topology, and of finite affine dimension
$d_X$. These are explicit model conditions on realized probability tables.
The prescribed raw mixing operations must give those tables. A convex hull,
closure or dual construction cannot supply a missing preparation or test.
Probability-equivalent labels map to the same point but remain raw labels;
the construction does not identify their histories or future behaviors.
Retain every original menu as an indexed family of raw outcome occurrences,
with its device, event and source bindings and each occurrence's test image.
Equal images never merge occurrences or records; a new list of effects
summing to the unit is not thereby an original menu.

Suppress $X$ temporarily. The canonical objects are

$$
V=\operatorname{span}_{\mathbb R}K,\qquad
C=\{\lambda k:\lambda\ge0,\ k\in K\},\qquad
u(v)=v(\mathbf1),\qquad
\widehat e(v)=v(e),\qquad
\mathcal E=\{\widehat e:e\in\mathcal T\}.
\tag{2}
$$

Only the supplied unit coordinate defines $u$. General test coordinates have
their given probabilities, which need not be constant, much less constant one.
For $k_*\in K$,

$$
V=\mathbb R k_*\oplus\operatorname{span}(K-k_*),\qquad \dim V=d+1,
\tag{3}
$$

since $u(k_*)=1$ and $u$ vanishes on the difference span. Coordinate
evaluations separate $V$ by its definition as a space of functions. Their span
is therefore $V^*$: otherwise its annihilator in finite-dimensional $V$ would
be nonzero. Select finitely many original coordinates, including $u$, forming
a dual basis. They identify $V$ with $\mathbb R^{d+1}$; every other coordinate
is a linear combination of them. Thus the pointwise topology on $V$ is its
ordinary finite-dimensional topology, and $K$ is compact there.

Real mixture closure makes $C$ convex, and its definition makes it generating.
For nonzero $\lambda k$, $u(\lambda k)=\lambda>0$, so $C$ is pointed.
It is closed: if $\lambda_jk_j\to v$, then $\lambda_j\to u(v)$; a positive
limit gives $v/u(v)\in K$ by compactness, while a zero limit gives $v=0$
by boundedness of $K$. Consequently

$$
C\cap\{u=1\}=K
\tag{4}
$$

is exactly the original normalized image, and $V$ is nonzero.
Every affine $g:K\to\mathbb R$ extends uniquely to a linear functional on
$V$. To check well-definedness, any relation $\sum_i a_i k_i=0$ has
$\sum_i a_i=0$ by $u$. Splitting its positive and negative coefficients and
normalizing their common total gives equality of two original convex mixtures;
affinity gives $\sum_i a_i g(k_i)=0$. This proves the extension and hence

$$
[0,u]_{C^*}\ \cong\ \operatorname{Aff}(K,[0,1]),\qquad
\widehat e(k_\sigma)=\pi(e,\sigma),\qquad
\mathcal E\subseteq[0,u]_{C^*}.
\tag{5}
$$

These are the finite-coordinate application details of the cited standard
representation, not a claim of full original effect availability. If $K$ is a
singleton, $V$ has dimension one and tests may still have any constant value
in $[0,1]$. Compact finite-dimensional convexity gives finite decompositions
over $P=\operatorname{ext}K$ even when $P$ is not closed; no pure point need
be exposed. Such decompositions do not provide a physical pure-state lottery.

### 2. Original bounded doubling and full effects

Assume original tests contain $0,\mathbf1$, admit real probability mixing,
and have original complements, all with their stated probability tables.
Bounded doubling means precisely

$$
\forall e\in\mathcal T:\quad
\bigl[\forall\sigma\in\Sigma,\ \pi(e,\sigma)\le\tfrac12\bigr]
\ \Longrightarrow\
\bigl[\exists b\in\mathcal T\ \forall\sigma\in\Sigma,
\ \pi(b,\sigma)=2\pi(e,\sigma)\bigr].
\tag{6}
$$

There is one original $b$ for **all** original preparations. In images this
is $f\in\mathcal E,\ 2f\le u\Rightarrow2f\in\mathcal E$.
It is equivalent, in finitely many algebraic steps, to

$$
f,g\in\mathcal E,\quad f+g\le u\quad\Longrightarrow\quad
f+g\in\mathcal E,
\tag{7}
$$

by mixing $f,g$ equally and doubling; conversely set $g=f$.
Together with complements and scaling by mixing with zero, (7) makes
$\mathcal E$ a convex effect subalgebra. The ambient interval generates
$V^*$: a linear functional is bounded on compact $K$, and an appropriate
multiple of $u$ shifts and scales it into $[0,u]$. Filippov et al., Theorem 3,
therefore applies with ambient space $V^*$, cone $C^*$ and subspace
$W=\operatorname{span}_{\mathbb R}\mathcal E$.

Here is the exact finite application, avoiding a menu-closure assumption.
For $h\in W\cap[0,u]$, write $h=\sum_jc_j f_j$, $f_j\in\mathcal E$,
and choose an integer $N\ge\max(1,\sum_j|c_j|)$. Original mixing with zero gives

$$
a=N^{-1}\sum_jc_j^+f_j\in\mathcal E,\qquad
b=N^{-1}\sum_jc_j^-f_j\in\mathcal E,\qquad a-b=h/N.
$$

Since $0\le b\le a\le u$, the bounded sum $(u-a)+b=u-h/N$ is available;
its complement is $h/N$. Repeated bounded addition gives $kh/N$ for
$k=1,\ldots,N$, always below $u$. Thus
$\mathcal E=W\cap[0,u]$. The original coordinate evaluations already span
$V^*$ by §1, so $W=V^*$. We have proved the finite equivalence

$$
\text{original bounded doubling}\quad\Longleftrightarrow\quad(7)
\quad\Longleftrightarrow\quad\mathcal E=[0,u]_{C^*}.
\tag{8}
$$

The reverse implication is immediate. No topological closure of the test
menu, limiting operation or new label is used. This expresses the original
no-restriction availability premise; reciprocal comparisons do not imply it.
Even availability of every binary effect supplies neither all joint meters
nor an instrument or update map for each effect.

### 3. Two tetrahedron menus with the same specified T

Let the original preparations be all points $x$ of the tetrahedron
$\Delta_4=\{x_i\ge0:\sum_i x_i=1\}$. An effect is its four vertex values
$a\in[0,1]^4$, with probability $a\cdot x$. With $u=(1,1,1,1)$ and
coordinate effects $e_i$, consider the original effect images

$$
\mathcal E_{\rm small}=\operatorname{conv}\{0,u,e_i,u-e_i:1\le i\le4\},
\qquad \mathcal E_{\rm full}=[0,1]^4.
\tag{9}
$$

Both are compact, convex, complement-closed and separating. Their preparation
probability images satisfy §1 and have affine dimension three. For every
pure vertex $p_i$ and **every original mixed target** $x\in\Delta_4$,

$$
T^{\mathcal E}_{p_i}(x)
=\min\{a\cdot x:a\in\mathcal E,\ a_i=1\}=x_i
\tag{10}
$$

in both menus: each confirmer has nonnegative coordinates and $a_i=1$,
giving the lower bound $x_i$, and the common effect $e_i$ attains it.
This covers every pure reference, including zero target coordinates and
arbitrary mixed targets; the resulting pure reciprocity and fixed-half tables
agree. It is not equality for arbitrary mixed references. For instance,
confirmation of $r=(p_1+p_2)/2$ forces $a_1=a_2=1$. In the small menu any
convex combination with these two coordinates one uses only
$u,u-e_3,u-e_4$, so $a_3+a_4\ge1$, with equality attained. At the mixed
target $(p_3+p_4)/2$ its minimum is therefore $1/2$, whereas the full menu's
effect $e_1+e_2$ gives minimum zero.

The bounded sum $h=e_1+e_2\le u$ is absent from the small menu.
Indeed $H(a)=a_1+a_2-a_3-a_4$ is at most one on every generator in (9),
and therefore on its convex hull, but $H(h)=2$. Both summands are original
tests, so (7) fails. Equivalently, the original mixed test $h/2$ cannot be
doubled. These menus test only sufficiency of the specified pure-reference
$T$ table, not sufficiency of either complete (80.14) or (81.14) candidate.

There are explicit original meter realizations. In the small realization
start with four labelled binary meters $(e_i,u-e_i)$ and allow exactly finite
random choice and stochastic classical output post-processing, as in
Filippov et al., equation (6). The binary event images are exactly

$$
\sum_i\lambda_i[\alpha_i e_i+\beta_i(u-e_i)],\qquad
\lambda_i\ge0,\quad\sum_i\lambda_i=1,\quad
0\le\alpha_i,\beta_i\le1.
\tag{11}
$$

For fixed $i$ the bracket is the convex hull of $0,u,e_i,u-e_i$;
mixing over $i$ proves equality with $\mathcal E_{\rm small}$ in both
directions. Flattening successive random choices and stochastic matrices
proves simulation closure. In the full realization supply the labelled
four-outcome meter $(e_1,e_2,e_3,e_4)$: a binary post-processing has arbitrary
acceptance coefficients in $[0,1]^4$, so gives exactly the full image.
The four binary meters cannot simulate this four-outcome meter, since its
coarse-graining of outcomes $1,2$ would give the excluded $h$.
This simulation boundary concerns random selection and classical
post-processing only. Neither realization supplies sequential, nondisturbing
or adaptive instrument implementations by its effect table alone.

### 4. Descent of the supplied original processes

The following are entrance conditions, not consequences of bare probabilities.
An original unnormalized output is supplied with its mass $m\ge0$ and, for
$m>0$, an original normalized preparation label $\sigma$; its image is
$w=m k_\sigma$. At zero mass its image is zero, while its event, failure and
record labels remain. A weighted preparation here is a mathematical encoding
of supplied mass data, not a newly callable source.

For the original specified join and readback, write their output images on
normalized inputs as

$$
w_L(\delta,\alpha)=m_L(\delta,\alpha)k_{\ell(\delta,\alpha)}\in C_E,
\qquad
w_p(\epsilon)=m_p(\epsilon)k_{r(\epsilon)}\in C_D.
\tag{12}
$$

Zero outputs use the preceding convention. Require preservation of **all
finite real relations** in each input slot: for arbitrary real coefficients,

$$
\begin{aligned}
\sum_i c_i k_{\delta_i}=0&\Rightarrow
  \sum_i c_i w_L(\delta_i,\alpha)=0 &&(\text{every original }\alpha),\\
\sum_j b_j k_{\alpha_j}=0&\Rightarrow
  \sum_j b_j w_L(\delta,\alpha_j)=0 &&(\text{every original }\delta),\\
\sum_i c_i k_{\epsilon_i}=0&\Rightarrow
  \sum_i c_i w_p(\epsilon_i)=0.
\end{aligned}
\tag{13}
$$

These include descent through duplicate preparation labels. In particular,
every prescribed real mixture must satisfy, in each input slot, the
**mass-weighted** identity $w(\operatorname{mix}_i\lambda_i\sigma_i)=\sum_i\lambda_i w(\sigma_i)$,
not affinity after renormalizing its output.
When raw weighted inputs are supplied, require the same images to scale as
$w_p(a\epsilon)=a w_p(\epsilon)$ and
$w_L(a\delta,b\alpha)=ab w_L(\delta,\alpha)$ for $a,b\ge0$,
with zero and unequal masses included. Conversely, duplicate-label descent
and these real mixture identities imply (13) on normalized inputs: apply
the unit to a finite relation, split positive/negative coefficients with
equal total, and use the two equal convex mixtures. Thus rational mixtures
alone, or equality of normalized conditional output probabilities, is
insufficient; the omitted masses affect linearity.

Relations (13) give unique maps, explicitly

$$
\begin{aligned}
L\left(\sum_i c_i k_{\delta_i},\sum_j b_j k_{\alpha_j}\right)
 &=\sum_{i,j}c_i b_j w_L(\delta_i,\alpha_j),\\
p\left(\sum_i c_i k_{\epsilon_i}\right)&=\sum_i c_i w_p(\epsilon_i).
\end{aligned}
\tag{14}
$$

Changing either expansion changes the right side by zero by (13), proving
well-definedness, real bilinearity/linearity and uniqueness since the images
span. Supplied positive output masses imply positivity on $C_D\times C_A$
and $C_E$, respectively, by homogeneity and (4). Crucially, $K_D,K_E$ are
the entire original joint images; this tests every positive joint direction,
including entangled ones after the geometry bridge, not just products.

Every other advertised carrier-valued original process, including a supplied
reference extension, must obey the corresponding mass-weighted descent and
real mixture laws on its **own original input image**. For correlated
reference inputs this is the original joint image, not a product of local
marginals. Keep the same event, branch and reference on its original product
extension law, and require its stated positivity on the full original joint
cone. The original sufficient-reference and source conditions remain extra
contracts. Present isolated-test equality alone proves neither these
contextual laws nor equal future behavior. Raw devices and records stay
distinct even when their current effect images agree; an extension may not
be fabricated by identifying those devices. If these contracts fail, this
relational entrance does not certify the proposed original process model.

### 5. The current (81.14) entrance and its exact (80.14) correspondence

First specify $\mathsf R_{80.14}$ on the supplied original labelled data;
the equivalent current $\mathsf R_{81.14}$ below changes only its zero and
mass interfaces, preserving every other condition.
Use §§1–2 separately in $A,D,E$, impose (6) in each, and require §4 for the
same supplied original $L,p$ and every supplied process/reference consumer.
On the resulting full effect interval define, only for pure first endpoint,

$$
T^X_\xi(x)=\min\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

The confirmation face is nonempty and compact: it contains $u$, and
$[0,u]$ is closed and bounded, as evaluation on a finite basis of states
bounds all its coordinates in the dual space.
Require exactly the existing fixed-half law

$$
T^X_\xi\!\left(\frac{\eta+x}{2}\right)
=\frac{T^X_\eta(\xi)+T^X_\xi(x)}2
\quad(\xi,\eta\in\operatorname{ext}K_X,\ x\in K_X),\qquad X=A,D,E.
\tag{15}
$$

Reuse the [fixed-half same-carrier theorem](mullerududec2012selfduality.md#appendix-a-fixed-half-puremixed-entrance-to-s)
without reproving it: (15) is equivalent to full $S$ and to the arbitrary
real-weight mixed-remainder law. Use it **after** (8). Keep the full
[conditional EJA bridge](mullerududec2012selfduality.md#least-confirmation-forces-face-filter-purity)
of Definitions 75.1, 78.1 and 79.1: positive-dual generation, faithful
state/effect pairing, common frames, signed spectrality, face projections,
projectivity, purity of filters, and the attributed Barnum–Müller–Ududec
Theorem 16 classification. Pure reciprocity or self-duality alone does not
replace that bridge. Work in its chosen faithful Jordan coordinates, with
$u_X=\tau_X$, the entire square cones and normalized bases, and
$\langle x,y\rangle_X=\tau_X(x\circ_X y)$. Direct sums, rank-one factors
and Albert alternatives remain allowed at this stage.

All remaining predicates of (80.14) are retained, as follows.

1. Keep the **same original** whole-cone-positive $L:V_D\times V_A\to V_E$
   and $p:V_E\to V_D$, and the supplied original reference whose image is
   $\omega=1_D/\tau_D1_D$. Define internally

   $$
   \begin{aligned}
   K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),&Q(a,b,c)&=L(M(a,b),c),\\
   J(a)&=M(a,1_A),&H_{\rm s}(d)&=L(d,1_A),&B_1&=pH_{\rm s},\\
   U&=M(1_A,1_A),&G&=H_{\rm s}1_D,&F&=P_{U^{-1/2}}M.
   \end{aligned}
   \tag{16}
   $$

   Here $K(a)$ is the source's derived map, distinct from the bases $K_X$;
   $P_v$ is the Jordan quadratic representation. The **same $p$ occurs
   twice** in $M$. Keep both $\operatorname{span}_{\mathbb R}M(V_A,V_A)=V_D$
   and $\operatorname{span}_{\mathbb R}L(V_D,V_A)=V_E$, and full-real
   $Z:B_1M(a,b)=u_A(a)Jb$ for all $a,b\in V_A$. Whole-cone positivity
   includes all joint directions; real spanning does not make a joint cone
   product-generated. As in Definition 80.1, positivity and the two spans
   give $U,G>0$ before any zero condition, so $F$ is defined at this stage.

2. Keep the **complete all-frame zero envelope**, precisely

   $$
   \mathcal D(L,p)=\max_{B\in\mathcal F(A)}\left[
   \|U\|_2^2-\sum_{e\in B}\|Je\|_2^2+
   \|G\|_2^2-\sum_{e,f\in B}\|H_{\rm s}F(e,f)\|_2^2\right]=0,
   \tag{17}
   $$

   where $\mathcal F(A)$ consists of **all complete primitive Jordan frames**
   of the chosen faithful structure, with
   $\|x\|_2^2=\tau_X(x\circ_Xx)$. No selected frame or infimum replaces
   the maximum. Theorem 80.3
   restores both whole-cone zero-preservation relations $D_J,D_H$, hence PRE.

3. Keep the original fixed $t,s\in(0,1)$ and $\mathsf{Mass}_{t,s}$:
   there exists real linear $\Phi:V_A\to V_A$ with
   $\Phi(C_A)\subseteq C_A$, $u_A\Phi=u_A$, and
   $\{f\in V_A^*:f\Phi=f\}=\mathbb R u_A$ over **all real functionals**.
   For the original $m_2=u_DM$, $m_3=u_EQ$, keep both identities

   $$
   \begin{aligned}
   m_2(a,b)&=t\,m_2(\Phi a,b)+(1-t)m_2(a,\Phi b),\\
   m_3(a,b,c)&=st\,m_3(\Phi a,b,c)+s(1-t)m_3(a,\Phi b,c)
     +(1-s)m_3(a,b,\Phi c)
   \end{aligned}
   \tag{18}
   $$

   for all original positive $a,b,c$, including zero and unequal masses.
   These $t,s$ are unrelated to the comparison half. Keep the original
   $\mathrm A_0:u_EL(\omega,1_A/n)=1$, $n=\tau_A1_A$.
   A mathematical $\Phi$ does not supply a physical randomizer or reset.

4. Interpret original qualified-state H13 only after (17) has restored PRE,
   exactly as in Definition 80.2. In each active ordered block $(i,k)$ with
   both endpoint ranks at least two, use the original block projection
   $x=\pi_{ik}\rho$ and
   $\alpha_{ik}=F(-,c_k)|_{A_i}$, $\beta_{ik}=F(c_i,-)|_{A_k}$, with
   $c_i,c_k$ the original factor units. The **same original** total-trace-one
   state $\rho$ must have a strictly negative direction in at least one of
   $\alpha_{ik}\alpha_{ik}^*x-x$ and $\beta_{ik}\beta_{ik}^*x-x$ on every
   active block. Adjoints use the original canonical traces and the
   unnormalized units. Inactive blocks are arbitrary positive components,
   including zero; with no active blocks the qualification is all of $K_D$.
   No purity or fixed Schmidt spectrum is required. For that same qualified
   original $\rho$, require its **entire output** $I^{\rm raw}\rho$ positive,
   where $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ and
   $T_{\rm raw}(a,c)=L(Ja,c)$. The inverse is used at its justified PRE stage.
   Neither a trace test, blockwise replacement state nor output-dependent
   choice of qualification suffices.

**Correspondence.** On these admissible original labelled models, forgetting
only mathematical witnesses, the canonical representation gives

$$
\mathsf R_{80.14}\quad\Longleftrightarrow\quad
\left[\mathrm{PRE}_0^{\rm mix}+\mathcal D=0+
\mathsf{Mass}_{t,s}+\mathrm A_0+\mathrm H13\right]
\quad\Longleftrightarrow\quad\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}.
\tag{19}
$$

The middle expression is **exactly (80.14)**, with the same supplied maps,
reference and decorations. Here $C_{\rm joint}$ is the original joint
calibration $u_EL(1_D,1_A)+u_D(p1_E)\le2n^3$ on PRE, and
$\mathrm{C13}$ is $I^{\rm raw}(C_D)\subseteq C_E$.

For the forward arrow, §§1–2 give exactly the original full bases and full
effects, §4 gives the same original real maps, and the cited fixed-half
theorem gives full $S$ before the conditional EJA bridge. Conditions
(16)–(18) and H13 are then exactly the retained original predicates.
Apply 80.3, 79.5–79.7 and (80.14) in their original order: zero envelope
restores PRE; both mass laws and the anchor restore joint calibration before
H13; H13 supplies C13. No classification consumer is reproved here.

For the reverse arrow, take an original full carrier satisfying (80.14)
with its original preparations, tests, maps and supplied decorations.
Its evaluation map is

$$
\iota_X(x)(e)=e(x),\qquad
L'(\iota_Dd,\iota_Aa)=\iota_EL(d,a),\qquad
p'(\iota_Ez)=\iota_Dp(z).
\tag{20}
$$

Full effects separate the carrier, so $\iota_X$ is injective and maps onto
the span of its full original base image. It is a cone/base isomorphism and
pullback identifies the full effect intervals. Hence §§1–2 hold and the
original real maps satisfy (13) and all mass-weighted mixture laws, including
zero outputs. The existing fixed-half theorem supplies (15).
Transport the **entire chosen faithful structure**: set
$\iota_Xx\circ'_X\iota_Xy=\iota_X(x\circ_Xy)$,
$1'_X=\iota_X1_X$, $\tau'_X\iota_X=\tau_X$, and transport the trace
inner products, quadratic representations, all complete frames, norms,
adjoints and witnesses. Thus (17), both (18), $\Phi$, the original $t,s$,
anchor and H13 correspond exactly. In particular this is not an arbitrary
cone isomorphism while incompatible geometry is held fixed.
Carry the **same** original $L,p,\omega,\rho$, devices, events, menus,
reference contexts, source labels and records through evaluation. Contextual
extensions are transported on their original joint carriers with the same
product laws; they are not constructed from isolated probabilities.
This proves the first equivalence. The second is the cited (80.14),
including its reverse witness construction. The equivalence is relative to
the declared original descent and process contracts; it does not turn an
undecorated probability table into an original operational model.

**Direct application of the current entrance.** On these very same canonical
carriers, chosen faithful Jordan/trace structures and original $z=(L,p)$,
apply Theorem 81.3 and Proposition 81.4. For each complete primitive frame
$B$, set $\Pi_B=\sum_{e\in B}|e\rangle\langle e|$ and, with
$n=\tau_A1_A$, use precisely the source objects

$$
\begin{aligned}
P_0&=|1_A\rangle\langle1_A|/n,&\mathsf h_A&=P_0\otimes P_0,\\
\mathscr H_A&=\operatorname{span}_{\mathbb R}\{\Pi_B\otimes\Pi_B:B\in\mathcal F(A)\},&
\mathsf P_A&:\operatorname{End}(V_A\otimes_{\mathbb R}V_A)\to\mathscr H_A,\\
v_A&=\mathsf P_A\mathsf h_A,&\mathcal T&=H_{\rm s}\widetilde F,\\
\Gamma_z&=(\|U\|_2^2+\|G\|_2^2)\mathsf h_A
-\tfrac12(J^*J\otimes P_0+P_0\otimes J^*J)-\mathcal T^*\mathcal T.
\end{aligned}
\tag{17a}
$$

Here $\mathsf P_A$ is the fixed Hilbert–Schmidt orthogonal projection,
not a new input or physical operation. Reuse the source's unique invariant
full-support probability $\nu_A$ on the diagonal-projection orbit and its
moments $\mathsf C_A=\int\Pi\,d\nu_A$ and
$\mathsf W_A=\int(\Pi\otimes\Pi)\,d\nu_A$. Proposition 81.4 gives
$v_A\ne0$, $\mathsf W_A=v_A/\|v_A\|_{\rm HS}^2$ and

$$
\mathcal Q(z)=\frac{\langle\Gamma_z,v_A\rangle_{\rm HS}}{\|v_A\|_{\rm HS}^2}
=\|U\|_2^2+\|G\|_2^2-\operatorname{Tr}(J^*J\mathsf C_A)
-\operatorname{Tr}(\mathcal T^*\mathcal T\mathsf W_A),
\qquad
\langle\Gamma_z,v_A\rangle_{\rm HS}=0
\ \Longleftrightarrow\ \mathcal Q=0
\ \Longleftrightarrow\ \mathcal D=0
\ \Longleftrightarrow\ D_J+D_H.
\tag{17b}
$$

The last equivalences are Theorem 81.3 on the complete base already supplied
above. $\mathcal Q$ is distinct from the trilinear map $Q$ in (16), and
$\operatorname{Tr}$ is operator trace, not $\tau_X$. The second moment
retains the **same frame twice**: it cannot in general be replaced by
$\mathsf C_A\otimes\mathsf C_A$. Nor is $\mathsf W_A$ generally a
projection. These formulas apply the existing Haar/projection results;
they neither reprove them nor supply finite experimental readouts.

For the mass interface, take exactly Definition 81.7's fixed mathematical
witness $R_A(a)=u_A(a)1_A/n$. Theorem 81.8 supplies its positivity,
mass preservation and full real fixed-functional space $\mathbb R u_A$.
Replace the existential witness in (18) by the fixed identities

$$
\begin{aligned}
\mathsf E_2:\quad m_2(a,b)&=\tfrac12[m_2(R_Aa,b)+m_2(a,R_Ab)],\\
\mathsf E_3:\quad m_3(a,b,c)&=\tfrac13[m_3(R_Aa,b,c)+m_3(a,R_Ab,c)+m_3(a,b,R_Ac)]
\end{aligned}
\tag{18a}
$$

on all original positive inputs, including zero and unequal masses, with
the same $m_2=u_DM$, $m_3=u_EQ$. These are (18) at
$\Phi=R_A,t=1/2,s=2/3$; no local randomizer or joint extension is supplied.
Keep the same original anchor $\mathrm A_0$. Define $\mathsf R_{81.14}$
by these replacements alone. H13 is exactly clause 4, interpreted only
after (17b) restores PRE, on the **same original** qualified state and its
entire original output. In particular its block units and adjoints are not
renormalized. Applying Theorem 81.8 directly now gives

$$
\boxed{\mathsf R_{81.14}\ \Longleftrightarrow\
\bigl[\mathrm{PRE}_0^{\rm mix}+\langle\Gamma_z,v_A\rangle_{\rm HS}=0
+\mathsf E_2+\mathsf E_3+\mathrm A_0+\mathrm H13\bigr]}
\ \Longleftrightarrow\ \mathrm{PRE}+C_{\rm joint}+\mathrm{C13}
\ \Longleftrightarrow\ \mathsf R_{80.14}.
\tag{19a}
$$

The bracket is exactly (81.14), the current complete entrance. Its forward
direction first restores PRE, then uses both fixed mass laws and the anchor
to calibrate $C_{\rm joint}$ before H13 yields C13. Conversely, the same
original PRE+$C_{\rm joint}$ gives product masses by 79.6–79.7, so the
unit-fixed $R_A$ satisfies (18a); 81.3 and the original direction theorem
supply zero contraction and H13. Thus (19a) and (19) describe the same
actual models after forgetting mathematical witnesses. This does not
identify $R_A$ with a preassigned $\Phi$, or assert that either mass law
follows from comparisons alone.

For the reverse evaluation correspondence, extend the **full faithful
transport** in (20) to the fixed source data as well. Each $\iota_X$ is
an isometry for its transported canonical trace. Write
$\mathscr I=\iota_A\otimes\iota_A$ and
$\operatorname{Ad}_{\mathscr I}(Y)=\mathscr IY\mathscr I^{-1}$; then

$$
\begin{aligned}
\Pi'_B&=\iota_A\Pi_B\iota_A^{-1},&
\mathsf C'_A&=\iota_A\mathsf C_A\iota_A^{-1},&
\mathsf W'_A&=\operatorname{Ad}_{\mathscr I}(\mathsf W_A),\\
\mathsf P'_A&=\operatorname{Ad}_{\mathscr I}\mathsf P_A\operatorname{Ad}_{\mathscr I}^{-1},&
v'_A&=\operatorname{Ad}_{\mathscr I}(v_A),&
\Gamma'_{z'}&=\operatorname{Ad}_{\mathscr I}(\Gamma_z),\\
R'_A\iota_A&=\iota_AR_A,&
\langle\Gamma'_{z'},v'_A\rangle_{\rm HS}&=\langle\Gamma_z,v_A\rangle_{\rm HS}.&&
\end{aligned}
\tag{20a}
$$

The primed orbit and its probability are the corresponding pushforwards;
the induced Hilbert–Schmidt isometry carries $\mathscr H_A$, its orthogonal
projection and $\mathsf h_A$ as displayed. This is the precise parameter
transport of 81.3–81.4, not an arbitrary cone relabelling. The transported
unit and trace keep $n$, $R_A$, both masses and (18a) unchanged, just as
(20) carries $\Phi$ and (18). Throughout, the same actual $L,p$ (with $p$
twice), supplied reference, both spans, full-real $Z$, whole-cone positivity,
anchor, H13 state and all process/source decorations are retained. No
classification, Haar/projection or mass theorem is reproved.

### 6. Quantum correspondence, geometry and remaining conditions

The consumers of Theorem 81.8, §§79.8 and 80.5 retain their complete original premises.
Their correspondence is concise:

| Quantum structure | Retained route and scope |
| --- | --- |
| Density states, full effects, Born pairing | Full effects, (15), the faithful conditional EJA bridge and the original two-interface classification give finite complex Hermitian direct sums, $\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i)$, $\sum_i\operatorname{Tr}\rho_i=1$, $0\le f_i\le I_i$. Reciprocity alone does not select the complex field. |
| Specified two- and three-copy tensors and readbacks | Both spans, full-real $Z$, the fixed projection's zero contraction (equivalently the zero envelope), fixed $\mathsf E_2,\mathsf E_3$, original anchor and H13 give the same original tensors and partial traces of (79.17), including scalar sectors and all correlated or entangled directions. |
| CP events, instruments and Lüders updates | The same actual event/branch/record, product extension, sufficient actual reference, full joint positivity, both budgets, complete-menu TP and update contracts remain required. |
| Hamiltonian evolution | Requires the supplied continuous, time-homogeneous reversible $*$-automorphism group in the original physical time, clock and units; static comparisons supply no such group or $\hbar$. |

More explicitly, CP/Kraus requires an original reference block of at least
each input block's dimension and positivity of that same event's extension
on the entire original joint cone. Preserve both original budgets (79.28),

$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik},\qquad
F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell},
\tag{21}
$$

and total TP on both sides for the same complete actual menu. Here $u_{ik}$
are the source's original matrix filter weights, distinct from $u_X$;
normalization makes them identities. Common-reset input-row consistency,
sequential composition and actual coarse-graining keep their original
contracts. Outcome probability is the original output mass; condition on
it only when strictly positive, retaining zero-branch records and permissions.
Lüders additionally needs the same CP branch to have sharp effect $P$ and
fix every normalized state certainly accepted by $P$. An effect does not
determine its update. Neither the mathematical $R_A$ in (18a) nor (18) for a
specified $\Phi$ certifies supplied physical reset operations; (18) does not
certify the positive joint extensions of (79.18); 79.9 supplies the original
counterexample. Mathematical existence witnesses create no physical menus.

All original preparation, event, reference, copy and source obligations
remain, including actual correlated joints, zero and unequal masses,
controls, ready/flags, complete records, failure, stopping, destruction,
return, future behavior, full menus, fixed supports and every specified
intermediate cut. The original analyzer acceptance interface and
$B_r$-to-active-ready connection mentioned in §§79.9 and 80.5 are not
constructed here. No additional bracketing, four-copy system, coherent
control, copying or infinite-dimensional consistency is supplied. The
fixed-carrier approximation result 80.5 still requires all its original
boundedness and noncollapse conditions (80.9); repair within C13 requires
80.6's additional whole-cone C13 premise. No noisy H13 bridge follows here.

Geometrically, a preparation is its original probability table and the cone
adds a mass coordinate to that same base. Bounded doubling concerns which
cuts of the base are actually present as tests. The tetrahedron shows that
identical least-confirmation numbers can conceal a missing cut. After full
effects and the fixed-half bridge, (17) measures cross-overlaps of positive
pieces in every complete frame. The current (17b) instead contracts the
same data against the fixed source projection: the existing nonnegative,
full-support average vanishes exactly when every frame has zero overlap.
Its moments preserve the common-frame correlation. The two mass laws use
the unit-fixed $R_A$, followed by the original anchor and same-state H13;
this is the simpler (81.14) entrance to the same complete model class.
Endpoint reciprocity exchanges two
arguments of a comparison; it differs from commuting successive physical
instruments. This reduces externally supplied geometry and expression,
without establishing fewer independent physical assumptions, least axioms,
lower experimental cost or a physical quantum origin.

可以把一个准备看成它面对所有原测试时给出的整张概率表，但原装置、菜单和记录仍然各自保留。只有这些原表本身允许实概率混合、形成有限维紧集合，才能从它们构造出这里的向量空间与带质量的正锥；取闭包不能替我们造出新准备。测试是否齐全还要另问：一个已有测试在所有原准备上的成功率都不超过一半时，是否有同一个原测试把这些数同时加倍？结合原混合与补测试，这恰好表达全效应可用性。四面体的两个菜单说明，纯参照对全部混态的最小确认数完全相同，仍能漏掉一个有界和。接回当前的完整候选 81.14 时，仍保留同一个读回用两次、原参考、两张成、全实零关系与全方向正性；但不必再搜索最坏框架，而把原几何固定的一个源投影与同一原映射导出的量作收缩。已有定理保证它为零恰好等于每套完整框架都零重叠，所以 80.14 的精确对应仍然保留。两条总质量关系现在采用由原单位固定的同一个数学见证，不另选局部变化；再用原锚校准倍率，最后才检查同一原混态的方向条件及其整个原输出。原过程还必须在保留输出质量的情况下尊重混合与等价关系，来源、参考、全菜单、时钟等义务也都保留。比较两端交换后数值相同，不等于两次仪器交换执行次序后状态相同。这使同一模型类的入口更简洁，不据此声称独立物理假设更少，也没有凭概率表生成仪器、来源、时钟或完整的物理量子起源。
