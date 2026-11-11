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

## Appendix: bounded uniform preparations and common confirmation

Keep the original nonzero finite-dimensional real space $A$, closed pointed generating cone $C$,
strictly positive $u\in A^*$, compact full base $K=\{x\in C:u(x)=1\}$, and **all** effects $[0,u]$.
Write $P=\operatorname{ext}K$. No symmetry, Jordan structure or closedness of $P$ is assumed here.
This appendix applies elementary finite convex geometry and compactness to (17); the subsequent
spectral and Jordan consequences reuse the attributed paper bridges above, including their proof
boundaries. This is a paper result, without a Lean-verification or literature-priority claim.

### The intrinsic bound and the exact minimum criterion

For $p\in P$ define, in the original effect geometry,
$$
F_p=\{f\in[0,u]:f(p)=1\},\qquad r_p=\operatorname{affdim}F_p,\qquad
T_p(x)=\min_{f\in F_p}f(x)\quad(x\in C).
\tag{BU1}
$$
The minimum agrees with the earlier infimum. Indeed, $[0,u]$ is closed and bounded: choose a
finite spanning family in $K$, on which all effects have values in $[0,1]$; these evaluations
bound their coordinates in $A^*$. Thus $F_p$ is compact, convex and nonempty, containing $u$.
In particular $r_p$ is defined before imposing S or invoking a Jordan representation.
For each pure $q$ let $H_q=\{f\in F_p:f(q)=T_p(q)\}$, with $p$ fixed in this notation.
These are nonempty closed exposed faces, possibly all of $F_p$.

For any finite pure tuple $(q_j)$ and strictly positive probability weights $(a_j)$,
$$
T_p\!\left(\sum_j a_jq_j\right)\ge\sum_j a_jT_p(q_j),\qquad
\text{equality}\ \Longleftrightarrow\ \bigcap_jH_{q_j}\ne\varnothing.
\tag{BU2}
$$
To prove the equivalence, minimize the continuous sum on compact $F_p$. Its excess over the
right side is $\sum_j a_j[f(q_j)-T_p(q_j)]$, a sum of nonnegative terms. It is zero exactly
when every term is zero. Conversely a common minimizer gives equality. Zero weights can be
discarded. Thus an exact equality asserts simultaneous attainment, not just separate minima.

**Effect-face intersection lemma.** If $r_p\ge1$, any finite family of the $H_q$ with empty
intersection has an empty subfamily of at most $r_p$ members.
To see the improvement over the generic $r_p+1$ bound, take an inclusion-minimal empty family
$H_{q_1},\ldots,H_{q_t}$. Each face is nonempty, so $t\ge2$. Choose $f_i$ in every face except
$H_{q_i}$, and put $c_j=T_p(q_j)$ and $d_j=f_j(q_j)-c_j>0$. Then
$$
f_i(q_j)=c_j+\delta_{ij}d_j.
\tag{BU3}
$$
An affine dependence $\sum_i\lambda_i f_i=0$, $\sum_i\lambda_i=0$, evaluated at each $q_j$, gives $\lambda_jd_j=0$. Hence the $f_i$ are affinely independent and $t\le r_p+1$. If $t=r_p+1$, they span $\operatorname{aff}F_p$, so $u=\sum_i b_i f_i$ with $\sum_i b_i=1$.
Evaluation at $q_j$ gives $b_j=(1-c_j)/d_j\ge1$, since $f_j(q_j)\le1$.
This contradicts $\sum_i b_i=1$ and $t\ge2$. Consequently $t\le r_p$.
The extra ingredient is the common upper effect $u$, not an unproved strengthening of Helly's
theorem. If $r_p=0$, $F_p$ is a singleton and every $H_q$ is that singleton.

### Bounded uniform comparison is equivalent to full S

Use $\mathsf{Cmp}_{\rm bd}$ for the following law, avoiding the symbol $U$ reserved below for $M(1_A,1_A)$. It quantifies **every** pure reference $p$ and **every** pure tuple, with repetitions:
$$
T_p\!\left(\frac1h\sum_{j=1}^h q_j\right)
=\frac1h\sum_{j=1}^h T_{q_j}(p),\qquad
1\le h\le\max(1,r_p),\quad q_j\in P.
\tag{BU4}
$$
**Bounded-arity theorem.** On the stated full carrier, $\mathsf{Cmp}_{\rm bd}$ is equivalent
to the full weighted finite law S in (17), and hence to reciprocal **least** proper confirmation.

**Proof.** S immediately gives (BU4). Conversely its $h=1$ case gives $T_p(q)=T_q(p)$.
Fix $p$. For $r_p\ge1$, (BU2) and (BU4) imply that every family of at most $r_p$ pure-state
minimum faces has a common point. The effect-face lemma makes every finite intersection
nonempty. For $r_p=0$ this already holds because $F_p$ is a singleton. Compactness of $F_p$
then gives a point $e_p\in\bigcap_{q\in P}H_q$, even when $P$ is not closed.
For any $f\in F_p$, $e_p(q)=T_p(q)\le f(q)$ on all pure $q$. Finite-dimensional compact
convex decomposition gives $K=\operatorname{conv}P$, and positive rescaling gives
$C=\operatorname{cone}P$. Therefore $e_p\le f$ on $C$. Since $e_p\in F_p$, it is a least
effect, below **every** confirming effect, rather than merely an undominated minimal one.
It is unique, and $T_p(x)=e_p(x)$ for every $x\in C$. Thus for arbitrary real probability
weights, including zeros,
$$
T_p\!\left(\sum_j a_jq_j\right)=\sum_j a_je_p(q_j)
=\sum_j a_jT_{q_j}(p).
\tag{BU5}
$$
This proves S without a rational-weight approximation. The argument also works at one fixed
reference if singleton reciprocity and its bounded tuple laws are assumed there. $\square$

When $r_p=1$, the lemma says that all the individually nonempty minimum faces already have
common intersection; the only comparison requirement is singleton reciprocity. When $r_p=0$
that same requirement is retained by $\max(1,r_p)$. If $K=\{p\}$, generation makes $C$ a ray,
$F_p=\{u\}$, $r_p=0$, and every preparation consists of repetitions of $p$, so both laws hold.
Repeated pure states cause no change to a minimum face or to the argument. No maximum over $P$
or limiting pure-state argument was used; compactness was used in effect space instead.

The equality $T_p=e_p$ here is on $C$, especially $K$. The functional $e_p$ has a linear
extension to all signed vectors in $A$; this is distinct from taking the original pointwise
infimum on signed inputs. For $x\in C$ that infimum at $-x$ is $-\max_{f\in F_p}f(x)$,
which need not equal $-e_p(x)$. In ordinary geometry, each $H_q$ records tests that confirm
$p$ while accepting $q$ as little as possible. The bounded comparisons force these demands
to fit one test; compactness joins all such demands, and cone order makes that test least.
The bound measures the freedom of this confirming-effect face, not a number of instruments.

### Two separate sharpness controls on full carriers

For either compact full-dimensional convex body $B\subset W$ below, use the exact carrier
$A_B=\mathbb R\oplus W$, $C_B=\{(t,tx):t\ge0,x\in B\}$ and $u_B(t,y)=t$.
Its cone is closed, pointed and generating, its normalization is strictly positive away from
zero, and its normalized base is $\{1\}\times B$. Linear proper effects are exactly all
affine functions $B\to[0,1]$. We suppress the leading coordinate in naming states.

**Fixed-reference sharpness.** Let $r\ge2$ and
$K_r=\operatorname{conv}\{0,e_1,\ldots,e_r,\mathbf1\}\subset\mathbb R^r$, with $p=\mathbf1$.
These listed points are exactly its pure vertices: $0$ uniquely minimizes the coordinate sum,
$\mathbf1$ uniquely maximizes it, and $e_i$ uniquely maximizes
$x_i-\varepsilon\sum_{j\ne i}x_j$ for $0<\varepsilon<1$.
For a confirming affine effect write $d_i=1-f(e_i)$. Affinity and $f(\mathbf1)=1$ give
$$
0\le d_i\le1,\quad \sum_i d_i\le r-1,\qquad
f(0)=1-\frac{\sum_i d_i}{r-1}.
\tag{BU6}
$$
These conditions are also sufficient for a proper effect, since they give values in $[0,1]$ at every vertex. They describe a full-dimensional truncated cube, so $r_p=r$.
For every other pure vertex $q$, $T_p(q)=T_q(p)=0$: coordinate effects $x_k$ confirm $p$
and vanish at $0$ and at $e_i$ when $k\ne i$; effects $1-x_k$ confirm $0$, and confirm
$e_i$ when $k\ne i$, while vanishing at $p$.
A tuple of length at most $r-1$ omits some $e_k$. The effect $x_k$ simultaneously gives
zero at all its non-$p$ entries and one at its $p$ entries. Hence the law at this fixed
reference holds through $r-1$, with repetitions. But (BU6) gives
$$
T_p\!\left(\frac1r\sum_{i=1}^r e_i\right)=\frac1r>0
=\frac1r\sum_{i=1}^rT_{e_i}(p).
\tag{BU7}
$$
Thus $r_p$ cannot generally be lowered at a fixed reference. This control makes no assertion that $K_r$ satisfies the corresponding weakened comparison law at every reference.

**No universal fixed arity, even with all references tested.** For $m\ge2$ let
$H=\{z\in\mathbb R^m:\sum_i z_i=0\}$, $W=H\oplus H$, and
$$
a_i=(e_i-\mathbf1/m,0),\qquad b_i=(0,e_i-\mathbf1/m),\qquad
B_m=\operatorname{conv}\{a_1,\ldots,a_m,b_1,\ldots,b_m\}.
\tag{BU8}
$$
The two centered $(m-1)$-simplices lie in complementary subspaces and have common barycentre $0$. The base dimension is $2m-2$, the carrier dimension is $2m-1$, and all $2m$ listed
vertices are exposed: the appropriate block coordinate uniquely maximizes at its own vertex.
Their sole affine dependence is $\sum_i a_i-\sum_i b_i=0$, with each sum zero. Thus the allowed
affine effect values $\alpha_i=f(a_i),\beta_i=f(b_i)$ are **exactly**
$$
0\le\alpha_i,\beta_i\le1,\qquad \sum_i\alpha_i=\sum_i\beta_i.
\tag{BU9}
$$
Necessity follows from the common barycentre; sufficiency follows because this sole relation
is precisely the consistency condition for an affine function on the spanning vertices.
To confirm $a_s$, set $\alpha_s=1$ and all other $\alpha_i=0$, and place one value $1$
at any chosen $b_j$, the other $\beta_i$ being zero. To make a distinct target $b_t$ zero,
choose $j\ne t$; distinct targets in the $a$ block are already zero. Interchanging blocks
proves $T_v(w)=\delta_{vw}$ for every pair of pure vertices, so reciprocity holds globally.
For any reference $a_s$ and any tuple of length at most $m-1$, there is an unlisted $b_j$. The same effect then vanishes at every nonreference entry and equals one at every reference
entry. The symmetric construction works at a $b$ reference. Thus **all** short tuple laws
hold, including repetitions and every reference. Yet for the length-$m$ tuple $(b_1,\ldots,b_m)$,
$$
T_{a_s}(0)=\min_{\alpha_s=1}\frac1m\sum_i\alpha_i=\frac1m,
\qquad \frac1m\sum_iT_{b_i}(a_s)=0.
\tag{BU10}
$$
The minimum is attainable by the displayed effects. Taking $m=k+1$ rules out every universal fixed positive arity $k$. Here $r_{a_s}=r_{b_s}=2m-2$: fix $\alpha_s=1$, take every other
$\alpha_i=1/2$ and all $\beta_i=(m+1)/(2m)$, strictly inside every remaining inequality in (BU9).
These are different conclusions: (BU7) is pointwise sharpness; (BU10) excludes a fixed global
cutoff. Neither proves that $\max(1,r_p)$ is the smallest possible adaptive bound when
comparison laws at all other references are available as additional constraints.

### Substitution into the complete same-index candidate

Let [V](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md)
denote the existing volume, specifically Definitions 75.1, 76.1–76.2 and (76.8).
Define $\mathrm{PRE}_0^{\rm bd}$ by substituting **only** (BU4) for its full comparison
premise on **each** $X=A,D,E$, using the intrinsic $F^X_\xi,r^X_\xi$ of (BU1).
All three original full carriers, state bases and effect intervals remain as in (BU1).
The theorem restores S on each; the complete paper S-to-EJA bridge of [V] §75.1 and the
preceding sections of this note is retained, not replaced by endpoint reciprocity or by an
independent Jordan axiom. In its faithful coordinates $\tau_X\Phi_X=u_X$,
$\Phi_XU_X=1_X$ and $B_X(x,y)=\tau_X(\Phi_Xx\circ\Phi_Xy)$; the whole original state and
effect domains correspond, and every primitive idempotent has canonical trace one.
Initially general EJAs, including direct sums, rank-one and Albert factors, remain allowed.
For completeness, the rest of this replacement candidate is the following exact original data.
Use canonical trace pairings, $P_x=2\ell_x^2-\ell_{x^2}$, $n=\tau_A1_A$, $d=\tau_D1_D$.
Supply only real-bilinear $L:D\times A\to E$, real-linear $p:E\to D$, positive on the
**entire** respective cones, and the original reference $\omega=1_D/d$. Define internally
$$
\begin{aligned}
\mathcal B(d',c)&=pL(d',c),& K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),\\
J(a)&=M(a,1_A),&H_{\rm s}(d')&=L(d',1_A),&B_1&=pH_{\rm s},\\
Q(a,b,c)&=L(M(a,b),c),&U&=M(1_A,1_A),&G&=H_{\rm s}1_D.
\end{aligned}
\tag{BU11}
$$
The two calls use this same $p$. Retain both real spans and the all-real reset/slice law
$$
\operatorname{span}_{\mathbb R}M(A,A)=D,\quad
\operatorname{span}_{\mathbb R}L(D,A)=E,\qquad
B_1M(a,b)=\tau_A(a)Jb\quad(a,b\in A).
\tag{BU12}
$$
Full positivity includes every entangled direction; real spanning is not positive-product
cone generation. As in [V] §§75.1–76.1 these premises give $U,G>0$ before either zero table,
so $F=P_{U^{-1/2}}M$ is defined. Choose one family $\mathfrak B=(B_t)_{t=1}^s$ of complete
primitive frames in this same geometry, with $1\le s\le3$, whose members Jordan-generate $A$
($\mathsf{JG}_3$ of Definition 75.2). Repeated frames are allowed; neither linear spanning of their
members nor natural or physical availability of the witness is assumed. On that **same** family impose (76.3)–(76.4):
$$
\begin{gathered}\langle Je,Je'\rangle_D=0\quad(e\ne e'\in B_t),\\
\langle H_{\rm s}F(e,f),H_{\rm s}F(e',f')\rangle_E=0\\
((e,f)\ne(e',f')\in B_t\times B_t),\quad 1\le t\le s.\end{gathered}
\tag{BU13}
$$
There is no cross-index $B_t\times B_{t'}$ requirement. After these tables restore PRE, read H13 exactly as in Definition 76.2: use central units $c_i$ of $A_i$, $n_i=\tau_Ac_i$,
$D_{ik}=\operatorname{span}_{\mathbb R}F(A_i,A_k)$, its central projection $\pi_{ik}$,
$\alpha_{ik}=F(-,c_k)|_{A_i}$, $\beta_{ik}=F(c_i,-)|_{A_k}$ and $\mathcal Q=\{(i,k):n_i,n_k\ge2\}$.
With original canonical-trace adjoints set
$$
\mathcal H(F)=\{\rho\in K_D:\ \forall(i,k)\in\mathcal Q,\ x=\pi_{ik}\rho,
\ \alpha_{ik}\alpha_{ik}^*x-x\not\succeq0\ \text{or}\ \beta_{ik}\beta_{ik}^*x-x\not\succeq0\},
$$
$$
T_{\rm raw}(a,c)=L(Ja,c),\quad I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1},\quad
\mathrm H13:\exists\rho\in\mathcal H(F),\ I^{\rm raw}\rho\in E_+.
\tag{BU14}
$$
Each active block needs at least one strictly negative direction, not both differences negative
or negative definite. Inactive blocks may be zero; only the same original total trace-one
constraint applies, and $\mathcal Q=\varnothing$ gives all $K_D$. The marginal extensions use
unnormalized units, with no purity, Schmidt-spectrum or conditional-block restriction.
Eligibility reads the first interface only; the test reads the **whole original output** of
the same original $\rho$, not a transported state, a chosen effect or its trace alone.

Consequently, forgetting the frame witness, the full replacement candidate satisfies
$$
\boxed{\mathrm{PRE}_0^{\rm bd}+\mathsf{JG}_3+\mathsf J_{\mathfrak B}
+\mathsf H^{\rm diag}_{\mathfrak B}+\mathrm H13}
\ \Longleftrightarrow\ \mathrm{PRE}+\mathrm{C13},\qquad
\mathrm{C13}:I^{\rm raw}(D_+)\subseteq E_+.
\tag{BU15}
$$
Indeed (BU4) restores precisely the comparison premise, after which [V] (76.8) applies on the
same actual data; conversely S gives (BU4). Deleting H13/C13 on both sides retains the
corresponding equivalence. No other premise, map, reference, trace or cone is changed.

### Retained quantum consumers and limits

By [V] §§75.7, 76.5, with their full conditional bridges, the carriers have complex Hermitian
sectors of sizes $n_i$, $n_in_k$, $n_in_jn_k$. The complete density and effect domains are
$\rho_\lambda\ge0$, $\sum_\lambda\operatorname{Tr}\rho_\lambda=1$, $0\le f_\lambda\le I_\lambda$,
with Born rule $\Pr(f\mid\rho)=\sum_\lambda\operatorname{Tr}(f_\lambda\rho_\lambda)$.
Single-system pure geometry is $\bigsqcup_i\mathbb{CP}^{n_i-1}$, same-sector comparison is
squared overlap, and different-sector comparison is zero. Classical and multiple sectors remain.
Only after H13 restores C13 can the auxiliary two- and three-copy tensors be simultaneously
ordinary. The exact original positive-filter family and unique readback remain (74.19)–(74.20):
$u_{ik},g_{ijk}>0$, $\sum_{i,k}n_i\operatorname{Tr}(u_{ik}^{-1})=n^2$, with the same $\omega$.
Auxiliary normalization does not make original $M,H_{\rm s}$ unital or $p$ trace preserving,
or impose cross-block symmetry or commutation of weights. The optional standard calibration of
Definitions 73.2, 73.10 and Theorems 73.11, 73.16 retains both original interfaces'
four bilateral positive reset completions with their full-cone, same-joining and fixed-reset
quantifiers, plus $\mathrm A_0:\tau_E L(\omega,1_A/n)=1$; together these force $u=g=I$.

Process consumers retain [V] §75.7 and Atlas IV §§69.1–69.11. In the fixed spectator family
$\Psi_\Phi=C_DT_\Phi C_D^{-1}$, $(T_\Phi X)_{jk}=\sum_i(\Phi_{ji}\otimes\mathrm{id}_k)X_{ik}$,
branches must be block CP, with $F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell}$ satisfying both aggregate budgets
$\sum_{a,j}F^a_{ji}\le I_i$ and $\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik}$.
Complete instruments require equality in both. Fix any output sector $j_0$, density $\sigma$ there,
and $0<c\le1$, with $R(a)_j=\delta_{j,j_0}(\sum_i\operatorname{Tr}a_i)\sigma$ as in [V] §75.7.
Simultaneous TP completion of $cR$ in that same family is equivalent to $u_{ik}=v_k$; a small
positive $c$ alone is insufficient, and row consistency leaves $v_k,g$ uncalibrated. Branch probabilities use original output traces, conditional
states require positive probability, and sequential composition and coarse graining stay in
that fixed family. Deriving CP from events still needs the same event's product extensions
and full-cone positivity on actual references at least as large as each input block's dimension
for the Choi/Bell criterion. Unique Lüders updates still need the actual CP branch's effect to be
the sharp projection and pointwise invariance of every certainly accepted normalized state;
Hamiltonian evolution still needs the supplied continuous time-homogeneous reversible $*$-automorphism group, with physical time, energy units and $\hbar$ identified separately.

白话说，完整候选仍保留三个系统的全部态、全部测试、全锥正的原接合与同一读回、原参考、两条实张成和全实重置关系；
只是把每个纯参照的任意权重、任意长度比较，等价改写成按其确认效应面维数限定长度的所有等份纯态比较。
这些比较保证各个最省误接受的要求能由同一个最小确认测试共同实现；随后仍须同一族至多三套 Jordan 生成框架、
第一零表、同标产品第二零表，以及原 H13 对同一原混态的完整输出检测，才与原 PRE+C13 等价。
Born 概率、全密度态、全效应和复射影纯态几何按原条件接回，权重、校准、共同重置补全、实际参考和过程前件均保留。
两两端点互反是静态比较，混合相容保证共同测试，两者都不表示先后测量交换；所得是量词缩减，
不是较少独立假设、通用有限实验清单或最少量子公理，也不完成整体量子起源、四份以上组合或无限维与动力学的来源任务。
