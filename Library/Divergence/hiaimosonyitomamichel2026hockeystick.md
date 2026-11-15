---
bibkey: hiaimosonyitomamichel2026hockeystick
authors: Fumio Hiai; Milan Mosonyi; Marco Tomamichel
year: 2026
title: Hockey stick f-divergences
doi: null
url: https://arxiv.org/abs/2607.08760v1
claim: "Proposition V.1 gives the maximal positive-overlap hockey formulas and a three-label attaining reverse test; the final equality question concerns maximal hockey-stick versus maximal f-divergence."
strata_touched:
  - D5/S3/Quantum/Divergence/MaximalHockeyStickOperational
  - D5/S3/Quantum/Divergence/MaximalHockeyStickConvex
  - D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
  - D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
  - D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment
  - D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes
  - D5/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
  - D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment
license: citation-only
triage: anchor
---

# Maximal hockey profiles and the original L1 equality question

Hiai, Mosonyi and Tomamichel, *Hockey stick f-divergences*,
arXiv:2607.08760v1, Proposition V.1, pp. 34--36, equations
(V.124)--(V.125), identify the maximal positive and negative hockey
divergences with the two trace masses minus the maximal positive common
overlap. Their proof constructs three classical labels from an attained
positive common lower bound and its two positive residuals. This is a
known result, following Matsumoto's formulation, rather than a new
conjecture solution. The final equality question on p. 62 asks when
maximal hockey-stick f-divergence equals maximal f-divergence.

The finite-matrix formalization uses all natural k and actual
density-matrix preparations on Fin k, with arbitrary nonnegative input
masses. For t>0, MaximalHockeyStickOperational proves both operational
infimum formulas using an attained PSD overlap X and the independently
indexed components X, A-X, tB-X. The same test attains both orientations.
Zero-mass components have an arbitrary coordinate state with zero weight;
empty matrix dimension uses the empty alphabet. The statements retain
singular and zero pairs and impose no trace-one or nonempty-dimension
hypothesis. The positive-threshold restriction is sufficient for every
curvature integral used here.

For S=A+B, C=normalize(S,A) and P the spectral projection of C onto
(0,1), the repository's finite-source classifier states the following.
For any real generator convex on the positive ray with actual
right-derivative curvature of full support, if the infimum of its closed
perspective cost over all finite tests is real finite, equality with its
integrated operational hockey value holds exactly when PSP commutes with
PCP. Sufficiency holds for every such convex generator as an equality
of extended values, without the full-support or finite-value hypotheses.
Necessity uses approximate finite tests with integrable nonnegative gaps,
not general-convex attainment. The atom at one belongs to the negative
branch; the scalar endpoint limits may be infinite. No infimum-integral
interchange is assumed.

Hiai, *Quantum f-divergences in von Neumann algebras II. Maximal
f-divergences*, arXiv:1807.03118v1, Theorem 4.2, Lemma 6.1 and Theorem
6.3, supplies canonical spectral and operator-convex optimality
antecedents. Matsumoto, *A new quantum version of f-divergence*, in
*Nagoya Winter Workshop 2015: Reality and Measurement in Algebraic
Quantum Theory*, pp. 229--273 (2018), is the attainment antecedent cited
by HMT. GGJ's *On the infimum of quantum effects* is separately credited
for common-support localization. None is credited with the repository's
general convex approximate-test classification. The separate actual
all-L1 general-f source bridge uses Bayer--Teichmann finite moments.
Matsumoto's arXiv:1311.4722v4, p. 8, Lemma 4.1, already supplies
one-cost finite-source compression with bound 2d^2+3; the formal
interface asserts a finite alphabet without a cardinality bound.

The original source quantifiers are all sigma-finite L1 spaces, not just
finite alphabets. MaximalHockeyStickL1ReverseTest formalizes the direct
positive-L1 part of Proposition V.1. For any actual positive
complex-linear TP map on the entire complex L1 space, integrable
nonnegative inputs p,q and one specified t>0, let h=min(p,tq).
Positivity and linearity give the three PSD components Gamma(h),
A-Gamma(h), tB-Gamma(h); TP preserves their trace masses. The existing
weighted-component supplier gives a finite reverse test with exactly
both Bochner integrals of max(p-tq,0) and max(tq-p,0). Empty output
dimension forces both inputs to vanish almost everywhere and uses the
empty alphabet. This construction needs neither a measure-class
hypothesis nor an assumed density factorization or continuity.
Measurable representatives preserve arbitrary original positive complex
L1 inputs and both integrals by almost-everywhere equality.

The universe-lifted finite counting preparation embeds every finite
test in every arbitrary source universe. Thus the positive and negative
profile value sets over the original sigma-finite sources, and also over
every s-finite source, equal the finite sets at each positive threshold.
Their infima are the two PSD-overlap formulas. This is the known HMT
Proposition V.1, not a new conjecture result; it asserts a finite
realization for each specified threshold, not one for all thresholds.

For general convex f, finite counting sources lie inside the original
sigma-finite class, which lies inside the s-finite class. The already
proved exact one-cost atomization equates the two extreme infima, so the
original maximal f-value has the same extended value. The actual
original L1 operational formulas are consumed pointwise in the exact
integrated identity of MaximalHockeyStickAllL1Convex. Its
original_eq_iff_commute compares the two original sigma-finite values:
with actual full-support curvature and real finite original maximal
f-value, equality holds exactly when PSP commutes with PCP. Its
commute_implies_original_eq retains convex sufficiency as extended
values without those two assumptions. The s-finite actual operational
classifier is also retained. Arbitrary traces, empty, singular and zero
outputs, infinite endpoints and the negative-branch atom at one remain
in scope. No infimum-integral interchange, all-threshold finite
compression, necessity from infinity=infinity, global commutator
criterion or arbitrary von Neumann output theorem is asserted.
Operator-convex generators are included under the stated necessity
conditions. Worldwide priority of the classification remains
unresolved; source attribution and Lean verification are distinct.

Remark VII.4 (PDF p. 60) raises existence of a minimal reverse test for general
convex generators, even in finite dimension. Matsumoto's
arXiv:1311.4722v4, Theorem 9.4 (PDF p. 30), already proves finite-dimensional
finite-value attainment under FC: f is proper, lower semicontinuous and convex,
its domain contains (0,infinity), and f(0)=0 (PDF p. 4). HMT's explicit
question does not negate this earlier overlap. MaximalHockeyStickAttainment proves
that whenever the actual original sigma-finite whole-complex-L1 maximal
value is a real number, an actual finite ReverseTest attains that number.
The output matrices are arbitrary finite complex PSD matrices, including
empty dimension, zero, singular and unnormalized pairs. The generator is
real and convex on the positive ray; both actual closed-perspective
endpoint costs may be infinite. No operator-convexity, faithfulness,
normalization or optimizer premise is added. This is a finite-dimensional
attainment result, not an arbitrary von Neumann algebra theorem.

The proof credits Matsumoto's finite-cardinality compression and compact
minimization architecture (arXiv:1311.4722v4, Lemmas 4.1 and 9.2--9.3).
It retains the general endpoints by minimizing the nonnegative curvature
remainder on a compact fixed-alphabet carrier, with the affine cost
contribution fixed by the two output traces. Exact Caratheodory compression
preserves both output matrices and the real cost. Infinite-cost boundary
points remain in the compact domain, and the zero pair uses the empty
test. The existing original-source equivalence transfers this finite
minimum to the original value. The alphabet bound is deliberately coarse.
Matsumoto's printed condition f(0)=0 alone is not a substantive novelty
distinction. If the actual endpoint c=f(0+) is finite, taking the closed
endpoint value and subtracting c subtracts the fixed constant c sigma(1)
from every reverse-test cost (c Tr(B) for matrix outputs), preserving
minimizers. Transposition, hat f(t)=t f(1/t), and swapping the two inputs
handle a finite opposite endpoint in the same way. The statement here also
retains the range where both endpoints are infinite; this normalization
observation does not establish priority for that remaining range. Worldwide
priority of the full endpoint-general attainment statement remains unresolved.

The arbitrary-support extension retains the same actual original sigma-finite
whole-complex-L1 values and the real-finite original maximal-value premise.
Let X(t) be the unique trace-maximizing PSD common lower bound of A and tB.
For every finite ordered tuple 0=t_0<t_1<...<t_m with positive knots in the
actual curvature support, require the matrix secants
D_i=(X(t_(i+1))-X(t_i))/(t_(i+1)-t_i) to satisfy 0<=D_i<=B and to be
antitone in Loewner order. Equality of the original maximal and integrated
original operational hockey values is equivalent to this condition. The
empty tuple and empty curvature support are included. Zero is a virtual
initial knot, rather than a curvature-support endpoint.

MaximalHockeyStickLoewnerSlopes proves necessity and exact interpolation of
each specified finite knot tuple by an actual finite reverse test.
MaximalHockeyStickArbitrarySupport proves sufficiency by exhausting a dense
support family while retaining tail anchors from one actual finite-cost
witness. Its integrable envelope controls both the literal test kernels
and their gaps, including labels on either axis with infinite scalar
endpoint costs. Dominated convergence and the existing exact cost-gap
identity close the infimum comparison. This argument alone does not assert a common
finite optimizer on infinite support, full-support commutation for a
restricted support, or necessity from infinity=infinity. The one-threshold
HMT construction, Matsumoto one-cost compression and previous source-class
bridges are antecedents; they and the consumed helpers are not additional
open-problem solutions. Worldwide novelty of the arbitrary-support
classification remains unverified.

## Verified locator

https://arxiv.org/abs/2607.08760v1

## Arbitrary convex posterior instruments

`GeneralConvexReverseTestAttainment` treats an arbitrary concrete von Neumann
algebra and the actual sigma-finite whole-complex-L1 source class. Its source
universe and operator-algebra universe are independent. The preparation is
initially only algebraic complex-linear, positive and complex-mass preserving,
with intrinsically all-directed order-normal outputs. Normality is not replaced
by an unproved identification with a chosen abstract predual.

The posterior source is the finite measure obtained by pushing
`(p+q) dmu` forward under `p/(p+q)`, with the zero fiber assigned zero.
The exact whole-L1 source equalities preserve both prepared moments without
assuming continuity of an original preparation. All continuous scalar integrals
identify this measure with the actual moment family's Riesz measure. The literal
extended closed-perspective integral is preserved, including zero fibers and
both infinite endpoint coefficients.

The converse uses the constructed normal whole-L1 realization for every point
of `NormalMomentFamily.Family`. Transport along the measurable equivalence
between the compact interval and its universe lift gives an actual original
source in the prescribed universe. Hence the full original attainable-cost set
equals the image of the literal family objective, before minimizing either side.
The objective is the fixed finite affine support contribution plus
`PosteriorCurvatureCost.posteriorCurvatureCost`. The latter is the exact
supremum of continuous truncated-curvature integrals and is lower
semicontinuous in Mathlib's full weak topology of finite measures. Minimization
in ENNReal on the actual compact nonempty family retains top as a possible
minimum. The resulting original value is attained and cannot be minus infinity.
If every admissible cost is +infinity, nonemptiness alone makes every admissible
test a minimizer. This branch retains scope and is not counted as an additional
independent solved optimization problem.

The comparison with earlier literature retains its hypotheses. Matsumoto,
[arXiv:1311.4722v4](https://arxiv.org/abs/1311.4722v4), Theorem 9.4,
already proves finite-dimensional finite-value attainment under FC. Theorem 9.9
(PDF p. 35) concerns separable B(H), under FC and the finite endpoint hypotheses
f(0)<infinity and hat f(0)<infinity stated throughout Section 9.3 (PDF p. 31).
Lemma 4.1 already provides the finite-compression architecture.
Hiai, *Quantum f-divergences in von Neumann algebras II. Maximal
f-divergences*, [arXiv:1807.03118v1](https://arxiv.org/abs/1807.03118v1),
Section 6, Lemma 6.1, Definition 6.2 and Theorem 6.3, gives an arbitrary-von-Neumann
whole-L1 spectral reverse test and attainment with infinite endpoint conventions
under the paper's standing operator-convexity hypothesis. The posterior
construction retains arbitrary convexity, without asserting spectral optimality
or finite-alphabet realization. This endpoint addresses only attainment for the
intrinsic all-directed order-normal source class stated above. HMT Remark VII.4
(PDF p. 60) asks about minimal reverse-test existence; the separate question on
PDF p. 62 asks for a classification of equality between maximal hockey-stick
f-divergence and maximal f-divergence. The attainment endpoint does not supply
that classification. These antecedents and scope distinctions do not establish
a global priority claim.
