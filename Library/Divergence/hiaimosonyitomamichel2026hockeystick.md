---
bibkey: hiaimosonyitomamichel2026hockeystick
authors: Fumio Hiai; Milan Mosonyi; Marco Tomamichel
year: 2026
title: Hockey stick f-divergences
doi: null
url: https://arxiv.org/abs/2607.08760v1
claim: "Proposition V.1 gives the maximal positive-overlap hockey formulas; the p. 62 maximal-hockey/maximal-f equality question is addressed by the repository's compressed-GNS-centralizer classifier for full-curvature-support convex generators, including every nonaffine operator-convex generator."
strata_touched:
  - D5/S3/Quantum/Divergence/MaximalHockeyStickOperational
  - D5/S3/Quantum/Divergence/MaximalHockeyStickConvex
  - D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
  - D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
  - D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment
  - D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes
  - D5/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
  - D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment
  - D5/S3/Quantum/Divergence/NormalOverlapCompatibility
  - D5/S3/Quantum/Divergence/NormalOverlapCurvatureEquality
  - D5/S3/Quantum/Divergence/NormalOverlapOperational
  - D5/S3/Quantum/Divergence/OriginalCentralizerClassification
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
algebra M on any complete complex Hilbert space H. Its standard concrete
predual class is independently defined by actual series
phi(a)=sum_n <xi_n,a eta_n>, with sum_n ||xi_n||^2 and sum_n ||eta_n||^2 finite.
`ConcreteCoefficientSeries.mem_coefficientSpace_iff_series` identifies this
class exactly with E, the norm-closed complex span of restricted vector
coefficients in the actual continuous dual of M. Its `dual_evaluation` proves
the isometric evaluation representation E*=M: every bounded complex-linear
functional on E is evaluation at an actual a in M, with equality of norms.
No separability assumption is imposed on H.

The positive output functionals rho,sigma belong to this series class.
`StandardL1Preparation` quantifies algebraic complex-linear preparations on
the entire complex L1 space, positive on nonnegative inputs, preserving the
integral mass of every complex input, and with every output in the independent
series class. Sources range over all sigma-finite measure spaces in an
arbitrary universe independent of the operator-algebra universe; the two
nonnegative inputs are original complex L1 elements. Continuity and contraction
of an original preparation are not hypotheses. Zero, singular and unnormalized
pairs, zero Hilbert space, infinite scalar endpoints and infinite total costs
remain in scope. The only generator hypothesis is that f:R->R is convex on
(0,infinity).

`ConcreteCoefficientPredual` proves positive heredity in E using the actual
GNS completion: if phi belongs to E and 0<=psi<=phi, then psi belongs to E.
Using `DirectedPositiveNet`, it constructs the ambient strong limit from an
operator upper bound. Commutation passes to vector limits, placing the limit
in M; an M-internal directed positive least upper bound is therefore this
strong limit.
Vector coefficients, and hence their entire norm closure E, are intrinsically
all-directed order-normal. This is the proved forward interface, without a
blanket converse from intrinsic normality or an appeal to Sakai uniqueness.

The posterior source is the finite measure obtained by pushing
`(p+q) dmu` forward under `p/(p+q)`, with the zero fiber assigned zero.
The exact whole-L1 source equalities preserve both prepared moments without
assuming continuity of an original preparation. All continuous scalar integrals
identify this measure with the actual moment family's Riesz measure. The literal
extended closed-perspective integral is preserved, including zero fibers and
both infinite endpoint coefficients.

For every point F of `NormalMomentFamily.Family`,
`standard_posterior_realization` uses the actual continuous whole-complex-L1
map Gamma agreeing with all its continuous moments. Positive continuous
coordinates are dominated by ||g||(rho+sigma), so GNS heredity puts them in E;
four positive parts and continuous-function density then put Gamma(h) in E
for every complex L1 input h. Its codRestriction to E retains exactly the
same values, positivity, every complex mass, norm bound at most one and both
prepared moments. The series equivalence applies to every output of this same
Gamma and of its lifted preparation.

Transport along the measurable equivalence between the compact interval and
its universe lift gives an actual original source in the prescribed universe.
`standardAttainableCosts_eq_range` proves that the entire standard-original
attainable-cost set equals the range of the literal family objective, before
minimizing either side; the intrinsic-original cost set has the same range.
The objective is the fixed finite affine support contribution plus
`PosteriorCurvatureCost.posteriorCurvatureCost`. The latter is the exact
supremum of continuous truncated-curvature integrals and is lower
semicontinuous in Mathlib's full weak topology of finite measures. Minimization
in ENNReal on the actual compact nonempty family retains top as a possible
minimum. The compiled `standard_original_reverse_test_extended_attainment`
attains the standard-original infimum with the lifted test explicitly built
from this same Gamma, densities t and 1-t, and the actual lifted finite regular
Riesz measure. Its cost is literally `closedPerspectiveCost`; the infimum
cannot be minus infinity and equals zero for the zero pair.
If every admissible cost is +infinity, nonemptiness alone makes every admissible
test a minimizer. This branch retains scope and is not counted as an additional
independent solved optimization problem.

The comparison with earlier literature retains its hypotheses. Matsumoto,
[arXiv:1311.4722v4](https://arxiv.org/abs/1311.4722v4), Theorem 9.4,
PDF p. 30, already proves finite-dimensional finite-value attainment under FC
(PDF p. 4). Theorem 9.9
(PDF p. 35) concerns separable B(H), under FC and the finite endpoint hypotheses
f(0)<infinity and hat f(0)<infinity stated throughout Section 9.3 (PDF p. 31).
Lemma 4.1 already provides the finite-compression architecture.
Hiai, *Quantum f-divergences in von Neumann algebras II. Maximal
f-divergences*, [arXiv:1807.03118v1](https://arxiv.org/abs/1807.03118v1),
Section 6, Lemma 6.1, Definition 6.2 and Theorem 6.3, gives an arbitrary-von-Neumann
whole-L1 spectral reverse test and attainment with infinite endpoint conventions
under the paper's standing operator-convexity hypothesis. The posterior
construction retains arbitrary convexity, without asserting spectral optimality
or arbitrary-von-Neumann finite-alphabet realization. These suppliers and
finite-dimensional overlaps are not separate solved conjectures.

Francesco Buscemi, *Quantum f-divergences from retrodictive tests: a unifying
classical variational principle*,
[arXiv:2610.29696v3](https://arxiv.org/abs/2610.29696v3), 31 October 2026,
Theorem 3.1 (PDF pp. 5--6), assumes faithful density operators rho,sigma,gamma
in finite dimension and operator-convex f with f(1)=0. It minimizes the distinct
coupled retrodictive objective D_f(R||F) between two joint laws, over finite
admissible implementations. As PDF p. 5 explicitly distinguishes, the separate
reverse-test objectives compare each joint law with the reference law J;
D_f(R||F) depends on their coupling. This theorem does not subsume the
arbitrary-convex standard-original attainment endpoint here.

HMT Remark VII.4 (PDF p. 60) asks about minimal reverse-test existence; the
separate question on PDF p. 62 asks for a classification of equality between
maximal hockey-stick f-divergence and maximal f-divergence. The attainment
endpoint does not supply that classification. Bounded literature searches
have not identified an exact subsuming theorem; worldwide priority remains
unresolved.

## Concrete von Neumann arbitrary-support equality

`NormalOverlapOperational.arbitrary_support_classification` treats arbitrary
concrete von Neumann algebras and positive inputs in the independently defined
coefficient-series predual. The source universe is independent of the concrete
Hilbert-space universe. The maximal value is literally the infimum over all
standard-original sigma-finite sources with algebraic positive complex-linear
preparations on their entire complex L1 spaces. Assume this infimum is real
finite; no optimizer or simultaneous overlap family is assumed.

For t>0, let v(t) be the attained maximum of eta(1) over actual positive
standard-predual functionals eta dominated by rho and t sigma. Equality of
the original maximal and integrated original operational hockey values is
equivalent to the following condition: every finite increasing tuple of
positive knots in the actual curvature support admits optimizers eta_j whose
functional secants D_j=(eta_j-eta_(j-1))/(t_j-t_(j-1)), with eta_0=t_0=0,
satisfy sigma>=D_1>=...>=D_m>=0. The optimizers need not be unique.
`NormalOverlapCompatibility` proves this finite-to-global condition using
positive functional block interpolation and the compact moment family's finite
intersection property. `NormalOverlapCurvatureEquality` proves the literal
endpoint-inclusive cost comparison and necessity from real-finite equality.

Under either equivalent condition, one actual whole-complex-L1 preparation on
a finite regular Borel measure on [0,1], with p=x and q=1-x, attains every
curvature-support overlap maximum and the common original finite cost. Its
total source mass is rho(1)+sigma(1); all preparation outputs lie in the
coefficient-series predual. Zero, singular and unnormalized inputs, empty or
unbounded curvature support, and infinite scalar endpoints remain included.
The complete atom at one uses the negative hinge branch. No finite alphabet,
spectral optimality, necessity from infinity=infinity, or converse from
intrinsic order-normality to the abstract predual is asserted. This is separate
from unconditional minimal-test existence and from the full-support localized
centralizer classification. Worldwide priority remains unresolved.

## Original equality and the compressed GNS centralizer

`OriginalCentralizerClassification` gives the structural criterion for the
last equality on HMT PDF p. 62, in the general-convex setting of Section VII
(p. 57). This is the equality between maximal hockey-stick f-divergence and
maximal f-divergence. The measured-hockey equality of Theorem VII.3 (p. 60)
compares different quantities.

Let M be any concrete von Neumann algebra on a complete complex Hilbert space.
The positive inputs rho,sigma lie in its standard concrete predual, represented
independently by coefficient series sum_n <xi_n,a eta_n> with both vector
sequences square-summable. The original values quantify all sigma-finite
sources in a universe independent of M, with positive complex-linear
preparations on the entire complex L1 space, preserving the integral mass of
every complex input and taking every output into this coefficient-series
class. No continuity premise is imposed on a preparation. The proved predual
bridge identifies the series class with the norm-closed span of restricted
vector coefficients; it does not assert the converse from intrinsic
order-normality to coefficient-series membership.

In the actual completed GNS representation of psi=rho+sigma, let Omega be
the unnormalized cyclic vector and N the actual commutant. The unique
coordinate 0<=C<=I has the original coefficients rho and sigma for C and I-C.
Put P=rangeSupport(C(I-C)), the interior spectral projection E_C((0,1)).
The condition `CompressedCentralizes` is
<Omega,(PCP)(PYP)Omega>=<Omega,(PYP)(PCP)Omega> for every Y in N.
It concerns the Omega functional on PNP, rather than global commutation of
rho and sigma.

For real f convex on (0,infinity), assume that its actual right-derivative
Stieltjes curvature measure has full support on that ray.
`full_support_finite_iff` says that, if the original maximal f-value is real
finite, equality with the original maximal hockey-stick value holds exactly
when `CompressedCentralizes` holds. Without the finite-value premise,
`full_support_iff_top_or_centralizes` says that equality holds exactly when
`originalHockeyValue=+infinity` or `CompressedCentralizes` holds.
`operatorConvex_finite_iff` and `operatorConvex_iff_top_or_centralizes` give
the same conclusions from literal nonaffine all-Hilbert operator convexity:
scalar convexity and full scalar curvature support are derived, not added
as hypotheses. Singular, zero and unnormalized pairs, nonseparable and zero
Hilbert spaces, and infinite scalar endpoints remain in scope. The top branch
follows from the comparison inequality; infinity=infinity implies no
centralization. This structural iff does not extend to arbitrary scalar-convex
generators with restricted curvature support, nor certify all of HMT's broad
question.

The classical components retain their attribution. HMT Proposition V.1 and
(V.127), PDF pp. 35--36, supply the positive-overlap operational formulas and
the maximal-hockey/maximal-f comparison. Hiai, *Quantum f-divergences in von
Neumann algebras II. Maximal f-divergences*,
[arXiv:1807.03118v1](https://arxiv.org/abs/1807.03118v1), Theorem 4.2 (p. 18),
Lemma 6.1 (p. 25) and Theorem 6.3 (p. 26), already gives the arbitrary-von-Neumann
operator-convex GNS spectral formula and optimal whole-L1 spectral reverse
test, including singular pairs and infinite endpoints. The coordinate,
spectral test and that attainment are not new here. Matsumoto's finite-source,
shorting and spectral antecedents, including the distinct hypotheses of his
optimizer-uniqueness theorem, are recorded in
[the Matsumoto entry](matsumoto2018newquantumfdivergence.md).
Gheondea, Gudder and Peter Jonas, *On the infimum of quantum effects*,
[doi:10.1063/1.1904704](https://doi.org/10.1063/1.1904704), Proposition 2.4,
Theorem 3.1 and its proof (PDF pp. 4--6), already localize to common support
and identify P_{C,I-C}=E_C((0,1)); Section IV (p. 7) gives the affine
normalization. Existence of an order-greatest lower bound is distinct from
maximizing a specified functional over all positive common lower bounds.

The structural contribution is the equivalence between simultaneous spectral
positive-overlap optimality at every threshold and this compressed
centralization, and its transfer to the original two-divergence equality.
Neither the classical spectral optimizer nor support localization alone
provides that equivalence. The bounded primary comparison found no exact
classifier in the inspected sources; it did not obtain a complete citation
graph and does not establish worldwide priority or official acceptance.

Related equality theorems retain their own targets. Capel and Costa Rico,
*Geodesic Quantum f-Divergences*,
[arXiv:2608.15833v1](https://arxiv.org/abs/2608.15833v1), Theorem 7.2 (p. 53),
classifies data-processing saturation for finite-dimensional strictly positive
states and channel outputs under the equality-determining representing-measure
condition (274) (p. 51). That Loewner-measure condition is not full scalar
curvature support, and the equality is across a channel, not between these two
divergences on one pair. Buscemi's Theorem 3.1, cited above, instead optimizes
a coupled retrodictive objective. Neither cited statement supplies this
compressed-centralizer classifier.
