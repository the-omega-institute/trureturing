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

## Verified locator

https://arxiv.org/abs/2607.08760v1
