---
bibkey: atlas2026strassencoupling
authors: Unattributed source file; copyright Meta Platforms, Inc. and affiliates
year: 2026
title: Finite Strassen coupling and compact Kantorovich duality in ATLAS Lean
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/StrassenCoupling.lean
claim: Finite-poset upper-set inequalities characterize ordered nonnegative equal-mass couplings; arbitrary continuous real rectangular costs on nonempty compact metric Borel probability spaces satisfy real primal and continuous two-potential dual equality.
strata_touched:
  - D5/S3/Analytic/Probability/FiniteOrderedStrassen
  - D5/S3/Geometry/ProbabilityTransport/CompactKantorovich
license: Complete upstream LICENSE including ML intended-use preface retained at docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# ATLAS coupling and compact transport

## Finite ordered Strassen coupling

The exact formal supplier is `facebookresearch/atlas-lean` at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`, file
`MathlibExt/Probability/StrassenCoupling.lean`. Its SHA-256 is
`1f02f5f2d11d673f8a90273c5cd00c81f12c0579f0e8f543aaa96499060be672`.
The source file supplies no named author; Meta Platforms, Inc. and affiliates
is its stated copyright holder. The metadata year is the verified year of the
pinned repository revision, not an asserted publication date or theorem date.

The source theorem `forall_isUpperSet_sum_le_iff_exists_coupling` concerns
every finite partial order alpha and functions p,q from alpha to the reals.
It assumes p and q are pointwise nonnegative and their finite total masses
are equal. It equates all inequalities sum over U of p <= sum over U of q,
for upward-closed finsets U, with existence of a nonnegative matrix pi with
row sums p, column sums q, and pi(x,y)=0 whenever x is not <= y. It allows
the empty carrier and equal zero mass, without normalization to probability
mass. It has no countable, linear-order, Boolean-configuration, martingale
or algorithmic claim. This is known classical mathematics and native library
integration, not a novelty or priority claim.

The native owner is `D5/S3/Analytic/Probability/FiniteOrderedStrassen.lean`.
The native adaptation retains only the consumed declaration closure and omits
the unused unit-mass wrapper. Its native namespace and private support
predicate are packaging adaptations. The public theorem unfolds the
upper-set predicate explicitly, so it adds no duplicate public upper-set API.
The retained proof bodies are unchanged. The source and native repository
use Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`; matching pins do not by
themselves establish native admission. No ATLAS Lake dependency is added.

The upstream source notice names the root LICENSE. Its complete text is
retained at `docs/reports/lovasz-suppliers/atlas-LICENSE.txt` with SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
The retained text includes its prefatory statement that the codebase is not
intended for use to train, fine-tune, distill, evaluate, or otherwise develop
ML models. This note preserves the actual source terms and does not assert
blanket permissive clearance.

Retire this transplant only when the locally adopted Mathlib pin provides
the full equivalent finite-poset result for arbitrary equal nonnegative
mass, including zero mass and the empty carrier. Bounded searches are not
evidence of global absence. Possible finite Markov one-step and
finite-configuration increasing-event applications are unmeasured, not
completed consumers.

## Compact Kantorovich duality

The separate exact supplier is the same immutable ATLAS revision,
file `MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean`, at
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean.
Its source SHA-256 is
`653662aba64d1482aab8429d73af3b27e6ce334f6e7317b4502fa94549da2d3f`.
The source gives the same Meta Platforms, Inc. and affiliates copyright
notice and root LICENSE reference. The complete license and its prefatory
intended-use statement identified above apply to this source as well.

The native owner is
`D5/S3/Geometry/ProbabilityTransport/CompactKantorovich.lean`, namespace
`CompactKantorovich`, with public endpoint `kantorovich_duality_compact`.
For independently arbitrary nonempty compact metric Borel spaces X and Y,
probability measures mu and nu, and any continuous real c on X times Y,
the real infimum of integrals of c over all joint probability measures
with exactly those marginals equals the real supremum of
integral(phi,mu) + integral(psi,nu) over continuous phi and psi satisfying
phi(x) + psi(y) <= c(x,y) everywhere. The spaces may be distinct and
infinite, and the cost may be signed, asymmetric and nontriangular.
No support restriction, extra moment, distance domination, attainment,
convergence or resource bound is part of this statement. This is known
classical mathematics and reception of an external formal proof, with no
novelty, priority or open-problem-resolution claim. The supplier cites
L. V. Kantorovich, *On the Translocation of Masses* (1942), English
translation in Journal of Mathematical Sciences 133 (2006), 1381–1382,
DOI 10.1007/S10958-006-0049-2, and C. Villani, *Topics in Optimal
Transportation* (2003).

The retained closure contains the weak dual comparison, the open convex
separation construction of a positive marginal-preserving functional
with an epsilon cost bound, its Riesz realization with both exact original
marginals, and the final epsilon comparison. The only public definitions
are the primal value set and dual feasibility; all supporting declarations
are private. A private abbreviation uses the sole existing
`CostTransport.IsCoupling` relation, with equality symmetry at the marginal
interfaces. Pinned `BoundedContinuousFunction.mkOfCompact`, finite-measure
regularity and `Measure.isFiniteMeasure_map` replace duplicate supplier
constructions. Unused `mkBCF_apply` and `phiPlusPsi_apply` are omitted;
the latter has no remaining simp-list references, and its pointwise evaluation
is supplied definitionally in the two linearity laws. The other retained
mathematical proof bodies are unchanged apart from these API adaptations
and namespace packaging. Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` match the supplier; no ATLAS
Lake dependency is added.

The adapted native source SHA-256 is
`877f49adc0fd5bc717f2c1ff840d156cca3fa91b6a14967fde5d5a092f537d15`.
Retire this compact-duality adaptation only when the locally adopted
Mathlib pin provides the full equivalent arbitrary continuous real
rectangular-cost compact probability-space theorem. The finite Strassen
adaptation has its separate retirement condition above.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/StrassenCoupling.lean
contains `forall_isUpperSet_sum_le_iff_exists_coupling` and its consumed
finite-carrier induction support.
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean
contains `kantorovich_duality_compact` and its consumed compact separation
and Riesz support. The full root license is at
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/LICENSE.
