---
slug: crown-order-polytope-log-concavity
bibkey: lundstrom2025crown
doi: 10.48550/arXiv.2504.05123
url: https://arxiv.org/abs/2504.05123v3
triage: theorem
motivation_gids:
  - D5/S3/Analytic/ChebyshevEndpointCertificate
---

# Crown order-polytope f-vector log-concavity

## Problem

Conjecture 3.7 on PDF page 12 of the pinned v3 source states:

> For any positive integer n, the entries of the f-vector of O(C₂ₙ) form a log-concave sequence.

The calligraphic symbols are transcribed here as `O` and `C`.
The crown has source cover relations `1<2>3<...>2n-1<2n>1`.
Its order polytope consists of real coordinates between zero and one
respecting those comparisons. Its full f-vector includes the empty face
and the whole `2n`-dimensional polytope. Precisely, for all `n,k : Nat`
with `0<n`, `0<k`, and `k<2*n+1`, the assertion is
`F(n,k-1)*F(n,k+1) <= F(n,k)^2`, where `F(n,0)=1` and
`F(n,k)=f_(k-1)` for `k>0`. The full vector has `2n+2` entries.

## Motivation

The existing frozen `ChebyshevEndpointCertificate` provides a repository
example of using the pinned Chebyshev polynomial API in an unbounded
symbolic argument. It motivates the polynomial route; it is not a proof
dependency or an exact solution to this problem. The target concerns
actual geometric face counts, so the delivered proof also connects the
published counting formula to the real polytope and justifies every
coefficient correction. A finite list of vectors cannot settle the target.

## Gap

The pinned primary v3, submitted at `2025-12-09T17:39:28Z`, reports
log-concavity checks through `n=200` and leaves
the universal assertion as Conjecture 3.7. Theorem 3.6 proves the face
formula. It does not prove the conjecture. Remark 3.8 states that the
displayed actual f-polynomials are not real-rooted, so directly claiming
real-rootedness of that polynomial did not supply the missing proof.

The repository formalization was later delivered by
[PR 8714](https://github.com/the-omega-institute/trureturing/pull/8714),
merged at `2026-09-20T09:08:33Z` as
`1fce15789f3bb988cf6df49ff7cfe560d16a08c8` from final head
`52b788c222ff73b3594088c98f1bc4aabb942351`; required CI run
`35498693398` completed with conclusion `SUCCESS`; its build, engineering,
current and delta checks succeeded. The prior delivery audit also
succeeded.

The arXiv record gives the later v4 submission time as
`2026-09-22T11:25:57Z`. Its new Section 3.1
[Theorem 3.12](https://arxiv.org/html/2504.05123v4#S3.SS1) proves
log-concavity for `n>=2` using Lemmas 3.9 and 3.13, a Chebyshev-root route,
and low-coefficient corrections; see also the
[arXiv record](https://arxiv.org/abs/2504.05123). The v4 result is now a
proved source result, not a current open gap.
Its submission postdates the recorded formal merge and therefore does not,
by itself, establish a pre-delivery resolution.

## Route

Map source vertex `j` to zero-based coordinate `j-1 : Fin (2*n)`.
`crownRelation` puts the even coordinates below their two cyclic
neighbors. `crownGeometricFaceCount` counts nonempty real exposed faces
by the dimension of their affine-span directions, independently of any
enumeration. Active inequalities, connected compatible partitions,
source-selected odd-block merging and its inverse establish the face
formula. The quotient-block count proves the affine dimension; the
two exceptional vertices and one-block edge are included.
The summand uses an explicit zero guard when `d>i`, preserving the
source's signed lower binomial index instead of truncating it to zero.

Normalize the proven formula as `f_d=2*[d=0]+[d=1]+s_d`, where `s_d`
is a coefficient of the auxiliary scalar polynomial in the Library note.
The Chebyshev identity and even/odd factorizations prove that this
auxiliary polynomial splits over the reals, with repeated roots retained.
The licensed elementary-symmetric Newton inequality handles its
coefficients through Vieta's formula inside the Crown proof.
The bounds `s_0>=n^2`, `s_0<=s_1<=2n*s_0` handle the comparisons
at vector indices `1,2,3` for `n>=2`; Newton handles the rest, including
the last internal index. The separate augmented-chain proof at `n=1`
gives the actual vector `(1,3,3,1)` and both internal comparisons.

## Falsifier

A mismatch in order direction, omission of the empty or whole face,
unjustified identification of faces with partitions, an incorrect affine
dimension, loss of the `d>i` zero case, missing repeated roots, an
unproved correction inequality, or failure of the `n=1` chain case
would invalidate source fidelity or the proof. For the historical delivery,
an independently established resolution of the same literal conjecture
predating the formal merge would have invalidated open-problem-resolution
eligibility without changing the mathematical theorem. The later v4
submission does not supply that earlier chronology. The classical status of
Newton's inequality is already acknowledged.

## Evidence

The public formal conclusion is
`D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`.
Its only hypotheses are the positive-size and internal-index conditions
above. The exact geometric carrier and full-vector definition occur in
`CrownOrderPolytope`, `CrownOrderPolytopeFaceCounts`, and
`CrownOrderPolytopePositive`; `Scalar` and `Chebyshev` prove the
intermediate polynomial identities. The licensed prerequisite is
`D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm`.
It is applied to the negated roots at reversed index `degree-k-2`, with
out-of-degree coefficients handled by vanishing. Its license and retirement
condition are in `Library/Combinatorics/tao2026newton.md`.
The Library note supplies the inspected primary-source SHA-256 values
and the source-to-module correspondence. The 19-module Crown/Newton chain
is canonically frozen. The final Scribe `Describe.Lean` binds exactly one
`OpenProblemResolutionClaim` of kind `Proved` to this problem and the
public conclusion above. Its handwritten Formula AST states the same
natural-number quantifiers, three bounds and geometric-vector inequality
as the compiled Lean type; it is not an automatic statement projection.
PR 8714 is the completed delivery of that one claim; the later v4 source
status adds no second claim, theorem credit or KPI.

## Triage

`theorem`; Tier 1 recent externally named conjecture at the historical
delivery cutoff.
[Issue 8670](https://github.com/the-omega-institute/trureturing/issues/8670)
records the preregistration. The PR 8714 merge identity, required CI result,
and delivery-audit status are recorded above.

For the final log-concavity theorem, the reviewed `proof_shape` is
`content`: the live proof constructs real splitting with multiplicities
and derives the three corrected coefficient comparisons for the
geometric vector. Its `admission_basis` is `escape-witness`; the full
prerequisite chain passed independent pre-freeze declaration review.
The typed `Proved` claim records the exact external conjecture resolved
by this conclusion. It does not change that admission basis or grant
an exception for bind-only companion declarations.

The reviewed `utility.kind` is `none`: these are symbolic geometric
correspondences, unbounded counting formulas and polynomial inequalities,
not bounded enumeration, reflection infrastructure, an undischarged
numeric reduction, or a certified positive finite instance. The finite
triangle-rank image calculation occurs inside the actual geometric face
counting proof; it has no standalone theorem. That geometry supplies the
necessary boundary case of the universal result. `basis`, `consumer`, `instance`,
`premises`, `result`, and `claim` are not applicable to this `none`
classification. Classical Newton and the source's published prerequisite
results carry no new-mathematics or separate resolution claim.

`question_answered` is exactly Conjecture 3.7 for all positive sizes and
all internal indices, with the preregistration above.
The historical pre-delivery `dominating_theorem_search` was
`not-found-in-searched-scope` for an exact pre-existing Crown resolution in
the bounded searches described by the Library note. That finding is not a
present-tense no-proof claim; the later v4 source status does not alter its
historical scope or result. For the generic Newton prerequisite it was
`found` at the
statement level in Mathlib PR 42876; its stronger multiset form is reused
by the licensed source port. Its Lean `v4.34.0-rc1` toolchain differs from
the repository's `v4.33.0`, excluding direct dependency admission;
the port and the in-proof coefficient adaptation preserve the current pins.

## ASSUMED-UNVERIFIED

The full native pre-freeze source-fidelity, declaration and test reviews
were approved. The bounded pre-delivery public searches found no exact Crown
resolution in their searched scope, but did not establish exhaustive absence
or worldwide priority. In particular, a citing paper was found outside
OpenAlex's zero-count citation list. The later v4 theorem updates the current
source status without changing that historical search result. The upstream
Newton source cannot be admitted as a direct dependency at the current pins.
The licensed port and its exact coefficient application were included in the
approved full-scope source-admission review.
The kernel checks the formal objects, not their correspondence to
natural-language sources or external priority.

PR 8714's final required CI, merge and delivery audit are complete as recorded
above. No broader main-branch or journal-publication chronology is asserted
beyond the evidence stated here. Freezing the prerequisites, porting classical
Newton, or recording the later v4 source theorem does not earn a separate
open-problem resolution or KPI. Information
registration, sidecars, templates and DTR judge work belong to owner
issue 5214 under the current policy, not to this content lane.
