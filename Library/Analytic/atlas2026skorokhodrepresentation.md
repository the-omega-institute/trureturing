---
bibkey: atlas2026skorokhodrepresentation
authors: Unattributed source file; copyright Meta Platforms, Inc. and affiliates
year: 2026
title: Skorokhod representation theorem in ATLAS Lean
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/SkorokhodRepresentation.lean
claim: Every weakly convergent sequence of probability measures on an arbitrary Polish Borel space has globally measurable copies on the same closed unit interval with exact original laws and almost-everywhere convergence of the full sequence.
strata_touched:
  - D5/S3/Analytic/Probability/SkorokhodRepresentation
license: Complete upstream LICENSE including ML intended-use preface retained at docs/reports/lovasz-suppliers/atlas-LICENSE.txt
triage: anchor
---

# ATLAS Skorokhod representation

The exact formal supplier is `facebookresearch/atlas-lean` at immutable revision
`a60759060b5616df0d5775b42da4d337719feb32`, file
`MathlibExt/Probability/SkorokhodRepresentation.lean`. Its SHA-256 is
`53ccb456e04b740e1787e74dccb23ab7d3603d466a50d9c90a20bc92322f4090`.
The source file supplies no named author; Meta Platforms, Inc. and affiliates
is its stated copyright holder. The metadata year is the verified year of the
pinned repository revision, not an asserted publication date or theorem date.

The source endpoint `skorokhod_representation` quantifies over an arbitrary
universe and a Polish topological space X with its Borel measurable structure,
a sequence mu of probability measures on X and a probability limit mu0.
Weak convergence of mu to mu0 implies existence of functions
Y : Nat -> Real -> X and Y0 : Real -> X, each globally measurable, whose
pushforwards of the same measure lambda = volume.restrict(Set.Icc(0,1))
are exactly mu(n) and mu0, respectively, and such that Y(n,t) converges to
Y0(t) for lambda-almost every t along the full natural sequence.
Nonemptiness of X follows from mu0. There is no compactness, support,
moment, density, atomlessness, subsequence, supplied realization or supplied
joint-law hypothesis. The copies preserve their individual laws; the theorem
asserts no preservation of original cross-index dependence, filtration,
adaptedness, independence or conditional laws, no convergence of original
variables, and no algorithm or rate.

The native owner is `D5/S3/Analytic/Probability/SkorokhodRepresentation.lean`.
It adapts the supplier's null-frontier Boolean-address embedding, convergence
reflection, continuity-set distribution-function convergence and quantile
argument. It reuses the native general `CompactQuantile` results and Cantor
homeomorphism. Raw quantiles and globally measurable `AEMeasurable.mk`
representatives are related on a common conull event, with equality of the
open- and closed-unit-interval restricted measures and exact pushforward laws.
The native endpoint retains the supplier's full scope. This is a known
classical theorem and an adaptation of an existing external formalization,
with no novelty, priority, first-formalization or open-problem-resolution claim.

The supplier and native repository use Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Matching pins alone establish
neither native admission nor proof fidelity. No external Lake dependency is
added. Retire this adaptation only when the locally adopted Mathlib pin
provides the full equivalent arbitrary-universe Polish Borel theorem with
globally measurable real-domain copies, both exact laws under this same
closed-unit-interval measure, and almost-everywhere full-sequence convergence.

The upstream notice refers to the root LICENSE. Its complete text is retained
at `docs/reports/lovasz-suppliers/atlas-LICENSE.txt`, SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
This includes its prefatory statement that the codebase is not intended for
use to train, fine-tune, distill, evaluate or otherwise develop ML models.
This note preserves the actual terms and does not assert blanket permissive
clearance.

The classical bibliographic anchor is A. V. Skorokhod, *Limit Theorems for
Stochastic Processes*, Theory of Probability & Its Applications 1(3) (1956),
261–290, DOI `10.1137/1101022`. The bibliographic metadata is verified through
`https://api.crossref.org/works/10.1137/1101022`. The original theorem body is
UNVERIFIED: the publisher PDF endpoint returned HTTP 403. No theorem number
or textbook locator is asserted. The pinned Lean file is the exact statement
and proof source for this adaptation.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/SkorokhodRepresentation.lean
contains `skorokhod_representation` and its consumed embedding, CDF and
quantile support. The complete root license is at
https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/LICENSE.
