---
bibkey: mathlib2026symmetricnewtonidentities
authors: Mathlib contributors
year: 2026
title: "Mathlib symmetric polynomial definitions and Newton identities"
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean
claim: "The universal Newton identities express evaluated power sums through elementary symmetric polynomials; the degree-two, degree-three and degree-four formulas are consumed specializations."
strata_touched:
  - D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality
license: citation-only
triage: anchor
---

## Verified locator

Source: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean

`MvPolynomial.psum_eq_mul_esymm_sub_sum` is applied at degrees two, three and four, then evaluated with `MvPolynomial.aeval`. The construction uses `MvPolynomial.esymm` and `MvPolynomial.psum` from the pinned `Symmetric/Defs.lean`. These universal polynomial identities and their scalar specializations are existing mathematics. They supply normalization steps in the curvature proof, not its new estimate.
