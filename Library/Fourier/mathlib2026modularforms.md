---
bibkey: mathlib2026modularforms
authors: "The Mathlib Community"
year: 2026
title: "Mathlib4: Modular Forms"
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ModularForms
claim: "Pinned Mathlib supplies normalized Eisenstein q-expansion coefficients and the actual level-one discriminant identity used in the integral divisor-sum construction."
strata_touched:
  - D5/S3/Arith/ModularForms/IntegralDiscriminant
license: citation-only
triage: anchor
---

# Pinned formal sources for the integral discriminant bridge

## Verified locator

Source: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ModularForms

This note identifies the formal source snapshot actually inspected, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, used with Lean v4.33.0.
The year records this snapshot review; no separate paper publication is asserted.

- `EisensteinSeries.E_qExpansion_coeff`, in
  `Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean`, gives
  the normalized analytic Eisenstein coefficients. Its weight-four and
  weight-six specializations, with Bernoulli values -1/30 and 1/42, give
  the classical series 1+240U and 1-504V.
- `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`, in
  `Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean`, identifies
  the actual analytic discriminant with (E4^3-E6^2)/1728. This identity
  alone is not an integer-coefficient proof.
- `PowerSeries.trunc_apply` and `PowerSeries.coeff_trunc`, in
  `Mathlib/RingTheory/PowerSeries/Trunc.lean`, express finite truncation at
  the strict bound n<N. They are correctness suppliers, not the executable
  coefficient algorithm.

The project proves exact divisibility of 5 sigma3(n)+7 sigma5(n) by 12,
constructs D=C+100U^2-147V^2+8000U^3 over the integers, identifies its image
with the actual analytic discriminant, and matches finite integer
convolutions with every coefficient. Those repository-specific realization
and algorithm statements are not attributed verbatim to an upstream theorem.
This is formalization of classical modular-form infrastructure, with no
claim of mathematical originality, unique credit or a new Maeda case.

The separate Hecke normalization context is already documented in
`Library/Fourier/ribetstein2017modularforms.md`, citing Ribet and Stein,
*Lectures on Modular Forms and Hecke Operators*, January 12, 2017, section
3.5.2. Its pages 20-22 are not used here as a source for discriminant
integrality or the repository's denominator-clearing implementation.

Citation and source-boundary note only; no upstream text or code is vendored.
