---
bibkey: mathlib2026radiationbudget
authors: Mathlib contributors
year: 2026
title: Monotone primitives and the fundamental theorem of calculus on a ray
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean
claim: A primitive continuous at the left endpoint with a nonpositive derivative and finite limit has an integrable derivative whose integral is the limit minus the initial value.
strata_touched:
  - D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget
license: Apache-2.0
triage: anchor
---

# Finite energy and radiation

## Verified locator

The pinned source is:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean

`MeasureTheory.integrableOn_Ioi_deriv_of_nonpos` proves integrability when the
primitive has a finite limit. `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`
identifies the integral with the terminal limit minus the left endpoint value.
Both accept derivatives only on the open ray and require right continuity at
its initial endpoint. The proof of integrability uses finite-interval calculus
and convergence of interval integrals, rather than assuming continuity of the derivative.

In the same pin, `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` supplies
`antitoneOn_of_deriv_nonpos`, and `Mathlib/Topology/Order/MonotoneConvergence.lean`
supplies `tendsto_atTop_ciInf`. The present energy theorem applies these to
the extension E(max(u0,u)), whose infimum is nonnegative, and then uses E'=-P.
The constant-power corollary combines the total bound with
`MeasureTheory.setIntegral_mono_set` and `intervalIntegral.integral_const`.
The energy notation and the assembly of these results are supplied by this repository.
