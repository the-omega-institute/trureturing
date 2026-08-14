/- GID: D5/S3/Analytic/EulerGerm/GoldenLocalFactor
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical golden Euler local factor and its vacuum exponent. -/

import Mathlib
import D5.S3.Analytic.GoldenEulerBeta

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-14): searched the repository D5 tree for
   `o5Beta`, `o5_beta_closed_form`, `germLocalFactor`, and the displacement
   bridge, then searched pinned mathlib for `Int.fract`, floor bounds, and the
   golden-ratio inverse identities. The shared declarations cannot be moved
   into `D5/S3/Analytic/GoldenEulerBeta.lean`: that module is frozen, and the
   repository freeze law forbids adding declarations to it in place.

   The displacement theorem
   `GoldenDisplacementComplexEulerProduct.o5_beta_eq_substitution_start_sub_conjugate`
   is a stronger statement of a different shape, relating `o5Beta` to the
   substitution start. This file neither reproves nor imports it. Instead,
   `o5_beta_zero` is the canonical specialization at the lowest unfrozen
   layer, proved directly from the frozen `o5_beta_closed_form` API.

   The displacement file still contains an inline copy of the formula now
   named `germLocalFactor` here. Eliminating that remaining duplicate would
   require editing the separately owned displacement lane, which is outside
   this change; this module therefore fixes the convergence-side dependency
   boundary without claiming to have fully removed the duplicate. -/

namespace D5.S3.Analytic.EulerGerm.GoldenLocalFactor

open D5.S3.Analytic.GoldenEulerBeta

noncomputable section

/-- The prime-local series with the frozen golden Euler exponents. -/
noncomputable def germLocalFactor (s : ℂ) (p : ℕ) : ℂ :=
  ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta v : ℂ))

/-- The vacuum exponent is zero. -/
theorem o5_beta_zero : o5Beta 0 = 0 := by
  rw [o5_beta_closed_form]
  simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_one,
    one_mul]
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using Real.one_lt_goldenRatio.le
    · norm_num
      exact Real.goldenRatio_lt_two
  rw [Int.fract, hfloor]
  simp only [Int.cast_one]
  rw [one_div, Real.inv_goldenRatio]
  linarith [Real.one_sub_goldenConj]

end

end D5.S3.Analytic.EulerGerm.GoldenLocalFactor
