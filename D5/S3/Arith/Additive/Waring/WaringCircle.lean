/- GID: D5/S3/Arith/Additive/Waring/WaringCircle
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringCircle.lean#L1-L194
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open intervalIntegral

namespace Waring

/-- **正交性**：`∫₀¹ exp(2πi m α) dα = 1`（`m = 0`）或 `0`（`m ≠ 0`）。 -/
theorem integral_exp_mul_int (m : ℤ) :
    (∫ x in (0 : ℝ)..1, Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I) * (x : ℂ)))
      = if m = 0 then 1 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hc : ((m : ℂ) * (2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [hm, Real.pi_ne_zero]
    rw [integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) hc]
    have hexp : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I m
    simp [hexp, hm]

end Waring
