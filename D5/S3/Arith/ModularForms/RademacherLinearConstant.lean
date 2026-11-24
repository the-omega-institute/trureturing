/- GID: D5/S3/Arith/ModularForms/RademacherLinearConstant
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/RademacherLinearConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.LSeries.Dirichlet, mathlib/module/Mathlib.NumberTheory.LSeries.HurwitzZetaValues]
   utility: none
   digest: The Möbius L-series arithmetic constant in the linear Rademacher term. -/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped LSeries.notation ArithmeticFunction.Moebius

namespace D5.S3.Arith.ModularForms.RademacherLinearConstant

/-- The arithmetic normalization `2 * π ^ 2 * L(μ, 2) = 12`. -/
theorem moebius_linear_constant :
    2 * (Real.pi : ℂ) ^ 2 * LSeries ↗μ (2 : ℂ) = 12 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs, riemannZeta_two] at h
  calc
    2 * (Real.pi : ℂ) ^ 2 * LSeries ↗μ (2 : ℂ) =
        12 * (((Real.pi : ℂ) ^ 2 / 6) * LSeries ↗μ (2 : ℂ)) := by ring
    _ = 12 := by rw [h, mul_one]

end D5.S3.Arith.ModularForms.RademacherLinearConstant
