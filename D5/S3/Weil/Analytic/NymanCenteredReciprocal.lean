/- GID: D5/S3/Weil/Analytic/NymanCenteredReciprocal
   generality: I
   mirror-B: none(waiver:nyman-centered-prime-analysis)
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: Reciprocal-scale representation of centered prime dilations by a Dirichlet convolution. -/

import D5.S3.Weil.Analytic.NymanPrimeDilations
import D5.S3.Weil.Analytic.NymanDilationTransform

/-! The weighted dilation representation at reciprocal scales. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace NymanCenteredReciprocal

open NymanPrimeDilations NymanDilationTransform
open NymanFixedRationalKernel (A_pos b b_zero_right b_zero_off continuous_b)

theorem centeredPrimeDilations_inv_eq_dilatedSum {t : ℝ} (ht : 0 < t) :
    (centeredPrimeDilations t⁻¹ : ℂ) =
      dilatedSum (fun n => ((centeredPrimeCoefficient * (μ : ArithmeticFunction ℝ)) n : ℝ))
        (fun u => (b u : ℂ)) t := by
  rw [centeredPrimeDilations_eq_convolution]
  unfold dilatedSum
  rw [tsum_eq_sum (s := Ioc 0 ⌊B * t⁻¹⌋₊)]
  · push_cast
    simp_rw [div_inv_eq_mul]
  · intro n hn
    by_cases hzero : n = 0
    · simp [hzero]
    have hfloor : ⌊B * t⁻¹⌋₊ < n := lt_of_not_ge fun h =>
      hn (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hzero, h⟩)
    have hval := Nat.lt_of_floor_lt hfloor
    have hb : B ≤ (n : ℝ) * t := by
      have h := (mul_lt_mul_of_pos_right hval ht).le
      simpa [mul_assoc, ht.ne'] using h
    simp [b_zero_right hb]

theorem continuousOn_centeredPrimeDilations_inv :
    ContinuousOn (fun t : ℝ => centeredPrimeDilations t⁻¹) (Set.Ioi 0) := by
  have h := continuousOn_dilatedSum
    (fun n => ((centeredPrimeCoefficient * (μ : ArithmeticFunction ℝ)) n : ℝ))
    (Complex.continuous_ofReal.comp continuous_b)
    (fun x hx => by simp [b_zero_off x hx])
  have h' := Complex.continuous_re.comp_continuousOn h
  apply h'.congr
  intro t ht
  change centeredPrimeDilations t⁻¹ =
    (dilatedSum (fun n => ((centeredPrimeCoefficient * (μ : ArithmeticFunction ℝ)) n : ℝ))
      (fun u => (b u : ℂ)) t).re
  rw [← centeredPrimeDilations_inv_eq_dilatedSum ht]
  simp

end NymanCenteredReciprocal
