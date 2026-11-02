/- GID: D5/S3/Arith/ModularForms/EtaCuspPhases
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaCuspPhases
   mirror-E: none(waiver:initial-component-review)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.DedekindEta]
   utility: none
   digest: Conjugate third-cusp and zero-cusp phases with unshifted Euler normalization. -/

import D5.S3.Arith.ModularForms.EtaThirdCusp

/-! Exact zero and third cusp identities. The reciprocal partition product and
Euler quotient retain their original normalization, with principal roots. -/

set_option autoImplicit false
noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate

namespace D5.S3.Arith.ModularForms.EtaCuspPhases

open EtaCuspTransform EtaThirdCusp

/-- Conjugation preserves the reciprocal Euler product; used by the conjugate cusp. -/
theorem partition_conj (q : ℂ) :
    conj (partitionProduct q) = partitionProduct (conj q) := by
  unfold partitionProduct eulerProduct
  rw [map_inv₀]
  congr 1
  have ht := Complex.conjCAE.toHomeomorph.isClosedEmbedding.map_tprod
    (g := Complex.conjCAE) (L := SummationFilter.unconditional ℕ) (fun n : ℕ => 1 - q ^ (n + 1))
  simpa using ht

/-- Principal-root conjugation on the open right half-plane. -/
theorem sqrt_conj_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    conj (Complex.sqrt z) = Complex.sqrt (conj z) := by
  have ha : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have h := (Complex.conj_cpow z (2⁻¹ : ℂ) ha).symm
  have hc : conj (2 : ℂ) = 2 := by
    apply Complex.ext <;> norm_num [Complex.conj_re, Complex.conj_im]
  simpa [Complex.sqrt, hc] using h

/-- The conjugate third cusp. No bound on `w.im` is imposed. -/
theorem partition_two_thirds (w : ℂ) (hw : 0 < w.re) :
    partitionProduct (exp (4 * Real.pi * I / 3 - w)) =
      exp (-Real.pi * I / 18) * Complex.sqrt (3 * w / (2 * Real.pi)) *
      exp (Real.pi ^ 2 / (54 * w) - w / 24) *
      partitionProduct (exp (2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w))) := by
  have hperiod : exp (4 * Real.pi * I / 3 - w) = exp (-2 * Real.pi * I / 3 - w) := by
    rw [show 4 * (Real.pi : ℂ) * I / 3 - w =
      (-2 * Real.pi * I / 3 - w) + 2 * Real.pi * I by ring,
      exp_add, exp_two_pi_mul_I, mul_one]
  rw [hperiod]
  have ht := congrArg conj (partition_one_third (conj w) (by simpa using hw))
  have hr : 0 < (3 * conj w / (2 * Real.pi)).re := by
    simp [Complex.div_re, Complex.mul_re]
    positivity
  simp only [map_mul, map_sub, map_div₀, map_neg, map_ofNat, map_pow, conj_ofReal,
    conj_I, conj_conj, ← exp_conj, partition_conj, sqrt_conj_of_re_pos hr] at ht
  convert ht using 1 <;> congr 2 <;> ring

/-- At denominator one the normalized partition multiplier is exactly one. -/
theorem partition_zero (w : ℂ) (hw : 0 < w.re) :
    partitionProduct (exp (-w)) =
      Complex.sqrt (w / (2 * Real.pi)) *
      exp (Real.pi ^ 2 / (6 * w) - w / 24) *
      partitionProduct (exp (-4 * Real.pi ^ 2 / w)) := by
  let τ := cuspPoint 1 0 w hw
  have hS := ModularForm.eta_comp_eq_csqrt_I_inv τ.im_pos
  have he : ModularForm.eta ((0 : ℂ) / 1 + 2 * Real.pi * I / ((1 : ℂ) ^ 2 * w)) =
      (Complex.sqrt I)⁻¹ * Complex.sqrt (I * ((1 : ℂ) * w / (2 * Real.pi))) *
        ModularForm.eta ((0 : ℂ) / 1 + I * w / (2 * Real.pi)) := by
    have ha := cusp_action 1 (by norm_num) 0 0 1 (by norm_num) w hw
    have hm : cuspMatrix 1 0 0 1 (by norm_num) = ModularGroup.S := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [cuspMatrix, ModularGroup.S]
    have hs : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
      rw [UpperHalfPlane.modular_S_smul]
      simp [div_eq_mul_inv]
    rw [hm] at ha
    norm_num only [Int.cast_zero, Nat.cast_one, zero_div, zero_add, one_pow, one_mul] at ha ⊢
    rw [← ha, hs]
    simpa [τ, cuspPoint, mul_assoc, mul_div_assoc] using hS
  have hu := (cuspMatrix 1 0 0 1 (by norm_num) • τ : ℍ).im_pos
  change 0 < ((cuspMatrix 1 0 0 1 (by norm_num) • τ : ℍ) : ℂ).im at hu
  rw [cusp_action 1 (by norm_num) 0 0 1 (by norm_num) w hw] at hu
  have ht := partition_cusp_of_eta 1 (by norm_num) 0 0 (Complex.sqrt I)⁻¹ w hw hu (by
    simpa only [Nat.cast_one, Int.cast_zero, zero_div, zero_add, one_mul, one_pow] using he)
  have hs : Complex.sqrt I ≠ 0 := by simp [Complex.sqrt]
  simpa [hs, neg_div] using ht

/-- The exact two third-cusp phases give Kane's first cosine sum. The summands
have the original negative Fourier-extraction exponent. -/
theorem first_phase_sum (n : ℕ) :
    exp (-Real.pi * I / 9) * exp (-2 * Real.pi * I * n / 3) +
      exp (Real.pi * I / 9) * exp (-4 * Real.pi * I * n / 3) =
        2 * Complex.cos (2 * Real.pi * n / 3 + Real.pi / 9) := by
  have hp : exp (-4 * Real.pi * I * n / 3) = exp (2 * Real.pi * I * n / 3) := by
    have he := Complex.exp_int_mul_two_pi_mul_I (-(n : ℤ))
    push_cast at he
    rw [show -4 * (Real.pi : ℂ) * I * n / 3 =
      2 * Real.pi * I * n / 3 + -(n : ℂ) * (2 * Real.pi * I) by ring,
      exp_add, he, mul_one]
  rw [hp, ← exp_add, ← exp_add, Complex.two_cos]
  rw [add_comm]
  congr 1 <;> congr 1 <;> ring

end D5.S3.Arith.ModularForms.EtaCuspPhases

#print axioms D5.S3.Arith.ModularForms.EtaCuspPhases.partition_two_thirds
#print axioms D5.S3.Arith.ModularForms.EtaCuspPhases.partition_zero
#print axioms D5.S3.Arith.ModularForms.EtaCuspPhases.first_phase_sum
