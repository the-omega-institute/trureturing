import D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC

namespace Reg.Support.AlmostFlatSICQutrit

open D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
open D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation
open D5.S3.Observer.WindowRegister D5.S3.Quantum.Algebra.WeylDisplacement
open Matrix
open scoped ComplexConjugate

set_option backward.isDefEq.respectTransparency false

noncomputable section

def vector : ZMod 3 → ℂ := fun j => if j = 0 then 2 * Complex.I else -Complex.I

theorem almostFlat : IsAlmostFlat 3 vector := by
  constructor
  · norm_num [vector, mul_comm]
  · intro j hj
    simp [vector, hj, neg_ne_zero.mpr hj]

private theorem sum_three (f : ZMod 3 → ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  change (∑ i : Fin 3, f (show ZMod 3 from i)) = _
  rw [Fin.sum_univ_three]

private theorem overlap (a b : ZMod 3) :
    star vector ⬝ᵥ (displacement 3 a b *ᵥ vector) =
      if a = 0 then if b = 0 then 6 else 3
      else if b = 0 then -3 else 3 * windowRoot 3 ^ (a * b).val := by
  have hc (r : ZMod 3) : ZMod.stdAddChar r = windowRoot 3 ^ r.val := by
    simpa [show (1 : ZMod 3).val = 1 from rfl,
      D5.S3.Fourier.FinitePoisson.character_apply] using
      (D5.S3.Observer.MatrixUnitCertificate.clock_phase_pow_eq_character r (1 : ZMod 3)).symm
  have hsum : 1 + windowRoot 3 + windowRoot 3 ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using
      (windowRoot_isPrimitiveRoot 3).geom_sum_eq_zero (by norm_num)
  rw [displacement_overlap_sum, sum_three]
  simp_rw [hc]
  fin_cases a <;> fin_cases b
  all_goals
    norm_num [vector, map_mul, Complex.conj_I,
      ZMod.val_mul, Fin.isValue, show (1 : ZMod 3).val = 1 from rfl,
      show (2 : ZMod 3).val = 2 from rfl]
  all_goals try simp +decide only [starRingEnd_apply, if_true, if_false]
  all_goals
    norm_num [star_mul, star_neg, star_ofNat, Complex.star_def,
      show (4 : ZMod 3).val = 1 from rfl, show (2 : ZMod 3) ≠ 0 from by decide]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals
    first
    | solve | ring
    | solve | linear_combination hsum
    | solve | linear_combination (-2 : ℂ) * hsum

theorem sic : IsSICFiducial 3 ((Real.sqrt (almostFlatNorm 3) : ℂ)⁻¹ • vector) := by
  have hL : almostFlatNorm 3 = 6 := by norm_num [almostFlatNorm]
  have hs : (Real.sqrt (almostFlatNorm 3) : ℂ) ^ 2 = 6 := by
    rw [hL]
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hscale : (Real.sqrt (almostFlatNorm 3) : ℂ)⁻¹ *
      (Real.sqrt (almostFlatNorm 3) : ℂ)⁻¹ = 1 / 6 := by
    rw [← mul_inv, ← pow_two, hs]
    norm_num
  constructor
  · change star ((Real.sqrt (almostFlatNorm 3) : ℂ)⁻¹ • vector) ⬝ᵥ
      ((Real.sqrt (almostFlatNorm 3) : ℂ)⁻¹ • vector) = 1
    rw [star_smul, smul_dotProduct, dotProduct_smul, squared_norm almostFlat]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    rw [← mul_assoc, hscale, hL]
    norm_num
  · intro a b hab
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    rw [← mul_assoc, hscale, overlap]
    have hw : ‖windowRoot 3‖ = 1 :=
      (windowRoot_isPrimitiveRoot 3).norm'_eq_one (by norm_num)
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by intro hb; exact hab (by simp [ha, hb])
      norm_num [ha, hb, norm_mul]
    · by_cases hb : b = 0 <;> norm_num [ha, hb, norm_mul, norm_pow, hw]

end
end Reg.Support.AlmostFlatSICQutrit
