/- GID: D5/S3/Geometry/Rauzy/TribonacciNullBoundary
   generality: I
   mirror-B: D5/B/S3/Geometry/Rauzy/TribonacciNullBoundary
   mirror-E: none(waiver:unbounded-planar-measure-inference)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar]
   utility: none
   digest: The frontier of the actual non-Perron Tribonacci Rauzy fractal has planar volume zero. -/

import D5.S3.Geometry.Rauzy.TribonacciRegularClosure
import D5.S3.Topology.ContractingCoverNullBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Normed.MulAction

/-! The finite interior-cylinder loss argument for the original Tribonacci Rauzy closure. -/

namespace D5.S3.Geometry.Rauzy.TribonacciNullBoundary

open D5.S0.Tower.Tribonacci
open RauzyFractal Set MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem affine_volume (t b : Complex) (S : Set Complex) :
    volume ((fun w : Complex => t + b * w) '' S) =
      (‖b‖₊ ^ 2 : NNReal) * volume S := by
  have he : (fun w : Complex => t + b * w) = (fun w => t + w) ∘ (fun w => b * w) := rfl
  rw [he, image_comp, image_add_left, measure_preimage_add]
  have h := Measure.addHaar_image_linearMap volume (Algebra.lmul ℝ Complex b) S
  change volume ((fun w : Complex => b * w) '' S) = _ at h
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (sq_nonneg ‖b‖)] at h
  simpa only [ENNReal.coe_nnreal_eq, NNReal.coe_pow, coe_nnnorm] using h

/-- The original closure of finite admissible sums has null frontier at either
characteristic root distinct from the real Perron root. -/
theorem rauzyFractal_frontier_volume_zero {z : Complex}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (Values.tribonacciConstant : Complex)) :
    volume (frontier (RauzyFractal.rauzyFractal z)) = 0 := by
  have hr := Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  have hroot := (Binet.tribonacci_secondary_root_relations hz hz_ne).2.2
  have hz0 : z ≠ 0 := by
    intro he
    simp [he] at hroot
  have h2 : ‖z ^ 2‖₊ ≤ ‖z‖₊ := by
    change ‖z ^ 2‖ ≤ ‖z‖
    rw [norm_pow]
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hr.le)]
  have h3 : ‖z ^ 3‖₊ ≤ ‖z‖₊ := by
    change ‖z ^ 3‖ ≤ ‖z‖
    calc
      ‖z ^ 3‖ = ‖z ^ 2‖ * ‖z‖ := by rw [pow_succ, norm_mul]
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right
        ((show ‖z ^ 2‖ ≤ ‖z‖ from h2).trans hr.le) (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  let f : Fin 3 → Complex → Complex :=
    ![zeroPrefixMap z, oneZeroPrefixMap z, oneOneZeroPrefixMap z]
  let a : Fin 3 → NNReal := ![‖z‖₊ ^ 2, ‖z‖₊ ^ 4, ‖z‖₊ ^ 6]
  have hnorm : ‖z‖ ^ 2 = Values.tribonacciConstant⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ Values.tribonacciConstant_ne_zero).mp
    simpa [mul_comm] using hroot
  have hsum : ∑ i, a i = 1 := by
    apply NNReal.coe_injective
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, a,
      Matrix.cons_val_zero, Matrix.cons_val_succ, NNReal.coe_add, NNReal.coe_pow,
      coe_nnnorm, NNReal.coe_one]
    have hv := Values.tribonacci_inverse_sum
    norm_num only [zpow_neg, zpow_ofNat, pow_one] at hv
    rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring,
      show ‖z‖ ^ 6 = (‖z‖ ^ 2) ^ 3 by ring, hnorm]
    simpa only [inv_pow, add_assoc] using hv
  apply D5.S3.Topology.ContractingCoverNullBoundary.measure_frontier_eq_zero_of_contracting_cover
    volume (rauzyFractal_isCompact hz hz_ne)
    (TribonacciInterior.rauzyFractal_interior_nonempty hz hz_ne)
    (q := ‖z‖₊) (show ‖z‖₊ < 1 from hr) f
    (a := a)
  · intro i
    have hmul (b : Complex) : LipschitzWith ‖b‖₊ (fun w : Complex => b * w) :=
      lipschitzWith_smul b
    fin_cases i
    · exact hmul z
    · exact ((isometry_add_left (1 : Complex)).lipschitzWith.comp (hmul (z ^ 2))).weaken
        (by simpa using h2)
    · exact ((isometry_add_left (1 + z)).lipschitzWith.comp (hmul (z ^ 3))).weaken
        (by simpa using h3)
  · intro i
    fin_cases i
    · exact (Homeomorph.mulLeft₀ z hz0).isOpenMap
    · exact (isOpenMap_add_left (1 : Complex)).comp
        (Homeomorph.mulLeft₀ (z ^ 2) (pow_ne_zero _ hz0)).isOpenMap
    · exact (isOpenMap_add_left (1 + z)).comp
        (Homeomorph.mulLeft₀ (z ^ 3) (pow_ne_zero _ hz0)).isOpenMap
  · apply Eq.trans ?_ (TribonacciRegularClosure.rauzyFractal_prefix_cover hz hz_ne)
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
      · exact mem_iUnion.mpr ⟨2, hx⟩
  · intro i
    have hp : 0 < ‖z‖₊ := nnnorm_pos.mpr hz0
    fin_cases i <;> exact pow_pos hp _
  · exact hsum
  · intro i S _
    fin_cases i
    · change volume ((fun w : Complex => z * w) '' S) =
        ((‖z‖₊ ^ 2 : NNReal) : ENNReal) * volume S
      simpa only [zero_add] using affine_volume 0 z S
    · change volume ((fun w : Complex => 1 + z ^ 2 * w) '' S) =
        ((‖z‖₊ ^ 4 : NNReal) : ENNReal) * volume S
      have h := affine_volume 1 (z ^ 2) S
      rw [nnnorm_pow, ← pow_mul] at h
      exact h
    · change volume ((fun w : Complex => 1 + z + z ^ 3 * w) '' S) =
        ((‖z‖₊ ^ 6 : NNReal) : ENNReal) * volume S
      have h := affine_volume (1 + z) (z ^ 3) S
      rw [nnnorm_pow, ← pow_mul] at h
      exact h

end D5.S3.Geometry.Rauzy.TribonacciNullBoundary
