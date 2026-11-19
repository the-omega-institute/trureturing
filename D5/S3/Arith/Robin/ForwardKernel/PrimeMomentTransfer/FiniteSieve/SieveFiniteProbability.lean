/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform residue expectations give fourth norms and interval moment scales. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveAnalyticDefs
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Normalized counting measure connects finite sieve moments to real L4 estimates. -/

open scoped BigOperators
open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Normalized counting measure on the residues has total mass one. -/
theorem sieve_probability (Q : ℕ+) : IsProbabilityMeasure (sieveUniformMeasure Q) := by
  simpa [sieveUniformMeasure, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    ZMod.card] using
      (inferInstance : IsProbabilityMeasure
        (((Measure.count : Measure (ZMod (Q : ℕ))) Set.univ)⁻¹ • Measure.count))

/-- Integration against the uniform residue measure is the finite sieve expectation. -/
theorem sieve_expectation_integral (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) :
    (∫ x, F x ∂sieveUniformMeasure Q) = sieveExpectation Q F := by
  simp [sieveUniformMeasure, integral_smul_measure, sieveExpectation, div_eq_mul_inv, mul_comm]

/-- Every real function on the finite residue space has a finite fourth norm. -/
theorem sieve_memLp_four (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) : MemLp F 4 (sieveUniformMeasure Q) := by
  have := sieve_probability Q
  exact MemLp.of_discrete

/-- The finite fourth norm is the real L4 norm for the uniform residue measure. -/
theorem sieve_norm4_eq_lpNorm (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) :
    sieveNorm4 Q F = lpNorm F 4 (sieveUniformMeasure Q) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (sieve_memLp_four Q F).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast, Real.norm_eq_abs]
  rw [sieve_expectation_integral]
  norm_num [sieveNorm4]

/-- The finite fourth norm is nonnegative. -/
theorem sieve_norm4_nonneg (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) : 0 ≤ sieveNorm4 Q F := by
  rw [sieve_norm4_eq_lpNorm]
  exact lpNorm_nonneg

/-- Taking the fourth power of the finite fourth norm recovers the fourth absolute moment. -/
theorem sieve_norm4_fourth (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) :
    (sieveNorm4 Q F) ^ 4 = sieveExpectation Q (fun x => |F x| ^ 4) := by
  have hnonneg : 0 ≤ sieveExpectation Q (fun x => |F x| ^ 4) := by
    unfold sieveExpectation
    positivity
  simpa only [sieveNorm4, one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hnonneg (by norm_num : (4 : ℕ) ≠ 0)

/-- The finite fourth norm satisfies Minkowski's inequality. -/
theorem sieve_norm4_add_le (Q : ℕ+) (F G : ZMod (Q : ℕ) → ℝ) :
    sieveNorm4 Q (fun x => F x + G x) ≤ sieveNorm4 Q F + sieveNorm4 Q G := by
  simp_rw [sieve_norm4_eq_lpNorm]
  exact lpNorm_add_le (sieve_memLp_four Q F) (by norm_num)

/-- A real scalar multiplies the finite fourth norm by its absolute value. -/
theorem sieve_norm4_smul (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) (c : ℝ) :
    sieveNorm4 Q (fun x => c * F x) = |c| * sieveNorm4 Q F := by
  simp_rw [sieve_norm4_eq_lpNorm]
  simpa only [Pi.smul_def, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs] using
    (lpNorm_const_smul c F (sieveUniformMeasure Q) (p := 4))

/-- Interval moments agree with moments of their interval-sum residue functions. -/
theorem sieve_interval_moment_eq_product_moment (k : ℕ) (Q : ℕ+) (H : ℝ) (a b : Fin k → ℝ) :
    sieveIntervalMoment Q H a b = sieveProductMoment Q (fun i => sieveIntervalSum Q H (a i) (b i)) := rfl

/-- The interval Wick defect agrees with the defect in residue-function coordinates. -/
theorem sieve_interval_defect_eq_wick_defect (Q : ℕ+) (H : ℝ) (a b : Fin 4 → ℝ) :
    sieveIntervalWickDefect Q H a b = sieveWickDefect Q (fun i => sieveIntervalSum Q H (a i) (b i)) := rfl

/-- Powers of the positive standard deviation equal the interval moment scales. -/
theorem sieve_scale_power (H : ℝ) (hH : 2 ≤ H) (k : ℕ) :
    0 < sieveScale H ∧ (sieveScale H) ^ k = momentScale k H := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hlog : 0 < Real.log H := Real.log_pos (lt_of_lt_of_le (by norm_num) hH)
  have hprod : 0 < H * Real.log H := mul_pos hHpos hlog
  refine ⟨Real.sqrt_pos.mpr hprod, ?_⟩
  unfold sieveScale momentScale
  rw [← Real.rpow_natCast]
  exact (Real.rpow_div_two_eq_sqrt (k : ℝ) hprod.le).symm

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
