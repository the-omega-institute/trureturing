/- GID: D5/S3/Estimation/ErrorExponents/ChernoffInformationZeroCriterion
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/ChernoffInformationZeroCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Chernoff information vanishes exactly when the finite laws agree. -/

/- Library-search audit trail (2026-08-25):
   * Repository searches for Chernoff information, its coefficient, and a zero characterization
     found no existing definition or exact theorem. The frozen Bhattacharyya coefficient is the
     half-parameter slice and its square bound separates unequal normalized mass functions.
   * Pinned Mathlib searches found tail bounds called Chernoff bounds, extended-real logarithms,
     and real-power primitives, but no statistical Chernoff information or zero criterion.
-/

import D5.S3.TotalVariation.Bhattacharyya
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

namespace D5.S3.Estimation.ErrorExponents.ChernoffInformationZeroCriterion

open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- The optimized Chernoff coefficient of two finite mass functions. -/
noncomputable def chernoffCoefficient {ι : Type*} [Fintype ι]
    (p q : ι -> ℝ) : ℝ :=
  sInf (Set.range fun lambda : Set.Icc (0 : ℝ) 1 =>
    ∑ i, (p i) ^ (lambda : ℝ) * (q i) ^ (1 - (lambda : ℝ)))

/-- Chernoff information, with the extended logarithm recording a zero coefficient as infinity. -/
noncomputable def chernoffInformation {ι : Type*} [Fintype ι]
    (p q : ι -> ℝ) : EReal :=
  -ENNReal.log (ENNReal.ofReal (chernoffCoefficient p q))

private theorem rpow_split_self (x lambda : ℝ) (hx : 0 <= x) :
    x ^ lambda * x ^ (1 - lambda) = x := by
  by_cases hx0 : x = 0
  · subst x
    by_cases hlambda : lambda = 0
    · subst lambda
      norm_num
    · simp [Real.zero_rpow hlambda]
  · rw [← Real.rpow_add (lt_of_le_of_ne hx (Ne.symm hx0))]
    norm_num

private theorem chernoffCoefficient_self {ι : Type*} [Fintype ι]
    (p : ι -> ℝ) (hp : (∀ i, 0 <= p i) ∧ ∑ i, p i = 1) :
    chernoffCoefficient p p = 1 := by
  have hvalue (lambda : Set.Icc (0 : ℝ) 1) :
      (∑ i, (p i) ^ (lambda : ℝ) * (p i) ^ (1 - (lambda : ℝ))) = 1 := by
    calc
      (∑ i, (p i) ^ (lambda : ℝ) * (p i) ^ (1 - (lambda : ℝ))) =
          ∑ i, p i := by
        apply Finset.sum_congr rfl
        intro i _
        exact rpow_split_self (p i) lambda (hp.1 i)
      _ = 1 := hp.2
  rw [chernoffCoefficient]
  have hrange :
      (Set.range fun lambda : Set.Icc (0 : ℝ) 1 =>
        ∑ i, (p i) ^ (lambda : ℝ) * (p i) ^ (1 - (lambda : ℝ))) = {1} := by
    ext value
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨lambda, rfl⟩
      exact hvalue lambda
    · rintro rfl
      exact ⟨⟨0, by norm_num⟩, hvalue ⟨0, by norm_num⟩⟩
  rw [hrange, csInf_singleton]

private theorem coefficient_range_bddBelow {ι : Type*} [Fintype ι]
    (p q : ι -> ℝ) (hp : ∀ i, 0 <= p i) (hq : ∀ i, 0 <= q i) :
    BddBelow (Set.range fun lambda : Set.Icc (0 : ℝ) 1 =>
      ∑ i, (p i) ^ (lambda : ℝ) * (q i) ^ (1 - (lambda : ℝ))) := by
  refine ⟨0, ?_⟩
  rintro value ⟨lambda, rfl⟩
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.rpow_nonneg (hp i) _) (Real.rpow_nonneg (hq i) _)

private theorem chernoffCoefficient_le_bhattacharyya
    {ι : Type*} [Fintype ι]
    (p q : ι -> ℝ) (hp : ∀ i, 0 <= p i) (hq : ∀ i, 0 <= q i) :
    chernoffCoefficient p q <= bhattacharyya p q := by
  rw [chernoffCoefficient, bhattacharyya]
  let hhalf : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  calc
    sInf (Set.range fun lambda : Set.Icc (0 : ℝ) 1 =>
        ∑ i, (p i) ^ (lambda : ℝ) * (q i) ^ (1 - (lambda : ℝ))) <=
        ∑ i, (p i) ^ (hhalf : ℝ) * (q i) ^ (1 - (hhalf : ℝ)) :=
      csInf_le (coefficient_range_bddBelow p q hp hq) (Set.mem_range_self hhalf)
    _ = ∑ i, Real.sqrt (p i * q i) := by
      apply Finset.sum_congr rfl
      intro i _
      norm_num [hhalf, ← Real.sqrt_eq_rpow, Real.sqrt_mul (hp i)]

/-- For finite nonnegative normalized laws, Chernoff information is zero exactly when the laws
agree; consequently every positive Chernoff exponent witnesses a genuine law difference. -/
theorem same_law_iff_chernoff_information_zero {ι : Type*} [Fintype ι]
    (p q : ι -> ℝ)
    (hp : (∀ i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 <= q i) ∧ ∑ i, q i = 1) :
    (p = q ↔ chernoffInformation p q = 0) ∧
      (0 < chernoffInformation p q -> p ≠ q) := by
  have hzero : p = q ↔ chernoffInformation p q = 0 := by
    constructor
    · rintro rfl
      simp [chernoffInformation, chernoffCoefficient_self p hp]
    · intro hinfo
      have hlog : ENNReal.log (ENNReal.ofReal (chernoffCoefficient p q)) = 0 := by
        simpa [chernoffInformation] using congrArg Neg.neg hinfo
      have hcoefficient : chernoffCoefficient p q = 1 := by
        exact ENNReal.ofReal_eq_one.mp (ENNReal.log_eq_one_iff.mp hlog)
      have hbc_le := bhattacharyya_le_one p q hp hq
      have hcoefficient_le := chernoffCoefficient_le_bhattacharyya p q hp.1 hq.1
      have hbc : bhattacharyya p q = 1 := by linarith
      have htv_sq := total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
      have htv : totalVariation p q = 0 := by
        nlinarith [sq_nonneg (totalVariation p q)]
      exact (total_variation_eq_zero_iff p q).mp htv
  refine ⟨hzero, ?_⟩
  intro hpositive heq
  have := hzero.mp heq
  rw [this] at hpositive
  exact (lt_irrefl 0) hpositive

#print axioms chernoffCoefficient
#print axioms chernoffInformation
#print axioms same_law_iff_chernoff_information_zero

end D5.S3.Estimation.ErrorExponents.ChernoffInformationZeroCriterion
