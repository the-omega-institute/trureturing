/- GID: D5/S3/TotalVariation/ProductSubadditive
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ProductSubadditive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove subadditivity of total variation over products and exhibit strictness. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `totalVariation.*prod`, `product.*totalVariation`,
     `total variation.*product`, `variationDist.*prod`, `sum_prod_type`, and `abs_mul`.
   * No total-variation product or subadditivity theorem was found. The proof reuses
     `Fintype.sum_prod_type`, `abs_mul`, `Finset.mul_sum`, and `Finset.sum_mul` for the two
     hybrid collapses.
   * Repository grep under `D5` found no total-variation product or subadditivity declaration.
     The `TotalVariation` bucket contained exactly Bhattacharyya, Convexity, DataProcessing,
     Hellinger, HellingerDataProcessing, HellingerDivergence, Metric, NegentropyBudget, and
     Pinsker before this file was added.
-/

import D5.S3.TotalVariation.Metric

namespace D5.S3.TotalVariation.ProductSubadditive

open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/- Total variation is subadditive over products when the two factors held fixed along the hybrid
path have absolute mass at most one. The universal hybrid identities scale by `∑ i, |p i|` and
`∑ k, |q' k|`; hence no pointwise sign, ordinary mass, or equal-mass hypothesis is needed. -/
theorem total_variation_product_subadditive {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι → ℝ) (p' q' : κ → ℝ)
    (hp : (∑ i, |p i|) ≤ 1)
    (hq' : (∑ k, |q' k|) ≤ 1) :
    totalVariation (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) ≤
      totalVariation p q + totalVariation p' q' := by
  let hybrid : ι × κ → ℝ := fun z => p z.1 * q' z.2
  have hfirst :
      totalVariation (fun z : ι × κ => p z.1 * p' z.2) hybrid =
        (∑ i, |p i|) * totalVariation p' q' := by
    rw [totalVariation, totalVariation]
    have hsum :
        (∑ z : ι × κ, |p z.1 * p' z.2 - hybrid z|) =
          (∑ i, |p i|) * ∑ k, |p' k - q' k| := by
      rw [Fintype.sum_prod_type]
      simp_rw [hybrid, ← mul_sub, abs_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
    rw [hsum]
    ring
  have hsecond :
      totalVariation hybrid (fun z : ι × κ => q z.1 * q' z.2) =
        (∑ k, |q' k|) * totalVariation p q := by
    rw [totalVariation, totalVariation]
    have hsum :
        (∑ z : ι × κ, |hybrid z - q z.1 * q' z.2|) =
          (∑ k, |q' k|) * ∑ i, |p i - q i| := by
      rw [Fintype.sum_prod_type]
      simp_rw [hybrid, ← sub_mul, abs_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    rw [hsum]
    ring
  calc
    totalVariation (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) ≤
        totalVariation (fun z : ι × κ => p z.1 * p' z.2) hybrid +
          totalVariation hybrid (fun z => q z.1 * q' z.2) :=
      total_variation_triangle _ _ _
    _ = (∑ i, |p i|) * totalVariation p' q' +
        (∑ k, |q' k|) * totalVariation p q := by rw [hfirst, hsecond]
    _ ≤ totalVariation p' q' + totalVariation p q :=
      add_le_add
        (mul_le_of_le_one_left (total_variation_nonneg p' q') hp)
        (mul_le_of_le_one_left (total_variation_nonneg p q) hq')
    _ = totalVariation p q + totalVariation p' q' := add_comm _ _

/- A point mass and the law `(1 / pi, 1 - 1 / pi)` on `Bool` have total variation
`1 - 1 / pi`. Their self-products have total variation `1 - 1 / pi ^ 2`, so product
subadditivity is genuinely strict: `1 - 1 / pi ^ 2 < 2 - 2 / pi`. -/
theorem total_variation_product_strict :
    totalVariation
        (fun z : Bool × Bool =>
          (if z.1 then (1 : ℝ) else 0) * (if z.2 then (1 : ℝ) else 0))
        (fun z =>
          (if z.1 then 1 / Real.pi else 1 - 1 / Real.pi) *
            (if z.2 then 1 / Real.pi else 1 - 1 / Real.pi)) <
      totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then 1 / Real.pi else 1 - 1 / Real.pi) +
        totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then 1 / Real.pi else 1 - 1 / Real.pi) := by
  let c : ℝ := 1 / Real.pi
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos zero_lt_one Real.pi_pos
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact (div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hone_sub_c : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
  have hmarginal :
      totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then c else 1 - c) = 1 - c := by
    rw [totalVariation, Fintype.sum_bool]
    simp only [eq_self, ↓reduceIte, Bool.false_eq_true]
    change (1 / 2 : ℝ) * (|1 - c| + |0 - (1 - c)|) = 1 - c
    rw [abs_of_nonneg hone_sub_c, abs_of_nonpos (by linarith)]
    ring
  have hproduct :
      totalVariation
          (fun z : Bool × Bool =>
            (if z.1 then (1 : ℝ) else 0) * (if z.2 then (1 : ℝ) else 0))
          (fun z =>
            (if z.1 then c else 1 - c) * (if z.2 then c else 1 - c)) =
        1 - c ^ 2 := by
    rw [totalVariation, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [eq_self, ↓reduceIte, Bool.false_eq_true, zero_mul, one_mul,
      Fintype.sum_bool]
    change (1 / 2 : ℝ) *
      ((|1 - c * c| + |0 - c * (1 - c)|) +
        (|0 - (1 - c) * c| + |0 - (1 - c) * (1 - c)|)) = 1 - c ^ 2
    rw [abs_of_nonneg (by
        have : 0 < (1 - c) * (1 + c) := mul_pos (sub_pos.mpr hc_lt_one) (by linarith)
        nlinarith),
      abs_of_nonpos (sub_nonpos.mpr (mul_nonneg hc_pos.le hone_sub_c)),
      abs_of_nonpos (sub_nonpos.mpr (mul_nonneg hone_sub_c hc_pos.le)),
      abs_of_nonpos (sub_nonpos.mpr (mul_nonneg hone_sub_c hone_sub_c))]
    ring
  change
    totalVariation
        (fun z : Bool × Bool =>
          (if z.1 then (1 : ℝ) else 0) * (if z.2 then (1 : ℝ) else 0))
        (fun z => (if z.1 then c else 1 - c) * (if z.2 then c else 1 - c)) <
      totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then c else 1 - c) +
        totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then c else 1 - c)
  rw [hproduct, hmarginal]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hc_lt_one)]

/- Neither reflexivity nor simplification proves product subadditivity. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι → ℝ) (p' q' : κ → ℝ)
    (hp : (∑ i, |p i|) ≤ 1)
    (hq' : (∑ k, |q' k|) ≤ 1) :
    totalVariation (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) ≤
      totalVariation p q + totalVariation p' q' := by
  fail_if_success rfl
  fail_if_success simp
  exact total_variation_product_subadditive p q p' q' hp hq'

/- Neither reflexivity nor simplification proves strictness of the concrete product example. -/
example :
    totalVariation
        (fun z : Bool × Bool =>
          (if z.1 then (1 : ℝ) else 0) * (if z.2 then (1 : ℝ) else 0))
        (fun z =>
          (if z.1 then 1 / Real.pi else 1 - 1 / Real.pi) *
            (if z.2 then 1 / Real.pi else 1 - 1 / Real.pi)) <
      totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then 1 / Real.pi else 1 - 1 / Real.pi) +
        totalVariation (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun b => if b then 1 / Real.pi else 1 - 1 / Real.pi) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact total_variation_product_strict

#print axioms total_variation_product_subadditive
#print axioms total_variation_product_strict

end D5.S3.TotalVariation.ProductSubadditive
