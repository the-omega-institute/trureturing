/- GID: D5/S3/TotalVariation/BhattacharyyaProduct
   generality: G
   mirror-B: D5/B/S3/TotalVariation/BhattacharyyaProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove Bhattacharyya product multiplicativity and check Renyi half-order additivity. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `Bhattacharyya`, `Hellinger affinity`,
     `Real.sqrt_mul`, `Fintype.sum_prod_type`, `Finset.sum_mul_sum`, and `Real.log_mul`.
   * No Bhattacharyya coefficient or product-multiplicativity theorem was found. The reusable
     lemmas are the asymmetric `Real.sqrt_mul`, the product-type sum identity, the finite
     sum-product factorization, and logarithm additivity under two nonzero hypotheses.
   * A repository grep below `D5` found the four existing Bhattacharyya declarations
     `bhattacharyya_self`, `bhattacharyya_eq_zero_of_mul_eq_zero`, `bhattacharyya_le_one`, and
     `bhattacharyya_channel_le`, with no product or multiplicativity statement.
-/

import D5.S3.RenyiDivergence.ProductAdditivity

namespace D5.S3.TotalVariation.Bhattacharyya

/-- Bhattacharyya affinity is multiplicative on product mass functions when the first marginal
radicands are nonnegative. No normalization or sign condition on the second marginal is needed. -/
theorem bhattacharyya_product_multiplicative
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι -> Real) (p' q' : κ -> Real)
    (hpq : forall i, 0 <= p i * q i) :
    bhattacharyya (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) =
      bhattacharyya p q * bhattacharyya p' q' := by
  fail_if_success rfl
  fail_if_success simp
  classical
  rw [bhattacharyya, bhattacharyya, bhattacharyya, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, Real.sqrt ((p i * p' j) * (q i * q' j))) =
        ∑ i, ∑ j, Real.sqrt (p i * q i) * Real.sqrt (p' j * q' j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show (p i * p' j) * (q i * q' j) =
          (p i * q i) * (p' j * q' j) by ring, Real.sqrt_mul (hpq i)]
    _ = (∑ i, Real.sqrt (p i * q i)) *
        ∑ j, Real.sqrt (p' j * q' j) := by
      rw [Finset.sum_mul_sum]

/- On the Bool functions with marginal radicands `(1, 36)` and `(1, 400)`, the two marginal
affinities are `7` and `21`; the joint affinity and their product both compute to `147`. -/
example :
    bhattacharyya
        (fun z : Bool × Bool =>
          (if z.1 then (4 : Real) else 1) * (if z.2 then (16 : Real) else 1))
        (fun z : Bool × Bool =>
          (if z.1 then (9 : Real) else 1) * (if z.2 then (25 : Real) else 1)) =
      bhattacharyya
          (fun b : Bool => if b then (4 : Real) else 1)
          (fun b : Bool => if b then (9 : Real) else 1) *
        bhattacharyya
          (fun b : Bool => if b then (16 : Real) else 1)
          (fun b : Bool => if b then (25 : Real) else 1) := by
  fail_if_success rfl
  simp only [mul_ite, ite_mul, one_mul, mul_one]
  fail_if_success simp
  norm_num [bhattacharyya, Fintype.sum_prod_type, Fintype.sum_bool]

#print axioms bhattacharyya_product_multiplicative

end D5.S3.TotalVariation.Bhattacharyya

namespace D5.S3.RenyiDivergence

open D5.S3.TotalVariation.Bhattacharyya

/-- The half-order specialization of product additivity, checked independently through
Bhattacharyya multiplicativity and through the frozen general-order theorem. -/
theorem renyi_divergence_product_additive_one_half_consistency
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ι -> Real) (p' q' : κ -> Real)
    (hp : forall i, 0 <= p i) (hq : forall i, 0 <= q i)
    (hp' : forall j, 0 <= p' j) (hq' : forall j, 0 <= q' j)
    (hsum : (∑ i, (p i) ^ (1 / 2 : Real) *
      (q i) ^ (1 - (1 / 2 : Real))) ≠ 0)
    (hsum' : (∑ j, (p' j) ^ (1 / 2 : Real) *
      (q' j) ^ (1 - (1 / 2 : Real))) ≠ 0) :
    (renyiDivergence (1 / 2) (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) =
      renyiDivergence (1 / 2) p q + renyiDivergence (1 / 2) p' q') ∧
    (renyiDivergence (1 / 2) (fun z : ι × κ => p z.1 * p' z.2)
        (fun z => q z.1 * q' z.2) =
      renyiDivergence (1 / 2) p q + renyiDivergence (1 / 2) p' q') := by
  constructor
  · norm_num
    simp only [one_div]
    fail_if_success rfl
    fail_if_success simp
    rw [← one_div]
    have hsum_eq :
        (∑ i, (p i) ^ (1 / 2 : Real) *
          (q i) ^ (1 - (1 / 2 : Real))) = bhattacharyya p q := by
      rw [bhattacharyya]
      apply Finset.sum_congr rfl
      intro i _
      rw [show 1 - (1 / 2 : Real) = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (hp i)]
    have hsum_eq' :
        (∑ j, (p' j) ^ (1 / 2 : Real) *
          (q' j) ^ (1 - (1 / 2 : Real))) = bhattacharyya p' q' := by
      rw [bhattacharyya]
      apply Finset.sum_congr rfl
      intro j _
      rw [show 1 - (1 / 2 : Real) = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (hp' j)]
    have hbc : bhattacharyya p q ≠ 0 := fun hzero => hsum (hsum_eq.trans hzero)
    have hbc' : bhattacharyya p' q' ≠ 0 := fun hzero => hsum' (hsum_eq'.trans hzero)
    rw [renyi_divergence_one_half
        (fun z : ι × κ => p z.1 * p' z.2)
        (fun z : ι × κ => q z.1 * q' z.2)
        (fun z : ι × κ => mul_nonneg (hp z.1) (hp' z.2)),
      renyi_divergence_one_half p q hp,
      renyi_divergence_one_half p' q' hp',
      bhattacharyya_product_multiplicative p q p' q'
        (fun i => mul_nonneg (hp i) (hq i)),
      Real.log_mul hbc hbc']
    ring
  · norm_num
    simp only [one_div]
    fail_if_success rfl
    fail_if_success simp
    rw [← one_div]
    exact renyi_divergence_product_additive (1 / 2) p q p' q'
      hp hq hp' hq' hsum hsum'

#print axioms renyi_divergence_product_additive_one_half_consistency

end D5.S3.RenyiDivergence
