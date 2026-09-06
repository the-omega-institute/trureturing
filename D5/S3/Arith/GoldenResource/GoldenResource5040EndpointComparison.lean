/- GID: D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single prime layer determines the two adjacent objective comparisons at 5040. -/

import D5.S3.Arith.GoldenResource5040PriceInterval

/- Library-search audit trail (2026-09-06):
   * D5 searches for `goldenResourceObjective`, `goldenLayerMarginal`, `single_layer`,
     `2520`, and `55440` found `golden_resource_objective_sum_on` and the frozen strict
     price-interval sufficiency theorem, but no public integer single-layer delta or endpoint
     comparison. The local difference identities in GoldenLocalThreshold and the price-interval
     module are private. The public sum-on theorem is applied directly below.
   * Pinned Mathlib v4.33.0 searches for the two objective names, `colossally`, `superabundant`,
     and objective/sigma combinations found no specialized theorem. Searches for
     `factorization_mul`, `primeFactors_mul`, and finite-sum cancellation found
     `Nat.factorization_mul`, `Nat.Prime.factorization`, `Nat.primeFactors_mul`, and
     `Finset.sum_eq_single`; these are applied directly with Real.log_div and Real.log_pos.
   * Third-party Lean ecosystem searches via NyxID/Tavily for "Lean theorem
     goldenResourceObjective goldenLayerMarginal single layer delta" and "Lean formalization
     colossally abundant 5040 divisor sum logarithm prime increment" returned generic Lean
     tutorials and ordinary number-theory references, but no matching Lean declaration.
   * The upper endpoint is marginal (2,4), not (2,5): removing the last 2 reverses the
     increment from exponent 3 to exponent 4. The single-layer theorem requires positive n.
   * Admission: escape-witness; computational content: none. The general single-layer delta
     connects integer multiplication to the local marginal by isolating the changed prime in
     a common finite support. The endpoint comparison consumes this delta on its live path.
     Companion dependency: endpoint comparison -> single-layer delta. -/

namespace D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison

open Finset
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResourceOptimalInteger

noncomputable section

/-- Multiplication by one prime adds exactly its next layer's net marginal contribution. -/
theorem golden_resource_objective_single_layer_delta (lambda : ℝ) {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) :
    goldenResourceObjective lambda (n * p) - goldenResourceObjective lambda n =
      (goldenLayerMarginal p (n.factorization p + 1) - lambda) * Real.log p := by
  have hn0 : n ≠ 0 := by omega
  let s := insert p n.primeFactors
  have hsupport : (n * p).primeFactors ⊆ s := by
    rw [Nat.primeFactors_mul hn0 hp.ne_zero, hp.primeFactors]
    exact union_subset (subset_insert _ _) (singleton_subset_iff.mpr (mem_insert_self _ _))
  rw [golden_resource_objective_sum_on lambda (by nlinarith [hp.pos]) s hsupport,
    golden_resource_objective_sum_on lambda hn s (subset_insert _ _), ← sum_sub_distrib]
  rw [sum_eq_single p]
  · have hexp : (n * p).factorization p = n.factorization p + 1 := by
      simp [Nat.factorization_mul hn0 hp.ne_zero, hp.factorization]
    rw [hexp]
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
    have hpInvLt : (p : ℝ)⁻¹ < 1 :=
      (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
    have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1) :=
      sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
    have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1 + 1) :=
      sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
    unfold goldenPrimeLocalObjective goldenLayerMarginal
    rw [Real.log_div hb.ne' (sub_pos.mpr hpInvLt).ne',
      Real.log_div ha.ne' (sub_pos.mpr hpInvLt).ne', Real.log_div hb.ne' ha.ne']
    push_cast
    field_simp [hpLog.ne']
    ring
  · intro q _ hqp
    have hexp : (n * p).factorization q = n.factorization q := by
      simp [Nat.factorization_mul hn0 hp.ne_zero, hp.factorization, Ne.symm hqp]
    rw [hexp, sub_self]
  · intro hpnot
    exact (hpnot (mem_insert_self _ _)).elim

private theorem adjacent_deltas (lambda : ℝ) :
    goldenResourceObjective lambda 5040 - goldenResourceObjective lambda 2520 =
        (Real.log (31 / 30) / Real.log 2 - lambda) * Real.log 2 ∧
      goldenResourceObjective lambda 55440 - goldenResourceObjective lambda 5040 =
        (Real.log (12 / 11) / Real.log 11 - lambda) * Real.log 11 := by
  have h2 : (2520 : ℕ).factorization 2 = 3 := by
    have hpow : (8 : ℕ).factorization = Finsupp.single 2 3 :=
      (by norm_num : Nat.Prime 2).factorization_pow (k := 3)
    rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [hpow,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 315)]
  have h11 : (5040 : ℕ).factorization 11 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have hremove := golden_resource_objective_single_layer_delta lambda
    (by norm_num : 1 ≤ (2520 : ℕ)) (by norm_num : Nat.Prime 2)
  have hadd := golden_resource_objective_single_layer_delta lambda
    (by norm_num : 1 ≤ (5040 : ℕ)) (by norm_num : Nat.Prime 11)
  have hupper : goldenLayerMarginal 2 4 = Real.log (31 / 30) / Real.log 2 := by
    norm_num [goldenLayerMarginal]
  have hlower : goldenLayerMarginal 11 1 = Real.log (12 / 11) / Real.log 11 := by
    norm_num [goldenLayerMarginal]
  constructor
  · simpa only [h2, hupper, Nat.cast_ofNat, show 2520 * 2 = 5040 from rfl] using hremove
  · simpa only [h11, hlower, Nat.cast_ofNat, show 5040 * 11 = 55440 from rfl] using hadd

/-- At or beyond either price endpoint, the corresponding adjacent integer is at least as good. -/
theorem golden_resource_5040_endpoint_comparisons (lambda : ℝ) :
    (Real.log (31 / 30) / Real.log 2 ≤ lambda →
      goldenResourceObjective lambda 5040 ≤ goldenResourceObjective lambda 2520) ∧
    (lambda ≤ Real.log (12 / 11) / Real.log 11 →
      goldenResourceObjective lambda 5040 ≤ goldenResourceObjective lambda 55440) := by
  obtain ⟨hremove, hadd⟩ := adjacent_deltas lambda
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h11 : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · intro hprice
    apply sub_nonpos.mp
    rw [hremove]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hprice) h2.le
  · intro hprice
    apply sub_nonneg.mp
    rw [hadd]
    exact mul_nonneg (sub_nonneg.mpr hprice) h11.le

end

#print axioms golden_resource_objective_single_layer_delta
#print axioms golden_resource_5040_endpoint_comparisons

end D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
