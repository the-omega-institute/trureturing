/- GID: D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global optimality is equivalent to boundary layer thresholds at a fixed positive price. -/

import D5.S3.Arith.GoldenResourceObjectiveFactorization

/- Library-search audit trail (2026-09-06):
   1. D5 searches for IsGoldenResourceOptimal, golden_resource_optimal_iff_layer_thresholds,
      golden_resource_strict_improvement, and goldenResourceObjective found no public criterion
      or strict improvement theorem. GoldenLocalThreshold supplies the public local sufficiency
      theorem, and GoldenResourceObjectiveFactorization supplies the public sum_on theorem;
      both are reused. The adjacent local difference in GoldenLocalThreshold is private,
      so it cannot be imported through a public declaration API.
   2. Pinned Mathlib v4.33.0 searches for goldenResource, goldenLayer, colossally, superabundant,
      factorization_mul, factorization_div, and primeFactors_mul found no specialized criterion.
      Nat.factorization_mul, Nat.Prime.factorization, Nat.primeFactors_mul, Real.log_div,
      Finset.sum_sub_distrib, and Finset.sum_eq_single supply the algebraic components below.
   3. Third-party Lean ecosystem search via Tavily/NyxID for Lean theorem prover,
      goldenResourceObjective, goldenLayerMarginal, and colossally abundant local threshold
      optimality returned Lean project/documentation pages, with no matching formal theorem.
      A second query, colossally abundant Lean formalization, returned ordinary mathematical
      descriptions (Wikipedia, MathWorld, Math StackExchange) and generic Lean material;
      no matching Lean theorem was found in these returned results.
   4. The new step constructs a strictly better integer by multiplying by one prime.

   Escape-witness preregistration v2, recorded before implementation in the attempt artifact:
   golden_resource_strict_improvement_of_marginal_gt has hn : 1 <= n in addition to the brief's
   assumptions. This is essential: at n = 0, n * p = n. The public criterion already has hn.
   The witness is consumed by the necessary upper threshold, via optimality at m = n * p.
   This is an analytic inequality for arbitrary integers and prices, not finite computation.
   Companion direction: the public iff consumes the strict-improvement witness. -/

namespace D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization

noncomputable section

/-- Global optimality among positive integers at a fixed price. -/
def IsGoldenResourceOptimal (lambda : ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → goldenResourceObjective lambda m ≤ goldenResourceObjective lambda n

private theorem local_step {p : ℕ} (hp : p.Prime) (lambda : ℝ) (a : ℕ) :
    goldenPrimeLocalObjective lambda p (a + 1) - goldenPrimeLocalObjective lambda p a =
      (goldenLayerMarginal p (a + 1) - lambda) * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hiPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hiLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hiPos.le hiLt (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hiPos.le hiLt (by omega))
  unfold goldenPrimeLocalObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr hiLt).ne',
    Real.log_div ha.ne' (sub_pos.mpr hiLt).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp [hpLog.ne']
  ring

private theorem resource_mul_prime_diff (lambda : ℝ) {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) :
    goldenResourceObjective lambda (n * p) - goldenResourceObjective lambda n =
      (goldenLayerMarginal p (n.factorization p + 1) - lambda) * Real.log p := by
  have hn0 : n ≠ 0 := by omega
  have hnp : 1 ≤ n * p := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hn0 hp.ne_zero)
  let s := insert p n.primeFactors
  have hsub : (n * p).primeFactors ⊆ s := by
    rw [Nat.primeFactors_mul hn0 hp.ne_zero, hp.primeFactors]
    exact union_subset (subset_insert _ _) (singleton_subset_iff.mpr (mem_insert_self _ _))
  rw [golden_resource_objective_sum_on lambda hnp s hsub,
    golden_resource_objective_sum_on lambda hn s (subset_insert _ _), ← sum_sub_distrib]
  rw [sum_eq_single p]
  · simpa only [Nat.factorization_mul hn0 hp.ne_zero, Finsupp.add_apply,
      hp.factorization, Finsupp.single_eq_same] using local_step hp lambda (n.factorization p)
  · intro q _ hqp
    simp [Nat.factorization_mul hn0 hp.ne_zero, hp.factorization, hqp, Ne.symm hqp]
  · intro h
    exact (h (mem_insert_self _ _)).elim

/-- Taking an unadopted layer above the price strictly improves the global objective. -/
theorem golden_resource_strict_improvement_of_marginal_gt {lambda : ℝ}
    (_hlambda : 0 < lambda) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hgain : lambda < goldenLayerMarginal p (n.factorization p + 1)) :
    goldenResourceObjective lambda n < goldenResourceObjective lambda (n * p) := by
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpos := mul_pos (sub_pos.mpr hgain) hpLog
  rw [← resource_mul_prime_diff lambda hn hp] at hpos
  exact sub_pos.mp hpos

/-- Boundary layer thresholds at a common positive price characterize global optimality. -/
theorem golden_resource_optimal_iff_layer_thresholds
    {lambda : ℝ} (hlambda : 0 < lambda) {n : ℕ} (hn : 1 ≤ n) :
    IsGoldenResourceOptimal lambda n ↔
      (∀ p : ℕ, p.Prime → goldenLayerMarginal p (n.factorization p + 1) ≤ lambda) ∧
      (∀ p : ℕ, p.Prime → p ∣ n → lambda ≤ goldenLayerMarginal p (n.factorization p)) := by
  constructor
  · intro hopt
    constructor
    · intro p hp
      by_contra h
      have hgain := golden_resource_strict_improvement_of_marginal_gt hlambda hn hp
        (lt_of_not_ge h)
      exact (not_lt_of_ge (hopt (n * p)
        (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hp.ne_zero)))) hgain
    · intro p hp hpn
      by_contra h
      have hdiv : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
      have hfact : (n / p).factorization p + 1 = n.factorization p := by
        have heq := congrArg (fun f : ℕ →₀ ℕ => f p)
          (Nat.factorization_mul (show n / p ≠ 0 by omega) hp.ne_zero)
        rw [Nat.div_mul_cancel hpn] at heq
        simpa [hp.factorization] using heq.symm
      have hdiff := resource_mul_prime_diff lambda hdiv hp
      rw [Nat.div_mul_cancel hpn, hfact] at hdiff
      have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge h)) hpLog
      have hcomp := hopt (n / p) hdiv
      linarith
  · rintro ⟨hupper, hlower⟩ m hm
    let s := n.primeFactors ∪ m.primeFactors
    rw [golden_resource_objective_sum_on lambda hm s subset_union_right,
      golden_resource_objective_sum_on lambda hn s subset_union_left]
    apply sum_le_sum
    intro p hp
    have hprime : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    apply golden_prime_local_objective_maximal_of_threshold hprime lambda (hupper p hprime)
    by_cases hpn : p ∣ n
    · exact Or.inr (hlower p hprime hpn)
    · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hpn)

end

end D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
