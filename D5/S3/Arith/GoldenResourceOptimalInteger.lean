/- GID: D5/S3/Arith/GoldenResourceOptimalInteger
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResourceOptimalInteger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:3b3e9c081bebcc4bed7568427decd41d64802ba7e03c60402e44a5454d643a19
   digest: The unique positive integer maximizing divisor benefit at cost 1/25 is 5040. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace D5.S3.Arith.GoldenResourceOptimalInteger

open Finset

/-- Divisor free energy minus the logarithmic resource cost. -/
noncomputable def goldenResourceObjective (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.log (∑ d ∈ n.divisors, (d : ℝ)⁻¹) - lambda * Real.log n

/-- Marginal benefit per logarithmic unit for the positive prime layer `a`. -/
noncomputable def goldenLayerMarginal (p a : ℕ) : ℝ :=
  Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) / Real.log p

private noncomputable def layerRatio (p a : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)

private theorem inverse_bounds {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ < 1 := by
  have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact ⟨inv_pos.mpr (by linarith), (inv_lt_one₀ (by linarith)).mpr h⟩

private theorem ratio_pos {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < layerRatio p a := by
  obtain ⟨h0, h1⟩ := inverse_bounds hp
  exact div_pos (sub_pos.mpr (pow_lt_one₀ h0.le h1 (by omega)))
    (sub_pos.mpr (pow_lt_one₀ h0.le h1 (by omega)))

private theorem ratio_strict_decrease {p a b : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hab : a < b) : layerRatio p b < layerRatio p a := by
  obtain ⟨h0, h1⟩ := inverse_bounds hp
  have hpa : (p : ℝ)⁻¹ ^ a < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have hpb : (p : ℝ)⁻¹ ^ b < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have hab' : (p : ℝ)⁻¹ ^ b < (p : ℝ)⁻¹ ^ a :=
    pow_lt_pow_right_of_lt_one₀ h0 h1 hab
  unfold layerRatio
  apply (div_lt_div_iff₀ (sub_pos.mpr hpb) (sub_pos.mpr hpa)).mpr
  simp only [pow_succ]
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hab')]

/-- Every prime's marginal benefit strictly decreases along its positive layers. -/
theorem golden_layer_strict_decrease {p a b : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hab : a < b) :
    goldenLayerMarginal p b < goldenLayerMarginal p a := by
  apply (div_lt_div_iff_of_pos_right (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr
  exact Real.log_lt_log (ratio_pos hp (by omega)) (ratio_strict_decrease hp ha hab)

private theorem threshold_lower {p a : ℕ} (hp : p.Prime)
    (h : (p : ℝ) < layerRatio p a ^ 25) :
    (1 / 25 : ℝ) < goldenLayerMarginal p a := by
  have hl := Real.log_lt_log (by exact_mod_cast hp.pos) h
  rw [Real.log_pow] at hl
  unfold goldenLayerMarginal
  apply (lt_div_iff₀ (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr
  change 1 / 25 * Real.log p < Real.log (layerRatio p a)
  norm_num at hl
  linarith

private theorem threshold_upper {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : layerRatio p a ^ 25 < (p : ℝ)) :
    goldenLayerMarginal p a < (1 / 25 : ℝ) := by
  have hl := Real.log_lt_log (pow_pos (ratio_pos hp ha) 25) h
  rw [Real.log_pow] at hl
  unfold goldenLayerMarginal
  apply (div_lt_iff₀ (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr
  change Real.log (layerRatio p a) < 1 / 25 * Real.log p
  norm_num at hl
  linarith

private theorem thresholds :
    ((1 / 25 : ℝ) < goldenLayerMarginal 2 4 ∧ goldenLayerMarginal 2 5 < 1 / 25) ∧
    ((1 / 25 : ℝ) < goldenLayerMarginal 3 2 ∧ goldenLayerMarginal 3 3 < 1 / 25) ∧
    ((1 / 25 : ℝ) < goldenLayerMarginal 5 1 ∧ goldenLayerMarginal 5 2 < 1 / 25) ∧
    ((1 / 25 : ℝ) < goldenLayerMarginal 7 1 ∧ goldenLayerMarginal 7 2 < 1 / 25) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals first
    | apply threshold_lower (by norm_num)
    | apply threshold_upper (by norm_num) (by norm_num)
  all_goals norm_num [layerRatio]

private theorem first_ratio {p : ℕ} (hp : p.Prime) :
    layerRatio p 1 = 1 + (p : ℝ)⁻¹ := by
  obtain ⟨h0, h1⟩ := inverse_bounds hp
  unfold layerRatio
  norm_num
  apply (div_eq_iff (ne_of_gt (sub_pos.mpr h1))).mpr
  ring

private theorem tail_exclusion {p a : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : 1 ≤ a) : goldenLayerMarginal p a < (1 / 25 : ℝ) := by
  have hr : layerRatio p 1 ≤ (12 / 11 : ℝ) := by
    rw [first_ratio hp]
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 11)
      (by exact_mod_cast hp11 : (11 : ℝ) ≤ p)
    norm_num at hi
    linarith
  have h1 : goldenLayerMarginal p 1 < (1 / 25 : ℝ) := by
    apply threshold_upper hp (by omega)
    calc
      layerRatio p 1 ^ 25 ≤ (12 / 11 : ℝ) ^ 25 :=
        pow_le_pow_left₀ (ratio_pos hp (by omega)).le hr 25
      _ < 11 := by norm_num
      _ ≤ (p : ℝ) := by exact_mod_cast hp11
  rcases eq_or_lt_of_le ha with rfl | hlt
  · exact h1
  · exact (golden_layer_strict_decrease hp (by omega) hlt).trans h1

private noncomputable def localObjective (p a : ℕ) : ℝ :=
  Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹)) -
    (1 / 25 : ℝ) * a * Real.log p

private theorem local_zero (p : ℕ) : localObjective p 0 = 0 := by
  by_cases hp : (p : ℝ)⁻¹ = 1 <;> simp [localObjective, hp]

private theorem local_diff {p : ℕ} (hp : p.Prime) (a : ℕ) :
    localObjective p (a + 1) - localObjective p a =
      (goldenLayerMarginal p (a + 1) - 1 / 25) * Real.log p := by
  obtain ⟨h0, h1⟩ := inverse_bounds hp
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ h0.le h1 (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ h0.le h1 (by omega))
  have hl : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  unfold localObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr h1).ne',
    Real.log_div ha.ne' (sub_pos.mpr h1).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp
  ring

private def optimalExponent (p : ℕ) : ℕ :=
  if p = 2 then 4 else if p = 3 then 2 else if p = 5 then 1 else if p = 7 then 1 else 0

private theorem exponent_thresholds {p : ℕ} (hp : p.Prime) :
    (0 < optimalExponent p → (1 / 25 : ℝ) < goldenLayerMarginal p (optimalExponent p)) ∧
      goldenLayerMarginal p (optimalExponent p + 1) < (1 / 25 : ℝ) := by
  by_cases h2 : p = 2
  · subst p
    simpa [optimalExponent] using thresholds.1
  by_cases h3 : p = 3
  · subst p
    simpa [optimalExponent] using thresholds.2.1
  by_cases h5 : p = 5
  · subst p
    simpa [optimalExponent] using thresholds.2.2.1
  by_cases h7 : p = 7
  · subst p
    simpa [optimalExponent] using thresholds.2.2.2
  have hp11 : 11 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at *
  simpa [optimalExponent, h2, h3, h5, h7] using
    And.intro (by simp : 0 < (0 : ℕ) → (1 / 25 : ℝ) < goldenLayerMarginal p 0)
      (tail_exclusion hp hp11 (by omega : 1 ≤ 1))

private theorem local_unique_max {p : ℕ} (hp : p.Prime) (a : ℕ) :
    localObjective p a ≤ localObjective p (optimalExponent p) ∧
      (localObjective p a = localObjective p (optimalExponent p) ↔ a = optimalExponent p) := by
  obtain ⟨hup, hdown⟩ := exponent_thresholds hp
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have up : StrictMonoOn (localObjective p) (Set.Iic (optimalExponent p)) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro k hk
    have hgain : (1 / 25 : ℝ) < goldenLayerMarginal p (k + 1) := by
      rcases eq_or_lt_of_le (show k + 1 ≤ optimalExponent p by omega) with heq | hlt
      · rw [heq]
        exact hup (by omega)
      · exact (hup (by omega)).trans (golden_layer_strict_decrease hp (by omega) hlt)
    have hh := mul_pos (sub_pos.mpr hgain) hl
    rw [← local_diff hp k] at hh
    exact sub_pos.mp hh
  have down : StrictAntiOn (localObjective p) (Set.Ici (optimalExponent p)) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Ici
    intro k _ hk _
    have hgain : goldenLayerMarginal p (k + 1) < (1 / 25 : ℝ) := by
      rcases eq_or_lt_of_le (show optimalExponent p + 1 ≤ k + 1 by exact Nat.succ_le_succ hk)
        with heq | hlt
      · rw [← heq]
        exact hdown
      · exact (golden_layer_strict_decrease hp (by omega) hlt).trans hdown
    have hh := mul_neg_of_neg_of_pos (sub_neg.mpr hgain) hl
    rw [← local_diff hp k] at hh
    exact sub_neg.mp hh
  rcases lt_trichotomy a (optimalExponent p) with h | rfl | h
  · have hs := up h.le (by simp) h
    exact ⟨hs.le, ⟨fun heq => (hs.ne heq).elim, fun heq => by rw [heq]⟩⟩
  · exact ⟨le_rfl, iff_of_true rfl rfl⟩
  · have hs := down (by simp) h.le h
    exact ⟨hs.le, ⟨fun heq => (hs.ne heq).elim, fun heq => by rw [heq]⟩⟩

private theorem reciprocal_divisor_sum {n : ℕ} (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, (d : ℝ)⁻¹) = (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, ← Nat.sum_div_divisors n
    (fun d => (d : ℝ)), sum_div]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

/-- The resource objective agrees with the divisor-sum ratio expression. -/
theorem golden_resource_sigma_identity (lambda : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective lambda n =
      Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) - lambda * Real.log n := by
  rw [goldenResourceObjective, reciprocal_divisor_sum hn]

private theorem local_sigma {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Real.log (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) -
      (26 / 25 : ℝ) * a * Real.log p = localObjective p a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hpow : (p : ℝ) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hs : 0 < (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
  have hg : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p : ℝ) ^ a =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    rw [geom_sum_eq hp1]
    simp only [inv_pow, pow_succ]
    field_simp
  unfold localObjective
  rw [← hg, Real.log_div hs.ne' hpow, Real.log_pow]
  ring

private theorem objective_factorization {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective (1 / 25) n =
      ∑ p ∈ n.primeFactors, localObjective p (n.factorization p) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hs : (ArithmeticFunction.sigma 1 n : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 n hn0).ne'
  rw [golden_resource_sigma_identity _ hn, Real.log_div hs hnR]
  rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0,
    Nat.cast_finsuppProd, Finsupp.prod, Nat.support_factorization]
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne')]
  rw [Real.log_nat_eq_sum_factorization n]
  simp only [Finsupp.sum, Nat.support_factorization,
    ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [← local_sigma (Nat.prime_of_mem_primeFactors hp)]
  ring

private theorem factorization_5040 :
    (5040 : ℕ).factorization =
      Finsupp.single 2 4 + Finsupp.single 3 2 + Finsupp.single 5 1 + Finsupp.single 7 1 := by
  rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 2).factorization_pow,
    (by norm_num : Nat.Prime 3).factorization_pow,
    (by norm_num : Nat.Prime 5).factorization_pow,
    (by norm_num : Nat.Prime 7).factorization_pow]

private theorem optimal_exponent_eq (p : ℕ) :
    optimalExponent p = (5040 : ℕ).factorization p := by
  rw [factorization_5040]
  simp only [Finsupp.add_apply, Finsupp.single_apply, optimalExponent]
  split_ifs <;> omega

private theorem objective_sum_on {n : ℕ} (hn : 1 ≤ n) (s : Finset ℕ)
    (hsub : n.primeFactors ⊆ s) : goldenResourceObjective (1 / 25) n =
      ∑ p ∈ s, localObjective p (n.factorization p) := by
  rw [objective_factorization hn]
  apply sum_subset hsub
  intro p _ hp
  have hzero : n.factorization p = 0 := by
    simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
  rw [hzero, local_zero]

/-- At resource price `1/25`, 5040 is the unique maximum among all positive integers. -/
theorem golden_resource_unique_optimum {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective (1 / 25) n ≤ goldenResourceObjective (1 / 25) 5040 ∧
      (goldenResourceObjective (1 / 25) n = goldenResourceObjective (1 / 25) 5040 ↔
        n = 5040) := by
  let s := n.primeFactors ∪ (5040 : ℕ).primeFactors
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hsumN := objective_sum_on hn s subset_union_left
  have hsumM := objective_sum_on (by norm_num : 1 ≤ (5040 : ℕ)) s subset_union_right
  have hlocal (p : ℕ) (hp : p ∈ s) :
      localObjective p (n.factorization p) ≤ localObjective p ((5040 : ℕ).factorization p) ∧
      (localObjective p (n.factorization p) = localObjective p ((5040 : ℕ).factorization p) ↔
        n.factorization p = (5040 : ℕ).factorization p) := by
    simpa only [optimal_exponent_eq] using local_unique_max (hprime p hp) (n.factorization p)
  refine ⟨?_, ⟨?_, fun h => by rw [h]⟩⟩
  · rw [hsumN, hsumM]
    exact sum_le_sum fun p hp => (hlocal p hp).1
  · intro heq
    rw [hsumN, hsumM] at heq
    have heach := (sum_eq_sum_iff_of_le (fun p hp => (hlocal p hp).1)).mp heq
    apply Nat.factorization_inj (by omega : n ≠ 0) (by norm_num : (5040 : ℕ) ≠ 0)
    ext p
    by_cases hp : p ∈ s
    · exact (hlocal p hp).2.mp (heach p hp)
    · have hn' : p ∉ n.primeFactors := fun h => hp (mem_union_left _ h)
      have hm' : p ∉ (5040 : ℕ).primeFactors := fun h => hp (mem_union_right _ h)
      have hn0 : n.factorization p = 0 := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hn'
      have hm0 : (5040 : ℕ).factorization p = 0 := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hm'
      rw [hn0, hm0]

end D5.S3.Arith.GoldenResourceOptimalInteger
