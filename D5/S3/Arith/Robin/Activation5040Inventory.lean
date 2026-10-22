/- GID: D5/S3/Arith/Robin/Activation5040Inventory
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Activation5040Inventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none

  Actual q11 activation inventory.

  This is a standalone extension of the compiled
  D5.S3.Arith.Robin.ActualTwoPriceDefect source.  It proves the endpoint
  inventory at q11 = goldenLayerMarginal 11 1 directly.  The finite case
  split below is only a proof of the all-prime statement; the domain of every
  count remains all primes and all positive layers.

  The threshold proof architecture and rational-power/log comparison below adapt
  the PRIVATE proof in GoldenResource5040PriceInterval (pinned source
  SHA256 7ee5aad22e0c4498d7e44a75bdf9226d86194620b7a1f3683d4fa490fd053873).
  Private facts are reproved, never invoked as public declarations. Selected
  layers instead reuse the PUBLIC fixed-price unique optimum and count APIs.

  No classification/certificate wrapper is used.  The strict and weak counts
  are consumed to identify the existing strictInteger and maximalInteger.
-/

import D5.S3.Arith.Robin.ActualTwoPriceDefect
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.ActualTwoPriceDefect

open Set Filter Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenLayerMarginalDecay

/-- The lower 5040 activation price, definitionally the first 11-layer. -/
def q11 : ℝ := goldenLayerMarginal 11 1

/-- The exponents of 5040, extended to every natural prime direction. -/
def targetExponent5040 (p : ℕ) : ℕ :=
  if p = 2 then 4 else if p = 3 then 2 else if p = 5 then 1 else if p = 7 then 1 else 0

/-- At the lower endpoint exactly the first 11-layer is weakly admitted. -/
def targetExponent55440 (p : ℕ) : ℕ :=
  if p = 11 then 1 else targetExponent5040 p

private theorem q11_eq : q11 = Real.log (12 / 11) / Real.log 11 := by
  norm_num [q11, goldenLayerMarginal]

private theorem q11_pos : 0 < q11 := by
  rw [q11_eq]
  have hlog : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have hratio : 1 < (12 / 11 : ℝ) := by norm_num
  exact div_pos (Real.log_pos hratio) hlog

private theorem layer_ratio_pos_activated {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  exact div_pos (sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega)))
    (sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega)))

private theorem layer_lt_one_div_nat_activated {p a k : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hk : 0 < k)
    (hpow : ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) ^ k <
      (p : ℝ)) :
    goldenLayerMarginal p a < (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog := Real.log_lt_log (pow_pos (layer_ratio_pos_activated hp ha) k) hpow
  rw [Real.log_pow] at hlog
  unfold goldenLayerMarginal
  rw [div_lt_iff₀ hpLog]
  calc
    Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) <
        Real.log p / (k : ℝ) :=
      (lt_div_iff₀ hkR).2 (by simpa [mul_comm] using hlog)
    _ = 1 / (k : ℝ) * Real.log p := by ring

private theorem q11_lt_one_div_25 : q11 < (1 / 25 : ℝ) := by
  rw [q11_eq]
  have hlog11 : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (12 / 11 : ℝ) ^ 25 < 11 := by norm_num
  have hlog := Real.log_lt_log
    (pow_pos (by norm_num : (0 : ℝ) < 12 / 11) 25) hpow
  rw [Real.log_pow] at hlog
  apply (div_lt_iff₀ hlog11).2
  norm_num at hlog ⊢
  linarith

private theorem one_div_28_lt_q11 : (1 / 28 : ℝ) < q11 := by
  rw [q11_eq]
  have hlog11 : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (11 : ℝ) < (12 / 11 : ℝ) ^ 28 := by norm_num
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < (11 : ℝ)) hpow
  rw [Real.log_pow] at hlog
  apply (lt_div_iff₀ hlog11).2
  norm_num at hlog ⊢
  linarith

private theorem selected_next_below_q11 :
    goldenLayerMarginal 2 5 < q11 ∧
    goldenLayerMarginal 3 3 < q11 ∧
    goldenLayerMarginal 5 2 < q11 ∧
    goldenLayerMarginal 7 2 < q11 := by
  have h2 : goldenLayerMarginal 2 5 < (1 / 28 : ℝ) :=
    layer_lt_one_div_nat_activated (p := 2) (a := 5) (k := 28)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : goldenLayerMarginal 3 3 < (1 / 28 : ℝ) :=
    layer_lt_one_div_nat_activated (p := 3) (a := 3) (k := 28)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : goldenLayerMarginal 5 2 < (1 / 28 : ℝ) :=
    layer_lt_one_div_nat_activated (p := 5) (a := 2) (k := 28)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : goldenLayerMarginal 7 2 < (1 / 28 : ℝ) :=
    layer_lt_one_div_nat_activated (p := 7) (a := 2) (k := 28)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h2.trans one_div_28_lt_q11, h3.trans one_div_28_lt_q11,
    h5.trans one_div_28_lt_q11, h7.trans one_div_28_lt_q11⟩

private theorem eleven_tail_below {a : ℕ} (ha : 1 < a) :
    goldenLayerMarginal 11 a < q11 := by
  change goldenLayerMarginal 11 a < goldenLayerMarginal 11 1
  exact golden_layer_strict_decrease (by norm_num) (by norm_num) ha

private theorem prime_ge_13_tail_below {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p)
    {a : ℕ} (ha : 1 ≤ a) : goldenLayerMarginal p a < q11 := by
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h11Log : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have hp13R : (13 : ℝ) ≤ p := by exact_mod_cast hp13
  have hinv : (p : ℝ)⁻¹ ≤ (1 / 13 : ℝ) := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 13) hp13R
  have hlog : Real.log (11 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 11 ≤ p by omega))
  have hbound : (p : ℝ)⁻¹ / Real.log p ≤ (1 / 13 : ℝ) / Real.log 11 := by
    calc
      (p : ℝ)⁻¹ / Real.log p ≤ (1 / 13 : ℝ) / Real.log p :=
        div_le_div_of_nonneg_right hinv hpLog.le
      _ ≤ (1 / 13 : ℝ) / Real.log 11 :=
        div_le_div_of_nonneg_left (by norm_num) h11Log hlog
  have hlogLower : (1 / 13 : ℝ) < Real.log (12 / 11 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 12 / 11 by norm_num)
    norm_num at h ⊢
    linarith
  have hquot : (1 / 13 : ℝ) / Real.log 11 < q11 := by
    rw [q11_eq]
    exact (div_lt_div_iff_of_pos_right h11Log).2 hlogLower
  have hfirst : goldenLayerMarginal p 1 < q11 := by
    apply (golden_layer_marginal_le_inv_pow hp (by omega : 1 ≤ (1 : ℕ))).trans_lt
    simpa only [pow_one] using hbound.trans_lt hquot
  rcases eq_or_lt_of_le ha with rfl | hlt
  · exact hfirst
  · exact (golden_layer_strict_decrease hp (by omega : 1 ≤ (1 : ℕ)) hlt).trans hfirst

private theorem prime_ge_13_of_not_small {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) (h11 : p ≠ 11) :
    13 ≤ p := by
  by_contra h
  interval_cases p <;> norm_num at *

private theorem target5040_factorization (p : ℕ) :
    targetExponent5040 p = (5040 : ℕ).factorization p := by
  rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 2).factorization_pow,
    (by norm_num : Nat.Prime 3).factorization_pow,
    (by norm_num : Nat.Prime 5).factorization_pow,
    (by norm_num : Nat.Prime 7).factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply, targetExponent5040]
  split_ifs <;> omega

private theorem target55440_factorization (p : ℕ) :
    targetExponent55440 p = (55440 : ℕ).factorization p := by
  rw [show (55440 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 2).factorization_pow,
    (by norm_num : Nat.Prime 3).factorization_pow,
    (by norm_num : Nat.Prime 5).factorization_pow,
    (by norm_num : Nat.Prime 7).factorization_pow,
    (by norm_num : Nat.Prime 11).factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply, targetExponent55440,
    targetExponent5040]
  split_ifs <;> omega

private theorem target5040_zero_of_not_prime {p : ℕ} (hp : ¬ p.Prime) :
    targetExponent5040 p = 0 := by
  rw [target5040_factorization]
  exact Nat.factorization_eq_zero_of_not_prime 5040 hp

/-- Public fixed-price optimum/count reuse; no private threshold is assumed. -/
private theorem selected_above_q11 {p : ℕ} (hp : p.Prime)
    (ht : 0 < targetExponent5040 p) :
    q11 < goldenLayerMarginal p (targetExponent5040 p) := by
  obtain ⟨n, hn, hcounts, hopt, _⟩ :=
    optimal_layer_count_spec (by norm_num : (0 : ℝ) < 1 / 25)
  have hn5040 : n = 5040 :=
    (golden_resource_unique_optimum hn).2.mp
      (le_antisymm (golden_resource_unique_optimum hn).1
        (hopt 5040 (by norm_num)))
  have hc : optimalLayerCount (1 / 25) p = targetExponent5040 p := by
    rw [← hcounts p, hn5040, target5040_factorization]
  have hmem : targetExponent5040 p ∈
      {k : ℕ | 1 ≤ k ∧ p.Prime ∧ (1 / 25 : ℝ) < goldenLayerMarginal p k} := by
    rw [positive_layers_eq_count_interval (by norm_num : (0 : ℝ) < 1 / 25) hp, hc]
    exact ⟨ht, le_rfl⟩
  exact q11_lt_one_div_25.trans hmem.2.2

/-- Exact strict count at q11, for every prime direction. -/
theorem optimalLayerCount_q11 (p : ℕ) :
    optimalLayerCount q11 p = targetExponent5040 p := by
  by_cases hp : p.Prime
  · have hinterval := positive_layers_eq_count_interval q11_pos hp
    have hactive : targetExponent5040 p = 0 ∨
        q11 < goldenLayerMarginal p (targetExponent5040 p) := by
      by_cases hz : targetExponent5040 p = 0
      · exact Or.inl hz
      · exact Or.inr (selected_above_q11 hp (Nat.pos_of_ne_zero hz))
    have hnext : ¬ q11 < goldenLayerMarginal p (targetExponent5040 p + 1) := by
      by_cases h2 : p = 2
      · subst p; simpa [targetExponent5040] using (not_lt_of_ge selected_next_below_q11.1.le)
      by_cases h3 : p = 3
      · subst p; simpa [targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.1.le)
      by_cases h5 : p = 5
      · subst p; simpa [targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.2.1.le)
      by_cases h7 : p = 7
      · subst p; simpa [targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.2.2.le)
      by_cases h11 : p = 11
      · subst p; simpa [targetExponent5040, q11, goldenLayerMarginal]
      have hp13 := prime_ge_13_of_not_small hp h2 h3 h5 h7 h11
      have hbelow := prime_ge_13_tail_below hp hp13
        (a := targetExponent5040 p + 1) (by omega)
      simpa [targetExponent5040, h2, h3, h5, h7] using (not_lt_of_ge hbelow.le)
    apply Nat.le_antisymm
    · by_contra hle
      have hmem : targetExponent5040 p + 1 ∈
          Set.Icc 1 (optimalLayerCount q11 p) := by
        exact ⟨by omega, Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)⟩
      rw [← hinterval] at hmem
      exact hnext hmem.2.2
    · by_cases hz : targetExponent5040 p = 0
      · omega
      · have hmem : targetExponent5040 p ∈
            {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q11 < goldenLayerMarginal p k} :=
          ⟨Nat.one_le_iff_ne_zero.mpr hz, hp, hactive.resolve_left hz⟩
        rw [hinterval] at hmem
        exact hmem.2
  · rw [target5040_zero_of_not_prime hp]
    simp [optimalLayerCount, hp]

/-- Exact weak count at q11, including the single equality layer (11,1). -/
theorem weakLayerCount_q11 (p : ℕ) :
    weakLayerCount q11 p = targetExponent55440 p := by
  by_cases hp : p.Prime
  · have hinterval := weak_layers_eq_count_interval q11_pos hp
    have hactive : targetExponent55440 p = 0 ∨
        q11 ≤ goldenLayerMarginal p (targetExponent55440 p) := by
      by_cases h11 : p = 11
      · subst p
        right
        change q11 ≤ goldenLayerMarginal 11 1
        exact le_rfl
      have ht : targetExponent55440 p = targetExponent5040 p := by
        simp only [targetExponent55440, if_neg h11]
      rw [ht]
      by_cases hz : targetExponent5040 p = 0
      · exact Or.inl hz
      · exact Or.inr (selected_above_q11 hp (Nat.pos_of_ne_zero hz)).le
    have hnext : ¬ q11 ≤ goldenLayerMarginal p (targetExponent55440 p + 1) := by
      by_cases h11 : p = 11
      · subst p; simpa [targetExponent55440] using (not_le_of_gt (eleven_tail_below (by norm_num : 1 < 1 + 1)))
      by_cases h2 : p = 2
      · subst p; simpa [targetExponent55440, targetExponent5040] using (not_le_of_gt selected_next_below_q11.1)
      by_cases h3 : p = 3
      · subst p; simpa [targetExponent55440, targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.1)
      by_cases h5 : p = 5
      · subst p; simpa [targetExponent55440, targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.2.1)
      by_cases h7 : p = 7
      · subst p; simpa [targetExponent55440, targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.2.2)
      have hp13 := prime_ge_13_of_not_small hp h2 h3 h5 h7 h11
      have hbelow := prime_ge_13_tail_below hp hp13
        (a := targetExponent55440 p + 1) (by omega)
      simpa [targetExponent55440, targetExponent5040, h11, h2, h3, h5, h7]
        using (not_le_of_gt hbelow)
    apply Nat.le_antisymm
    · by_contra hle
      have hmem : targetExponent55440 p + 1 ∈ Set.Icc 1 (weakLayerCount q11 p) := by
        exact ⟨by omega, Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)⟩
      rw [← hinterval] at hmem
      exact hnext hmem.2.2
    · by_cases hz : targetExponent55440 p = 0
      · omega
      · have hmem : targetExponent55440 p ∈
            {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q11 ≤ goldenLayerMarginal p k} :=
          ⟨Nat.one_le_iff_ne_zero.mpr hz, hp, hactive.resolve_left hz⟩
        rw [hinterval] at hmem
        exact hmem.2
  · have h11 : p ≠ 11 := by
      rintro rfl
      exact hp (by norm_num)
    rw [targetExponent55440, if_neg h11, target5040_zero_of_not_prime hp]
    simp [weakLayerCount, hp]

/-- Strict q11 inventory is exactly the factorization of 5040. -/
theorem strictInteger_q11 : strictInteger q11 = 5040 := by
  apply Nat.factorization_inj
    (by change strictInteger q11 ≠ 0; have := strictInteger_pos q11_pos; omega)
    (by norm_num)
  ext p
  rw [strictInteger_counts q11_pos, optimalLayerCount_q11, target5040_factorization]

/-- Weak q11 inventory is exactly the factorization of 55440. -/
theorem maximalInteger_q11 : maximalInteger q11 = 55440 := by
  apply Nat.factorization_inj
    (by change maximalInteger q11 ≠ 0; have := (maximalInteger_spec q11_pos).1; omega)
    (by norm_num)
  ext p
  rw [(maximalInteger_spec q11_pos).2.1 p, weakLayerCount_q11,
    target55440_factorization]

/-- Every strict layer is identified without restricting the quantified domain. -/
theorem q11_strict_layer_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    q11 < goldenLayerMarginal p k ↔ k ≤ targetExponent5040 p := by
  have hinterval := positive_layers_eq_count_interval q11_pos hp
  have hm : (1 ≤ k ∧ p.Prime ∧ q11 < goldenLayerMarginal p k) ↔
      k ∈ Set.Icc 1 (optimalLayerCount q11 p) := by
    rw [← hinterval]
    rfl
  simpa only [Set.mem_Icc, hk, hp, true_and, optimalLayerCount_q11] using hm

/-- Every weak layer is identified without restricting the quantified domain. -/
theorem q11_weak_layer_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    q11 ≤ goldenLayerMarginal p k ↔ k ≤ targetExponent55440 p := by
  have hinterval := weak_layers_eq_count_interval q11_pos hp
  have hm : (1 ≤ k ∧ p.Prime ∧ q11 ≤ goldenLayerMarginal p k) ↔
      k ∈ Set.Icc 1 (weakLayerCount q11 p) := by
    rw [← hinterval]
    rfl
  simpa only [Set.mem_Icc, hk, hp, true_and, weakLayerCount_q11] using hm

/-- The only weak layer not already strict is the equality layer (11,1). -/
theorem q11_equality_layer_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    goldenLayerMarginal p k = q11 ↔ p = 11 ∧ k = 1 := by
  constructor
  · intro heq
    have hw : k ≤ targetExponent55440 p :=
      (q11_weak_layer_iff hp hk).mp (by rw [heq])
    have hs : ¬ k ≤ targetExponent5040 p := by
      intro h
      have hlt := (q11_strict_layer_iff hp hk).mpr h
      rw [heq] at hlt
      exact (lt_irrefl q11) hlt
    by_cases h11 : p = 11
    · subst p
      have hw' : k ≤ 1 := by simpa [targetExponent55440] using hw
      exact ⟨rfl, by omega⟩
    · have ht : targetExponent55440 p = targetExponent5040 p := by
        simp only [targetExponent55440, if_neg h11]
      exact (hs (ht ▸ hw)).elim
  · rintro ⟨rfl, rfl⟩
    rfl

end D5.S3.Arith.Robin.ActualTwoPriceDefect
