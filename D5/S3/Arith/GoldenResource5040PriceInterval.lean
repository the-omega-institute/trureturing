/- GID: D5/S3/Arith/GoldenResource5040PriceInterval
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource5040PriceInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prices strictly between the adjacent layer thresholds make 5040 uniquely optimal. -/

import D5.S3.Arith.GoldenLayerMarginalDecay
import D5.S3.Arith.GoldenResourceObjectiveFactorization

/- Library-search audit trail (2026-09-06):
   * Repository searches for `5040`, inverse optimality, price thresholds, the golden resource
     objective, and unique maxima found only
     `GoldenResourceOptimalInteger.golden_resource_unique_optimum` at the fixed price 1/25.
     The arbitrary-price factorization and local maximality declarations imported above are
     exact reusable prerequisites, but no repository declaration states this price interval.
   * Pinned Mathlib was searched for prime-layer optimality, marginal-prime comparisons,
     threshold-layer divisibility, and `5040`; no specialized declaration was found. Its generic
     logarithm order lemmas and finite-sum equality lemma are used below.
   * Three NyxID/Tavily searches of the third-party Lean ecosystem for the objective names,
     prime-layer thresholds, and formalized 5040 divisor-sum optimality found no matching Lean
     declaration. The first proxy attempt returned HTTP 422 until an explicit JSON content type
     was supplied; the corrected searches returned only unrelated Lean projects and ordinary
     number-theory literature.
   * The fixed-price module contains private factorization and local-difference lemmas. They
     cannot be imported as declarations, so the thin private bridges needed below are reproved. -/

namespace D5.S3.Arith.GoldenResource5040PriceInterval

open Finset
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResourceOptimalInteger

noncomputable section

private def targetExponent5040 (p : ℕ) : ℕ :=
  if p = 2 then 4 else if p = 3 then 2 else if p = 5 then 1 else if p = 7 then 1 else 0

private theorem layer_ratio_pos {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  exact div_pos (sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega)))
    (sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega)))

private theorem one_div_nat_lt_golden_layer_marginal {p a k : ℕ} (hp : p.Prime)
    (_ha : 1 ≤ a) (hk : 0 < k)
    (hpow : (p : ℝ) <
      ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) ^ k) :
    (1 / (k : ℝ)) < goldenLayerMarginal p a := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog := Real.log_lt_log (by exact_mod_cast hp.pos) hpow
  rw [Real.log_pow] at hlog
  unfold goldenLayerMarginal
  rw [lt_div_iff₀ hpLog]
  calc
    1 / (k : ℝ) * Real.log p = Real.log p / (k : ℝ) := by ring
    _ < Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) :=
      (div_lt_iff₀ hkR).2 (by simpa [mul_comm] using hlog)

private theorem golden_layer_marginal_lt_one_div_nat {p a k : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hk : 0 < k)
    (hpow : ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) ^ k <
      (p : ℝ)) :
    goldenLayerMarginal p a < (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog := Real.log_lt_log (pow_pos (layer_ratio_pos hp ha) k) hpow
  rw [Real.log_pow] at hlog
  unfold goldenLayerMarginal
  rw [div_lt_iff₀ hpLog]
  calc
    Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a)) <
        Real.log p / (k : ℝ) :=
      (lt_div_iff₀ hkR).2 (by simpa [mul_comm] using hlog)
    _ = 1 / (k : ℝ) * Real.log p := by ring

private theorem layer_threshold_separation_5040 :
    goldenLayerMarginal 2 4 = Real.log (31 / 30) / Real.log 2 ∧
      goldenLayerMarginal 11 1 = Real.log (12 / 11) / Real.log 11 ∧
      (∀ p : ℕ, p.Prime → 0 < targetExponent5040 p →
        Real.log (31 / 30) / Real.log 2 ≤
          goldenLayerMarginal p (targetExponent5040 p)) ∧
      ∀ p : ℕ, p.Prime →
        goldenLayerMarginal p (targetExponent5040 p + 1) ≤
          Real.log (12 / 11) / Real.log 11 := by
  have hUpperEq :
      goldenLayerMarginal 2 4 = Real.log (31 / 30) / Real.log 2 := by
    norm_num [goldenLayerMarginal]
  have hLowerEq :
      goldenLayerMarginal 11 1 = Real.log (12 / 11) / Real.log 11 := by
    norm_num [goldenLayerMarginal]
  have hUpper20 : Real.log (31 / 30) / Real.log 2 < (1 / 20 : ℝ) := by
    rw [← hUpperEq]
    apply golden_layer_marginal_lt_one_div_nat (p := 2) (a := 4) (k := 20)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h3 : (1 / 20 : ℝ) < goldenLayerMarginal 3 2 := by
    apply one_div_nat_lt_golden_layer_marginal (p := 3) (a := 2) (k := 20)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h5 : (1 / 20 : ℝ) < goldenLayerMarginal 5 1 := by
    apply one_div_nat_lt_golden_layer_marginal (p := 5) (a := 1) (k := 20)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h7 : (1 / 20 : ℝ) < goldenLayerMarginal 7 1 := by
    apply one_div_nat_lt_golden_layer_marginal (p := 7) (a := 1) (k := 20)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have hLower28 : (1 / 28 : ℝ) < Real.log (12 / 11) / Real.log 11 := by
    rw [← hLowerEq]
    apply one_div_nat_lt_golden_layer_marginal (p := 11) (a := 1) (k := 28)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h2Next : goldenLayerMarginal 2 5 < (1 / 28 : ℝ) := by
    apply golden_layer_marginal_lt_one_div_nat (p := 2) (a := 5) (k := 28)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h3Next : goldenLayerMarginal 3 3 < (1 / 28 : ℝ) := by
    apply golden_layer_marginal_lt_one_div_nat (p := 3) (a := 3) (k := 28)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h5Next : goldenLayerMarginal 5 2 < (1 / 28 : ℝ) := by
    apply golden_layer_marginal_lt_one_div_nat (p := 5) (a := 2) (k := 28)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h7Next : goldenLayerMarginal 7 2 < (1 / 28 : ℝ) := by
    apply golden_layer_marginal_lt_one_div_nat (p := 7) (a := 2) (k := 28)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num
  refine ⟨hUpperEq, hLowerEq, ?_, ?_⟩
  · intro p hp hselected
    by_cases h2 : p = 2
    · subst p
      simpa [targetExponent5040] using hUpperEq.ge
    by_cases h3p : p = 3
    · subst p
      simpa [targetExponent5040] using (hUpper20.trans h3).le
    by_cases h5p : p = 5
    · subst p
      simpa [targetExponent5040] using (hUpper20.trans h5).le
    by_cases h7p : p = 7
    · subst p
      simpa [targetExponent5040] using (hUpper20.trans h7).le
    have hzero : targetExponent5040 p = 0 := by
      simp [targetExponent5040, h2, h3p, h5p, h7p]
    omega
  · intro p hp
    by_cases h2 : p = 2
    · subst p
      simpa [targetExponent5040] using (h2Next.trans hLower28).le
    by_cases h3p : p = 3
    · subst p
      simpa [targetExponent5040] using (h3Next.trans hLower28).le
    by_cases h5p : p = 5
    · subst p
      simpa [targetExponent5040] using (h5Next.trans hLower28).le
    by_cases h7p : p = 7
    · subst p
      simpa [targetExponent5040] using (h7Next.trans hLower28).le
    by_cases h11 : p = 11
    · subst p
      simpa [targetExponent5040] using hLowerEq.le
    have hp13 : 13 ≤ p := by
      by_contra h
      interval_cases p <;> norm_num at *
    have htarget : targetExponent5040 p = 0 := by
      simp [targetExponent5040, h2, h3p, h5p, h7p]
    rw [htarget, zero_add]
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
    have hlogLower : (1 / 13 : ℝ) < Real.log (12 / 11) := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 12 / 11 by norm_num)
      norm_num at h ⊢
      linarith
    have hquot : (1 / 13 : ℝ) / Real.log 11 <
        Real.log (12 / 11) / Real.log 11 :=
      (div_lt_div_iff_of_pos_right h11Log).2 hlogLower
    have hbound' : (p : ℝ)⁻¹ ^ 1 / Real.log p ≤
        Real.log (12 / 11) / Real.log 11 := by
      simpa using hbound.trans hquot.le
    exact (golden_layer_marginal_le_inv_pow hp (by omega)).trans hbound'

private theorem golden_prime_local_objective_diff {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (a : ℕ) :
    goldenPrimeLocalObjective lambda p (a + 1) - goldenPrimeLocalObjective lambda p a =
      (goldenLayerMarginal p (a + 1) - lambda) * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  unfold goldenPrimeLocalObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr hpInvLt).ne',
    Real.log_div ha.ne' (sub_pos.mpr hpInvLt).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp [hpLog.ne']
  ring

private theorem golden_prime_local_objective_unique_maximal_of_strict_threshold
    {p a : ℕ} (hp : p.Prime) (lambda : ℝ)
    (hupper : goldenLayerMarginal p (a + 1) < lambda)
    (hlower : a = 0 ∨ lambda < goldenLayerMarginal p a) :
    ∀ b, goldenPrimeLocalObjective lambda p b ≤ goldenPrimeLocalObjective lambda p a ∧
      (goldenPrimeLocalObjective lambda p b = goldenPrimeLocalObjective lambda p a ↔ b = a) := by
  have hweak := golden_prime_local_objective_maximal_of_threshold hp lambda hupper.le
    (hlower.elim (fun h => Or.inl h) (fun h => Or.inr h.le))
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have up : StrictMonoOn (goldenPrimeLocalObjective lambda p) (Set.Iic a) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro k hk
    have hgain : lambda < goldenLayerMarginal p (k + 1) := by
      rcases hlower with rfl | hlower
      · simp at hk
      · rcases eq_or_lt_of_le (show k + 1 ≤ a by omega) with heq | hlt
        · simpa [heq] using hlower
        · exact hlower.trans (golden_layer_strict_decrease hp (by omega) hlt)
    have hstep := mul_pos (sub_pos.mpr hgain) hpLog
    rw [← golden_prime_local_objective_diff hp lambda k] at hstep
    exact sub_pos.mp hstep
  have down : StrictAntiOn (goldenPrimeLocalObjective lambda p) (Set.Ici a) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Ici
    intro k _ hk _
    have hgain : goldenLayerMarginal p (k + 1) < lambda := by
      rcases eq_or_lt_of_le (show a + 1 ≤ k + 1 by exact Nat.succ_le_succ hk) with heq | hlt
      · simpa [← heq] using hupper
      · exact (golden_layer_strict_decrease hp (by omega) hlt).trans hupper
    have hstep := mul_neg_of_neg_of_pos (sub_neg.mpr hgain) hpLog
    rw [← golden_prime_local_objective_diff hp lambda k] at hstep
    exact sub_neg.mp hstep
  intro b
  refine ⟨hweak b, ?_⟩
  constructor
  · intro heq
    rcases lt_trichotomy b a with hba | hba | hab
    · exact (up hba.le (by simp) hba).ne heq |>.elim
    · exact hba
    · exact (down (by simp) hab.le hab).ne heq |>.elim
  · intro hba
    rw [hba]

private theorem target_exponent_eq_factorization_5040 (p : ℕ) :
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

/-- Every price strictly between the adjacent 5040 layer thresholds makes 5040 the unique
maximum of the golden resource objective over positive integers. -/
theorem golden_resource_5040_unique_maximum_of_price_interval
    {lambda : ℝ}
    (hlower : Real.log (12 / 11) / Real.log 11 < lambda)
    (hupper : lambda < Real.log (31 / 30) / Real.log 2)
    {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective lambda n ≤ goldenResourceObjective lambda 5040 ∧
      (goldenResourceObjective lambda n = goldenResourceObjective lambda 5040 ↔ n = 5040) := by
  obtain ⟨hUpperEq, hLowerEq, hselected, hunselected⟩ :=
    layer_threshold_separation_5040
  let s := n.primeFactors ∪ (5040 : ℕ).primeFactors
  have hprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hsumN := golden_resource_objective_sum_on lambda hn s subset_union_left
  have hsumM := golden_resource_objective_sum_on lambda
    (by norm_num : 1 ≤ (5040 : ℕ)) s subset_union_right
  have hlocal (p : ℕ) (hp : p ∈ s) :
      goldenPrimeLocalObjective lambda p (n.factorization p) ≤
        goldenPrimeLocalObjective lambda p ((5040 : ℕ).factorization p) ∧
      (goldenPrimeLocalObjective lambda p (n.factorization p) =
          goldenPrimeLocalObjective lambda p ((5040 : ℕ).factorization p) ↔
        n.factorization p = (5040 : ℕ).factorization p) := by
    have hpPrime := hprime p hp
    have htarget := target_exponent_eq_factorization_5040 p
    rw [← htarget]
    apply golden_prime_local_objective_unique_maximal_of_strict_threshold hpPrime lambda
    · exact (hunselected p hpPrime).trans_lt (hLowerEq ▸ hlower)
    · by_cases hzero : targetExponent5040 p = 0
      · exact Or.inl hzero
      · exact Or.inr (hupper.trans_le
          (hselected p hpPrime (Nat.pos_of_ne_zero hzero)))
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

end

end D5.S3.Arith.GoldenResource5040PriceInterval
