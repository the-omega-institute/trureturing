/- GID: D5/S3/Arith/GoldenResource/EightStepAbundancy
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/EightStepAbundancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:4fe323b6326388b3aebf9da0f2910f0388dd51193f4933d1324e9bcb52f37844
   digest: At eight prime factors, 180180 uniquely maximizes sigma(n)/n at 224/55. -/

import D5.S3.Arith.GoldenResourceObjectiveFactorization
import D5.S3.Arith.GoldenLocalThreshold

/- Search audit (2026-09-07, base 6634808834be9ae3d669f1f7075a92ae7771eeee):
   Repository searches with positive controls and Lean LSP found only adjacent results:
   finite non-strict prefix greedy optimality, the logarithmic-size-priced 5040 optimum,
   local threshold sufficiency, and objective factorization. The latter two are reused.
   Pinned Mathlib supplies sigma prime-power evaluation, multiplicative factorization,
   cardFactors_eq_sum_factorization, factorization_mul, and logarithm identities.
   GitHub Lean searches for 180180 and abundancy found no existing eight-step optimum.
   This is a known arithmetic result: OEIS A137825(8), with Wu (2019), arXiv:1906.05796.
   The new formal content is the unbounded prime-layer cutoff and strict uniqueness. -/

namespace D5.S3.Arith.GoldenResource.EightStepAbundancy

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization

/-- The denominator of the gain from the positive prime layer `k`. -/
def layerDenominator (p k : ℕ) : ℕ := ∑ i ∈ range k, p ^ (i + 1)

private theorem denominator_mono (p : ℕ) {a b : ℕ} (h : a ≤ b) :
    layerDenominator p a ≤ layerDenominator p b :=
  sum_le_sum_of_subset (range_mono h)

/-- Exactly these eight prime layers have gain denominator below fourteen. -/
theorem eight_step_layer_cutoff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    layerDenominator p k < 14 ↔
      (p, k) ∈ ({(2, 1), (3, 1), (5, 1), (2, 2),
        (7, 1), (11, 1), (3, 2), (13, 1)} : Finset (ℕ × ℕ)) := by
  constructor
  · intro hd
    have hk2 : k ≤ 2 := by
      by_contra h
      have h3 := denominator_mono p (show 3 ≤ k by omega)
      have h2 : 14 ≤ layerDenominator p 3 := by
        calc
          14 = layerDenominator 2 3 := by decide
          _ ≤ layerDenominator p 3 :=
            sum_le_sum fun i _ => Nat.pow_le_pow_left hp.two_le (i + 1)
      omega
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · have hp14 : p < 14 := by simpa [layerDenominator, sum_range_succ] using hd
      interval_cases p <;> norm_num at *
    · have hp3 : p ≤ 3 := by
        norm_num [layerDenominator, sum_range_succ] at hd
        nlinarith [hp.two_le]
      interval_cases p <;> norm_num at *
  · intro h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals norm_num [layerDenominator, sum_range_succ]

private def optimalExponent (p : ℕ) : ℕ :=
  if p = 2 ∨ p = 3 then 2 else if p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 then 1 else 0

private theorem cutoff_exponent {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    layerDenominator p k < 14 ↔ k ≤ optimalExponent p := by
  rw [eight_step_layer_cutoff hp hk]
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  unfold optimalExponent
  split_ifs <;> omega

private theorem denominator_pos {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 < layerDenominator p k := by
  have h := denominator_mono p hk
  have h1 : layerDenominator p 1 = p := by simp [layerDenominator]
  rw [h1] at h
  exact hp.pos.trans_le h

private theorem layer_ratio_identity {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (1 - (p : ℝ)⁻¹ ^ (k + 1)) / (1 - (p : ℝ)⁻¹ ^ k) =
      1 + 1 / (layerDenominator p k : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hpk : (p : ℝ) ^ k ≠ 1 :=
    ne_of_gt (one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega))
  have hd : (layerDenominator p k : ℝ) =
      ((p : ℝ) ^ k - 1) / ((p : ℝ) - 1) * p := by
    unfold layerDenominator
    push_cast
    simp only [pow_succ, ← sum_mul]
    rw [geom_sum_eq hp1]
  rw [hd]
  simp only [inv_pow, pow_succ]
  field_simp
  ring

private noncomputable def lowerPrice : ℝ := Real.log (15 / 14)
private noncomputable def upperPrice : ℝ := Real.log (14 / 13)
private noncomputable def middlePrice : ℝ := (lowerPrice + upperPrice) / 2

private theorem price_gap : lowerPrice < upperPrice :=
  Real.log_lt_log (by norm_num) (by norm_num)

private theorem exponent_thresholds {p : ℕ} (hp : p.Prime) :
    (0 < optimalExponent p →
      upperPrice / Real.log p ≤ goldenLayerMarginal p (optimalExponent p)) ∧
    goldenLayerMarginal p (optimalExponent p + 1) ≤ lowerPrice / Real.log p := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  constructor
  · intro ha
    have hd : (layerDenominator p (optimalExponent p) : ℝ) ≤ 13 := by
      exact_mod_cast (show layerDenominator p (optimalExponent p) ≤ 13 from
        Nat.le_of_lt_succ ((cutoff_exponent hp ha).mpr le_rfl))
    have hd0 : (0 : ℝ) < layerDenominator p (optimalExponent p) := by
      exact_mod_cast denominator_pos hp ha
    unfold goldenLayerMarginal
    rw [layer_ratio_identity hp ha]
    apply (div_le_div_iff_of_pos_right hl).mpr
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 14 / 13)
    have hi := one_div_le_one_div_of_le hd0 hd
    norm_num at hi ⊢
    linarith
  · have hd : (14 : ℝ) ≤ layerDenominator p (optimalExponent p + 1) := by
      exact_mod_cast (show 14 ≤ layerDenominator p (optimalExponent p + 1) from
        Nat.le_of_not_gt (fun h => by
          have := (cutoff_exponent hp (by omega)).mp h
          omega))
    unfold goldenLayerMarginal
    rw [layer_ratio_identity hp (by omega)]
    apply (div_le_div_iff_of_pos_right hl).mpr
    apply Real.log_le_log (by positivity)
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 14) hd
    norm_num at hi ⊢
    linarith

private noncomputable def countLocal (c : ℝ) (p a : ℕ) : ℝ :=
  goldenPrimeLocalObjective 0 p a - c * a

private theorem count_local_eq (c : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    countLocal c p a = goldenPrimeLocalObjective (c / Real.log p) p a := by
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  unfold countLocal goldenPrimeLocalObjective
  field_simp
  ring

private theorem count_local_maximal {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hcL : lowerPrice ≤ c) (hcU : c ≤ upperPrice) (b : ℕ) :
    countLocal c p b ≤ countLocal c p (optimalExponent p) := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨hup, hdown⟩ := exponent_thresholds hp
  rw [count_local_eq c hp b, count_local_eq c hp (optimalExponent p)]
  apply golden_prime_local_objective_maximal_of_threshold hp (c / Real.log p)
  · exact hdown.trans ((div_le_div_iff_of_pos_right hl).mpr hcL)
  · by_cases ha : optimalExponent p = 0
    · exact Or.inl ha
    · exact Or.inr (((div_le_div_iff_of_pos_right hl).mpr hcU).trans (hup (by omega)))

private theorem count_local_unique {p : ℕ} (hp : p.Prime) (b : ℕ) :
    countLocal middlePrice p b ≤ countLocal middlePrice p (optimalExponent p) ∧
    (countLocal middlePrice p b = countLocal middlePrice p (optimalExponent p) ↔
      b = optimalExponent p) := by
  have hgap := price_gap
  have hmidL : lowerPrice < middlePrice := by unfold middlePrice; linarith
  have hmidU : middlePrice < upperPrice := by unfold middlePrice; linarith
  refine ⟨count_local_maximal hp hmidL.le hmidU.le b, ⟨?_, fun h => by rw [h]⟩⟩
  intro heq
  have hL := count_local_maximal hp le_rfl hgap.le b
  have hU := count_local_maximal hp hgap.le le_rfl b
  rcases lt_trichotomy b (optimalExponent p) with h | h | h
  · have hb : (b : ℝ) < optimalExponent p := by exact_mod_cast h
    have hpos := mul_pos (sub_pos.mpr hmidU) (sub_pos.mpr hb)
    unfold countLocal at hU heq
    nlinarith
  · exact h
  · have hb : (optimalExponent p : ℝ) < b := by exact_mod_cast h
    have hpos := mul_pos (sub_pos.mpr hmidL) (sub_pos.mpr hb)
    unfold countLocal at hL heq
    nlinarith

private theorem factorization_180180 :
    (180180 : ℕ).factorization =
      Finsupp.single 2 2 + Finsupp.single 3 2 + Finsupp.single 5 1 +
        Finsupp.single 7 1 + Finsupp.single 11 1 + Finsupp.single 13 1 := by
  rw [show (180180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1 * 13 ^ 1 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 2).factorization_pow,
    (by norm_num : Nat.Prime 3).factorization_pow,
    (by norm_num : Nat.Prime 5).factorization_pow,
    (by norm_num : Nat.Prime 7).factorization_pow,
    (by norm_num : Nat.Prime 11).factorization_pow,
    (by norm_num : Nat.Prime 13).factorization_pow]

private theorem optimal_exponent_eq (p : ℕ) :
    optimalExponent p = (180180 : ℕ).factorization p := by
  rw [factorization_180180]
  simp only [Finsupp.add_apply, Finsupp.single_apply, optimalExponent]
  split_ifs <;> omega

private noncomputable def benefit (n : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 n : ℝ) / n

private theorem benefit_pos {n : ℕ} (hn : 0 < n) : 0 < benefit n :=
  div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
    (by exact_mod_cast hn)

private theorem count_sum_on (c : ℝ) {n : ℕ} (hn : 0 < n) (s : Finset ℕ)
    (hsub : n.primeFactors ⊆ s) :
    (∑ p ∈ s, countLocal c p (n.factorization p)) =
      Real.log (benefit n) - c * ArithmeticFunction.cardFactors n := by
  have hobj := golden_resource_objective_sum_on 0 hn s hsub
  rw [golden_resource_sigma_identity 0 hn] at hobj
  simp only [zero_mul, sub_zero] at hobj
  have hcount : (∑ p ∈ s, n.factorization p) = ArithmeticFunction.cardFactors n := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization]
    symm
    apply sum_subset hsub
    intro p _ hp
    simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
  have hcast := congrArg (fun k : ℕ => (k : ℝ)) hcount
  push_cast at hcast
  simp only [countLocal, sum_sub_distrib, ← mul_sum, hcast, ← hobj, benefit]

private theorem global_count_optimum {n : ℕ} (hn : 0 < n) :
    Real.log (benefit n) - middlePrice * ArithmeticFunction.cardFactors n ≤
      Real.log (benefit 180180) - middlePrice * ArithmeticFunction.cardFactors 180180 ∧
    (Real.log (benefit n) - middlePrice * ArithmeticFunction.cardFactors n =
      Real.log (benefit 180180) - middlePrice * ArithmeticFunction.cardFactors 180180 ↔
        n = 180180) := by
  let s := n.primeFactors ∪ (180180 : ℕ).primeFactors
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hsumN := count_sum_on middlePrice hn s subset_union_left
  have hsumM := count_sum_on middlePrice (by norm_num : 0 < (180180 : ℕ))
    s subset_union_right
  have hlocal (p : ℕ) (hp : p ∈ s) :
      countLocal middlePrice p (n.factorization p) ≤
        countLocal middlePrice p ((180180 : ℕ).factorization p) ∧
      (countLocal middlePrice p (n.factorization p) =
        countLocal middlePrice p ((180180 : ℕ).factorization p) ↔
          n.factorization p = (180180 : ℕ).factorization p) := by
    simpa only [optimal_exponent_eq] using count_local_unique (hprime p hp) (n.factorization p)
  rw [← hsumN, ← hsumM]
  refine ⟨sum_le_sum (fun p hp => (hlocal p hp).1), ⟨?_, fun h => by rw [h]⟩⟩
  intro heq
  have heach := (sum_eq_sum_iff_of_le (fun p hp => (hlocal p hp).1)).mp heq
  apply Nat.factorization_inj hn.ne' (by norm_num : (180180 : ℕ) ≠ 0)
  ext p
  by_cases hp : p ∈ s
  · exact (hlocal p hp).2.mp (heach p hp)
  · have hn' : p ∉ n.primeFactors := fun h => hp (mem_union_left _ h)
    have hm' : p ∉ (180180 : ℕ).primeFactors := fun h => hp (mem_union_right _ h)
    have hn0 : n.factorization p = 0 := by
      simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hn'
    have hm0 : (180180 : ℕ).factorization p = 0 := by
      simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hm'
    rw [hn0, hm0]

private theorem target_count : ArithmeticFunction.cardFactors 180180 = 8 := by
  simp [ArithmeticFunction.cardFactors_eq_sum_factorization, factorization_180180,
    Finsupp.sum_add_index]

private theorem comparison_count : ArithmeticFunction.cardFactors 5040 = 8 := by
  rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num]
  rw [ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.cardFactors_apply_prime_pow (by decide : Nat.Prime 3),
    ArithmeticFunction.cardFactors_apply_prime_pow (by decide : Nat.Prime 5),
    ArithmeticFunction.cardFactors_apply_prime_pow (by decide : Nat.Prime 7)]

private theorem target_value : benefit 180180 = 224 / 55 := by
  have hs : ArithmeticFunction.sigma 1 180180 = 733824 := by
    rw [show (180180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1 * 13 ^ 1 by norm_num,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 2 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1) (13 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 2 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1) (11 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 2 * 3 ^ 2 * 5 ^ 1) (7 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 2 * 3 ^ 2) (5 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 2) (3 ^ 2)),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 11),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 13)]
    norm_num [sum_range_succ]
  norm_num [benefit, hs]

private theorem comparison_value : benefit 5040 = 403 / 105 := by
  have hs : ArithmeticFunction.sigma 1 5040 = 19344 := by
    rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 4 * 3 ^ 2 * 5 ^ 1) (7 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 4 * 3 ^ 2) (5 ^ 1)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime (2 ^ 4) (3 ^ 2)),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
    norm_num [sum_range_succ]
  norm_num [benefit, hs]

/-- The global eight-step maximum, its unique achiever, and the strict 5040 comparison. -/
theorem eight_step_abundancy_optimum :
    let omega : ℕ → ℕ := fun n => n.factorization.sum (fun _ a => a)
    let Z : ℕ → ℝ := fun n => (ArithmeticFunction.sigma 1 n : ℝ) / (n : ℝ)
    Z 180180 = 224 / 55 ∧
    (∀ n : ℕ, 0 < n → omega n = 8 →
      Z n ≤ 224 / 55 ∧ (Z n = 224 / 55 ↔ n = 180180)) ∧
    Z 5040 = 403 / 105 ∧ Z 5040 < Z 180180 ∧
    omega 180180 = 8 ∧ omega 5040 = 8 ∧
    (180180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 * 7 * 11 * 13 := by
  dsimp only
  simp only [← ArithmeticFunction.cardFactors_eq_sum_factorization]
  refine ⟨target_value, ?_, comparison_value, ?_, target_count, comparison_count, by norm_num⟩
  · intro n hn hcount
    obtain ⟨hle, heq⟩ := global_count_optimum hn
    rw [hcount, target_count, target_value] at hle heq
    refine ⟨?_, ?_⟩
    · apply (Real.log_le_log_iff (benefit_pos hn) (by norm_num : (0 : ℝ) < 224 / 55)).mp
      linarith
    · constructor
      · intro h
        apply heq.mp
        change benefit n = 224 / 55 at h
        rw [h]
      · intro h
        subst n
        exact target_value
  · change benefit 5040 < benefit 180180
    rw [comparison_value, target_value]
    norm_num

#print axioms eight_step_layer_cutoff
#print axioms eight_step_abundancy_optimum

end D5.S3.Arith.GoldenResource.EightStepAbundancy
