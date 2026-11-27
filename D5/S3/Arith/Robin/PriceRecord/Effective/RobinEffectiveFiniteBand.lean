/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand
   mirror-E: none(waiver:exact-integer-certificates)
   anchors: []
   utility: none
   digest: Exact prefix counts supply the Robin reserve on eight dyadic intervals. -/

import D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.PriceRecord.Effective

open Finset
open D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus

private def cutoff (i : ℕ) : ℕ := 140 * 2^i

private theorem cutoff_succ (i : ℕ) : cutoff (i + 1) = 2 * cutoff i := by
  simp only [cutoff, pow_succ] <;> ring

private theorem cutoff_ge (i : ℕ) : 140 ≤ cutoff i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [cutoff_succ]
    omega

private theorem cutoff_covers {a : ℝ} (ha : 140 ≤ a) (i : ℕ)
    (hu : a ≤ (cutoff (i + 1) : ℝ)) :
    ∃ j ≤ i, (cutoff j : ℝ) ≤ a ∧ a ≤ (cutoff (j + 1) : ℝ) := by
  induction i with
  | zero => exact ⟨0, le_rfl, ha, hu⟩
  | succ i ih =>
    by_cases h : a ≤ (cutoff (i + 1) : ℝ)
    · obtain ⟨j, hj, hja, haj⟩ := ih h
      exact ⟨j, hj.trans (Nat.le_succ _), hja, haj⟩
    · exact ⟨i + 1, le_rfl, le_of_lt (lt_of_not_ge h), hu⟩

/-- Trial division stops at the square root or after the given number of tests. -/
private def noDivisor (p : ℕ) (start : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if p < start * start then true
    else if p % start = 0 then false
    else noDivisor p (start + 1) fuel

private theorem noDivisor_eq_true (p start fuel : ℕ) :
    noDivisor p start fuel = true ↔
      ∀ d, start ≤ d → d < start + fuel → d*d ≤ p → ¬d ∣ p := by
  induction fuel generalizing start with
  | zero =>
    constructor
    · intro _ d hlo hhi
      omega
    · intro _
      rfl
  | succ fuel ih =>
    by_cases hstop : p < start * start
    · simp only [noDivisor, if_pos hstop, true_iff]
      intro d hlo _ hsq _
      exact (not_le_of_gt hstop) ((Nat.mul_self_le_mul_self hlo).trans hsq)
    · rw [noDivisor, if_neg hstop]
      by_cases hdvd : start ∣ p
      · simp only [if_pos (Nat.dvd_iff_mod_eq_zero.mp hdvd), Bool.false_eq_true, false_iff]
        intro h
        exact h start le_rfl (by omega) (le_of_not_gt hstop) hdvd
      · have hmod : p % start ≠ 0 := fun h => hdvd (Nat.dvd_iff_mod_eq_zero.mpr h)
        rw [if_neg hmod, ih]
        constructor
        · intro h d hlo hhi hsq
          rcases eq_or_lt_of_le hlo with rfl | hlt
          · exact hdvd
          · exact h d (by omega) (by omega) hsq
        · intro h d hlo hhi hsq
          exact h d (by omega) (by omega) hsq

/-- All row candidates are below 268², so divisors past 267 are unnecessary. -/
private def trialPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && noDivisor p 2 266

private theorem trialPrime_eq_true {p : ℕ} (hcap : p < 268^2) :
    trialPrime p = true ↔ p.Prime := by
  have hs : p.sqrt < 268 := Nat.sqrt_lt'.mpr hcap
  simp only [trialPrime, Bool.and_eq_true_iff, decide_eq_true_eq, noDivisor_eq_true]
  constructor
  · rintro ⟨hp₂, hd⟩
    exact Nat.prime_def_le_sqrt.mpr ⟨hp₂, fun d hd₂ hds =>
      hd d hd₂ (hds.trans_lt hs) (Nat.le_sqrt.mp hds)⟩
  · intro hp
    exact ⟨hp.two_le, fun d hd₂ _ hdp =>
      (Nat.prime_def_le_sqrt.mp hp).2 d hd₂ (Nat.le_sqrt.mpr hdp)⟩

/-- Split the range so kernel reduction only traverses short lists. -/
private def trialCount : ℕ → ℕ → ℕ → ℕ
  | 0, start, len => (List.range' start len).countP trialPrime
  | fuel + 1, start, len =>
    let half := len / 2
    trialCount fuel start half + trialCount fuel (start + half) (len - half)

private theorem trialCount_eq (fuel start len : ℕ) :
    trialCount fuel start len = (List.range' start len).countP trialPrime := by
  induction fuel generalizing start len with
  | zero => rfl
  | succ fuel ih =>
    let half := len / 2
    change trialCount fuel start half + trialCount fuel (start + half) (len - half) = _
    have hsum : half + (len - half) = len := by dsimp [half]; omega
    rw [ih, ih, ← List.countP_append, List.range'_append_1, hsum]

/-- Each row stores the first band's full count, the second band's prefix length,
and the prime count in that prefix. -/
private def rowData : List (ℕ × ℕ × ℕ) :=
  [ (22, 127, 20),
    (44, 169, 23),
    (76, 347, 44),
    (140, 559, 70),
    (260, 1021, 115),
    (479, 1919, 202),
    (895, 3649, 348),
    (1669, 6737, 623) ]

-- Eight bisections leave at most 70 candidates per leaf.
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem row_check (i : ℕ) (hi : i < 8) :
    let A := cutoff i
    let k := 7 + i
    let row := rowData.getD i (0, 0, 0)
    let c₁ := row.1
    let len₂ := row.2.1
    let c₂ := row.2.2
    1 ≤ k ∧ 2^k ≤ A ∧ 4*A < 268^2 ∧ len₂ ≤ A ∧
      trialCount 8 (2*A + 1) A = c₁ ∧ trialCount 8 (3*A + 1) len₂ = c₂ ∧
      1152000*A ≤ 23667*(2*k - 1)*(16*c₁ + 9*c₂) := by
  interval_cases i <;> decide +kernel

private def countedPrimes (lo len : ℕ) : Finset ℕ :=
  ((List.range' (lo + 1) len).filter trialPrime).toFinset

private theorem countedPrimes_card {lo len c : ℕ}
    (hcount : trialCount 8 (lo + 1) len = c) : (countedPrimes lo len).card = c := by
  have hnodup : (List.range' (lo + 1) len).Nodup := List.nodup_range' (step := 1)
  unfold countedPrimes
  rw [List.toFinset_card_of_nodup (hnodup.filter _), ← List.countP_eq_length_filter]
  simpa only [trialCount_eq] using hcount

private theorem countedPrimes_bounds {lo len hi p : ℕ}
    (hwidth : lo + len ≤ hi) (hcap : hi < 268^2) (hp : p ∈ countedPrimes lo len) :
    p.Prime ∧ lo < p ∧ p ≤ hi := by
  change p ∈ ((List.range' (lo + 1) len).filter trialPrime).toFinset at hp
  have ⟨hpRange, hpTrial⟩ := List.mem_filter.mp (List.mem_toFinset.mp hp)
  have hbdd : lo < p ∧ p ≤ hi := by
    have := List.mem_range'_1.mp hpRange
    omega
  exact ⟨(trialPrime_eq_true (hbdd.2.trans_lt hcap)).mp hpTrial, hbdd⟩

noncomputable section

private theorem band_weight_nonneg {z : ℝ} {p : ℕ} (hp : p ∈ primeBand z) :
    0 ≤ primeBandWeight p := by
  have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hp₀ : (0 : ℝ) < p := by linarith
  have hp₁ : 0 < (p : ℝ) - 1 := by linarith
  unfold primeBandWeight
  exact div_nonneg (by linarith) (by positivity)

/-- The two disjoint prime subsets give the weighted estimate in the native band. -/
private theorem normalized_row {z : ℝ} (hz : 10000 ≤ z) {A k len₂ c₁ c₂ : ℕ}
    (hA : 140 ≤ A) (hAa : (A : ℝ) ≤ Real.sqrt (2*z))
    (haB : Real.sqrt (2*z) ≤ 2*(A : ℝ))
    (hk : 1 ≤ k) (hkA : 2^k ≤ A) (hcap : 4*A < 268^2) (hlen : len₂ ≤ A)
    (hcount₁ : trialCount 8 (2*A + 1) A = c₁)
    (hcount₂ : trialCount 8 (3*A + 1) len₂ = c₂)
    (hcalc : 1152000*A ≤ 23667*(2*k - 1)*(16*c₁ + 9*c₂)) :
    (2/25 : ℝ) ≤ normalizedPrimeBand z := by
  let a := Real.sqrt (2*z)
  let primes₁ := countedPrimes (2*A) A
  let primes₂ := countedPrimes (3*A) len₂
  have hz₀ : 0 < z := by linarith
  have hz₁ : 1 < z := by linarith
  have hA₀ : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hA₁ : (140 : ℝ) ≤ A := by exact_mod_cast hA
  have ha₀ : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha₂ : a^2 = 2*z := Real.sq_sqrt (by positivity)
  have hlog₂ : (69/100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_a : (k : ℝ)*Real.log 2 ≤ Real.log a := by
    have hk₂ : (2 : ℝ)^k ≤ a := by
      exact (by exact_mod_cast hkA : (2 : ℝ)^k ≤ A).trans hAa
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hk₂
  have hlog_z : Real.log z = 2*Real.log a - Real.log 2 := by
    change Real.log z = 2*Real.log (Real.sqrt (2*z)) - Real.log 2
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hz₀.ne']
    ring
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : 0 ≤ 2*(k : ℝ) - 1 := by linarith
  have hlog_lb : (69/100)*(2*(k : ℝ) - 1) ≤ Real.log z := by
    have h := mul_le_mul_of_nonneg_left hlog₂ hfactor
    nlinarith only [h, hlog_a, hlog_z]
  have hs₂ : Real.sqrt 2 ≤ (10/7 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have ha_eq : a = Real.sqrt 2 * Real.sqrt z := Real.sqrt_mul (by norm_num) z
  have hs_lb : (7/10)*(A : ℝ) ≤ Real.sqrt z := by
    have h := mul_le_mul_of_nonneg_right hs₂ (Real.sqrt_nonneg z)
    change (A : ℝ) ≤ a at hAa
    rw [← ha_eq] at h
    linarith only [h, hAa]
  have hD : (483/1000)*(A : ℝ)*(2*(k : ℝ) - 1) ≤ D z := by
    unfold D
    convert mul_le_mul hs_lb hlog_lb (mul_nonneg (by norm_num) hfactor)
      (Real.sqrt_nonneg z) using 1 <;> ring
  have hD₀ : 0 ≤ D z := mul_nonneg (Real.sqrt_nonneg z) (Real.log_pos hz₁).le
  have hcard₁ : primes₁.card = c₁ := countedPrimes_card hcount₁
  have hcard₂ : primes₂.card = c₂ := countedPrimes_card hcount₂
  have hdata₁ (p : ℕ) (hp : p ∈ primes₁) : p.Prime ∧ 2*A < p ∧ p ≤ 3*A :=
    countedPrimes_bounds (by omega) (by omega) hp
  have hdata₂ (p : ℕ) (hp : p ∈ primes₂) : p.Prime ∧ 3*A < p ∧ p ≤ 4*A :=
    countedPrimes_bounds (by omega) hcap hp
  have hmem (p : ℕ) (hpp : p.Prime) (hlo : 2*A < p) (hhi : p ≤ 4*A) :
      p ∈ primeBand z := by
    have hlo' : 2*(A : ℝ) < p := by exact_mod_cast hlo
    have hhi' : (p : ℝ) ≤ 4*(A : ℝ) := by exact_mod_cast hhi
    have ha_sq : (A : ℝ)^2 ≤ a^2 :=
      (sq_le_sq₀ hA₀.le ha₀.le).mpr hAa
    have hA_sq : 8*(A : ℝ) ≤ (A : ℝ)^2 := by
      nlinarith only [mul_nonneg hA₀.le (show 0 ≤ (A : ℝ) - 8 by linarith)]
    have hpz : (p : ℝ) ≤ z := by linarith only [hhi', hA_sq, ha_sq, ha₂]
    have hap : a < (p : ℝ) := haB.trans_lt hlo'
    have hpp₂ : 2*z < (p : ℝ)^2 := by
      rw [← ha₂]
      exact (sq_lt_sq₀ ha₀.le (Nat.cast_nonneg _)).mpr hap
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpz, hpp⟩, hpp₂⟩
  have hsub : primes₁ ∪ primes₂ ⊆ primeBand z := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hpp, hlo, hhi⟩ := hdata₁ p hp
      exact hmem p hpp hlo (by omega)
    · obtain ⟨hpp, hlo, hhi⟩ := hdata₂ p hp
      exact hmem p hpp (by omega) hhi
  have hdis : Disjoint primes₁ primes₂ := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    exact (not_lt_of_ge (hdata₁ p hp₁).2.2) (hdata₂ p hp₂).2.1
  have hw (p : ℕ) (hlo : 2*A < p) {q : ℝ} (hhi : (p : ℝ) ≤ q) :
      (49/100 : ℝ)*(1/q^2) ≤ primeBandWeight p := by
    have hlo' : 2*(A : ℝ) < p := by exact_mod_cast hlo
    have hp₅₁ : (51 : ℝ) ≤ p := by linarith only [hA₁, hlo']
    have hp₀ : (0 : ℝ) < p := by linarith
    have hp₁ : 0 < (p : ℝ) - 1 := by linarith
    have hq₀ : 0 < q := hp₀.trans_le hhi
    have hsquare : (p : ℝ)^2 ≤ q^2 := (sq_le_sq₀ hp₀.le hq₀.le).mpr hhi
    have hweight : (49/100 : ℝ)*(1/(p : ℝ)^2) ≤ primeBandWeight p := by
      unfold primeBandWeight
      apply (le_div_iff₀ (by positivity : 0 < 2*((p : ℝ) - 1)*(p : ℝ)^2)).mpr
      rw [show (49/100 : ℝ)*(1/(p : ℝ)^2)*(2*((p : ℝ) - 1)*(p : ℝ)^2) =
          (49/50)*((p : ℝ) - 1) by field_simp [hp₀.ne'] <;> ring]
      linarith only [hp₅₁]
    refine le_trans ?_ hweight
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsquare) (by norm_num)
  have hw₁ (p : ℕ) (hp : p ∈ primes₁) :
      (49/100 : ℝ)*(1/(3*(A : ℝ))^2) ≤ primeBandWeight p := by
    obtain ⟨_, hlo, hhi⟩ := hdata₁ p hp
    exact hw p hlo (by exact_mod_cast hhi)
  have hw₂ (p : ℕ) (hp : p ∈ primes₂) :
      (49/100 : ℝ)*(1/(4*(A : ℝ))^2) ≤ primeBandWeight p := by
    obtain ⟨_, hlo, hhi⟩ := hdata₂ p hp
    exact hw p (by omega) (by exact_mod_cast hhi)
  have hsum : (c₁ : ℝ)*((49/100)*(1/(3*(A : ℝ))^2)) +
      (c₂ : ℝ)*((49/100)*(1/(4*(A : ℝ))^2)) ≤ ∑ p ∈ primeBand z, primeBandWeight p := by
    have hweights₁ := Finset.sum_le_sum (s := primes₁) hw₁
    have hweights₂ := Finset.sum_le_sum (s := primes₂) hw₂
    rw [Finset.sum_const, nsmul_eq_mul, hcard₁] at hweights₁
    rw [Finset.sum_const, nsmul_eq_mul, hcard₂] at hweights₂
    have hweights := add_le_add hweights₁ hweights₂
    rw [← Finset.sum_union (f := primeBandWeight) hdis] at hweights
    exact hweights.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun p hp _ => band_weight_nonneg hp)
  have hcalc' : (1152000 : ℝ)*A ≤ 23667*(2*(k : ℝ) - 1)*(16*(c₁ : ℝ) + 9*(c₂ : ℝ)) := by
    have hreal : (1152000 : ℝ)*A ≤
        23667*((2*k - 1 : ℕ) : ℝ)*(16*(c₁ : ℝ) + 9*(c₂ : ℝ)) := by
      exact_mod_cast hcalc
    rw [Nat.cast_sub (show 1 ≤ 2*k by omega)] at hreal
    push_cast at hreal
    exact hreal
  have hcalc'' : (2/25 : ℝ) ≤ ((483/1000)*(A : ℝ)*(2*(k : ℝ) - 1))*
      ((c₁ : ℝ)*((49/100)*(1/(3*(A : ℝ))^2)) + (c₂ : ℝ)*((49/100)*(1/(4*(A : ℝ))^2))) := by
    rw [show ((483/1000)*(A : ℝ)*(2*(k : ℝ) - 1))*
        ((c₁ : ℝ)*((49/100)*(1/(3*(A : ℝ))^2)) + (c₂ : ℝ)*((49/100)*(1/(4*(A : ℝ))^2))) =
          23667*(2*(k : ℝ) - 1)*(16*(c₁ : ℝ) + 9*(c₂ : ℝ))/(14400000*(A : ℝ)) by
      field_simp [hA₀.ne'] <;> ring]
    exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hcalc'])
  exact hcalc''.trans (mul_le_mul hD hsum (by positivity) hD₀)

private theorem neededReserve_lt_two_twenty_fifths {z : ℝ} (hz : 10000 ≤ z) :
    neededReserve z < 2/25 := by
  have hz₀ : 0 < z := by linarith
  have hlog : 9 ≤ Real.log z := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 10000) hz
    rw [show (10000 : ℝ) = (2*5)^4 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)] at hl
    norm_num at hl
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hi : 1/Real.log z ≤ 1/9 :=
    (div_le_iff₀ (show 0 < Real.log z by linarith)).mpr (by linarith)
  have hs : 100 ≤ Real.sqrt z :=
    Real.le_sqrt_of_sq_le (by norm_num <;> linarith : (100 : ℝ)^2 ≤ z)
  have hroot : 2/Real.sqrt z ≤ 2/100 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hc : (1+1/Real.log z)/(8*z*Real.sqrt z) ≤ (1+1/9)/(8*10000*100) := by
    refine (div_le_div_of_nonneg_right (add_le_add le_rfl hi) (by positivity)).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have h := mul_le_mul hz hs (by norm_num : (0 : ℝ) ≤ 100) hz₀.le
    nlinarith only [h]
  unfold neededReserve
  linarith only [hi, hroot, hc]

/-- Eight dyadic rows cover the Robin reserve below the Chebyshev cutoff. -/
theorem neededReserve_lt_normalizedPrimeBand_of_sqrt_le {z : ℝ}
    (hz : 10000 ≤ z) (ha : Real.sqrt (2*z) ≤ 25000) :
    neededReserve z < normalizedPrimeBand z := by
  have ha₀ : 140 ≤ Real.sqrt (2*z) :=
    Real.le_sqrt_of_sq_le (by norm_num <;> linarith : (140 : ℝ)^2 ≤ 2*z)
  have hu : Real.sqrt (2*z) ≤ (cutoff 8 : ℝ) :=
    ha.trans (by exact_mod_cast (show 25000 ≤ cutoff 8 by decide +kernel))
  obtain ⟨i, hi, hAi, hBi⟩ := cutoff_covers ha₀ 7 hu
  rw [cutoff_succ] at hBi
  push_cast at hBi
  obtain ⟨hk, hkA, hcap, hlen, hcount₁, hcount₂, hcalc⟩ := row_check i (by omega)
  exact (neededReserve_lt_two_twenty_fifths hz).trans_le
    (normalized_row hz (cutoff_ge i) hAi hBi hk hkA hcap hlen hcount₁ hcount₂ hcalc)

end
end D5.S3.Arith.Robin.PriceRecord.Effective
