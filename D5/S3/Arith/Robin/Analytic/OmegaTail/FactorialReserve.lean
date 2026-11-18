/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/FactorialReserve
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Factorial thresholds, rounded prime excess, and exact far deletion at fixed order. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion

/-! The factorial threshold and the prime reserves at a fixed order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real Asymptotics Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve

open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
  (primeCount primeInterval prime_counting_factorial_residual theta_error_log_power)
open D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
  (far_window_capacity far_deletion_of_card_le)

/-- The continuous factorial threshold expressed at the real prime cutoff P. -/
def centeredThreshold (r : ℕ) (P : ℝ) : ℝ :=
  P * ∑ j ∈ range r, (j.factorial : ℝ) / log P ^ (j + 1)

/-- The factorial threshold at the original integer-counting cutoff x. -/
def threshold (r : ℕ) (x : ℝ) : ℝ := centeredThreshold r (log x)

/-- The count of positive integers at most x strictly above the factorial threshold. -/
def tailCount (r : ℕ) (x : ℝ) : ℕ :=
  ((Icc 1 ⌊x⌋₊).filter
    (fun n => threshold r x < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card

/-- The smallest natural count strictly exceeding the centered threshold when P > 1. -/
def cutoff (r : ℕ) (P : ℝ) : ℕ := ⌊centeredThreshold r P⌋₊ + 1

/-- The excess of the prime count over the rounded threshold, in real arithmetic. -/
def primeExcess (r : ℕ) (P : ℝ) : ℝ := primeCount P - cutoff r P

/-- The natural number of primes to delete. -/
def deletionCount (r : ℕ) (P : ℝ) : ℕ := Nat.primeCounting ⌊P⌋₊ - cutoff r P

/-- The rounded reserve pricing each deletion at the central logarithm. -/
def roundedReserve (r : ℕ) (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + primeExcess r P * log P

/-- The reserve guaranteed by a lower bound on the logarithm of each deleted prime. -/
def safeReserve (r : ℕ) (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + primeExcess r P * log (P / 2)

private lemma centeredThreshold_nonneg (r : ℕ) {P : ℝ} (hP : 1 < P) :
    0 ≤ centeredThreshold r P := by
  unfold centeredThreshold
  exact mul_nonneg (by linarith) (sum_nonneg fun j _ =>
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (log_pos hP).le _))

private lemma rounding (r : ℕ) {P : ℝ} (hP : 1 < P) :
    0 < (cutoff r P : ℝ) - centeredThreshold r P ∧
      (cutoff r P : ℝ) - centeredThreshold r P ≤ 1 := by
  rw [cutoff, Nat.cast_add, Nat.cast_one]
  exact ⟨sub_pos.mpr (Nat.lt_floor_add_one _),
    by linarith [Nat.floor_le (centeredThreshold_nonneg r hP)]⟩

private lemma rounded_excess (r : ℕ) :
    Tendsto (fun P : ℝ => primeExcess r P / (P / log P ^ (r + 1)))
      atTop (𝓝 (r.factorial : ℝ)) := by
  have hcontinuous :
      Tendsto (fun P : ℝ => (primeCount P - centeredThreshold r P) / (P / log P ^ (r + 1)))
        atTop (𝓝 (r.factorial : ℝ)) := by
    simpa only [centeredThreshold, mul_sum, mul_div_assoc, mul_comm] using
      prime_counting_factorial_residual r
  have hlog : Tendsto (fun P : ℝ => log P ^ (r + 1) / P) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (↑(r + 1 : ℕ)) (by norm_num : (0 : ℝ) < 1))
        .tendsto_div_nhds_zero
  have hsmall : Tendsto
      (fun P : ℝ => ((cutoff r P : ℝ) - centeredThreshold r P) / (P / log P ^ (r + 1)))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      exact div_nonneg (rounding r hP).1.le
        (div_nonneg (by linarith) (pow_nonneg (log_pos hP).le _))
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      calc
        _ ≤ 1 / (P / log P ^ (r + 1)) :=
          div_le_div_of_nonneg_right (rounding r hP).2
            (div_nonneg (by linarith) (pow_nonneg (log_pos hP).le _))
        _ = log P ^ (r + 1) / P := by rw [one_div, inv_div]
  simpa only [sub_zero, ← sub_div, sub_sub_sub_cancel_right, primeExcess] using
    hcontinuous.sub hsmall

/-- The strict count at exp P uses exactly the natural cutoff, including integer thresholds. -/
theorem tailCount_exp_eq (r : ℕ) {P : ℝ} (hP : 1 < P) :
    tailCount r (exp P) =
      ((Icc 1 ⌊exp P⌋₊).filter
        (fun n => cutoff r P ≤ ArithmeticFunction.cardDistinctFactors n)).card := by
  unfold tailCount threshold
  rw [log_exp]
  congr 1
  ext n
  simp only [mem_filter, cutoff, Nat.succ_le_iff, Nat.floor_lt (centeredThreshold_nonneg r hP)]

/-- The rounded excess and the two reserves retain the next factorial coefficient. -/
theorem factorial_reserve (r : ℕ) :
    Tendsto (fun P : ℝ => primeExcess r P / (P / log P ^ (r + 1)))
      atTop (𝓝 (r.factorial : ℝ)) ∧
    (∀ᶠ P : ℝ in atTop, cutoff r P ≤ Nat.primeCounting ⌊P⌋₊ ∧
      (deletionCount r P : ℝ) = primeExcess r P) ∧
    Tendsto (fun P : ℝ => roundedReserve r P / (P / log P ^ r))
      atTop (𝓝 (r.factorial : ℝ)) ∧
    Tendsto (fun P : ℝ => safeReserve r P / (P / log P ^ r))
      atTop (𝓝 (r.factorial : ℝ)) := by
  have htheta : Tendsto (fun P : ℝ => (P - Chebyshev.theta P) / (P / log P ^ r))
      atTop (𝓝 0) := by
    simpa only [← neg_div, neg_sub, neg_zero] using
      ((theta_error_log_power r).tendsto_div_nhds_zero).neg
  have hhalf : Tendsto (fun P : ℝ => log (P / 2) / log P) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
      (tendsto_log_atTop.const_div_atTop (log 2))
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    rw [log_div (by linarith : P ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      sub_div, div_self (log_pos hP).ne']
  have hfact : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  refine ⟨rounded_excess r, ?_, ?_, ?_⟩
  · filter_upwards [(rounded_excess r).eventually_const_lt hfact,
      eventually_gt_atTop (1 : ℝ)] with P hE hP
    have hpos : 0 < primeExcess r P :=
      (div_pos_iff_of_pos_right (div_pos (by linarith) (pow_pos (log_pos hP) _))).mp hE
    have hk : cutoff r P ≤ Nat.primeCounting ⌊P⌋₊ := by
      have h : (cutoff r P : ℝ) ≤ (Nat.primeCounting ⌊P⌋₊ : ℝ) := sub_nonneg.mp hpos.le
      exact_mod_cast h
    exact ⟨hk, Nat.cast_sub hk⟩
  · have h := htheta.add (rounded_excess r)
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [roundedReserve]
    rw [pow_succ]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  · have h := htheta.add ((rounded_excess r).mul hhalf)
    rw [mul_one, zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [safeReserve]
    rw [pow_succ]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring

/-- A far-window deletion exists, and every such choice leaves exactly the strict cutoff
of distinct primes with a uniform reserve for the logarithm of their product. -/
theorem factorial_far_deletion (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ P : ℝ in atTop,
      (∃ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount r P) ∧
      ∀ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount r P →
        (∀ p ∈ R, P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * P ∧ p.Prime) ∧
        ∃ S : Finset ℕ, S = Nat.primesLE ⌊P⌋₊ \ R ∧ S.card = cutoff r P ∧
          (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ P) ∧
          (Nat.primesLE ⌊P⌋₊ \ primeInterval (P / 2) (3 / 4 * P)) ⊆ S ∧
          log (∏ p ∈ S, (p : ℝ)) ≤ P - safeReserve r P := by
  obtain ⟨hE, hcast, _⟩ := factorial_reserve r
  have hinv : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have hexcess : Tendsto (fun P : ℝ => (deletionCount r P : ℝ) / (P / log P))
      atTop (𝓝 0) := by
    have h := hE.mul (hinv.pow r)
    rw [zero_pow (by omega : r ≠ 0), mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hcast] with P hP hcastP
    rw [hcastP.2, pow_succ, div_pow, one_pow]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  filter_upwards [hexcess.eventually_lt far_window_capacity (by norm_num), hcast,
    eventually_gt_atTop (1 : ℝ)] with P hfit hcastP hP
  have hscale : 0 < P / log P := div_pos (by linarith) (log_pos hP)
  have hroom : deletionCount r P ≤ (primeInterval (P / 2) (3 / 4 * P)).card := by
    exact_mod_cast ((div_lt_div_iff_of_pos_right hscale).mp hfit).le
  obtain ⟨hmem, hexists, hbudget⟩ := far_deletion_of_card_le hP hcastP.1 hroom
  refine ⟨hexists, fun R hR hcard => ⟨fun p hp => (hmem p).mp (hR hp), ?_⟩⟩
  obtain ⟨hsize, hsum⟩ := hbudget R hR hcard
  refine ⟨_, rfl, hsize, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    exact ⟨hprime, (Nat.le_floor_iff (by linarith : 0 ≤ P)).mp hle⟩
  · intro p hp
    obtain ⟨hle, houtside⟩ := mem_sdiff.mp hp
    exact mem_sdiff.mpr ⟨hle, fun hpR => houtside (hR hpR)⟩
  · rw [log_prod (fun p hp =>
      Nat.cast_ne_zero.mpr (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2.ne_zero)]
    simpa only [safeReserve, primeExcess] using hsum

end D5.S3.Arith.Robin.Analytic.OmegaTail.FactorialReserve
