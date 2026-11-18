/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Centered prime excess, logarithmic reserves, and a uniform far deletion budget. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

/-! Centered prime excess and the reserves available after far deletion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real Asymptotics Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion

open D5.S3.Arith.Robin.Analytic.OmegaTailUpper (scale threshold)
open D5.S3.Arith.Robin.Analytic.OmegaTail.Selection (primeInterval_capacity selectedCount)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
  (countingPolynomial primeCount primeInterval prime_counting_four_terms theta_error_log_power)

/-- The continuous threshold at the real prime cutoff. -/
def centeredThreshold (P : ℝ) : ℝ := P / log P + P / log P ^ 2

/-- The smallest natural count strictly above the threshold, at original cutoff exp P. -/
abbrev centeredCount (P : ℝ) : ℕ := selectedCount 1 (exp P)

/-- The real difference between the prime count and the rounded threshold. -/
def primeExcess (P : ℝ) : ℝ := primeCount P - centeredCount P

/-- The natural cardinality of the deletion set. -/
def deletionCount (P : ℝ) : ℕ := Nat.primeCounting ⌊P⌋₊ - centeredCount P

/-- The budget from the continuous threshold. -/
def continuousReserve (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + (primeCount P - centeredThreshold P) * log P

/-- The budget from the rounded count. -/
def roundedReserve (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + primeExcess P * log P

/-- The reserve obtained using the lower endpoint for the cost of each deleted prime. -/
def safeReserve (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + primeExcess P * log (P / 2)

private lemma centeredCount_floor (P : ℝ) :
    centeredCount P = ⌊centeredThreshold P⌋₊ + 1 := by
  have ha : threshold 1 (exp P) = centeredThreshold P := by
    simp only [threshold, scale, log_exp, one_mul, centeredThreshold]
    rw [div_div, pow_two]
  simp only [centeredCount, selectedCount, ha]

private lemma count_rounding {P : ℝ} (hP : 1 < P) :
    0 < (centeredCount P : ℝ) - centeredThreshold P ∧
      (centeredCount P : ℝ) - centeredThreshold P ≤ 1 := by
  have ha : 0 ≤ centeredThreshold P := by
    unfold centeredThreshold
    positivity [log_pos hP, (show 0 < P by linarith)]
  rw [centeredCount_floor P, Nat.cast_add, Nat.cast_one]
  exact ⟨sub_pos.mpr (Nat.lt_floor_add_one _), by linarith [Nat.floor_le ha]⟩

private lemma continuous_excess :
    Tendsto (fun P : ℝ => (primeCount P - centeredThreshold P) / (P / log P ^ 3))
      atTop (𝓝 2) := by
  have hinv : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have h := ((tendsto_const_nhds (x := (2 : ℝ)) (f := atTop)).add
    (hinv.const_mul 6)).add (prime_counting_four_terms.mul (hinv.pow 2))
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [centeredThreshold, countingPolynomial]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
  ring

private lemma rounded_excess :
    Tendsto (fun P : ℝ => primeExcess P / (P / log P ^ 3)) atTop (𝓝 2) := by
  have hlog : Tendsto (fun P : ℝ => log P ^ 3 / P) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (↑(3 : ℕ)) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hsmall : Tendsto
      (fun P : ℝ => ((centeredCount P : ℝ) - centeredThreshold P) / (P / log P ^ 3))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlog
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      exact div_nonneg (count_rounding hP).1.le
        (div_nonneg (by linarith) (pow_nonneg (log_pos hP).le _))
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      calc
        _ ≤ 1 / (P / log P ^ 3) :=
          div_le_div_of_nonneg_right (count_rounding hP).2
            (div_nonneg (by linarith) (pow_nonneg (log_pos hP).le _))
        _ = log P ^ 3 / P := by rw [one_div, inv_div]
  simpa only [sub_zero, ← sub_div, sub_sub_sub_cancel_right, primeExcess] using
    continuous_excess.sub hsmall

/-- The rounded excess and all three centered reserves have their exact leading constants. -/
theorem centered_reserve :
    Tendsto (fun P : ℝ => primeExcess P / (P / log P ^ 3)) atTop (𝓝 2) ∧
    (∀ P : ℝ, 1 < P → centeredCount P = ⌊centeredThreshold P⌋₊ + 1 ∧
      0 < (centeredCount P : ℝ) - centeredThreshold P ∧
        (centeredCount P : ℝ) - centeredThreshold P ≤ 1) ∧
    (∀ᶠ P : ℝ in atTop, 0 ≤ primeExcess P ∧ (deletionCount P : ℝ) = primeExcess P) ∧
    Tendsto (fun P : ℝ => continuousReserve P / (P / log P ^ 2)) atTop (𝓝 2) ∧
    Tendsto (fun P : ℝ => roundedReserve P / (P / log P ^ 2)) atTop (𝓝 2) ∧
    Tendsto (fun P : ℝ => safeReserve P / (P / log P ^ 2)) atTop (𝓝 2) := by
  have hgap : Tendsto (fun P : ℝ => (P - Chebyshev.theta P) / (P / log P ^ 2))
      atTop (𝓝 0) := by
    simpa only [← neg_div, neg_sub, neg_zero] using
      ((theta_error_log_power 2).tendsto_div_nhds_zero).neg
  have hhalf : Tendsto (fun P : ℝ => log (P / 2) / log P) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
      (tendsto_log_atTop.const_div_atTop (log 2))
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    rw [log_div (by linarith : P ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      sub_div, div_self (log_pos hP).ne']
  refine ⟨rounded_excess, fun P hP => ⟨centeredCount_floor P, count_rounding hP⟩,
    ?_, ?_, ?_, ?_⟩
  · filter_upwards [rounded_excess.eventually_const_lt (by norm_num : (0 : ℝ) < 2),
      eventually_gt_atTop (1 : ℝ)] with P hE hP
    have hpos : 0 < primeExcess P :=
      (div_pos_iff_of_pos_right (div_pos (by linarith) (pow_pos (log_pos hP) _))).mp hE
    have hle : centeredCount P ≤ Nat.primeCounting ⌊P⌋₊ := by
      have h : (centeredCount P : ℝ) ≤ (Nat.primeCounting ⌊P⌋₊ : ℝ) :=
        sub_nonneg.mp hpos.le
      exact_mod_cast h
    exact ⟨hpos.le, Nat.cast_sub hle⟩
  · have h := hgap.add continuous_excess
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [continuousReserve]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  · have h := hgap.add rounded_excess
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [roundedReserve]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  · have h := hgap.add (rounded_excess.mul hhalf)
    rw [mul_one, zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [safeReserve]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring

/-- There is a far deletion of the required size. Every such deletion has the same retained
cardinality and satisfies the stated log budget. -/
theorem far_deletion :
    ∀ᶠ P : ℝ in atTop,
      (∀ p : ℕ, p ∈ primeInterval (P / 2) (3 / 4 * P) ↔
        P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * P ∧ p.Prime) ∧
      (∃ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount P) ∧
      ∀ R ⊆ primeInterval (P / 2) (3 / 4 * P), R.card = deletionCount P →
        (Nat.primesLE ⌊P⌋₊ \ R).card = centeredCount P ∧
          (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) ≤ P - safeReserve P := by
  have hcap : Tendsto
      (fun P : ℝ => ((primeInterval (P / 2) (3 / 4 * P)).card : ℝ) / (P / log P))
      atTop (𝓝 (1 / 4)) := by
    have h := (primeInterval_capacity (a := 1 / 2) (b := 3 / 4)
      (by norm_num) (by norm_num)).comp tendsto_exp_atTop
    rw [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at h
    simpa only [Function.comp_def, scale, log_exp, div_eq_mul_inv, one_mul,
      mul_comm (2 : ℝ)⁻¹] using h
  obtain ⟨hE, _, hcast, _⟩ := centered_reserve
  have hinv : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have hexcess : Tendsto (fun P : ℝ => (deletionCount P : ℝ) / (P / log P))
      atTop (𝓝 0) := by
    have h := hE.mul (hinv.pow 2)
    norm_num at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hcast] with P hP hcastP
    rw [hcastP.2]
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  filter_upwards [hexcess.eventually_lt hcap (by norm_num), hcast,
    eventually_gt_atTop (1 : ℝ)] with P hfit hcastP hP
  have hPpos : 0 < P := by linarith
  have hscale : 0 < P / log P := div_pos hPpos (log_pos hP)
  have hroom : deletionCount P ≤ (primeInterval (P / 2) (3 / 4 * P)).card := by
    exact_mod_cast ((div_lt_div_iff_of_pos_right hscale).mp hfit).le
  have hmem (p : ℕ) : p ∈ primeInterval (P / 2) (3 / 4 * P) ↔
      P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * P ∧ p.Prime := by
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc, and_assoc]
    rw [Nat.floor_lt (by positivity : 0 ≤ P / 2),
      Nat.le_floor_iff (by positivity : 0 ≤ 3 / 4 * P)]
  refine ⟨hmem, Finset.exists_subset_card_eq hroom, ?_⟩
  intro R hR hcard
  have hsub : R ⊆ Nat.primesLE ⌊P⌋₊ := by
    intro p hp
    obtain ⟨_, hhi, hprime⟩ := (hmem p).mp (hR hp)
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (by linarith), hprime⟩
  have hk : centeredCount P ≤ Nat.primeCounting ⌊P⌋₊ := by
    have h : (centeredCount P : ℝ) ≤ (Nat.primeCounting ⌊P⌋₊ : ℝ) :=
      sub_nonneg.mp hcastP.1
    exact_mod_cast h
  constructor
  · rw [Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting, hcard,
      deletionCount, Nat.sub_sub_self hk]
  · have hremoved : primeExcess P * log (P / 2) ≤ ∑ p ∈ R, log (p : ℝ) := by
      rw [← hcastP.2, ← hcard]
      calc
        _ = ∑ _p ∈ R, log (P / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun p hp =>
          log_le_log (by positivity) ((hmem p).mp (hR hp)).1.le
    have hsplit := Finset.sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ))
    rw [← Chebyshev.theta_eq_sum_primesLE] at hsplit
    unfold safeReserve
    linarith

end D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
