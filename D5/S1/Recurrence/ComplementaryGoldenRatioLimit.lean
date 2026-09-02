/- GID: D5/S1/Recurrence/ComplementaryGoldenRatioLimit
   generality: G
   mirror-B: D5/B/S1/Recurrence/ComplementaryGoldenRatioLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Vanishing relative errors preserve the golden ratio limit. -/

import Mathlib

/- Library-search audit trail (2026-09-02):
   * Repository search found no theorem for a positive Fibonacci recurrence
     with a vanishing signed relative perturbation.
   * Pinned Mathlib provides `tendsto_fib_succ_div_fib_atTop` for the
     unperturbed recurrence and `tendsto_pow_atTop_nhds_zero_of_lt_one` for
     geometric decay, but no nonautonomous perturbed-ratio theorem.
   * Pinned Mathlib provides `Nat.nth`, `Nat.nth_strictMono`,
     `Nat.nth_mem_of_infinite`, and `Nat.count_nth_of_infinite`; the concrete
     OEIS construction below instead uses an executable finite positive-mex
     scan so that its published initial values can be kernel-checked.
   * Golden-ratio algebra reuses `Real.goldenRatio_sq`,
     `Real.goldenRatio_pos`, and `Real.one_lt_goldenRatio`.
   * No repository or pinned-Mathlib definition of complementary sequences or
     positive mex was found. -/

namespace D5.S1.Recurrence.ComplementaryGoldenRatioLimit

open Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Scan successive candidates, stopping at the first one outside `used`.
The public positive-mex function supplies one more candidate than `used` has
elements, so the zero-fuel fallback is unreachable. -/
def mexScan (used : Finset ℕ) : ℕ → ℕ → ℕ
  | 0, candidate => candidate
  | fuel + 1, candidate =>
      if candidate ∈ used then mexScan used fuel (candidate + 1) else candidate

/-- The least positive natural number outside a finite set. -/
def mexPos (used : Finset ℕ) : ℕ :=
  mexScan used (used.card + 1) 1

/-- `false` selects A293317 (the `-1` recurrence), while `true` selects
A293316 (the `+1` recurrence). Each state contains both prefixes through the
displayed index. -/
def complementaryState (plusOne : Bool) : ℕ → List ℕ × List ℕ
  | 0 => ([1], [2])
  | 1 => ([1, 3], [2, 4])
  | n + 2 =>
      let previous := complementaryState plusOne (n + 1)
      let nextA :=
        previous.1.getD (n + 1) 0 + previous.1.getD n 0 +
          previous.2.getD n 0 + if plusOne then 1 else 0
      let nextA := if plusOne then nextA else nextA - 1
      let nextB := mexPos (insert nextA (previous.1 ++ previous.2).toFinset)
      (previous.1 ++ [nextA], previous.2 ++ [nextB])

/-- The `a` sequence for either Kimberling recurrence. -/
def kimberlingA (plusOne : Bool) (n : ℕ) : ℕ :=
  (complementaryState plusOne n).1.getD n 0

/-- The complementary `b` sequence for either Kimberling recurrence. -/
def kimberlingB (plusOne : Bool) (n : ℕ) : ℕ :=
  (complementaryState plusOne n).2.getD n 0

/-- Executable statement echo for OEIS A293317 through index 12. -/
theorem A293317_data_through_twelve :
    List.ofFn (fun i : Fin 13 => kimberlingA false i) =
      [1, 3, 5, 11, 21, 38, 66, 112, 187, 310, 509, 832, 1355] := by
  decide

/-- Executable statement echo for OEIS A293316 through index 12. -/
theorem A293316_data_through_twelve :
    List.ofFn (fun i : Fin 13 => kimberlingA true i) =
      [1, 3, 7, 15, 28, 50, 87, 147, 245, 404, 662, 1080, 1757] := by
  decide

theorem mexScan_bounds (used : Finset ℕ) (fuel candidate : ℕ) :
    candidate ≤ mexScan used fuel candidate ∧
      mexScan used fuel candidate ≤ candidate + fuel := by
  induction fuel generalizing candidate with
  | zero => simp [mexScan]
  | succ fuel ih =>
      simp only [mexScan]
      split_ifs
      · have hbounds := ih (candidate + 1)
        omega
      · omega

theorem mexPos_pos (used : Finset ℕ) : 1 ≤ mexPos used := by
  exact (mexScan_bounds used (used.card + 1) 1).1

theorem mexPos_le_card_add_two (used : Finset ℕ) :
    mexPos used ≤ used.card + 2 := by
  have hbound := (mexScan_bounds used (used.card + 1) 1).2
  simpa [mexPos, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

theorem state_length (plusOne : Bool) (n : ℕ) :
    (complementaryState plusOne n).1.length = n + 1 ∧
      (complementaryState plusOne n).2.length = n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [complementaryState]
  | one => simp [complementaryState]
  | more n _ ih =>
      simp [complementaryState, ih]

theorem state_succ_append (plusOne : Bool) (n : ℕ) :
    ∃ nextA nextB,
      complementaryState plusOne (n + 1) =
        ((complementaryState plusOne n).1 ++ [nextA],
          (complementaryState plusOne n).2 ++ [nextB]) := by
  cases n with
  | zero =>
      exact ⟨3, 4, by simp [complementaryState]⟩
  | succ n =>
      exact ⟨_, _, rfl⟩

theorem state_succ_getD_first (plusOne : Bool) (n : ℕ) :
    (complementaryState plusOne (n + 1)).1.getD n 0 =
      kimberlingA plusOne n := by
  obtain ⟨nextA, nextB, hstate⟩ := state_succ_append plusOne n
  rw [hstate]
  unfold kimberlingA
  apply List.getD_append
  rw [(state_length plusOne n).1]
  omega

theorem state_succ_getD_second (plusOne : Bool) (n : ℕ) :
    (complementaryState plusOne (n + 1)).2.getD n 0 =
      kimberlingB plusOne n := by
  obtain ⟨nextA, nextB, hstate⟩ := state_succ_append plusOne n
  rw [hstate]
  unfold kimberlingB
  apply List.getD_append
  rw [(state_length plusOne n).2]
  omega

theorem b_pos (plusOne : Bool) (n : ℕ) : 1 ≤ kimberlingB plusOne n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [kimberlingB, complementaryState]
  | one => simp [kimberlingB, complementaryState]
  | more n _ _ =>
      unfold kimberlingB
      rw [complementaryState]
      dsimp only
      rw [List.getD_append_right]
      · rw [(state_length plusOne (n + 1)).2]
        have hindex : n + 2 - (n + 1 + 1) = 0 := by omega
        rw [hindex]
        simpa using mexPos_pos _
      · rw [(state_length plusOne (n + 1)).2]

theorem a_rec_false (n : ℕ) :
    kimberlingA false (n + 2) + 1 =
      kimberlingA false (n + 1) + kimberlingA false n +
        kimberlingB false n := by
  change (complementaryState false (n + 2)).1.getD (n + 2) 0 + 1 = _
  rw [complementaryState]
  dsimp only
  rw [List.getD_append_right]
  · rw [(state_length false (n + 1)).1]
    have hindex : n + 2 - (n + 1 + 1) = 0 := by omega
    rw [hindex]
    simp only [List.getD_cons_zero]
    simp only [if_neg (by decide : false ≠ true)]
    rw [state_succ_getD_first, state_succ_getD_second]
    have hpositive := b_pos false n
    simp only [add_zero]
    exact Nat.sub_add_cancel (by omega)
  · rw [(state_length false (n + 1)).1]

theorem a_rec_true (n : ℕ) :
    kimberlingA true (n + 2) =
      kimberlingA true (n + 1) + kimberlingA true n +
        kimberlingB true n + 1 := by
  change (complementaryState true (n + 2)).1.getD (n + 2) 0 = _
  rw [complementaryState]
  dsimp only
  rw [List.getD_append_right]
  · rw [(state_length true (n + 1)).1]
    have hindex : n + 2 - (n + 1 + 1) = 0 := by omega
    rw [hindex]
    simp only [List.getD_cons_zero]
    simp only [if_true]
    rw [state_succ_getD_first, state_succ_getD_second]
    change kimberlingA true (n + 1) + kimberlingA true n +
        kimberlingB true n + 1 = _
    rfl
  · rw [(state_length true (n + 1)).1]

theorem a_pos (plusOne : Bool) (n : ℕ) : 1 ≤ kimberlingA plusOne n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [kimberlingA, complementaryState]
  | one => simp [kimberlingA, complementaryState]
  | more n hn _ =>
      cases plusOne with
      | false =>
          have hrec := a_rec_false n
          have hb := b_pos false n
          omega
      | true =>
          have hrec := a_rec_true n
          omega

theorem a_mono_succ (plusOne : Bool) (n : ℕ) :
    kimberlingA plusOne n ≤ kimberlingA plusOne (n + 1) := by
  cases n with
  | zero =>
      cases plusOne <;> simp [kimberlingA, complementaryState]
  | succ n =>
      cases plusOne with
      | false =>
          have hrec := a_rec_false n
          have hb := b_pos false n
          change kimberlingA false (n + 1) ≤
            kimberlingA false (n + 2)
          omega
      | true =>
          have hrec := a_rec_true n
          change kimberlingA true (n + 1) ≤
            kimberlingA true (n + 2)
          omega

theorem a_two_step (plusOne : Bool) (n : ℕ) :
    2 * kimberlingA plusOne n ≤ kimberlingA plusOne (n + 2) := by
  cases plusOne with
  | false =>
      have hrec := a_rec_false n
      have hb := b_pos false n
      have hmono := a_mono_succ false n
      omega
  | true =>
      have hrec := a_rec_true n
      have hmono := a_mono_succ true n
      omega

theorem a_ge_geometric (plusOne : Bool) (n : ℕ) :
    (6 / 5 : ℝ) ^ n ≤ kimberlingA plusOne n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [kimberlingA, complementaryState]
  | one => norm_num [kimberlingA, complementaryState]
  | more n hn _ =>
      have htwo := a_two_step plusOne n
      calc
        (6 / 5 : ℝ) ^ (n + 2) = (6 / 5 : ℝ) ^ n * (36 / 25) := by
          rw [pow_add]
          norm_num
        _ ≤ (6 / 5 : ℝ) ^ n * 2 := by
          exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ ≤ (kimberlingA plusOne n : ℝ) * 2 := by
          exact mul_le_mul_of_nonneg_right hn (by norm_num)
        _ = (2 * kimberlingA plusOne n : ℕ) := by
          push_cast
          ring
        _ ≤ kimberlingA plusOne (n + 2) := by exact_mod_cast htwo

theorem b_linear (plusOne : Bool) (n : ℕ) :
    kimberlingB plusOne n ≤ 2 * n + 4 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [kimberlingB, complementaryState]
  | one => simp [kimberlingB, complementaryState]
  | more n _ _ =>
      unfold kimberlingB
      rw [complementaryState]
      dsimp only
      rw [List.getD_append_right]
      · rw [(state_length plusOne (n + 1)).2]
        have hindex : n + 2 - (n + 1 + 1) = 0 := by omega
        rw [hindex]
        simp only [List.getD_cons_zero]
        have hfinset := List.toFinset_card_le
          ((complementaryState plusOne (n + 1)).1 ++
            (complementaryState plusOne (n + 1)).2)
        rw [List.length_append, (state_length plusOne (n + 1)).1,
          (state_length plusOne (n + 1)).2] at hfinset
        refine (mexPos_le_card_add_two _).trans ?_
        have hinsert := Finset.card_insert_le
          (if plusOne then
            (complementaryState plusOne (n + 1)).1.getD (n + 1) 0 +
                (complementaryState plusOne (n + 1)).1.getD n 0 +
              (complementaryState plusOne (n + 1)).2.getD n 0 +
                if plusOne then 1 else 0
          else
            ((complementaryState plusOne (n + 1)).1.getD (n + 1) 0 +
                (complementaryState plusOne (n + 1)).1.getD n 0 +
              (complementaryState plusOne (n + 1)).2.getD n 0 +
                if plusOne then 1 else 0) - 1)
          (((complementaryState plusOne (n + 1)).1 ++
            (complementaryState plusOne (n + 1)).2).toFinset)
        omega
      · rw [(state_length plusOne (n + 1)).2]

theorem linear_over_geometric_tendsto :
    Tendsto
      (fun n : ℕ =>
        (2 * (n : ℝ) + 5) / (6 / 5 : ℝ) ^ (n + 1))
      atTop (nhds 0) := by
  have hlinear :
      Tendsto (fun n : ℕ => (n : ℝ) / (6 / 5 : ℝ) ^ n)
        atTop (nhds 0) := by
    simpa using
      tendsto_pow_const_div_const_pow_of_one_lt 1
        (by norm_num : (1 : ℝ) < 6 / 5)
  have hconstant :
      Tendsto (fun n : ℕ => (1 : ℝ) / (6 / 5 : ℝ) ^ n)
        atTop (nhds 0) := by
    simpa using
      tendsto_pow_const_div_const_pow_of_one_lt 0
        (by norm_num : (1 : ℝ) < 6 / 5)
  have hsum :=
    (hlinear.const_mul (5 / 3 : ℝ)).add
      (hconstant.const_mul (25 / 6 : ℝ))
  convert hsum using 1
  · funext n
    field_simp [show (6 / 5 : ℝ) ≠ 0 by norm_num]
    ring
  · norm_num

theorem b_add_one_relative_error_tendsto (plusOne : Bool) :
    Tendsto
      (fun n =>
        ((kimberlingB plusOne n : ℝ) + 1) /
          kimberlingA plusOne (n + 1))
      atTop (nhds 0) := by
  refine squeeze_zero ?_ ?_ linear_over_geometric_tendsto
  · intro n
    have ha : (0 : ℝ) < kimberlingA plusOne (n + 1) := by
      exact_mod_cast a_pos plusOne (n + 1)
    exact div_nonneg (by positivity) ha.le
  · intro n
    have hbNat : kimberlingB plusOne n + 1 ≤ 2 * n + 5 := by
      have hb := b_linear plusOne n
      omega
    have hb :
        (kimberlingB plusOne n : ℝ) + 1 ≤ 2 * (n : ℝ) + 5 := by
      exact_mod_cast hbNat
    have ha := a_ge_geometric plusOne (n + 1)
    have hpower : (0 : ℝ) < (6 / 5 : ℝ) ^ (n + 1) := by positivity
    calc
      ((kimberlingB plusOne n : ℝ) + 1) /
            kimberlingA plusOne (n + 1) ≤
          ((kimberlingB plusOne n : ℝ) + 1) /
            (6 / 5 : ℝ) ^ (n + 1) :=
        div_le_div_of_nonneg_left (by positivity) hpower ha
      _ ≤ (2 * (n : ℝ) + 5) / (6 / 5 : ℝ) ^ (n + 1) :=
        div_le_div_of_nonneg_right hb hpower.le

/-- A nonnegative sequence driven by a strict affine contraction and a
vanishing additive error tends to zero. -/
theorem vanishing_affine_error {d error : ℕ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hd : ∀ n, 0 ≤ d n)
    (herror : Tendsto error atTop (nhds 0))
    (hstep : ∀ᶠ n in atTop, d (n + 1) ≤ q * d n + |error n|) :
    Tendsto d atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have herrorScale : 0 < (1 - q) * (epsilon / 2) :=
    mul_pos (sub_pos.mpr hq1) hhalf
  obtain ⟨errorIndex, herrorIndex⟩ :=
    Metric.tendsto_atTop.1 herror ((1 - q) * (epsilon / 2)) herrorScale
  obtain ⟨stepIndex, hstepIndex⟩ := eventually_atTop.1 hstep
  let start := max errorIndex stepIndex
  have herrorTail (n : ℕ) (hn : start ≤ n) :
      |error n| < (1 - q) * (epsilon / 2) := by
    have hdist := herrorIndex n (le_trans (le_max_left _ _) hn)
    simpa [Real.dist_eq] using hdist
  have hstepTail (n : ℕ) (hn : start ≤ n) :
      d (n + 1) ≤ q * d n + |error n| :=
    hstepIndex n (le_trans (le_max_right _ _) hn)
  have hpowerLimit :
      Tendsto (fun k : ℕ => q ^ k * d start) atTop (nhds 0) :=
    by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (d start)
  obtain ⟨powerIndex, hpowerIndex⟩ :=
    Metric.tendsto_atTop.1 hpowerLimit (epsilon / 2) hhalf
  have hbound : ∀ k : ℕ,
      d (start + k) ≤
        q ^ k * d start + (epsilon / 2) * (1 - q ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          d (start + (k + 1)) = d ((start + k) + 1) := by
            simp [Nat.add_assoc]
          _ ≤ q * d (start + k) + |error (start + k)| :=
            hstepTail (start + k) (by omega)
          _ ≤ q * (q ^ k * d start + (epsilon / 2) * (1 - q ^ k)) +
                (1 - q) * (epsilon / 2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left ih hq0)
              (herrorTail (start + k) (by omega)).le
          _ = q ^ (k + 1) * d start +
                (epsilon / 2) * (1 - q ^ (k + 1)) := by ring
  refine ⟨start + powerIndex, ?_⟩
  intro n hn
  let k := n - start
  have hk : powerIndex ≤ k := by
    dsimp [k]
    omega
  have hstartk : start + k = n := by
    dsimp [k]
    omega
  have hpowerDist := hpowerIndex k hk
  have hpowerNonnegative : 0 ≤ q ^ k * d start :=
    mul_nonneg (pow_nonneg hq0 k) (hd start)
  have hpowerSmall : q ^ k * d start < epsilon / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpowerNonnegative] at hpowerDist
    exact hpowerDist
  have hqPowerNonnegative : 0 ≤ q ^ k := pow_nonneg hq0 k
  have hqPowerLeOne : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd n)]
  rw [← hstartk]
  have := hbound k
  nlinarith

/-- Positive Fibonacci recurrences retain the golden consecutive-ratio limit
when the signed perturbation is negligible relative to the next denominator. -/
theorem perturbed_fibonacci_ratio {x error : ℕ → ℝ}
    (hx : ∀ n, 0 < x n)
    (hrec : ∀ n, x (n + 2) = x (n + 1) + x n + error n)
    (herror : Tendsto (fun n => error n / x (n + 1)) atTop (nhds 0)) :
    Tendsto (fun n => x (n + 1) / x n) atTop
      (nhds Real.goldenRatio) := by
  let ratio : ℕ → ℝ := fun n => x (n + 1) / x n
  let relativeError : ℕ → ℝ := fun n => error n / x (n + 1)
  have hratioPositive (n : ℕ) : 0 < ratio n := by
    exact div_pos (hx (n + 1)) (hx n)
  have hratioRecurrence (n : ℕ) :
      ratio (n + 1) = 1 + 1 / ratio n + relativeError n := by
    dsimp [ratio, relativeError]
    rw [show n + 1 + 1 = n + 2 by omega, hrec n]
    field_simp [ne_of_gt (hx n), ne_of_gt (hx (n + 1))]
  have hrelativeError : Tendsto relativeError atTop (nhds 0) := herror
  obtain ⟨errorIndex, herrorIndex⟩ :=
    Metric.tendsto_atTop.1 hrelativeError (1 / 10 : ℝ) (by norm_num)
  have herrorSmall (n : ℕ) (hn : errorIndex ≤ n) :
      |relativeError n| < (1 / 10 : ℝ) := by
    have hdist := herrorIndex n hn
    simpa [Real.dist_eq] using hdist
  have hfirstLower (n : ℕ) (hn : errorIndex ≤ n) :
      (9 / 10 : ℝ) ≤ ratio (n + 1) := by
    have hinverse : 0 < 1 / ratio n := one_div_pos.mpr (hratioPositive n)
    have hsmall := (abs_lt.mp (herrorSmall n hn)).1
    rw [hratioRecurrence n]
    nlinarith
  have hupper (n : ℕ) (hn : errorIndex ≤ n) : ratio (n + 2) ≤ 3 := by
    have hpositive := hratioPositive (n + 1)
    have hlower := hfirstLower n hn
    have hinverse : 1 / ratio (n + 1) ≤ (10 / 9 : ℝ) := by
      apply (div_le_iff₀ hpositive).2
      nlinarith
    have hsmall := (abs_lt.mp (herrorSmall (n + 1) (by omega))).2
    rw [show n + 2 = (n + 1) + 1 by omega, hratioRecurrence (n + 1)]
    nlinarith
  have hlower (n : ℕ) (hn : errorIndex ≤ n) :
      (6 / 5 : ℝ) ≤ ratio (n + 3) := by
    have hpositive := hratioPositive (n + 2)
    have hbounded := hupper n hn
    have hinverse : (1 / 3 : ℝ) ≤ 1 / ratio (n + 2) := by
      apply (div_le_div_iff₀ (by norm_num) hpositive).2
      nlinarith
    have hsmall := (abs_lt.mp (herrorSmall (n + 2) (by omega))).1
    rw [show n + 3 = (n + 2) + 1 by omega, hratioRecurrence (n + 2)]
    nlinarith
  have hinterval : ∀ᶠ n in atTop,
      (6 / 5 : ℝ) ≤ ratio n ∧ ratio n ≤ 3 := by
    refine eventually_atTop.2 ⟨errorIndex + 3, ?_⟩
    intro n hn
    have hbase : errorIndex ≤ n - 3 := by omega
    constructor
    · simpa only [show n - 3 + 3 = n by omega] using hlower (n - 3) hbase
    · have hbase' : errorIndex ≤ n - 2 := by omega
      simpa only [show n - 2 + 2 = n by omega] using hupper (n - 2) hbase'
  have hgoldenContraction (y : ℝ) (hy : (6 / 5 : ℝ) ≤ y) :
      |(1 + 1 / y) - Real.goldenRatio| ≤
        (5 / 6 : ℝ) * |y - Real.goldenRatio| := by
    have hyPositive : 0 < y := lt_of_lt_of_le (by norm_num) hy
    have hfixed : 1 + 1 / Real.goldenRatio = Real.goldenRatio := by
      calc
        1 + 1 / Real.goldenRatio =
            (Real.goldenRatio + 1) / Real.goldenRatio := by
              field_simp [Real.goldenRatio_ne_zero]
        _ = Real.goldenRatio ^ 2 / Real.goldenRatio := by
              rw [Real.goldenRatio_sq]
        _ = Real.goldenRatio := by
              field_simp [Real.goldenRatio_ne_zero]
    have hidentity :
        1 + 1 / y - Real.goldenRatio =
          -(y - Real.goldenRatio) / (y * Real.goldenRatio) := by
      calc
        1 + 1 / y - Real.goldenRatio =
            1 / y - 1 / Real.goldenRatio := by nlinarith [hfixed]
        _ = -(y - Real.goldenRatio) / (y * Real.goldenRatio) := by
            field_simp [ne_of_gt hyPositive, Real.goldenRatio_ne_zero]
            ring
    rw [hidentity, abs_div, abs_neg, abs_mul, abs_of_pos hyPositive,
      abs_of_pos Real.goldenRatio_pos, div_eq_mul_inv]
    have hyLeProduct : y ≤ y * Real.goldenRatio := by
      nlinarith [mul_pos hyPositive (sub_pos.mpr Real.one_lt_goldenRatio)]
    have hdenominator : (6 / 5 : ℝ) ≤ y * Real.goldenRatio :=
      hy.trans hyLeProduct
    have hinverse : (y * Real.goldenRatio)⁻¹ ≤ (5 / 6 : ℝ) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (mul_pos hyPositive Real.goldenRatio_pos)).2
      nlinarith
    rw [mul_comm (5 / 6 : ℝ) |y - Real.goldenRatio|]
    exact mul_le_mul_of_nonneg_left hinverse (abs_nonneg _)
  have hdistanceStep : ∀ᶠ n in atTop,
      |ratio (n + 1) - Real.goldenRatio| ≤
        (5 / 6 : ℝ) * |ratio n - Real.goldenRatio| + |relativeError n| := by
    filter_upwards [hinterval] with n hn
    calc
      |ratio (n + 1) - Real.goldenRatio| =
          |(1 + 1 / ratio n - Real.goldenRatio) + relativeError n| := by
        rw [hratioRecurrence n]
        congr 1
        ring
      _ ≤ |1 + 1 / ratio n - Real.goldenRatio| + |relativeError n| :=
        abs_add_le _ _
      _ ≤ (5 / 6 : ℝ) * |ratio n - Real.goldenRatio| + |relativeError n| :=
        add_le_add (hgoldenContraction (ratio n) hn.1) le_rfl
  have habsoluteLimit :
      Tendsto (fun n => |ratio n - Real.goldenRatio|) atTop (nhds 0) :=
    vanishing_affine_error (q := (5 / 6 : ℝ))
      (by norm_num) (by norm_num) (fun n => abs_nonneg _)
      hrelativeError hdistanceStep
  apply tendsto_iff_dist_tendsto_zero.2
  simpa [Real.dist_eq] using habsoluteLimit

/-- The consecutive ratios of OEIS A293317 tend to the golden ratio. -/
theorem A293317_ratio_tendsto :
    Tendsto
      (fun n => (kimberlingA false (n + 1) : ℝ) /
        kimberlingA false n)
      atTop (nhds Real.goldenRatio) := by
  apply perturbed_fibonacci_ratio
    (x := fun n => (kimberlingA false n : ℝ))
    (error := fun n => (kimberlingB false n : ℝ) - 1)
  · intro n
    exact_mod_cast a_pos false n
  · intro n
    have hrec := congrArg (fun k : ℕ => (k : ℝ)) (a_rec_false n)
    push_cast at hrec
    linarith
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun n => abs_nonneg _) ?_
      (b_add_one_relative_error_tendsto false)
    intro n
    have ha : (0 : ℝ) < kimberlingA false (n + 1) := by
      exact_mod_cast a_pos false (n + 1)
    change
      |((kimberlingB false n : ℝ) - 1) /
          kimberlingA false (n + 1)| ≤ _
    rw [abs_div, abs_of_pos ha]
    apply div_le_div_of_nonneg_right _ ha.le
    calc
      |(kimberlingB false n : ℝ) - 1| ≤
          |(kimberlingB false n : ℝ)| + |(1 : ℝ)| := abs_sub _ _
      _ = (kimberlingB false n : ℝ) + 1 := by simp

/-- The consecutive ratios of OEIS A293316 tend to the golden ratio. -/
theorem A293316_ratio_tendsto :
    Tendsto
      (fun n => (kimberlingA true (n + 1) : ℝ) /
        kimberlingA true n)
      atTop (nhds Real.goldenRatio) := by
  apply perturbed_fibonacci_ratio
    (x := fun n => (kimberlingA true n : ℝ))
    (error := fun n => (kimberlingB true n : ℝ) + 1)
  · intro n
    exact_mod_cast a_pos true n
  · intro n
    exact_mod_cast a_rec_true n
  · exact b_add_one_relative_error_tendsto true

/-- The two complementary Kimberling sequences satisfy their conjectured
golden consecutive-ratio limits. -/
theorem kimberling_complementary_golden_limits :
    Tendsto
        (fun n => (kimberlingA false (n + 1) : ℝ) /
          kimberlingA false n)
        atTop (nhds Real.goldenRatio) ∧
      Tendsto
        (fun n => (kimberlingA true (n + 1) : ℝ) /
          kimberlingA true n)
        atTop (nhds Real.goldenRatio) :=
  ⟨A293317_ratio_tendsto, A293316_ratio_tendsto⟩

#print axioms A293317_ratio_tendsto
#print axioms A293316_ratio_tendsto

end D5.S1.Recurrence.ComplementaryGoldenRatioLimit
