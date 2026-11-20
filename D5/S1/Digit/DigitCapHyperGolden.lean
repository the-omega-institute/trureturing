import D5.S1.Digit.DigitCapSubcritical
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Digit.DigitCapHyperGolden

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapSubcritical (low count_rec)
open Finset

noncomputable section

/-- The sum of the last `L` values of `count ell ell` ending at `q`. -/
private def win (ell L q : ℕ) : ℕ :=
  ∑ j ∈ (range L).filter (· ≤ q), count ell ell (q - j)

/-- The number of admissible digit lifts of a residue `r` under the cap `ell`. -/
private def lifts (r : ℕ) : ℕ := if r = 0 then 2 else 1

private lemma cap_iff (ell r j : ℕ) (hell : 2 ≤ ell) (hr : r < ell) :
    r + ell * j ≤ ell ↔ j < lifts r := by
  unfold lifts
  split_ifs with h
  · subst h
    constructor
    · intro hle
      by_contra hj
      rw [not_lt] at hj
      nlinarith
    · intro hj
      interval_cases j <;> simp
  · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero h
    constructor
    · intro hle
      by_contra hj
      rw [not_lt] at hj
      nlinarith
    · intro hj
      have : j = 0 := by omega
      subst this; simp; omega

/-- Lowest-digit recursion for the cap `ell`. -/
private lemma count_digit (ell q r : ℕ) (hell : 2 ≤ ell) (hr : r < ell) :
    count ell ell (ell * q + r) = win ell (lifts r) q := by
  rw [count_rec _ _ _ hell]
  unfold win
  symm
  have hmod : (ell * q + r) % ell = r := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  apply Finset.sum_nbij' (fun j => r + ell * j) (fun d => d / ell)
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    simp only [low, mem_filter, mem_range]
    refine ⟨Nat.lt_succ_of_le ((cap_iff ell r j hell hr).mpr hj.1), ?_, ?_⟩
    · nlinarith [hj.2]
    · rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  · intro d hd
    simp only [low, mem_filter, mem_range] at hd
    simp only [mem_filter, mem_range]
    rw [hmod] at hd
    have hd' : r + ell * (d / ell) = d := by
      have := Nat.mod_add_div d ell
      rw [hd.2.2] at this; exact this
    refine ⟨(cap_iff ell r _ hell hr).mp (by rw [hd']; omega), ?_⟩
    have h1 : d / ell ≤ (ell * q + r) / ell := Nat.div_le_div_right hd.2.1
    rwa [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero] at h1
  · intro j _
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]
  · intro d hd
    simp only [low, mem_filter, mem_range] at hd
    rw [hmod] at hd
    have := Nat.mod_add_div d ell
    rw [hd.2.2] at this; exact this
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    congr 1
    have : ell * q + r - (r + ell * j) = ell * (q - j) := by
      rw [Nat.mul_sub]; omega
    rw [this, Nat.mul_div_cancel_left _ (by omega)]

private lemma win_one (ell q : ℕ) : win ell 1 q = count ell ell q := by
  unfold win
  rw [show (range 1).filter (· ≤ q) = {0} by ext j; simp only [mem_filter, mem_range, mem_singleton]; omega]
  simp

private lemma win_two_zero (ell : ℕ) : win ell 2 0 = count ell ell 0 := by
  unfold win
  rw [show (range 2).filter (· ≤ 0) = {0} by ext j; simp only [mem_filter, mem_range, mem_singleton]; omega]
  simp

private lemma win_two (ell q : ℕ) (hq : 1 ≤ q) :
    win ell 2 q = count ell ell q + count ell ell (q - 1) := by
  unfold win
  rw [show (range 2).filter (· ≤ q) = range 2 by
    apply Finset.filter_true_of_mem; intro j hj; simp at hj; omega]
  simp [Finset.sum_range_succ]

/-- A last digit `0` reads the pair window; any other last digit reads one value. -/
private lemma count_zero_digit (ell q : ℕ) (hell : 2 ≤ ell) :
    count ell ell (ell * q) = win ell 2 q := by
  have := count_digit ell q 0 hell (by omega)
  simpa [lifts] using this

private lemma count_pos_digit (ell q r : ℕ) (hell : 2 ≤ ell) (hr : r < ell) (h0 : r ≠ 0) :
    count ell ell (ell * q + r) = count ell ell q := by
  rw [count_digit ell q r hell hr, show lifts r = 1 by simp [lifts, h0], win_one]

private lemma count_le_win (ell n : ℕ) (hell : 2 ≤ ell) :
    count ell ell n ≤ win ell 2 (n / ell) := by
  have h := count_digit ell (n / ell) (n % ell) hell (Nat.mod_lt _ (by omega))
  rw [Nat.div_add_mod] at h
  rw [h]
  unfold win lifts
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [mem_filter, mem_range] at hj ⊢
  refine ⟨?_, hj.2⟩
  split_ifs at hj <;> omega

private lemma count_eq_parent (ell n : ℕ) (hell : 2 ≤ ell) (hn : n % ell ≠ 0) :
    count ell ell n = count ell ell (n / ell) := by
  have h := count_pos_digit ell (n / ell) (n % ell) hell (Nat.mod_lt _ (by omega)) hn
  rwa [Nat.div_add_mod] at h

private lemma pred_mod (ell q : ℕ) (hell : 2 ≤ ell) (h : q % ell = 0) (hq : 1 ≤ q) :
    (q - 1) % ell ≠ 0 := by
  intro h1
  have h2 : ell ∣ q - (q - 1) :=
    Nat.dvd_sub (Nat.dvd_of_mod_eq_zero h) (Nat.dvd_of_mod_eq_zero h1)
  rw [show q - (q - 1) = 1 by omega] at h2
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- Fibonacci envelopes for the pair window and for single values below `ell ^ m`. -/
private def env (c : ℕ) : ℕ → ℕ × ℕ
  | 0 => (c, c)
  | m + 1 => ((env c m).1 + (env c m).2, (env c m).1)

private lemma env_le (c m : ℕ) : (env c m).2 ≤ (env c m).1 := by
  cases m with
  | zero => simp [env]
  | succ m => simp only [env]; omega

private lemma upper (ell m : ℕ) (hell : 2 ≤ ell) : ∀ q < ell ^ m,
    win ell 2 q ≤ (env (count ell ell 0) m).1 ∧
      count ell ell q ≤ (env (count ell ell 0) m).2 := by
  set c := count ell ell 0
  induction m with
  | zero =>
    intro q hq
    have : q = 0 := by simpa using hq
    subst this
    simp only [env]
    exact ⟨(win_two_zero ell).le, le_rfl⟩
  | succ m ih =>
    intro q hq
    have hpar : ∀ n ≤ q, n / ell < ell ^ m := by
      intro n hn
      apply Nat.div_lt_of_lt_mul
      calc n ≤ q := hn
        _ < ell ^ (m + 1) := hq
        _ = ell * ell ^ m := by ring
    have hX : ∀ n ≤ q, count ell ell n ≤ (env c m).1 := fun n hn =>
      (count_le_win ell n hell).trans (ih _ (hpar n hn)).1
    have hY : ∀ n ≤ q, n % ell ≠ 0 → count ell ell n ≤ (env c m).2 := fun n hn hr => by
      rw [count_eq_parent ell n hell hr]
      exact (ih _ (hpar n hn)).2
    refine ⟨?_, ?_⟩
    · simp only [env]
      rcases Nat.eq_zero_or_pos q with h0 | hq1
      · subst h0
        rw [win_two_zero]
        exact (hX 0 le_rfl).trans (Nat.le_add_right _ _)
      · rw [win_two ell q hq1]
        by_cases h : q % ell = 0
        · have h' := pred_mod ell q hell h hq1
          have := hX q le_rfl
          have := hY (q - 1) (Nat.sub_le _ _) h'
          omega
        · have := hY q le_rfl h
          have := hX (q - 1) (Nat.sub_le _ _)
          omega
    · simp only [env]
      exact hX q le_rfl

private lemma env_bound (c : ℕ) (m : ℕ) :
    ((env c m).1 : ℝ) ≤ 2 * c * Real.goldenRatio ^ m ∧
      ((env c (m + 1)).1 : ℝ) ≤ 2 * c * Real.goldenRatio ^ (m + 1) := by
  have hg1 := Real.one_lt_goldenRatio
  have hsq := Real.goldenRatio_sq
  have hc : (0 : ℝ) ≤ c := by positivity
  induction m with
  | zero =>
    simp only [env, pow_zero, mul_one, zero_add, pow_one]
    push_cast
    constructor <;> nlinarith
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : ((env c (m + 2)).1 : ℝ) = (env c (m + 1)).1 + (env c m).1 := by
      simp only [env]; push_cast; ring
    calc ((env c (m + 1 + 1)).1 : ℝ) = (env c (m + 1)).1 + (env c m).1 := hrec
      _ ≤ 2 * c * Real.goldenRatio ^ (m + 1) + 2 * c * Real.goldenRatio ^ m :=
          add_le_add ih.2 ih.1
      _ = 2 * c * Real.goldenRatio ^ m * (Real.goldenRatio + 1) := by ring
      _ = 2 * c * Real.goldenRatio ^ (m + 1 + 1) := by rw [← hsq]; ring

/-- Below `ell ^ (m + 1)` the count is at most `2 c φ ^ m`. -/
private lemma count_upper (ell m n : ℕ) (hell : 2 ≤ ell) (hn : n < ell ^ (m + 1)) :
    (count ell ell n : ℝ) ≤ 2 * count ell ell 0 * Real.goldenRatio ^ m := by
  have hq : n / ell < ell ^ m := by
    apply Nat.div_lt_of_lt_mul
    calc n < ell ^ (m + 1) := hn
      _ = ell * ell ^ m := by ring
  have h1 := count_le_win ell n hell
  have h2 := (upper ell m hell (n / ell) hq).1
  calc (count ell ell n : ℝ) ≤ (env (count ell ell 0) m).1 := by exact_mod_cast h1.trans h2
    _ ≤ _ := (env_bound _ m).1

private lemma count_one_le (ell n : ℕ) (hell : 2 ≤ ell) : 1 ≤ count ell ell n :=
  count_positive ell ell n hell (by omega)

/-- Quotients whose digits alternate `0, 1, 0, ...` above a leading `1`. -/
private def qs (ell : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ell * qs ell k + k % 2

private lemma qs_bounds (ell k : ℕ) (hell : 2 ≤ ell) :
    ell ^ k ≤ qs ell k ∧ qs ell k < ell ^ (k + 1) := by
  induction k with
  | zero => simp [qs]; omega
  | succ k ih =>
    have hk2 : k % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [qs]
    constructor
    · calc ell ^ (k + 1) = ell * ell ^ k := by ring
        _ ≤ ell * qs ell k := Nat.mul_le_mul_left _ ih.1
        _ ≤ _ := Nat.le_add_right _ _
    · have h1 : qs ell k + 1 ≤ ell ^ (k + 1) := ih.2
      calc ell * qs ell k + k % 2 < ell * qs ell k + ell := by omega
        _ = ell * (qs ell k + 1) := by ring
        _ ≤ ell * ell ^ (k + 1) := Nat.mul_le_mul_left _ h1
        _ = ell ^ (k + 1 + 1) := by ring

private lemma qs_pos (ell k : ℕ) (hell : 2 ≤ ell) : 1 ≤ qs ell k :=
  le_trans (Nat.one_le_pow _ _ (by omega)) (qs_bounds ell k hell).1

private lemma win_at_one (ell q : ℕ) (hell : 2 ≤ ell) :
    win ell 2 (ell * q + 1) = count ell ell q + win ell 2 q := by
  rw [win_two ell _ (by omega), count_pos_digit ell q 1 hell (by omega) (by omega),
    Nat.add_sub_cancel, count_zero_digit ell q hell]

private lemma win_at_zero (ell q : ℕ) (hell : 2 ≤ ell) (hq : 1 ≤ q) :
    win ell 2 (ell * q) = win ell 2 q + count ell ell (q - 1) := by
  have hle : ell ≤ ell * q := Nat.le_mul_of_pos_right ell hq
  rw [win_two ell _ (by omega), count_zero_digit ell q hell]
  have hlast : ell * q - 1 = ell * (q - 1) + (ell - 1) := by
    have : ell * (q - 1) = ell * q - ell := by rw [Nat.mul_sub, mul_one]
    omega
  rw [hlast, count_pos_digit ell (q - 1) (ell - 1) hell (by omega) (by omega)]

/-- Along alternating digits the pair window obeys `v (k + 2) = v (k + 1) + v k`. -/
private lemma qs_rec (ell k : ℕ) (hell : 2 ≤ ell) :
    win ell 2 (qs ell (k + 2)) = win ell 2 (qs ell (k + 1)) + win ell 2 (qs ell k) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hq1 : qs ell (k + 1) = ell * qs ell k := by simp [qs, hk]
    have hq2 : qs ell (k + 2) = ell * qs ell (k + 1) + 1 := by
      simp only [qs] at hq1 ⊢; rw [show (k + 1) % 2 = 1 by omega]
    rw [hq2, win_at_one ell _ hell, hq1, count_zero_digit ell _ hell]
    ring
  · have hq1 : qs ell (k + 1) = ell * qs ell k + 1 := by simp [qs, hk]
    have hq2 : qs ell (k + 2) = ell * qs ell (k + 1) := by
      simp only [qs] at hq1 ⊢; rw [show (k + 1) % 2 = 0 by omega]; simp
    rw [hq2, win_at_zero ell _ hell (qs_pos ell (k + 1) hell), hq1, Nat.add_sub_cancel,
      count_zero_digit ell _ hell]

private lemma win_two_pos (ell q : ℕ) (hell : 2 ≤ ell) : 1 ≤ win ell 2 q := by
  rcases Nat.eq_zero_or_pos q with h0 | hq
  · subst h0; rw [win_two_zero]; exact count_one_le ell 0 hell
  · rw [win_two ell q hq]; have := count_one_le ell q hell; omega

private lemma qs_lower (ell k : ℕ) (hell : 2 ≤ ell) :
    Real.goldenRatio ^ k ≤ Real.goldenRatio * win ell 2 (qs ell k) ∧
      Real.goldenRatio ^ (k + 1) ≤ Real.goldenRatio * win ell 2 (qs ell (k + 1)) := by
  have hg1 := Real.one_lt_goldenRatio
  have hsq := Real.goldenRatio_sq
  have hv : ∀ q, (1 : ℝ) ≤ win ell 2 q := fun q => by exact_mod_cast win_two_pos ell q hell
  induction k with
  | zero =>
    simp only [pow_zero, zero_add, pow_one]
    exact ⟨by nlinarith [hv (qs ell 0)], by nlinarith [hv (qs ell 1)]⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (win ell 2 (qs ell (k + 2)) : ℝ) =
        win ell 2 (qs ell (k + 1)) + win ell 2 (qs ell k) := by
      rw [qs_rec ell k hell]; push_cast; ring
    calc Real.goldenRatio ^ (k + 1 + 1) = Real.goldenRatio ^ (k + 1) + Real.goldenRatio ^ k := by
          rw [show Real.goldenRatio ^ (k + 1 + 1) = Real.goldenRatio ^ k *
            Real.goldenRatio ^ 2 by ring, hsq]; ring
      _ ≤ Real.goldenRatio * win ell 2 (qs ell (k + 1)) +
            Real.goldenRatio * win ell 2 (qs ell k) := add_le_add ih.2 ih.1
      _ = Real.goldenRatio * win ell 2 (qs ell (k + 1 + 1)) := by rw [hrec]; ring

/-- Upper bound for `log b(t) / log n` whenever `t ≤ n`. -/
private lemma ratio_upper (ell n t : ℕ) (hell : 2 ≤ ell) (hn : 2 ≤ n) (ht : t ≤ n) :
    Real.log (count ell ell t) / Real.log n ≤
      Real.log Real.goldenRatio / Real.log ell +
        Real.log (2 * count ell ell 0) / Real.log n := by
  set m := Nat.log ell n
  set c := count ell ell 0
  have hlt : n < ell ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hge : ell ^ m ≤ n := Nat.pow_log_le_self ell (by omega)
  have hcnt : (0 : ℝ) < count ell ell t := by exact_mod_cast count_one_le ell t hell
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast count_one_le ell 0 hell
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hg1 := Real.one_lt_goldenRatio
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hloggr : 0 ≤ Real.log Real.goldenRatio := Real.log_nonneg hg1.le
  have hup := count_upper ell m t hell (lt_of_le_of_lt ht hlt)
  have h1 : Real.log (count ell ell t) ≤ Real.log (2 * c) + m * Real.log Real.goldenRatio := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hcnt hup
  have h2 : (m : ℝ) * Real.log (ell : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hge)
  have h3 : (m : ℝ) * Real.log Real.goldenRatio ≤
      Real.log Real.goldenRatio / Real.log ell * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlogell]
    nlinarith
  calc Real.log (count ell ell t) / Real.log n
      ≤ (Real.log (2 * c) + Real.log Real.goldenRatio / Real.log ell * Real.log n) /
          Real.log n := by
        apply div_le_div_of_nonneg_right _ hlogn.le; linarith
    _ = _ := by field_simp; ring

/-- Lower bound for `log b(ell qs k) / log n` when `n < ell ^ (k + 2)`. -/
private lemma ratio_lower (ell k n : ℕ) (hell : 2 ≤ ell) (hk : 1 ≤ k) (hn : 2 ≤ n)
    (hnlt : n < ell ^ (k + 2)) :
    Real.log Real.goldenRatio / Real.log ell * ((k - 1) / (k + 2)) ≤
      Real.log (count ell ell (ell * qs ell k)) / Real.log n := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hg1 := Real.one_lt_goldenRatio
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hloggr : 0 ≤ Real.log Real.goldenRatio := Real.log_nonneg hg1.le
  have hv : (1 : ℝ) ≤ win ell 2 (qs ell k) := by exact_mod_cast win_two_pos ell _ hell
  have hlow := (qs_lower ell k hell).1
  have hlogv : ((k : ℝ) - 1) * Real.log Real.goldenRatio ≤
      Real.log (win ell 2 (qs ell k)) := by
    have : Real.log (Real.goldenRatio ^ k) ≤
        Real.log (Real.goldenRatio * win ell 2 (qs ell k)) :=
      Real.log_le_log (by positivity) hlow
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at this
    linarith
  have hlogn' : Real.log (n : ℝ) ≤ (k + 2) * Real.log (ell : ℝ) := by
    rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hnlt.le)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [count_zero_digit ell _ hell, le_div_iff₀ hlogn]
  calc Real.log Real.goldenRatio / Real.log ell * ((k - 1) / (k + 2)) * Real.log n
      ≤ Real.log Real.goldenRatio / Real.log ell * ((k - 1) / (k + 2)) *
          ((k + 2) * Real.log ell) := by
        apply mul_le_mul_of_nonneg_left hlogn'
        exact mul_nonneg (div_nonneg hloggr hlogell.le) (div_nonneg hk1 (by positivity))
    _ = ((k : ℝ) - 1) * Real.log Real.goldenRatio := by field_simp
    _ ≤ _ := hlogv

/-- Squeezing the infimum of tail suprema between an eventual upper bound and a cofinal
lower bound. -/
private lemma sandwich (f : ℕ → ℝ) (α B : ℝ)
    (hup : ∀ n, 2 ≤ n → f n ≤ α + B / Real.log n) (s : ℕ → ℕ) (hs : ∀ k, k ≤ s k)
    (hlow : ∀ k, 1 ≤ k → α * ((k - 1) / (k + 2)) ≤ f (s k)) :
    (⨅ (N : ℕ) (_ : 2 ≤ N), ⨆ (n : ℕ) (_ : N ≤ n), (f n : EReal)) = (α : EReal) := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    obtain ⟨r, hαr, hrs⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hr : α < r := EReal.coe_lt_coe_iff.mp hαr
    set ε := r - α
    have hε : 0 < ε := by simp only [ε]; linarith
    set N : ℕ := ⌈Real.exp (B / ε)⌉₊ + 2
    have hN2 : 2 ≤ N := by omega
    have hNexp : Real.exp (B / ε) < N := by
      have := Nat.le_ceil (Real.exp (B / ε))
      simp only [N]; push_cast; linarith
    have htail : ⨆ (n : ℕ) (_ : N ≤ n), (f n : EReal) ≤ (r : EReal) := by
      apply iSup₂_le
      intro n hn
      apply EReal.coe_le_coe
      have hn2 : 2 ≤ n := le_trans hN2 hn
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hlogN : B / ε < Real.log n := by
        rw [Real.lt_log_iff_exp_lt (by positivity)]
        exact hNexp.trans_le (by exact_mod_cast hn)
      have hsmall : B / Real.log n ≤ ε := by
        rw [div_le_iff₀ hlogn]
        rw [div_lt_iff₀ hε] at hlogN
        linarith
      have := hup n hn2
      simp only [ε] at hsmall
      linarith
    exact (not_lt_of_ge (iInf₂_le_of_le N hN2 htail)) hrs
  · refine le_iInf₂ fun N hN => ?_
    apply le_of_not_gt
    intro hlt
    obtain ⟨r, hsr, hrα⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hr : r < α := EReal.coe_lt_coe_iff.mp hrα
    have hd : 0 < α - r := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℝ) ((α + 2 * r) / (α - r)))
    have hkN : N < k := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hk)
    have hkr : (α + 2 * r) / (α - r) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have hk1 : 1 ≤ k := by omega
    have hfrac : r < α * ((k - 1) / (k + 2)) := by
      have hmul := (div_lt_iff₀ hd).mp hkr
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
      nlinarith
    have hval : (r : EReal) < (f (s k) : EReal) :=
      EReal.coe_lt_coe (hfrac.trans_le (hlow k hk1))
    have hsup : (f (s k) : EReal) ≤ ⨆ (n : ℕ) (_ : N ≤ n), (f n : EReal) :=
      le_iSup₂_of_le (s k) (le_trans hkN.le (hs k)) le_rfl
    exact (not_lt_of_ge hsup) (hsr.trans hval)

/-- The upper exponent with the source convention `s_ell(n) = b(ell, ell, n - 1)`. -/
def hyperExponent (ell : ℕ) : EReal :=
  ⨅ (N : ℕ) (_ : 2 ≤ N), ⨆ (n : ℕ) (_ : N ≤ n),
    ((Real.log (count ell ell (n - 1)) / Real.log n : ℝ) : EReal)

/-- Coons–Spiegelhofer: for the cap `ell` both conventions give the exponent `log_ell φ`. -/
def claim : Prop :=
  ∀ ell : ℕ, 2 ≤ ell →
    exponent ell ell = ((Real.logb ell Real.goldenRatio : ℝ) : EReal) ∧
      hyperExponent ell = ((Real.logb ell Real.goldenRatio : ℝ) : EReal)

theorem result : claim := by
  intro ell hell
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hα0 : 0 ≤ Real.log Real.goldenRatio / Real.log ell :=
    div_nonneg (Real.log_nonneg Real.one_lt_goldenRatio.le) hlogell.le
  have hc1 : (1 : ℝ) ≤ count ell ell 0 := by exact_mod_cast count_one_le ell 0 hell
  have hB : 0 ≤ Real.log (2 * count ell ell 0) := Real.log_nonneg (by nlinarith)
  have hsN : ∀ k, k ≤ ell * qs ell k := fun k => by
    have h1 := (qs_bounds ell k hell).1
    have h2 : k < ell ^ k := Nat.lt_pow_self (by omega)
    have h3 : qs ell k ≤ ell * qs ell k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnlt : ∀ k, ell * qs ell k + 1 < ell ^ (k + 2) := fun k => by
    have h1 : qs ell k + 1 ≤ ell ^ (k + 1) := (qs_bounds ell k hell).2
    calc ell * qs ell k + 1 < ell * qs ell k + ell := by omega
      _ = ell * (qs ell k + 1) := by ring
      _ ≤ ell * ell ^ (k + 1) := Nat.mul_le_mul_left _ h1
      _ = ell ^ (k + 2) := by ring
  have hn2 : ∀ k, 2 ≤ ell * qs ell k := fun k =>
    le_trans hell (Nat.le_mul_of_pos_right _ (qs_pos ell k hell))
  rw [show Real.logb ell Real.goldenRatio = Real.log Real.goldenRatio / Real.log ell from rfl]
  refine ⟨?_, ?_⟩
  · unfold exponent readout
    exact sandwich _ _ _ (fun n hn => ratio_upper ell n n hell hn le_rfl)
      (fun k => ell * qs ell k) hsN
      (fun k hk => ratio_lower ell k _ hell hk (hn2 k) (by have := hnlt k; omega))
  · unfold hyperExponent
    refine sandwich _ _ _ (fun n hn => ratio_upper ell n (n - 1) hell hn (Nat.sub_le _ _))
      (fun k => ell * qs ell k + 1) (fun k => (hsN k).trans (Nat.le_succ _)) ?_
    intro k hk
    simpa using ratio_lower ell k (ell * qs ell k + 1) hell hk (by have := hn2 k; omega) (hnlt k)

end

end D5.S1.Digit.DigitCapHyperGolden
