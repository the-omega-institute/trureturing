/- GID: D5/S1/Digit/DigitCapNearSquare
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapNearSquare
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The cap ell^2-2 has upper growth exponent log_ell of the root of x^2=(ell-1)(x+1), below 1. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#308)
escape_witness: win_split (among the ell window terms at most one has last digit ell - 1, so
  the full window is at most (ell - 1) X + Y) with upper (the envelope recursion
  x' = (ell - 1) x + y, y' = (ell - 1) x below ell ^ m), and qs_rec (along alternating digits
  ell - 2, ell - 1 the full window satisfies v(k + 2) = (ell - 1)(v(k + 1) + v k) exactly,
  through full_at_top, full_at_low and short_at_low).
proof_shape:
  win, lifts, env, qs: private definitions; consumers: the lemmas below.
  lam, claim: source definitions; consumers: result.
  cap_iff: content (digit range of a residue class under the cap); consumer: count_digit.
  count_digit: content (lowest-digit recursion specialised to ell ^ 2 - 2 via count_rec);
    consumers: count_le_win, count_eq_short, count_low_digit, full_at_top, full_at_low.
  lifts_of_ne, lifts_top, win_len_le, win_eq_range, win_zero, count_low_digit: bind-only
    helpers; consumers: count_le_win, count_eq_short, upper, the window identities.
  count_le_win, count_eq_short: content; consumer: upper.
  pos_of_res, res_of_pos: content (residue arithmetic); consumer: win_split.
  win_split, upper: content; consumer: count_upper.
  lam_sq, one_le_lam, lam_lt: content (root facts); consumers: env_bound, qs_lower, result.
  env_bound, count_upper: content; consumer: readout_upper.
  short_at_low, full_at_top, full_at_low: content (exact window identities); consumer: qs_rec.
  qs_bounds, qs_pos, qs_rec, win_pos, qs_lower: content; consumer: readout_lower.
  count_zero_pos: bind-only helper (count_positive at 0); consumers: readout_upper, result.
  readout_upper, readout_lower: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S1/Digit/CoonsAdjacentGrowthRefutation (count, readout,
  exponent, count_positive; statement_id
  sha256:adc04d4c318958807e0c995604326199d16ca889d5bd0f774bec45e46b1859ac),
  D5/S1/Digit/DigitCapSubcritical (low, count_rec; made public in this delivery and re-pinned).
Search record (§3.1): D5/S1/Digit has exact exponents only on the plateaus
  (q-1)(ell+1) <= k <= q ell - 1 (DigitCapPlateau.exponent_plateau) and for caps
  ell^r - 1 (DigitCapPowerGF); the cap ell^2 - 2 lies between the plateaus q = ell - 1 and
  q = ell. DigitCapSubcritical.count_rec is the lowest-digit recursion reused here. Mathlib has
  no bounded-digit representation counts.
-/

import D5.S1.Digit.DigitCapSubcritical

/-! # The digit cap `ell ^ 2 - 2`

For a radix `ell ≥ 2`, the number `b(n)` of representations of `n` with digits at most
`ell ^ 2 - 2` satisfies `b(ell q + r) = b(q) + ... + b(q - ell + 1)` for `r ≤ ell - 2` and
the same sum with `ell - 1` terms for `r = ell - 1`. Among `ell` consecutive window terms at
most one has last digit `ell - 1`, so the window maxima obey `X' ≤ (ell - 1) X + Y`,
`Y' ≤ (ell - 1) X`, and `b(n) = O(λ ^ m)` below `ell ^ (m + 1)`, where `λ` is the positive
root of `λ ^ 2 = (ell - 1)(λ + 1)`. Along quotients whose digits alternate `ell - 2, ell - 1`
the full window satisfies `v(k + 2) = (ell - 1)(v(k + 1) + v k)` exactly. Hence the upper
growth exponent equals `log_ell λ`, and `λ < ell` makes it smaller than `1`.
-/

set_option autoImplicit false

namespace D5.S1.Digit.DigitCapNearSquare

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapSubcritical (low count_rec)
open Finset

noncomputable section

/-- The sum of the last `L` values of `count (ell ^ 2 - 2) ell` ending at `q`. -/
private def win (ell L q : ℕ) : ℕ :=
  ∑ j ∈ (range L).filter (· ≤ q), count (ell ^ 2 - 2) ell (q - j)

/-- The number of admissible digit lifts of a residue `r` under the cap `ell ^ 2 - 2`. -/
private def lifts (ell r : ℕ) : ℕ := if r = ell - 1 then ell - 1 else ell

private lemma cap_iff (ell r j : ℕ) (hell : 2 ≤ ell) (hr : r < ell) :
    r + ell * j ≤ ell ^ 2 - 2 ↔ j < lifts ell r := by
  obtain ⟨e, rfl⟩ : ∃ e, ell = e + 2 := ⟨ell - 2, by omega⟩
  have hsq : (e + 2) ^ 2 - 2 = e * e + 4 * e + 2 := by
    rw [sq]; ring_nf; omega
  rw [hsq]
  unfold lifts
  split_ifs with h
  · have hr' : r = e + 1 := by omega
    subst hr'
    constructor
    · intro hle
      by_contra hj
      rw [not_lt] at hj
      nlinarith
    · intro hj
      have : j ≤ e := by omega
      nlinarith
  · have hr' : r ≤ e := by omega
    constructor
    · intro hle
      by_contra hj
      rw [not_lt] at hj
      nlinarith
    · intro hj
      have : j ≤ e + 1 := by omega
      nlinarith

/-- Lowest-digit recursion for the cap `ell ^ 2 - 2`. -/
private lemma count_digit (ell q r : ℕ) (hell : 2 ≤ ell) (hr : r < ell) :
    count (ell ^ 2 - 2) ell (ell * q + r) = win ell (lifts ell r) q := by
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

private lemma lifts_of_ne (ell r : ℕ) (h : r ≠ ell - 1) : lifts ell r = ell := by
  simp [lifts, h]

private lemma lifts_top (ell : ℕ) : lifts ell (ell - 1) = ell - 1 := by
  simp [lifts]

private lemma win_len_le (ell q : ℕ) : win ell (ell - 1) q ≤ win ell ell q := by
  unfold win
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [mem_filter, mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

/-- Every count is bounded by the full window at its quotient. -/
private lemma count_le_win (ell n : ℕ) (hell : 2 ≤ ell) :
    count (ell ^ 2 - 2) ell n ≤ win ell ell (n / ell) := by
  have h := count_digit ell (n / ell) (n % ell) hell (Nat.mod_lt _ (by omega))
  rw [Nat.div_add_mod] at h
  rw [h]
  by_cases hr : n % ell = ell - 1
  · rw [hr, lifts_top]; exact win_len_le ell _
  · rw [lifts_of_ne _ _ hr]

/-- A count whose last digit is `ell - 1` is the short window at its quotient. -/
private lemma count_eq_short (ell n : ℕ) (hell : 2 ≤ ell) (hn : n % ell = ell - 1) :
    count (ell ^ 2 - 2) ell n = win ell (ell - 1) (n / ell) := by
  have h := count_digit ell (n / ell) (n % ell) hell (Nat.mod_lt _ (by omega))
  rw [Nat.div_add_mod, hn, lifts_top] at h
  exact h

private lemma pos_of_res (ell q j : ℕ) (hell : 2 ≤ ell) (hj : j < ell) (hjq : j ≤ q)
    (h : (q - j) % ell = ell - 1) : j = (q + 1) % ell := by
  have hsplit : q + 1 = (q - j + 1) + j := by omega
  have h0 : (q - j + 1) % ell = 0 := by
    rw [Nat.add_mod, h, Nat.mod_eq_of_lt (by omega : 1 < ell), Nat.sub_add_cancel (by omega),
      Nat.mod_self]
  rw [hsplit, Nat.add_mod, h0, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj]

private lemma res_of_pos (ell q : ℕ) (hell : 2 ≤ ell) (hq : ell - 1 ≤ q) :
    (q - (q + 1) % ell) % ell = ell - 1 := by
  set t := (q + 1) / ell
  have h1 : (q + 1) % ell + ell * t = q + 1 := Nat.mod_add_div (q + 1) ell
  have ht : 1 ≤ t := Nat.div_pos (by omega) (by omega)
  have hP : ell ≤ ell * t := Nat.le_mul_of_pos_right ell ht
  have hQ : ell * (t - 1) = ell * t - ell := by rw [Nat.mul_sub, mul_one]
  have : q - (q + 1) % ell = (ell - 1) + ell * (t - 1) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Among the `ell` window terms at most one has last digit `ell - 1`, and the others are
at most `ell - 1` in number. -/
private lemma win_split (ell q X Y : ℕ) (hell : 2 ≤ ell)
    (hX : ∀ j ≤ q, count (ell ^ 2 - 2) ell (q - j) ≤ X)
    (hY : ∀ j ≤ q, (q - j) % ell = ell - 1 → count (ell ^ 2 - 2) ell (q - j) ≤ Y) :
    win ell ell q ≤ (ell - 1) * X + Y := by
  unfold win
  set S := (range ell).filter (· ≤ q) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun j => (q - j) % ell = ell - 1)]
  have h1 : ∑ j ∈ S.filter (fun j => (q - j) % ell = ell - 1), count (ell ^ 2 - 2) ell (q - j)
      ≤ (S.filter (fun j => (q - j) % ell = ell - 1)).card * Y := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro j hj
    simp only [hS, mem_filter, mem_range] at hj
    exact hY j hj.1.2 hj.2
  have h2 : ∑ j ∈ S.filter (fun j => ¬ (q - j) % ell = ell - 1),
      count (ell ^ 2 - 2) ell (q - j)
      ≤ (S.filter (fun j => ¬ (q - j) % ell = ell - 1)).card * X := by
    rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro j hj
    simp only [hS, mem_filter, mem_range] at hj
    exact hX j hj.1.2
  have hc1 : (S.filter (fun j => (q - j) % ell = ell - 1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [hS, mem_filter, mem_range] at ha hb
    rw [pos_of_res ell q a hell ha.1.1 ha.1.2 ha.2, pos_of_res ell q b hell hb.1.1 hb.1.2 hb.2]
  have hc2 : (S.filter (fun j => ¬ (q - j) % ell = ell - 1)).card ≤ ell - 1 := by
    by_cases hq : ell - 1 ≤ q
    · have hsub : S.filter (fun j => ¬ (q - j) % ell = ell - 1) ⊆
          (range ell).erase ((q + 1) % ell) := by
        intro j hj
        simp only [hS, mem_filter, mem_range, mem_erase] at hj ⊢
        refine ⟨?_, hj.1.1⟩
        intro hj0
        exact hj.2 (hj0 ▸ res_of_pos ell q hell hq)
      calc _ ≤ ((range ell).erase ((q + 1) % ell)).card := Finset.card_le_card hsub
        _ = ell - 1 := by
          rw [Finset.card_erase_of_mem (mem_range.mpr (Nat.mod_lt _ (by omega))), card_range]
    · have hsub : S.filter (fun j => ¬ (q - j) % ell = ell - 1) ⊆ range (q + 1) := by
        intro j hj
        simp only [hS, mem_filter, mem_range] at hj ⊢
        omega
      calc _ ≤ (range (q + 1)).card := Finset.card_le_card hsub
        _ ≤ ell - 1 := by rw [card_range]; omega
  calc _ ≤ (S.filter (fun j => (q - j) % ell = ell - 1)).card * Y +
        (S.filter (fun j => ¬ (q - j) % ell = ell - 1)).card * X := add_le_add h1 h2
    _ ≤ 1 * Y + (ell - 1) * X := add_le_add (Nat.mul_le_mul_right _ hc1)
        (Nat.mul_le_mul_right _ hc2)
    _ = (ell - 1) * X + Y := by ring

/-- Upper envelopes for the full and short windows below `ell ^ m`. -/
private def env (ell c : ℕ) : ℕ → ℕ × ℕ
  | 0 => (c, c)
  | m + 1 => ((ell - 1) * (env ell c m).1 + (env ell c m).2, (ell - 1) * (env ell c m).1)

private lemma win_zero (ell L : ℕ) :
    win ell L 0 ≤ count (ell ^ 2 - 2) ell 0 := by
  unfold win
  calc _ ≤ ∑ j ∈ ({0} : Finset ℕ), count (ell ^ 2 - 2) ell (0 - j) := by
        apply Finset.sum_le_sum_of_subset
        intro j hj
        simp only [mem_filter, mem_range] at hj
        simp only [mem_singleton]; omega
    _ = _ := by simp

private lemma upper (ell m : ℕ) (hell : 2 ≤ ell) : ∀ q < ell ^ m,
    win ell ell q ≤ (env ell (count (ell ^ 2 - 2) ell 0) m).1 ∧
      win ell (ell - 1) q ≤ (env ell (count (ell ^ 2 - 2) ell 0) m).2 := by
  set c := count (ell ^ 2 - 2) ell 0
  induction m with
  | zero =>
    intro q hq
    have : q = 0 := by simpa using hq
    subst this
    exact ⟨win_zero ell ell, win_zero ell (ell - 1)⟩
  | succ m ih =>
    intro q hq
    have hpar : ∀ j ≤ q, (q - j) / ell < ell ^ m := by
      intro j _
      apply Nat.div_lt_of_lt_mul
      calc q - j ≤ q := Nat.sub_le _ _
        _ < ell ^ (m + 1) := hq
        _ = ell * ell ^ m := by ring
    have hX : ∀ j ≤ q, count (ell ^ 2 - 2) ell (q - j) ≤ (env ell c m).1 := fun j hj =>
      (count_le_win ell (q - j) hell).trans (ih _ (hpar j hj)).1
    have hY : ∀ j ≤ q, (q - j) % ell = ell - 1 →
        count (ell ^ 2 - 2) ell (q - j) ≤ (env ell c m).2 := fun j hj hr => by
      rw [count_eq_short ell _ hell hr]; exact (ih _ (hpar j hj)).2
    refine ⟨?_, ?_⟩
    · simp only [env]
      exact win_split ell q _ _ hell hX hY
    · simp only [env]
      unfold win
      calc _ ≤ ((range (ell - 1)).filter (· ≤ q)).card • (env ell c m).1 := by
            apply Finset.sum_le_card_nsmul
            intro j hj
            simp only [mem_filter, mem_range] at hj
            exact hX j hj.2
        _ ≤ (ell - 1) * (env ell c m).1 := by
            rw [smul_eq_mul]
            apply Nat.mul_le_mul_right
            calc _ ≤ (range (ell - 1)).card := Finset.card_filter_le _ _
              _ = ell - 1 := card_range _

/-- The dominant root `λ` of `λ ^ 2 = (ell - 1) (λ + 1)`. -/
def lam (ell : ℕ) : ℝ := ((ell : ℝ) - 1 + Real.sqrt ((ell : ℝ) ^ 2 + 2 * ell - 3)) / 2

private lemma lam_sq (ell : ℕ) (hell : 2 ≤ ell) :
    lam ell ^ 2 = ((ell : ℝ) - 1) * (lam ell + 1) := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hD : (0 : ℝ) ≤ (ell : ℝ) ^ 2 + 2 * ell - 3 := by nlinarith
  have hs := Real.sq_sqrt hD
  unfold lam
  nlinarith [hs]

private lemma one_le_lam (ell : ℕ) (hell : 2 ≤ ell) : 1 ≤ lam ell := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : (1 : ℝ) ≤ Real.sqrt ((ell : ℝ) ^ 2 + 2 * ell - 3) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith)
  unfold lam
  linarith

private lemma lam_lt (ell : ℕ) (hell : 2 ≤ ell) : lam ell < ell := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : Real.sqrt ((ell : ℝ) ^ 2 + 2 * ell - 3) < ell + 1 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  unfold lam
  linarith

/-- The full-window envelope grows at most like `ell * c * λ ^ m`. -/
private lemma env_bound (ell c : ℕ) (hell : 2 ≤ ell) (m : ℕ) :
    ((env ell c m).1 : ℝ) ≤ ell * c * lam ell ^ m ∧
      ((env ell c (m + 1)).1 : ℝ) ≤ ell * c * lam ell ^ (m + 1) := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 := one_le_lam ell hell
  have hsq := lam_sq ell hell
  have hc : (0 : ℝ) ≤ c := by positivity
  have hsub : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hlc : (0 : ℝ) ≤ ell * c * (lam ell - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hc) (by linarith)
  induction m with
  | zero =>
    simp only [env, pow_zero, mul_one]
    push_cast [hsub]
    constructor <;> nlinarith
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : ((env ell c (m + 2)).1 : ℝ) =
        ((ell : ℝ) - 1) * (env ell c (m + 1)).1 + ((ell : ℝ) - 1) * (env ell c m).1 := by
      simp only [env]
      push_cast [hsub]
      ring
    have hl0 : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left ih.1 hl0
    have h2 := mul_le_mul_of_nonneg_left ih.2 hl0
    calc ((env ell c (m + 1 + 1)).1 : ℝ)
        = ((ell : ℝ) - 1) * (env ell c (m + 1)).1 + ((ell : ℝ) - 1) * (env ell c m).1 := hrec
      _ ≤ ((ell : ℝ) - 1) * (ell * c * lam ell ^ (m + 1)) +
          ((ell : ℝ) - 1) * (ell * c * lam ell ^ m) := add_le_add h2 h1
      _ = ell * c * lam ell ^ m * (((ell : ℝ) - 1) * (lam ell + 1)) := by ring
      _ = ell * c * lam ell ^ (m + 1 + 1) := by rw [← hsq]; ring

/-- The count below `ell ^ (m + 1)` is at most `ell * c * λ ^ m`. -/
private lemma count_upper (ell m n : ℕ) (hell : 2 ≤ ell) (hn : n < ell ^ (m + 1)) :
    (count (ell ^ 2 - 2) ell n : ℝ) ≤ ell * count (ell ^ 2 - 2) ell 0 * lam ell ^ m := by
  have hq : n / ell < ell ^ m := by
    apply Nat.div_lt_of_lt_mul
    calc n < ell ^ (m + 1) := hn
      _ = ell * ell ^ m := by ring
  have h1 := count_le_win ell n hell
  have h2 := (upper ell m hell (n / ell) hq).1
  have h3 := (env_bound ell (count (ell ^ 2 - 2) ell 0) hell m).1
  calc (count (ell ^ 2 - 2) ell n : ℝ) ≤ (env ell (count (ell ^ 2 - 2) ell 0) m).1 := by
        exact_mod_cast h1.trans h2
    _ ≤ _ := h3

/-- A last digit `t ≤ ell - 2` reads the full window. -/
private lemma count_low_digit (ell q t : ℕ) (hell : 2 ≤ ell) (ht : t ≤ ell - 2) :
    count (ell ^ 2 - 2) ell (ell * q + t) = win ell ell q := by
  rw [count_digit ell q t hell (by omega), lifts_of_ne _ _ (by omega)]

private lemma win_eq_range (ell L q : ℕ) (hL : L ≤ q + 1) :
    win ell L q = ∑ j ∈ range L, count (ell ^ 2 - 2) ell (q - j) := by
  unfold win
  congr 1
  apply Finset.filter_true_of_mem
  intro j hj
  simp only [mem_range] at hj
  omega

private lemma short_at_low (ell q : ℕ) (hell : 2 ≤ ell) :
    win ell (ell - 1) (ell * q + (ell - 2)) = (ell - 1) * win ell ell q := by
  rw [win_eq_range ell _ _ (by omega)]
  calc _ = ∑ _j ∈ range (ell - 1), win ell ell q := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [mem_range] at hj
        rw [show ell * q + (ell - 2) - j = ell * q + (ell - 2 - j) by omega]
        exact count_low_digit ell q _ hell (by omega)
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

private lemma full_at_top (ell q : ℕ) (hell : 2 ≤ ell) :
    win ell ell (ell * q + (ell - 1)) = (ell - 1) * win ell ell q + win ell (ell - 1) q := by
  rw [win_eq_range ell _ _ (by omega)]
  obtain ⟨e, he⟩ : ∃ e, ell = e + 1 := ⟨ell - 1, by omega⟩
  have hsum : ∑ j ∈ range ell, count (ell ^ 2 - 2) ell (ell * q + (ell - 1) - j) =
      ∑ j ∈ range (ell - 1), count (ell ^ 2 - 2) ell (ell * q + (ell - 1) - (j + 1)) +
        count (ell ^ 2 - 2) ell (ell * q + (ell - 1) - 0) := by
    rw [he, Finset.sum_range_succ', show e + 1 - 1 = e by omega]
  rw [hsum, Nat.sub_zero, count_digit ell q (ell - 1) hell (by omega), lifts_top]
  congr 1
  calc _ = ∑ _j ∈ range (ell - 1), win ell ell q := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [mem_range] at hj
        rw [show ell * q + (ell - 1) - (j + 1) = ell * q + (ell - 2 - j) by omega]
        exact count_low_digit ell q _ hell (by omega)
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

private lemma full_at_low (ell q : ℕ) (hell : 2 ≤ ell) (hq : 1 ≤ q) :
    win ell ell (ell * q + (ell - 2)) =
      (ell - 1) * win ell ell q + win ell (ell - 1) (q - 1) := by
  have hle : ell ≤ ell * q := Nat.le_mul_of_pos_right ell hq
  rw [win_eq_range ell _ _ (by omega)]
  obtain ⟨e, he⟩ : ∃ e, ell = e + 1 := ⟨ell - 1, by omega⟩
  have hsum : ∑ j ∈ range ell, count (ell ^ 2 - 2) ell (ell * q + (ell - 2) - j) =
      ∑ j ∈ range (ell - 1), count (ell ^ 2 - 2) ell (ell * q + (ell - 2) - j) +
        count (ell ^ 2 - 2) ell (ell * q + (ell - 2) - (ell - 1)) := by
    rw [he, Finset.sum_range_succ, show e + 1 - 1 = e by omega]
  have hlast : ell * q + (ell - 2) - (ell - 1) = ell * (q - 1) + (ell - 1) := by
    have : ell * (q - 1) = ell * q - ell := by rw [Nat.mul_sub, mul_one]
    omega
  rw [hsum, hlast, count_digit ell (q - 1) (ell - 1) hell (by omega), lifts_top]
  congr 1
  calc _ = ∑ _j ∈ range (ell - 1), win ell ell q := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [mem_range] at hj
        rw [show ell * q + (ell - 2) - j = ell * q + (ell - 2 - j) by omega]
        exact count_low_digit ell q _ hell (by omega)
    _ = _ := by rw [sum_const, card_range, smul_eq_mul]

/-- Quotients whose digits alternate `ell - 2, ell - 1, ell - 2, ...` above a leading `1`. -/
private def qs (ell : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ell * qs ell k + (ell - 2 + k % 2)

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
      calc ell * qs ell k + (ell - 2 + k % 2) < ell * qs ell k + ell := by omega
        _ = ell * (qs ell k + 1) := by ring
        _ ≤ ell * ell ^ (k + 1) := Nat.mul_le_mul_left _ h1
        _ = ell ^ (k + 1 + 1) := by ring

private lemma qs_pos (ell k : ℕ) (hell : 2 ≤ ell) : 1 ≤ qs ell k :=
  le_trans (Nat.one_le_pow _ _ (by omega)) (qs_bounds ell k hell).1

/-- Along alternating digits the full window obeys `v (k + 2) = (ell - 1) (v (k + 1) + v k)`. -/
private lemma qs_rec (ell k : ℕ) (hell : 2 ≤ ell) :
    win ell ell (qs ell (k + 2)) =
      (ell - 1) * (win ell ell (qs ell (k + 1)) + win ell ell (qs ell k)) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h1 : (k + 1) % 2 = 1 := by omega
    have hq1 : qs ell (k + 1) = ell * qs ell k + (ell - 2) := by simp [qs, hk]
    have hq2 : qs ell (k + 2) = ell * qs ell (k + 1) + (ell - 1) := by
      simp only [qs] at hq1 ⊢; rw [h1]; congr 1; omega
    rw [hq2, full_at_top ell _ hell, hq1, short_at_low ell _ hell]
    ring
  · have h1 : (k + 1) % 2 = 0 := by omega
    have hq1 : qs ell (k + 1) = ell * qs ell k + (ell - 1) := by
      simp only [qs]; rw [hk]; congr 1; omega
    have hq2 : qs ell (k + 2) = ell * qs ell (k + 1) + (ell - 2) := by
      simp only [qs] at hq1 ⊢; rw [h1]; simp
    rw [hq2, full_at_low ell _ hell (qs_pos ell (k + 1) hell)]
    have hq1' : qs ell (k + 1) - 1 = ell * qs ell k + (ell - 2) := by rw [hq1]; omega
    rw [hq1', short_at_low ell _ hell]
    ring

private lemma win_pos (ell q : ℕ) (hell : 2 ≤ ell) : 1 ≤ win ell ell q := by
  have hk : ell - 1 ≤ ell ^ 2 - 2 := by
    have : ell ≤ ell ^ 2 := by nlinarith
    have : 2 * ell ≤ ell ^ 2 := by nlinarith
    omega
  unfold win
  calc 1 ≤ count (ell ^ 2 - 2) ell (q - 0) := count_positive _ ell _ hell hk
    _ ≤ _ := by
      apply Finset.single_le_sum (f := fun j => count (ell ^ 2 - 2) ell (q - j))
        (fun _ _ => Nat.zero_le _)
      simp only [mem_filter, mem_range]; omega

private lemma qs_lower (ell k : ℕ) (hell : 2 ≤ ell) :
    lam ell ^ k ≤ lam ell * win ell ell (qs ell k) ∧
      lam ell ^ (k + 1) ≤ lam ell * win ell ell (qs ell (k + 1)) := by
  have hl1 := one_le_lam ell hell
  have hsq := lam_sq ell hell
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hsub : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hv : ∀ q, (1 : ℝ) ≤ win ell ell q := fun q => by exact_mod_cast win_pos ell q hell
  induction k with
  | zero =>
    simp only [pow_zero, zero_add, pow_one]
    exact ⟨by nlinarith [hv (qs ell 0)], by nlinarith [hv (qs ell 1)]⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (win ell ell (qs ell (k + 2)) : ℝ) =
        ((ell : ℝ) - 1) * (win ell ell (qs ell (k + 1)) + win ell ell (qs ell k)) := by
      rw [qs_rec ell k hell]; push_cast [hsub]; ring
    have hl0 : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    calc lam ell ^ (k + 1 + 1) = ((ell : ℝ) - 1) * (lam ell ^ (k + 1) + lam ell ^ k) := by
          rw [show lam ell ^ (k + 1 + 1) = lam ell ^ k * lam ell ^ 2 by ring, hsq]; ring
      _ ≤ ((ell : ℝ) - 1) * (lam ell * win ell ell (qs ell (k + 1)) +
            lam ell * win ell ell (qs ell k)) :=
          mul_le_mul_of_nonneg_left (add_le_add ih.2 ih.1) hl0
      _ = lam ell * win ell ell (qs ell (k + 1 + 1)) := by rw [hrec]; ring

private lemma count_zero_pos (ell : ℕ) (hell : 2 ≤ ell) : 1 ≤ count (ell ^ 2 - 2) ell 0 := by
  have hk : ell - 1 ≤ ell ^ 2 - 2 := by
    have : 2 * ell ≤ ell ^ 2 := by nlinarith
    omega
  exact count_positive _ ell _ hell hk

private lemma readout_upper (ell n : ℕ) (hell : 2 ≤ ell) (hn : 2 ≤ n) :
    readout (ell ^ 2 - 2) ell n ≤
      Real.log (lam ell) / Real.log ell +
        Real.log (ell * count (ell ^ 2 - 2) ell 0) / Real.log n := by
  set m := Nat.log ell n
  set c := count (ell ^ 2 - 2) ell 0
  have hlt : n < ell ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hge : ell ^ m ≤ n := Nat.pow_log_le_self ell (by omega)
  have hk : ell - 1 ≤ ell ^ 2 - 2 := by
    have : 2 * ell ≤ ell ^ 2 := by nlinarith
    omega
  have hcnt : (0 : ℝ) < count (ell ^ 2 - 2) ell n := by
    exact_mod_cast count_positive _ ell n hell hk
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast count_zero_pos ell hell
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 := one_le_lam ell hell
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hloglam : 0 ≤ Real.log (lam ell) := Real.log_nonneg hl1
  have hup := count_upper ell m n hell hlt
  have h1 : Real.log (count (ell ^ 2 - 2) ell n) ≤ Real.log (ell * c) + m * Real.log (lam ell) := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hcnt hup
  have h2 : (m : ℝ) * Real.log (ell : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hge)
  have h3 : (m : ℝ) * Real.log (lam ell) ≤
      Real.log (lam ell) / Real.log ell * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlogell]
    nlinarith
  unfold readout
  calc Real.log (count (ell ^ 2 - 2) ell n) / Real.log n
      ≤ (Real.log (ell * c) + Real.log (lam ell) / Real.log ell * Real.log n) /
          Real.log n := by
        apply div_le_div_of_nonneg_right _ hlogn.le; linarith
    _ = _ := by field_simp; ring

private lemma readout_lower (ell k : ℕ) (hell : 2 ≤ ell) (hk : 1 ≤ k) :
    Real.log (lam ell) / Real.log ell * ((k - 1) / (k + 2)) ≤
      readout (ell ^ 2 - 2) ell (ell * qs ell k) := by
  set n := ell * qs ell k
  have hb := qs_bounds ell k hell
  have hn2 : 2 ≤ n := le_trans hell (Nat.le_mul_of_pos_right _ (qs_pos ell k hell))
  have hnlt : n < ell ^ (k + 2) := by
    calc n < ell * ell ^ (k + 1) := Nat.mul_lt_mul_of_pos_left hb.2 (by omega)
      _ = ell ^ (k + 2) := by ring
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 := one_le_lam ell hell
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hloglam : 0 ≤ Real.log (lam ell) := Real.log_nonneg hl1
  have hcount : count (ell ^ 2 - 2) ell n = win ell ell (qs ell k) := by
    have := count_low_digit ell (qs ell k) 0 hell (by omega)
    simpa using this
  have hv : (1 : ℝ) ≤ win ell ell (qs ell k) := by exact_mod_cast win_pos ell _ hell
  have hlow := (qs_lower ell k hell).1
  have hlogv : ((k : ℝ) - 1) * Real.log (lam ell) ≤ Real.log (win ell ell (qs ell k)) := by
    have : Real.log (lam ell ^ k) ≤ Real.log (lam ell * win ell ell (qs ell k)) :=
      Real.log_le_log (by positivity) hlow
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at this
    linarith
  have hlogn' : Real.log (n : ℝ) ≤ (k + 2) * Real.log (ell : ℝ) := by
    rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hnlt.le)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold readout
  rw [hcount]
  rw [le_div_iff₀ hlogn]
  calc Real.log (lam ell) / Real.log ell * ((k - 1) / (k + 2)) * Real.log n
      ≤ Real.log (lam ell) / Real.log ell * ((k - 1) / (k + 2)) *
          ((k + 2) * Real.log ell) := by
        apply mul_le_mul_of_nonneg_left hlogn'
        exact mul_nonneg (div_nonneg hloglam hlogell.le) (div_nonneg hk1 (by positivity))
    _ = ((k : ℝ) - 1) * Real.log (lam ell) := by field_simp
    _ ≤ _ := hlogv

/-- The source exponent `log_ell λ` for the cap `ell ^ 2 - 2`. -/
def claim : Prop :=
  ∀ ell : ℕ, 2 ≤ ell →
    exponent (ell ^ 2 - 2) ell = ((Real.logb ell (lam ell) : ℝ) : EReal) ∧
      Real.logb ell (lam ell) < 1

theorem result : claim := by
  intro ell hell
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl1 := one_le_lam ell hell
  have hlogell : 0 < Real.log (ell : ℝ) := Real.log_pos (by linarith)
  have hloglam : 0 ≤ Real.log (lam ell) := Real.log_nonneg hl1
  set α : ℝ := Real.log (lam ell) / Real.log ell with hα
  have hα0 : 0 ≤ α := div_nonneg hloglam hlogell.le
  set c := count (ell ^ 2 - 2) ell 0
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast count_zero_pos ell hell
  have hB : 0 ≤ Real.log (ell * c) := Real.log_nonneg (by nlinarith)
  refine ⟨?_, ?_⟩
  · rw [show Real.logb ell (lam ell) = α by rw [hα, Real.logb]]
    -- every tail supremum is at least `α`
    have hlowtail : ∀ N : ℕ, 2 ≤ N →
        (α : EReal) ≤ ⨆ (n : ℕ) (_ : N ≤ n), (readout (ell ^ 2 - 2) ell n : EReal) := by
      intro N hN
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
      have hnN : N ≤ ell * qs ell k := by
        have h1 := (qs_bounds ell k hell).1
        have h2 : k < ell ^ k := Nat.lt_pow_self (by omega)
        have h3 : qs ell k ≤ ell * qs ell k := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hval : (r : EReal) < (readout (ell ^ 2 - 2) ell (ell * qs ell k) : EReal) :=
        EReal.coe_lt_coe (hfrac.trans_le (readout_lower ell k hell hk1))
      have hsup : (readout (ell ^ 2 - 2) ell (ell * qs ell k) : EReal) ≤
          ⨆ (n : ℕ) (_ : N ≤ n), (readout (ell ^ 2 - 2) ell n : EReal) :=
        le_iSup₂_of_le (ell * qs ell k) hnN le_rfl
      exact (not_lt_of_ge hsup) (hsr.trans hval)
    unfold exponent
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      obtain ⟨r, hαr, hrs⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have hr : α < r := EReal.coe_lt_coe_iff.mp hαr
      set ε := r - α
      have hε : 0 < ε := by simp only [ε]; linarith
      set N : ℕ := ⌈Real.exp (Real.log (ell * c) / ε)⌉₊ + 2
      have hN2 : 2 ≤ N := by omega
      have hNexp : Real.exp (Real.log (ell * c) / ε) < N := by
        have := Nat.le_ceil (Real.exp (Real.log (ell * c) / ε))
        simp only [N]; push_cast; linarith
      have htail : ⨆ (n : ℕ) (_ : N ≤ n), (readout (ell ^ 2 - 2) ell n : EReal) ≤ (r : EReal) := by
        apply iSup₂_le
        intro n hn
        apply EReal.coe_le_coe
        have hn2 : 2 ≤ n := le_trans hN2 hn
        have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
        have hlogN : Real.log (ell * c) / ε < Real.log n := by
          rw [Real.lt_log_iff_exp_lt (by positivity)]
          exact hNexp.trans_le (by exact_mod_cast hn)
        have hsmall : Real.log (ell * c) / Real.log n ≤ ε := by
          rw [div_le_iff₀ hlogn]
          rw [div_lt_iff₀ hε] at hlogN
          linarith
        have := readout_upper ell n hell hn2
        simp only [ε] at hsmall
        linarith
      have hinf : (⨅ (N' : ℕ) (_ : 2 ≤ N'),
          ⨆ (n : ℕ) (_ : N' ≤ n), (readout (ell ^ 2 - 2) ell n : EReal)) ≤ (r : EReal) :=
        iInf₂_le_of_le N hN2 htail
      exact (not_lt_of_ge hinf) hrs
    · exact le_iInf₂ fun N hN => hlowtail N hN
  · rw [Real.logb, div_lt_one hlogell]
    exact Real.log_lt_log (by linarith) (lam_lt ell hell)

end

end D5.S1.Digit.DigitCapNearSquare
