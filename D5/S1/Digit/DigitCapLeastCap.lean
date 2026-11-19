/- GID: D5/S1/Digit/DigitCapLeastCap
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapLeastCap
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The least digit cap whose upper growth exponent reaches r - 1 is ell^r - 1. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#301, remaining least-cap
  claims)
escape_witness: exponent_ge (the cap ell^(s+1) - 1 has upper exponent at least s, from the
  frozen Θ lower bound and a limsup estimate) and exponent_lt (every cap ell^r - 2 or
  below has upper exponent below r - 1, from the subcritical O-bound).
proof_shape:
  exists_log_ge: bind-only helper; consumers: exponent_ge, exponent_lt, least_linear_min.
  exponent_ge: content (Θ lower bound to the limsup exponent); consumer: least_cap.
  exponent_lt: content (O-bound to the limsup exponent); consumer: least_cap.
  least_cap: content via exponent_ge and exponent_lt.
  least_linear_min: content (linear growth against the subcritical O-bound with e < 1).
Direct frozen dependencies: D5/S1/Digit/CoonsAdjacentGrowthRefutation (count, readout,
  exponent), D5/S1/Digit/DigitCapPowerGF (count_isTheta), D5/S1/Digit/DigitCapMultipleCount
  (count_square_sub_one), D5/S1/Digit/DigitCapSubcritical (subcritical; frozen by
  the-omega-institute/trureturing#31963).
Search record (§3.1): DigitCapPlateau.exponent_plateau computes the exponent log_ell q for caps
  up to q ell - 1 with q ≤ ell, which covers ell^2 - 1 but not ell^r - 1 for r ≥ 3 and no
  exclusion below the critical cap; DigitCapExponentOrder gives finiteness and monotonicity
  only. DigitCapPowerGF.count_isTheta gives the Θ(n^(r-1)) count bound, reused here; no frozen
  module turns it into a bound on the limsup exponent, or excludes linear growth below
  ell^2 - 1.
-/

import D5.S1.Digit.DigitCapPowerGF
import D5.S1.Digit.DigitCapSubcritical

/-! # The least digit cap with upper exponent `r - 1`

For a radix `ell ≥ 2` and `r ≥ 2`, the least digit cap `k` whose upper logarithmic growth
exponent `limsup log b(k, ell, n) / log n` is at least `r - 1` is `ell ^ r - 1`. The cap
`ell ^ r - 1` has at least `C(⌊n / ell ^ (r-1)⌋ + r - 1, r - 1) ≥ c n ^ (r - 1)` representations,
while every cap `k ≤ ell ^ r - 2` has `O(n ^ ((log_ell H) / 2))` with `(log_ell H) / 2 < r - 1`.
Separately, `ell ^ 2 - 1` is the least cap whose counts grow at least linearly (Coons's CW3).
-/

set_option autoImplicit false

namespace D5.S1.Digit.DigitCapLeastCap

open D5.S1.Digit.CoonsAdjacentGrowthRefutation

noncomputable section

/-- Logarithms of naturals grow without bound. -/
private lemma exists_log_ge (N : ℕ) (L : ℝ) : ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧ L ≤ Real.log n := by
  refine ⟨max N (Nat.ceil (Real.exp L) + 2), le_max_left _ _, by omega, ?_⟩
  rw [Real.le_log_iff_exp_le (by positivity)]
  calc Real.exp L ≤ (Nat.ceil (Real.exp L) : ℝ) := Nat.le_ceil _
    _ ≤ ((max N (Nat.ceil (Real.exp L) + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show Nat.ceil (Real.exp L) ≤ max N (Nat.ceil (Real.exp L) + 2) by omega)

/-- The cap `ell ^ (s+1) - 1` has upper exponent at least `s`. -/
private lemma exponent_ge (ell s : ℕ) (hell : 2 ≤ ell) :
    ((s : ℝ) : EReal) ≤ exponent (ell ^ (s + 1) - 1) ell := by
  obtain ⟨C, hCpos, hC⟩ := (DigitCapPowerGF.count_isTheta ell s hell).2.exists_pos
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hC.bound
  unfold exponent
  apply le_iInf₂
  intro N _
  by_contra hlt
  push Not at hlt
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hqs : q < s := EReal.coe_lt_coe_iff.mp hq2
  obtain ⟨n, hNn, hn2, hlog⟩ :=
    exists_log_ge (max N N0) (|Real.log C| / ((s : ℝ) - q) + 1)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnpos : (0 : ℝ) < n := by positivity
  have hb := hN0 n (le_trans (le_max_right _ _) hNn)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hb
  have hcpos : (0 : ℝ) < count (ell ^ (s + 1) - 1) ell n := by
    by_contra h0
    push Not at h0
    have : (n : ℝ) ^ s ≤ 0 := hb.trans (mul_nonpos_of_nonneg_of_nonpos hCpos.le h0)
    have : 0 < (n : ℝ) ^ s := by positivity
    linarith
  have hread : q < readout (ell ^ (s + 1) - 1) ell n := by
    unfold readout
    rw [lt_div_iff₀ hlogpos]
    have hl := Real.log_le_log (by positivity) hb
    rw [Real.log_pow, Real.log_mul hCpos.ne' hcpos.ne'] at hl
    have hsq : 0 < (s : ℝ) - q := by linarith
    have habs : |Real.log C| < ((s : ℝ) - q) * Real.log n := by
      have := (div_lt_iff₀ hsq).mp (show |Real.log C| / ((s : ℝ) - q) < Real.log n by linarith)
      linarith
    have := le_abs_self (Real.log C)
    nlinarith
  have hle : (readout (ell ^ (s + 1) - 1) ell n : EReal) ≤
      ⨆ (n : ℕ) (_ : N ≤ n), (readout (ell ^ (s + 1) - 1) ell n : EReal) :=
    le_iSup₂_of_le n (le_trans (le_max_left _ _) hNn) le_rfl
  have : (q : EReal) < readout (ell ^ (s + 1) - 1) ell n := EReal.coe_lt_coe_iff.mpr hread
  exact absurd (hq1.trans (this.trans_le hle)) (lt_irrefl _)

/-- Every cap `k ≤ ell ^ r - 2` has upper exponent below `r - 1`. -/
private lemma exponent_lt (ell r k : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2) :
    exponent k ell < (((r : ℝ) - 1 : ℝ) : EReal) := by
  obtain ⟨-, hO, he⟩ := DigitCapSubcritical.subcritical ell r k hell hr hk
  set e := Real.logb ell ((ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell : ℕ) : ℝ) / 2
  have he0 : 0 ≤ e := by
    apply div_nonneg _ (by norm_num)
    apply Real.logb_nonneg (by exact_mod_cast (show 1 < ell by omega))
    have hQ : ell ≤ ell ^ (r - 1) := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ (r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : ell ^ (r - 1) / ell ≤ ell ^ (r - 1) := Nat.div_le_self _ _
    have h2 : 2 * ell ^ (r - 1) ≤ ell ^ (r - 1) * ell ^ (r - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast (show 1 ≤ ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell by omega)
  set q := (e + ((r : ℝ) - 1)) / 2 with hqdef
  have heq : e < q := by rw [hqdef]; linarith
  have hqr : q < (r : ℝ) - 1 := by rw [hqdef]; linarith
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hC.bound
  obtain ⟨N, hNN, hN2, hlogN⟩ := exists_log_ge N0 (|Real.log C| / (q - e) + 1)
  have hle : exponent k ell ≤ (q : EReal) := by
    unfold exponent
    refine iInf₂_le_of_le N hN2 (iSup₂_le fun n hn => ?_)
    rw [EReal.coe_le_coe_iff]
    have hn2 : 2 ≤ n := by omega
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogle : Real.log N ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hn)
    unfold readout
    rw [div_le_iff₀ hlogpos]
    by_cases hc0 : count k ell n = 0
    · rw [hc0, Nat.cast_zero, Real.log_zero]
      have : 0 ≤ q := by linarith
      positivity
    · have hcpos : (0 : ℝ) < count k ell n := by exact_mod_cast Nat.pos_of_ne_zero hc0
      have hb := hN0 n (by omega)
      rw [Real.norm_of_nonneg hcpos.le, Real.norm_of_nonneg (by positivity)] at hb
      have hnpos : (0 : ℝ) < n := by positivity
      have hl := Real.log_le_log hcpos hb
      rw [Real.log_mul hCpos.ne' (by positivity), Real.log_rpow hnpos] at hl
      have hqe : 0 < q - e := by linarith
      have habs : |Real.log C| < (q - e) * Real.log n := by
        have := (div_lt_iff₀ hqe).mp
          (show |Real.log C| / (q - e) < Real.log n by linarith)
        linarith
      have := le_abs_self (Real.log C)
      nlinarith
  exact hle.trans_lt (EReal.coe_lt_coe_iff.mpr hqr)

/-- For a radix `ell ≥ 2` and `r ≥ 2`, the least digit cap whose upper logarithmic growth
exponent is at least `r - 1` is `ell ^ r - 1`. -/
theorem least_cap (ell r : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) :
    IsLeast {k : ℕ | (((r : ℝ) - 1 : ℝ) : EReal) ≤ exponent k ell} (ell ^ r - 1) := by
  constructor
  · have h := exponent_ge ell (r - 1) hell
    rw [show r - 1 + 1 = r by omega, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one] at h
    exact h
  · intro k hk
    by_contra hlt
    push Not at hlt
    exact absurd hk (not_le.mpr (exponent_lt ell r k hell hr (by omega)))


/-- For a radix `ell ≥ 2`, the least digit cap whose counts grow at least linearly, i.e. with
`c n ≤ b(k, ell, n)` for some `c > 0` and all large `n`, is `ell ^ 2 - 1` (Coons's CW3). -/
theorem least_linear_min (ell : ℕ) (hell : 2 ≤ ell) :
    IsLeast {k : ℕ | ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c * n ≤ count k ell n}
      (ell ^ 2 - 1) := by
  constructor
  · refine ⟨1 / ell, by positivity, Filter.Eventually.of_forall fun n => ?_⟩
    rw [DigitCapMultipleCount.count_square_sub_one ell n hell]
    have hell0 : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    have := Nat.lt_div_mul_add (a := n) (show 0 < ell by omega)
    have h' : (n : ℝ) < ((n / ell : ℕ) : ℝ) * ell + ell := by exact_mod_cast this
    push_cast
    rw [one_div_mul_eq_div, div_le_iff₀ hell0]
    nlinarith
  · intro k ⟨c, hc, hlin⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨-, hO, he⟩ := DigitCapSubcritical.subcritical ell 2 k hell le_rfl (by omega)
    set e := Real.logb ell ((ell ^ (2 - 1) * ell ^ (2 - 1) - ell ^ (2 - 1) / ell : ℕ) : ℝ) / 2
    have he1 : e < 1 := by norm_num at he ⊢; linarith
    obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hC.bound
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hlin
    obtain ⟨n, hNn, hn2, hlog⟩ := exists_log_ge (max N0 N1)
      ((|Real.log C| + |Real.log c|) / (1 - e) + 1)
    have hnpos : (0 : ℝ) < n := by positivity
    have hlow := hN1 n (le_trans (le_max_right _ _) hNn)
    have hup := hN0 n (le_trans (le_max_left _ _) hNn)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hup
    have hchain : c * n ≤ C * (n : ℝ) ^ e := hlow.trans hup
    have hl := Real.log_le_log (by positivity) hchain
    rw [Real.log_mul hc.ne' hnpos.ne', Real.log_mul hCpos.ne' (by positivity),
      Real.log_rpow hnpos] at hl
    have h1e : 0 < 1 - e := by linarith
    have habs : |Real.log C| + |Real.log c| < (1 - e) * Real.log n := by
      have := (div_lt_iff₀ h1e).mp
        (show (|Real.log C| + |Real.log c|) / (1 - e) < Real.log n by linarith)
      linarith
    have := le_abs_self (Real.log C)
    have := neg_abs_le (Real.log c)
    nlinarith
end

end D5.S1.Digit.DigitCapLeastCap
