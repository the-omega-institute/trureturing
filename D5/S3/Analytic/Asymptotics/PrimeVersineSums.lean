/- GID: D5/S3/Analytic/Asymptotics/PrimeVersineSums
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PrimeVersineSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime versine sums: thresholds 1/2 and 1/4 and the constant on sigma = 1/2. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.PSeries
import D5.S3.Weil.Mertens.Third

/-! # Versine sums over the primes

For `σ > 0` and a prime `p` put `t = p ^ (-σ)`, so `0 < t ≤ 1`. The versine `1 - cos t` lies
between `t ^ 2 / 2 - 5 t ^ 4 / 96` and `t ^ 2 / 2`, and its fourth-order defect
`cos t - (1 - t ^ 2 / 2)` lies between `t ^ 4 / 30` and `5 t ^ 4 / 96`. Comparison with
`∑ p ^ r`, which converges over the primes exactly when `r < -1`, gives the two thresholds:
`∑ (1 - cos p ^ (-σ))` converges exactly when `σ > 1 / 2`, and
`∑ (1 - cos p ^ (-σ) - p ^ (-2σ) / 2)` converges exactly when `σ > 1 / 4`; for `σ ≤ 1 / 4` its
partial sums tend to `-∞`. On the line `σ = 1 / 2` the partial sums equal
`(log log x) / 2` plus an explicit constant built from Mertens' constant, up to half the error
of Mertens' second theorem and a tail of size `O (1 / x)`, hence up to `O (1 / log x)`.
-/

open Real Filter Asymptotics Finset Topology

namespace D5.S3.Analytic.Asymptotics.PrimeVersineSums

/-- `∑_{p ≤ x} (1 - cos p ^ (-σ))` over primes `p`, with the summation range of the Mertens
error `Mertens.E₂p`. -/
noncomputable def primeVersineSum (σ x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 - Real.cos ((p : ℝ) ^ (-σ)))

/-- `(n ^ (-σ)) ^ m = n ^ (-(m σ))`. -/
private lemma rpow_neg_pow (n m : ℕ) (σ : ℝ) :
    ((n : ℝ) ^ (-σ)) ^ m = (n : ℝ) ^ (-(m * σ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

/-- For `n ≥ 1` and `σ ≥ 0`, `|n ^ (-σ)| ≤ 1`. -/
private lemma abs_rpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 ≤ σ) :
    |(n : ℝ) ^ (-σ)| ≤ 1 := by
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- The fourth-order defect of the versine is at least `t ^ 4 / 30` on `|t| ≤ 1`. -/
private lemma quartic_le_defect {t : ℝ} (ht : |t| ≤ 1) :
    t ^ 4 / 30 ≤ Real.cos t - (1 - t ^ 2 / 2) := by
  set y := t / 2 with hy
  have hty : t = 2 * y := by rw [hy]; ring
  have hyle : |y| ≤ 1 / 2 := by
    rw [hy, abs_div, abs_two]; linarith
  set u := |y| with hu
  have hu0 : 0 ≤ u := abs_nonneg y
  have hyu : y ^ 2 = u ^ 2 := (sq_abs y).symm
  have hsb := Real.sin_bound (x := y) (by linarith)
  have hpoly : |y - y ^ 3 / 6| = u - u ^ 3 / 6 := by
    have hfac : y - y ^ 3 / 6 = y * (1 - y ^ 2 / 6) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - y ^ 2 / 6), hyu]
    ring
  have hsin : |Real.sin y| ≤ u - u ^ 3 / 6 + u ^ 5 / 100 := by
    have h1 : |Real.sin y| ≤ |y - y ^ 3 / 6| + |Real.sin y - (y - y ^ 3 / 6)| := by
      have := abs_add_le (y - y ^ 3 / 6) (Real.sin y - (y - y ^ 3 / 6))
      simpa using this
    rw [hpoly] at h1
    linarith
  have hB0 : 0 ≤ u - u ^ 3 / 6 + u ^ 5 / 100 := (abs_nonneg _).trans hsin
  have hsq : Real.sin y ^ 2 ≤ (u - u ^ 3 / 6 + u ^ 5 / 100) ^ 2 := by
    rw [← sq_abs (Real.sin y)]
    exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
  have hv : u ^ 2 ≤ 1 / 4 := by nlinarith
  have hpolyineq : (u - u ^ 3 / 6 + u ^ 5 / 100) ^ 2 ≤ u ^ 2 - 4 * u ^ 4 / 15 := by
    set v := u ^ 2 with hvdef
    have hv0 : 0 ≤ v := sq_nonneg u
    have hP : -1 / 15 + 43 * v / 900 - v ^ 2 / 300 + v ^ 3 / 10000 ≤ 0 := by
      nlinarith [mul_nonneg hv0 hv0, mul_nonneg (mul_nonneg hv0 hv0) hv0]
    have hexp : (u - u ^ 3 / 6 + u ^ 5 / 100) ^ 2 - (u ^ 2 - 4 * u ^ 4 / 15) =
        v ^ 2 * (-1 / 15 + 43 * v / 900 - v ^ 2 / 300 + v ^ 3 / 10000) := by
      rw [hvdef]; ring
    nlinarith [mul_nonneg (sq_nonneg v) (neg_nonneg.mpr hP)]
  have hcos : Real.cos t = 1 - 2 * Real.sin y ^ 2 := by
    rw [hty, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq y]
  rw [hcos, hty]
  have : (2 * y) ^ 4 / 30 = 8 * u ^ 4 / 15 := by
    have : y ^ 4 = u ^ 4 := by rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hyu]; ring
    rw [show (2 * y) ^ 4 = 16 * y ^ 4 by ring, this]; ring
  rw [this, show (2 * y) ^ 2 = 4 * u ^ 2 by rw [mul_pow, hyu]; norm_num]
  nlinarith

/-- Partial sums over primes rewritten as range sums of the indicator on primes. -/
private lemma sum_primes_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Ioc 0 N with p.Prime, f p = ∑ n ∈ range (N + 1), {p : ℕ | p.Prime}.indicator f n := by
  rw [Finset.sum_filter]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]; omega
  · intro n hn hn'
    have h0 : n = 0 := by
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Ioc] at hn'
      omega
    subst h0
    simp [Nat.not_prime_zero]

/-- A non-summable family that is nonnegative on primes has partial sums tending to `+∞`. -/
private lemma tendsto_sum_primes_atTop {f : ℕ → ℝ} (hf : ∀ p : ℕ, p.Prime → 0 ≤ f p)
    (h : ¬ Summable (fun p : Nat.Primes => f p)) :
    Tendsto (fun x : ℝ => ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, f p) atTop atTop := by
  set g := {p : ℕ | p.Prime}.indicator f with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => Set.indicator_nonneg (fun p hp => hf p hp) n
  have hgs : ¬ Summable g := fun hs => h (summable_subtype_iff_indicator.mpr hs)
  have hlim := (not_summable_iff_tendsto_nat_atTop_of_nonneg hg0).mp hgs
  have hfl : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  refine (hlim.comp hfl).congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [sum_primes_eq_sum_range]

/-- If the defect series converges over primes, then `1 / 4 < σ`. -/
private lemma quarter_lt_of_summable {σ : ℝ} (hσ : 0 < σ)
    (h : Summable (fun p : Nat.Primes =>
      Real.cos ((p : ℝ) ^ (-σ)) - (1 - ((p : ℝ) ^ (-σ)) ^ 2 / 2))) : 1 / 4 < σ := by
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(4 * σ))) := by
    refine Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun p => ?_) (h.mul_left 30)
    have hq := quartic_le_defect (abs_rpow_neg_le_one (n := p) p.prop.one_lt.le hσ.le)
    rw [rpow_neg_pow] at hq
    push_cast at hq
    linarith
  have := Nat.Primes.summable_rpow.mp hs
  linarith

/-- The fourth-order versine defect at `t = n ^ (-1 / 2)`, kept on primes and zero elsewhere. -/
private noncomputable def primeDefect (n : ℕ) : ℝ :=
  {p : ℕ | p.Prime}.indicator
    (fun m : ℕ => Real.cos ((m : ℝ) ^ (-(1 / 2 : ℝ))) - (1 - ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 / 2)) n

/-- The defect is nonnegative. -/
private lemma primeDefect_nonneg (n : ℕ) : 0 ≤ primeDefect n :=
  Set.indicator_nonneg (fun m _ => by
    linarith [Real.one_sub_sq_div_two_le_cos (x := (m : ℝ) ^ (-(1 / 2 : ℝ)))]) n

/-- The defect is at most `5 / (96 n ^ 2)`. -/
private lemma primeDefect_le (n : ℕ) : primeDefect n ≤ 5 / 96 * ((n : ℝ) ^ 2)⁻¹ := by
  unfold primeDefect
  by_cases hn : n.Prime
  · rw [Set.indicator_of_mem (by exact hn)]
    have ht := abs_rpow_neg_le_one (n := n) hn.one_lt.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hb := Real.cos_bound ht
    have h4 : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4 = ((n : ℝ) ^ 2)⁻¹ := by
      have he : -(((4 : ℕ) : ℝ) * (1 / 2)) = -((2 : ℕ) : ℝ) := by push_cast; ring
      rw [rpow_neg_pow, he, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), h4] at hb
    have := (abs_le.mp hb).2
    linarith
  · rw [Set.indicator_of_notMem (by exact hn)]
    positivity

/-- The defect series converges. -/
private lemma summable_primeDefect : Summable primeDefect :=
  Summable.of_nonneg_of_le primeDefect_nonneg primeDefect_le
    ((Real.summable_nat_pow_inv.mpr one_lt_two).mul_left _)

/-- Tail of the defect series beyond `N`. -/
private lemma primeDefect_tail (N : ℕ) :
    0 ≤ ∑' n, primeDefect n - ∑ n ∈ range (N + 1), primeDefect n ∧
      ∑' n, primeDefect n - ∑ n ∈ range (N + 1), primeDefect n ≤ 5 / 48 / (N + 1) := by
  refine ⟨sub_nonneg.mpr (summable_primeDefect.sum_le_tsum _ (fun n _ => primeDefect_nonneg n)), ?_⟩
  have hle : ∑' n, primeDefect n ≤ ∑ n ∈ range (N + 1), primeDefect n + 5 / 48 / (N + 1) := by
    refine le_of_tendsto summable_primeDefect.hasSum.tendsto_sum_nat
      (eventually_atTop.2 ⟨N + 1, fun M hM => ?_⟩)
    rw [← Finset.sum_range_add_sum_Ico _ hM, Finset.Ico_add_one_left_eq_Ioo]
    have h1 : ∑ i ∈ Ioo N M, primeDefect i ≤ ∑ i ∈ Ioo N M, 5 / 96 * ((i : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum (fun i _ => primeDefect_le i)
    have h2 := sum_Ioo_inv_sq_le (α := ℝ) N M
    rw [← Finset.mul_sum] at h1
    have h3 : 5 / 96 * (2 / ((N : ℝ) + 1)) = 5 / 48 / (N + 1) := by ring
    nlinarith
  linarith

/-- For `σ > 0`: the versine series over primes converges exactly when `σ > 1 / 2`; the series of
`1 - cos p ^ (-σ) - p ^ (-2σ) / 2` converges exactly when `σ > 1 / 4`; for `σ ≤ 1 / 4` the partial
sums of the latter tend to `-∞`; and on `σ = 1 / 2` the partial sums of the versine equal
`(log log x) / 2 + M / 2 + ∑_p (1 - cos p ^ (-1/2) - 1 / (2 p))` up to `O (1 / log x)`, where `M` is
Mertens' constant. -/
theorem prime_versine_phases :
    (∀ σ : ℝ, 0 < σ →
      (Summable (fun p : Nat.Primes => 1 - Real.cos ((p : ℝ) ^ (-σ))) ↔ 1 / 2 < σ)) ∧
    (∀ σ : ℝ, 0 < σ →
      (Summable (fun p : Nat.Primes => 1 - Real.cos ((p : ℝ) ^ (-σ)) - (p : ℝ) ^ (-(2 * σ)) / 2) ↔
        1 / 4 < σ)) ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 →
      Tendsto (fun x : ℝ => primeVersineSum σ x -
        ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (p : ℝ) ^ (-(2 * σ)) / 2) atTop atBot) ∧
    (fun x : ℝ => primeVersineSum (1 / 2) x - Real.log (Real.log x) / 2 -
        (Mertens.M / 2 + ∑' p : Nat.Primes,
          (1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ))) - 1 / (2 * (p : ℝ)))))
      =O[atTop] (fun x : ℝ => 1 / Real.log x) := by
  -- the summand of the second series is minus the fourth-order defect
  have hterm : ∀ (n : ℕ) (σ : ℝ), 1 - Real.cos ((n : ℝ) ^ (-σ)) - (n : ℝ) ^ (-(2 * σ)) / 2 =
      -(Real.cos ((n : ℝ) ^ (-σ)) - (1 - ((n : ℝ) ^ (-σ)) ^ 2 / 2)) := by
    intro n σ
    rw [rpow_neg_pow]; push_cast; ring
  refine ⟨fun σ hσ => ⟨fun h => ?_, fun h => ?_⟩, fun σ hσ => ⟨fun h => ?_, fun h => ?_⟩,
    fun σ hσ hσ' => ?_, ?_⟩
  · -- conjunct 1, forward
    have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * σ))) := by
      refine Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun p => ?_) (h.mul_left (96 / 43))
      have ht := abs_rpow_neg_le_one (n := p) p.prop.one_lt.le hσ.le
      have hb := Real.cos_bound ht
      have h2 := rpow_neg_pow p 2 σ
      have h4 : ((p : ℝ) ^ (-σ)) ^ 4 ≤ ((p : ℝ) ^ (-σ)) ^ 2 := by
        rw [abs_le] at ht
        have h1 : ((p : ℝ) ^ (-σ)) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ((p : ℝ) ^ (-σ)))]
      rw [abs_le] at hb
      push_cast at h2
      rw [← h2]
      rw [show |(p : ℝ) ^ (-σ)| ^ 4 = ((p : ℝ) ^ (-σ)) ^ 4 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at hb
      nlinarith
    have := Nat.Primes.summable_rpow.mp hs
    linarith
  · -- conjunct 1, backward
    refine Summable.of_nonneg_of_le (fun p => by linarith [Real.cos_le_one ((p : ℝ) ^ (-σ))])
      (fun p => ?_) ((Nat.Primes.summable_rpow (r := -(2 * σ)).mpr (by linarith)).div_const 2)
    have h2 := rpow_neg_pow p 2 σ
    push_cast at h2
    rw [← h2]
    linarith [Real.one_sub_sq_div_two_le_cos (x := (p : ℝ) ^ (-σ))]
  · -- conjunct 2, forward
    refine quarter_lt_of_summable hσ ?_
    have := h.neg
    refine this.congr (fun p => ?_)
    simp only [hterm, neg_neg]
  · -- conjunct 2, backward
    refine Summable.of_norm_bounded
      ((Nat.Primes.summable_rpow.mpr (by linarith : -(4 * σ) < -1)).mul_left (5 / 96))
      (fun p => ?_)
    have ht := abs_rpow_neg_le_one (n := p) p.prop.one_lt.le hσ.le
    have hb := Real.cos_bound ht
    rw [hterm, norm_neg, Real.norm_eq_abs]
    have h4 := rpow_neg_pow p 4 σ
    push_cast at h4
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), h4] at hb
    linarith
  · -- conjunct 3
    have hns : ¬ Summable (fun p : Nat.Primes =>
        Real.cos ((p : ℝ) ^ (-σ)) - (1 - ((p : ℝ) ^ (-σ)) ^ 2 / 2)) :=
      fun hs => by linarith [quarter_lt_of_summable hσ hs]
    have hlim := tendsto_sum_primes_atTop
      (f := fun n : ℕ => Real.cos ((n : ℝ) ^ (-σ)) - (1 - ((n : ℝ) ^ (-σ)) ^ 2 / 2))
      (fun p _ => by linarith [Real.one_sub_sq_div_two_le_cos (x := (p : ℝ) ^ (-σ))]) hns
    refine (tendsto_neg_atTop_atBot.comp hlim).congr (fun x => ?_)
    simp only [Function.comp_apply, primeVersineSum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => (hterm n σ).symm)
  · -- conjunct 4
    set T : ℝ → ℝ := fun x => ∑' n, primeDefect n - ∑ n ∈ range (⌊x⌋₊ + 1), primeDefect n with hT
    have hsq : ∀ n : ℕ, ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
      intro n
      have he : -(((2 : ℕ) : ℝ) * (1 / 2)) = -1 := by push_cast; ring
      rw [rpow_neg_pow, he, Real.rpow_neg_one]
    have htsum : ∑' p : Nat.Primes,
        (1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ))) - 1 / (2 * (p : ℝ))) = -∑' n, primeDefect n := by
      have h1 : ∀ p : Nat.Primes, 1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ))) - 1 / (2 * (p : ℝ)) =
          -(Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ))) - (1 - ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 / 2)) := by
        intro p; rw [hsq]; ring
      simp_rw [h1]
      rw [tsum_neg]
      congr 1
      exact tsum_subtype {p : ℕ | p.Prime} (fun m : ℕ =>
        Real.cos ((m : ℝ) ^ (-(1 / 2 : ℝ))) - (1 - ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 / 2))
    have hid : ∀ x : ℝ, primeVersineSum (1 / 2) x - Real.log (Real.log x) / 2 -
        (Mertens.M / 2 + ∑' p : Nat.Primes,
          (1 - Real.cos ((p : ℝ) ^ (-(1 / 2 : ℝ))) - 1 / (2 * (p : ℝ)))) =
        1 / 2 * Mertens.E₂p x + T x := by
      intro x
      have hsplit : primeVersineSum (1 / 2) x =
          1 / 2 * (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) -
            ∑ n ∈ range (⌊x⌋₊ + 1), primeDefect n := by
        unfold primeVersineSum primeDefect
        rw [← sum_primes_eq_sum_range, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hsq]; ring
      rw [htsum, hsplit, hT]
      simp only [Mertens.E₂p]
      ring
    have hTO : T =O[atTop] (fun x : ℝ => 1 / Real.log x) := by
      refine IsBigO.of_bound (5 / 48) ((eventually_ge_atTop (2 : ℝ)).mono (fun x hx => ?_))
      obtain ⟨h0, h1⟩ := primeDefect_tail ⌊x⌋₊
      have hlog : 0 < Real.log x := Real.log_pos (by linarith)
      have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hlx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have hinv : 1 / ((⌊x⌋₊ : ℝ) + 1) ≤ 1 / Real.log x :=
        one_div_le_one_div_of_le hlog (by linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
        abs_of_pos (one_div_pos.mpr hlog)]
      calc T x ≤ 5 / 48 / ((⌊x⌋₊ : ℝ) + 1) := h1
        _ = 5 / 48 * (1 / ((⌊x⌋₊ : ℝ) + 1)) := by ring
        _ ≤ 5 / 48 * (1 / Real.log x) := by gcongr
    exact ((Mertens.E₂p.bound.const_mul_left (1 / 2)).add hTO).congr_left (fun x => (hid x).symm)

end D5.S3.Analytic.Asymptotics.PrimeVersineSums
