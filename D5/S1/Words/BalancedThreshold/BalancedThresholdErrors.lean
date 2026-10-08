/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdErrors
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdErrors
   mirror-E: none(waiver:infinite-quadratic-error-orbit)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence]
   utility: none
   digest: Induction identifies the exact alternating tail ratio of every continuant error. -/

import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import D5.S1.Words.BalancedThreshold.BalancedThresholdExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

/-- The predecessor error is the negative complete quotient times the current error.
The initial tail is exceptional; subsequent tails alternate at every unbounded index. -/
theorem uniform_continuant_errors (t : ℕ) (ht : 5 ≤ t) :
    let theta := uniformSlope t / (1 - uniformSlope t)
    let g := GenContFract.of theta
    let digit := fun n : ℕ =>
      (if n = 0 then t + 2 else if n = 1 then t
        else if n % 2 = 0 then t - 2 else t + 1 : ℕ)
    let tail := fun n : ℕ =>
      if n = 0 then 1 / ((t : ℝ) + quadraticTail t)
      else if n % 2 = 1 then quadraticTail t
      else 1 / ((t : ℝ) + 1 + quadraticTail t)
    ∀ n, 0 < tail n ∧ tail n < 1 ∧
      (g.contsAux (n + 1)).a - theta * (g.contsAux (n + 1)).b ≠ 0 ∧
      (g.contsAux n).a - theta * (g.contsAux n).b =
        -((digit n : ℝ) + tail n) *
          ((g.contsAux (n + 1)).a - theta * (g.contsAux (n + 1)).b) := by
  let x := quadraticTail t
  let y := 1 / ((t : ℝ) + 1 + x)
  let delta := 1 / ((t : ℝ) + x)
  let theta := uniformSlope t / (1 - uniformSlope t)
  let g := GenContFract.of theta
  let digit := fun n : ℕ =>
    (if n = 0 then t + 2 else if n = 1 then t
      else if n % 2 = 0 then t - 2 else t + 1 : ℕ)
  let tail := fun n : ℕ => if n = 0 then delta else if n % 2 = 1 then x else y
  have hp :
    Irrational (quadraticTail t) ∧
    ((t : ℝ) - 2) * quadraticTail t ^ 2 +
      ((t : ℝ) - 2) * ((t : ℝ) + 1) * quadraticTail t - ((t : ℝ) + 1) = 0 ∧
    1 / ((t : ℝ) - 1) < quadraticTail t ∧
    quadraticTail t < 1 / ((t : ℝ) - 2) ∧
    2 < (2 * (t : ℝ) - 1) * quadraticTail t ∧
    (2 * (t : ℝ) + 1) * quadraticTail t < t ∧
    Irrational (uniformSlope t) ∧
    1 / ((t : ℝ) + 4) < uniformSlope t ∧
    uniformSlope t < 1 / ((t : ℝ) + 3) := by
    let N := (t - 2) * (t + 1)
    have hN : 18 ≤ N := by dsimp [N]; nlinarith [show 3 ≤ t - 2 by omega]
    have hns : ¬ IsSquare (N * (N + 4)) := by
      have hl : (N + 1) * (N + 1) < N * (N + 4) := by nlinarith
      have hu : N * (N + 4) < (N + 1 + 1) * (N + 1 + 1) := by nlinarith
      rintro ⟨k, hk⟩
      exact Nat.not_exists_sq hl hu ⟨k, hk.symm⟩
    have hsirr := irrational_sqrt_natCast_iff.mpr hns
    have hirr : Irrational (quadraticTail t) := by
      change Irrational ((Real.sqrt (N * (N + 4) : ℕ) - N) / (2 * (t - 2 : ℕ)))
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (hsirr.sub_natCast N).div_natCast (by omega : 2 * (t - 2) ≠ 0)
    have htR : (5 : ℝ) ≤ t := by exact_mod_cast ht
    have hA : (0 : ℝ) < (t : ℝ) - 2 := by linarith
    have hB : (0 : ℝ) < (t : ℝ) + 1 := by linarith
    have hcast : (N : ℝ) = ((t : ℝ) - 2) * ((t : ℝ) + 1) := by
      dsimp [N]
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add]
      norm_num
    let s := Real.sqrt (N * (N + 4) : ℕ)
    let x := quadraticTail t
    have hs : s ^ 2 = (N : ℝ) * ((N : ℝ) + 4) := by
      simpa [s] using Real.sq_sqrt (Nat.cast_nonneg (N * (N + 4)))
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNs : (N : ℝ) < s := by nlinarith
    have hxformula : x = (s - N) / (2 * ((t : ℝ) - 2)) := by
      change (s - (N : ℝ)) / (2 * (t - 2 : ℕ)) = _
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hxpos : 0 < x := by rw [hxformula]; positivity
    have hxe : 2 * ((t : ℝ) - 2) * x = s - N := by
      rw [hxformula]
      field_simp
    have hpoly : ((t : ℝ) - 2) * x ^ 2 +
        ((t : ℝ) - 2) * ((t : ℝ) + 1) * x - ((t : ℝ) + 1) = 0 := by
      have he := congrArg (fun z : ℝ => z ^ 2) hxe
      rw [hcast] at hs he
      nlinarith
    have hupper : x < 1 / ((t : ℝ) - 2) := by
      rw [lt_div_iff₀ hA]
      by_contra hn
      have hax : 1 ≤ ((t : ℝ) - 2) * x := by nlinarith
      have hbx : (t : ℝ) + 1 ≤ ((t : ℝ) + 1) * (((t : ℝ) - 2) * x) :=
        le_mul_of_one_le_right hB.le hax
      nlinarith [mul_pos hA (sq_pos_of_pos hxpos)]
    have hlower : 1 / ((t : ℝ) - 1) < x := by
      rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (t : ℝ) - 1)]
      by_contra hn
      have hxle : x ≤ 1 := by
        have ht3 : (3 : ℝ) ≤ (t : ℝ) - 2 := by linarith
        have := (lt_div_iff₀ hA).mp hupper
        nlinarith
      have hsq : x ^ 2 ≤ x := by nlinarith
      have hAx : ((t : ℝ) - 2) * x ^ 2 ≤ ((t : ℝ) - 2) * x :=
        mul_le_mul_of_nonneg_left hsq hA.le
      have hsum : ((t : ℝ) - 2) * x +
          ((t : ℝ) - 2) * ((t : ℝ) + 1) * x < (t : ℝ) + 1 := by
        nlinarith
      linarith
    have hsep1 : 2 < (2 * (t : ℝ) - 1) * x := by
      have := (div_lt_iff₀ (by linarith : (0 : ℝ) < (t : ℝ) - 1)).mp hlower
      nlinarith
    have hmargin : (2 * (t : ℝ) + 1) < (t : ℝ) * ((t : ℝ) - 2) := by
      nlinarith [sq_nonneg ((t : ℝ) - 5)]
    have hsep2 : (2 * (t : ℝ) + 1) * x < t := by
      have := (lt_div_iff₀ hA).mp hupper
      have hm := mul_lt_mul_of_pos_right hmargin hxpos
      nlinarith
    let delta := 1 / ((t : ℝ) + x)
    have hd0 : 0 < delta := by dsimp [delta]; positivity
    have hd1 : delta < 1 := by
      dsimp [delta]
      rw [div_lt_one (by positivity : (0 : ℝ) < (t : ℝ) + x)]
      linarith
    have hdi : Irrational delta := by
      simpa [delta, one_div] using (hirr.natCast_add t).inv
    have hai : Irrational (uniformSlope t) := by
      have hi := (hdi.natCast_add (t + 3)).inv
      simpa [uniformSlope, delta, x, Nat.cast_add, one_div, add_assoc] using hi
    have hal : 1 / ((t : ℝ) + 4) < uniformSlope t := by
      change 1 / ((t : ℝ) + 4) < 1 / ((t : ℝ) + 3 + delta)
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hau : uniformSlope t < 1 / ((t : ℝ) + 3) := by
      change 1 / ((t : ℝ) + 3 + delta) < 1 / ((t : ℝ) + 3)
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    exact ⟨hirr, hpoly, hlower, hupper, hsep1, hsep2, hai, hal, hau⟩
  have htR : (5 : ℝ) ≤ t := by exact_mod_cast ht
  have hA : (0 : ℝ) < (t : ℝ) - 2 := by linarith
  have hx0 : 0 < x :=
    lt_trans (one_div_pos.mpr (by linarith : (0 : ℝ) < (t : ℝ) - 1)) hp.2.2.1
  have hx1 : x < 1 := by
    have he := (lt_div_iff₀ hA).mp hp.2.2.2.1
    nlinarith only [he, htR, hx0]
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy1 : y < 1 := by
    dsimp [y]
    rw [div_lt_one (by positivity)]
    linarith
  have hd0 : 0 < delta := by dsimp [delta]; positivity
  have hd1 : delta < 1 := by
    dsimp [delta]
    rw [div_lt_one (by positivity)]
    linarith
  have hpoly : ((t : ℝ) - 2) * x ^ 2 +
      ((t : ℝ) - 2) * ((t : ℝ) + 1) * x - ((t : ℝ) + 1) = 0 := hp.2.1
  have hxy : x * ((t : ℝ) - 2 + y) = 1 := by
    dsimp [y]
    field_simp
    nlinarith only [hpoly]
  have hyx : y * ((t : ℝ) + 1 + x) = 1 := by
    dsimp [y]
    exact one_div_mul_cancel (by positivity)
  have hdx : delta * ((t : ℝ) + x) = 1 := by
    dsimp [delta]
    exact one_div_mul_cancel (by positivity)
  have htheta : theta = 1 / ((t : ℝ) + 2 + delta) := by
    have hdne : ((t : ℝ) + 3 + delta) ≠ 0 := by positivity
    change (1 / ((t : ℝ) + 3 + delta)) /
      (1 - 1 / ((t : ℝ) + 3 + delta)) = _
    rw [div_div]
    congr 1
    rw [mul_sub, mul_one, mul_one_div_cancel hdne]
    ring
  have bounds : ∀ n, 0 < tail n ∧ tail n < 1 := by
    intro n
    dsimp [tail]
    split_ifs <;> constructor <;> assumption
  have step : ∀ n, tail n * ((digit (n + 1) : ℝ) + tail (n + 1)) = 1 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [tail, digit] using hdx
    by_cases hn1 : n % 2 = 1
    · have he : (n + 1) % 2 = 0 := by omega
      have hne1 : n + 1 ≠ 1 := by omega
      simpa [tail, digit, hn, hn1, he, hne1, Nat.cast_sub (by omega : 2 ≤ t)]
        using hxy
    · have he : (n + 1) % 2 = 1 := by omega
      have hne1 : n + 1 ≠ 1 := by omega
      simpa [tail, digit, hn, hn1, he, hne1, Nat.cast_add, add_assoc] using hyx
  have digits : ∀ n, g.s.get? n = some ⟨1, (digit n : ℝ)⟩ :=
    (uniform_ratio_expansion t ht).2
  have hg0 : g.h = 0 := (uniform_ratio_expansion t ht).1
  let e := fun n => (g.contsAux (n + 1)).a - theta * (g.contsAux (n + 1)).b
  let f := fun n => (g.contsAux n).a - theta * (g.contsAux n).b
  have recurrence : ∀ n, e (n + 1) = (digit n : ℝ) * e n + f n := by
    intro n
    dsimp only [e, f]
    rw [GenContFract.contsAux_recurrence (digits n) rfl rfl]
    dsimp only
    ring
  have orbit : ∀ n, e n ≠ 0 ∧ f n = -((digit n : ℝ) + tail n) * e n := by
    intro n
    induction n with
    | zero =>
      have he0 : e 0 = -theta := by simp [e, GenContFract.contsAux, hg0]
      have hf0 : f 0 = 1 := by simp [f, GenContFract.contsAux]
      rw [he0, hf0]
      constructor
      · rw [htheta]
        exact neg_ne_zero.mpr (ne_of_gt (by positivity))
      · simp only [digit, tail, if_pos rfl, Nat.cast_add, Nat.cast_ofNat]
        rw [htheta]
        field_simp
    | succ n ih =>
      have he : e (n + 1) = -(tail n) * e n := by
        rw [recurrence, ih.2]
        ring
      refine ⟨?_, ?_⟩
      · rw [he]
        exact mul_ne_zero (neg_ne_zero.mpr (bounds n).1.ne') ih.1
      · change e n = -((digit (n + 1) : ℝ) + tail (n + 1)) * e (n + 1)
        rw [he]
        have hs := step n
        nlinarith only [congrArg (fun v : ℝ => v * e n) hs]
  change ∀ n, 0 < tail n ∧ tail n < 1 ∧ e n ≠ 0 ∧
    f n = -((digit n : ℝ) + tail n) * e n
  intro n
  exact ⟨(bounds n).1, (bounds n).2, (orbit n).1, (orbit n).2⟩

end D5.S1.Words.BalancedThreshold
