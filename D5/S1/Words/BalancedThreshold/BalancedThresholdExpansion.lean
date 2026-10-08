/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdExpansion
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdExpansion
   mirror-E: none(waiver:infinite-period-two-expansion)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.Computation.Translations]
   utility: none
   digest: The computed ratio expansion has two initial digits and an infinite alternating tail. -/

import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import D5.S1.Words.BalancedThreshold.BalancedThresholdSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

/-- The floor algorithm follows the two reciprocal quadratic tails at every depth. -/
theorem uniform_ratio_expansion (t : ℕ) (ht : 5 ≤ t) :
    let theta := uniformSlope t / (1 - uniformSlope t)
    (GenContFract.of theta).h = 0 ∧
    ∀ n, (GenContFract.of theta).s.get? n = some ⟨1,
      ((if n = 0 then t + 2 else if n = 1 then t
        else if n % 2 = 0 then t - 2 else t + 1 : ℕ) : ℝ)⟩ := by
  let A := t - 2
  let B := t + 1
  let x := quadraticTail t
  let y := 1 / ((B : ℝ) + x)
  let delta := 1 / ((t : ℝ) + x)
  let theta := 1 / ((t : ℝ) + 2 + delta)
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
  have hA : (A : ℝ) = (t : ℝ) - 2 := by
    dsimp [A]
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hB : (B : ℝ) = (t : ℝ) + 1 := by simp [B]
  have hx0 : 0 < x :=
    lt_trans (one_div_pos.mpr (by linarith : (0 : ℝ) < (t : ℝ) - 1)) hp.2.2.1
  have hx1 : x < 1 := by
    have hx := hp.2.2.2.1
    have hden : (0 : ℝ) < (t : ℝ) - 2 := by linarith
    have hm := (lt_div_iff₀ hden).mp hx
    nlinarith only [hm, hx0, htR]
  have hy0 : 0 < y := by dsimp [y]; rw [hB]; positivity
  have hy1 : y < 1 := by
    dsimp [y]
    rw [hB, div_lt_one (by positivity)]
    linarith
  have hd0 : 0 < delta := by dsimp [delta]; positivity
  have hd1 : delta < 1 := by
    dsimp [delta]
    rw [div_lt_one (by positivity)]
    linarith
  have htheta0 : 0 < theta := by dsimp [theta]; positivity
  have htheta1 : theta < 1 := by
    dsimp [theta]
    rw [div_lt_one (by positivity)]
    linarith
  have hpoly : (A : ℝ) * x ^ 2 + (A : ℝ) * (B : ℝ) * x - (B : ℝ) = 0 := by
    rw [hA, hB]
    exact hp.2.1
  have hxinv : x⁻¹ = (A : ℝ) + y := by
    apply inv_eq_of_mul_eq_one_right
    dsimp [y]
    field_simp [ne_of_gt (by positivity : 0 < (B : ℝ) + x)]
    nlinarith only [hpoly]
  have hyinv : y⁻¹ = (B : ℝ) + x := by simp [y, one_div]
  have hdinv : delta⁻¹ = (t : ℝ) + x := by simp [delta, one_div]
  have hthetainv : theta⁻¹ = (t : ℝ) + 2 + delta := by simp [theta, one_div]
  have floor_add : ∀ (a : ℕ) z, 0 ≤ z → z < 1 → ⌊(a : ℝ) + z⌋ = (a : ℤ) := by
    intro a z hz0 hz1
    rw [Int.floor_natCast_add, Int.floor_eq_zero_iff.mpr ⟨hz0, hz1⟩, add_zero]
  have fract_add : ∀ (a : ℕ) z, 0 ≤ z → z < 1 → Int.fract ((a : ℝ) + z) = z := by
    intro a z hz0 hz1
    rw [Int.fract, floor_add a z hz0 hz1]
    simp only [Int.cast_natCast, add_sub_cancel_left]
  let X := (A : ℝ) + y
  let Y := (B : ℝ) + x
  have hfloorX : ⌊(A : ℝ) + y⌋ = (A : ℤ) := floor_add A y hy0.le hy1
  have hfloorY : ⌊(B : ℝ) + x⌋ = (B : ℤ) := floor_add B x hx0.le hx1
  have hfractX : Int.fract X = y := fract_add A y hy0.le hy1
  have hfractY : Int.fract Y = x := fract_add B x hx0.le hx1
  have alternating : ∀ n,
      (GenContFract.of X).s.get? n =
        some ⟨1, ((if n % 2 = 0 then B else A : ℕ) : ℝ)⟩ ∧
      (GenContFract.of Y).s.get? n =
        some ⟨1, ((if n % 2 = 0 then A else B : ℕ) : ℝ)⟩ := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa only [Stream'.Seq.head, hfractX, hyinv, hfloorY,
            Int.cast_natCast, Nat.zero_mod, ite_true] using
              GenContFract.of_s_head (v := X) (by rw [hfractX]; exact hy0.ne')
        · simpa only [Stream'.Seq.head, hfractY, hxinv, hfloorX,
            Int.cast_natCast, Nat.zero_mod, ite_true] using
              GenContFract.of_s_head (v := Y) (by rw [hfractY]; exact hx0.ne')
    | succ n ih =>
        rw [GenContFract.of_s_succ, GenContFract.of_s_succ, hfractX, hfractY,
          hyinv, hxinv]
        by_cases hn : n % 2 = 0
        · have hn' : ¬ (n + 1) % 2 = 0 := by omega
          simpa only [if_pos hn, if_neg hn'] using And.intro ih.2 ih.1
        · have hn' : (n + 1) % 2 = 0 := by omega
          simpa only [if_neg hn, if_pos hn'] using And.intro ih.2 ih.1
  let Q := (t : ℝ) + x
  let P := ((t + 2 : ℕ) : ℝ) + delta
  have hfloorQ : ⌊(t : ℝ) + x⌋ = (t : ℤ) := floor_add t x hx0.le hx1
  have hfractQ : Int.fract Q = x := fract_add t x hx0.le hx1
  have hfloorP : ⌊P⌋ = (t + 2 : ℕ) := floor_add (t + 2) delta hd0.le hd1
  have hfractP : Int.fract P = delta := fract_add (t + 2) delta hd0.le hd1
  have hfracttheta : Int.fract theta = theta := by
    rw [Int.fract, Int.floor_eq_zero_iff.mpr ⟨htheta0.le, htheta1⟩]
    simp
  have hthetaP : theta⁻¹ = P := by
    rw [hthetainv]
    simp [P, Nat.cast_add, add_assoc]
  have tailQ : ∀ n, (GenContFract.of Q).s.get? n =
      some ⟨1, ((if n % 2 = 0 then A else B : ℕ) : ℝ)⟩ := by
    intro n
    cases n with
    | zero =>
        simpa only [Stream'.Seq.head, hfractQ, hxinv, hfloorX,
          Int.cast_natCast, Nat.zero_mod, ite_true] using
            GenContFract.of_s_head (v := Q) (by rw [hfractQ]; exact hx0.ne')
    | succ n =>
        rw [GenContFract.of_s_succ, hfractQ, hxinv]
        have hn := (alternating n).1
        by_cases he : n % 2 = 0
        · have he' : ¬ (n + 1) % 2 = 0 := by omega
          simpa only [if_pos he, if_neg he'] using hn
        · have he' : (n + 1) % 2 = 0 := by omega
          simpa only [if_neg he, if_pos he'] using hn
  have hratio : uniformSlope t / (1 - uniformSlope t) = theta := by
    have hdne : ((t : ℝ) + 3 + delta) ≠ 0 := by positivity
    change (1 / ((t : ℝ) + 3 + delta)) /
      (1 - 1 / ((t : ℝ) + 3 + delta)) = 1 / ((t : ℝ) + 2 + delta)
    rw [div_div]
    congr 1
    rw [mul_sub, mul_one, mul_one_div_cancel hdne]
    ring
  change (GenContFract.of (uniformSlope t / (1 - uniformSlope t))).h = 0 ∧ _
  rw [hratio]
  constructor
  · rw [GenContFract.of_h_eq_floor, Int.floor_eq_zero_iff.mpr ⟨htheta0.le, htheta1⟩]
    simp
  · intro n
    cases n with
    | zero =>
        simpa only [Stream'.Seq.head, hfracttheta, hthetaP, hfloorP, Int.cast_natCast,
          ite_true] using
            GenContFract.of_s_head (v := theta) (by rw [hfracttheta]; exact htheta0.ne')
    | succ n =>
        rw [GenContFract.of_s_succ, hfracttheta, hthetaP]
        cases n with
        | zero =>
            simpa only [Stream'.Seq.head, hfractP, hdinv, hfloorQ,
              Int.cast_natCast, if_neg (by omega : ¬ 0 + 1 = 0), ite_true] using
                GenContFract.of_s_head (v := P) (by rw [hfractP]; exact hd0.ne')
        | succ n =>
            rw [GenContFract.of_s_succ, hfractP, hdinv]
            have he : (n + 1 + 1) % 2 = n % 2 := by omega
            simpa only [if_neg (by omega : ¬ n + 1 + 1 = 0),
              if_neg (by omega : ¬ n + 1 + 1 = 1), he, A, B] using tailQ n

end D5.S1.Words.BalancedThreshold
