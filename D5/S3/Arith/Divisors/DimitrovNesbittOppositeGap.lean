/- GID: D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovNesbittOppositeGap
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For 0<X≤Y≤Z and 1≤s≤Z/Y, N(X,Y,Z)≥s/2+2/(1+s), with equality iff X=Y, Z=sY. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The opposite-gap Nesbitt bound

Let `N(X,Y,Z) = X/(Y+Z) + Y/(X+Z) + Z/(X+Y)` and `G(s) = s/2 + 2/(1+s)`. For
`0 < X ≤ Y ≤ Z` and `1 ≤ s ≤ Z/Y`, `N(X,Y,Z) ≥ G(s)`; when `s > 1`, equality holds exactly
when `X = Y` and `Z = sY`.
-/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovNesbittOppositeGap

/-- At `Y = 1`: `N(x,1,t) ≥ G(t)` for `0 < x ≤ 1 ≤ t`, and equality with `t > 1` forces `x = 1`. -/
private lemma nesbitt_gap {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : 1 ≤ t) :
    t / 2 + 2 / (1 + t) ≤ x / (1 + t) + 1 / (x + t) + t / (x + 1) ∧
    (1 < t → x / (1 + t) + 1 / (x + t) + t / (x + 1) = t / 2 + 2 / (1 + t) → x = 1) := by
  have hC : 0 ≤ t * (x + t) * (1 + t) - 2 * (x + 1) * (x + t - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hx1),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)) (sub_nonneg.mpr ht),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)) (sub_nonneg.mpr hx1),
      mul_nonneg (sub_nonneg.mpr hx1) hx.le]
  have hid : x / (1 + t) + 1 / (x + t) + t / (x + 1) - (t / 2 + 2 / (1 + t)) =
      (1 - x) * (t * (x + t) * (1 + t) - 2 * (x + 1) * (x + t - 1)) /
        (2 * (x + 1) * (x + t) * (1 + t)) := by
    field_simp
    ring
  have hden : 0 < 2 * (x + 1) * (x + t) * (1 + t) := by positivity
  constructor
  · have : 0 ≤ (1 - x) * (t * (x + t) * (1 + t) - 2 * (x + 1) * (x + t - 1)) /
        (2 * (x + 1) * (x + t) * (1 + t)) :=
      div_nonneg (mul_nonneg (by linarith) hC) hden.le
    linarith
  · intro ht1 he
    have hCpos : 0 < t * (x + t) * (1 + t) - 2 * (x + 1) * (x + t - 1) := by
      nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ht1),
        mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hx1),
        mul_pos (mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ht1)) (sub_pos.mpr ht1),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)) (sub_nonneg.mpr hx1),
        mul_nonneg (sub_nonneg.mpr hx1) hx.le]
    have hz : (1 - x) * (t * (x + t) * (1 + t) - 2 * (x + 1) * (x + t - 1)) /
        (2 * (x + 1) * (x + t) * (1 + t)) = 0 := by rw [← hid]; linarith
    rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hden.ne') with h | h
    · linarith
    · linarith

/-- `G(s) = s/2 + 2/(1+s)` is nondecreasing on `[1, ∞)`, strictly once `s > 1`. -/
private lemma G_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    s / 2 + 2 / (1 + s) ≤ t / 2 + 2 / (1 + t) ∧
    (1 < s → t / 2 + 2 / (1 + t) = s / 2 + 2 / (1 + s) → t = s) := by
  have hid : t / 2 + 2 / (1 + t) - (s / 2 + 2 / (1 + s)) =
      (t - s) * (s * t + s + t - 3) / (2 * (1 + s) * (1 + t)) := by
    have h1s : 1 + s ≠ 0 := by linarith
    have h1t : 1 + t ≠ 0 := by linarith
    field_simp
    ring
  have hden : 0 < 2 * (1 + s) * (1 + t) := by
    have : 0 < 1 + s := by linarith
    have : 0 < 1 + t := by linarith
    positivity
  constructor
  · have : 0 ≤ (t - s) * (s * t + s + t - 3) / (2 * (1 + s) * (1 + t)) :=
      div_nonneg (mul_nonneg (by linarith) (by nlinarith)) hden.le
    linarith
  · intro hs1 he
    have hz : (t - s) * (s * t + s + t - 3) / (2 * (1 + s) * (1 + t)) = 0 := by
      rw [← hid]; linarith
    rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hden.ne') with h | h
    · linarith
    · nlinarith

/-- For `0 < X ≤ Y ≤ Z` and `1 ≤ s ≤ Z/Y`,
`X/(Y+Z) + Y/(X+Z) + Z/(X+Y) ≥ s/2 + 2/(1+s)`; for `s > 1` equality holds if and only if
`X = Y` and `Z = sY`. -/
theorem opposite_gap {X Y Z s : ℝ} (hX : 0 < X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) (hs : 1 ≤ s)
    (hsZ : s ≤ Z / Y) :
    s / 2 + 2 / (1 + s) ≤ X / (Y + Z) + Y / (X + Z) + Z / (X + Y) ∧
    (1 < s → (X / (Y + Z) + Y / (X + Z) + Z / (X + Y) = s / 2 + 2 / (1 + s) ↔
      X = Y ∧ Z = s * Y)) := by
  have hY : 0 < Y := lt_of_lt_of_le hX hXY
  have hx0 : 0 < X / Y := div_pos hX hY
  have hx1 : X / Y ≤ 1 := (div_le_one hY).mpr hXY
  have ht : 1 ≤ Z / Y := (one_le_div hY).mpr hYZ
  have hN : X / (Y + Z) + Y / (X + Z) + Z / (X + Y) =
      X / Y / (1 + Z / Y) + 1 / (X / Y + Z / Y) + Z / Y / (X / Y + 1) := by
    have hZ : 0 < Z := lt_of_lt_of_le hY hYZ
    field_simp
  obtain ⟨n1, n2⟩ := nesbitt_gap hx0 hx1 ht
  obtain ⟨g1, g2⟩ := G_mono hs hsZ
  refine ⟨by rw [hN]; linarith, fun hs1 => ⟨fun h => ?_, ?_⟩⟩
  · rw [hN] at h
    have e2 := g2 hs1 (by linarith)
    have e1 := n2 (by linarith) (by linarith)
    rw [div_eq_iff hY.ne'] at e1 e2
    exact ⟨by linarith, e2⟩
  · rintro ⟨rfl, rfl⟩
    have h1s : 1 + s ≠ 0 := by linarith
    field_simp
    ring

end D5.S3.Arith.Divisors.DimitrovNesbittOppositeGap
