/- GID: D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/EgyptianFiveFirstMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separation of the first and maximal third denominators forces residue one modulo five. -/

import Mathlib.Tactic
import Mathlib.NumberTheory.Multiplicity

namespace D5.S3.Arith.Congruence.EgyptianFiveFirstMaximum

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def Sol (k x y z : ℤ) : Prop :=
  0 < x ∧ x < y ∧ y < z ∧ 5 * x * y * z = k * (y * z + x * z + x * y)

private theorem basic_bounds {k x y z : ℤ} (h : Sol k x y z) :
    0 < k ∧ k < 5 * x ∧ 5 * x < 3 * k ∧
      0 < (5 * x - k) * y - k * x := by
  rcases h with ⟨hx, hxy, hyz, he⟩
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hk : 0 < k := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (show k ≤ 0 by omega)
      (show 0 ≤ y * z + x * z + x * y by positivity)
    have : 0 < 5 * x * y * z := by positivity
    nlinarith
  have he' : ((5 * x - k) * y - k * x) * z = k * x * y := by
    nlinarith [he]
  have hd : 0 < (5 * x - k) * y - k * x := by
    have hp : 0 < k * x * y := by positivity
    exact (mul_pos_iff_of_pos_right hz).mp (he' ▸ hp)
  have ha : k < 5 * x := by
    have : 0 < (5 * x - k) * y := by nlinarith [mul_pos hk hx]
    have := (mul_pos_iff_of_pos_right hy).mp this
    omega
  have h1 : x * z < y * z := mul_lt_mul_of_pos_right hxy hz
  have h2 : x * y < y * z := by nlinarith
  have h3 : k * (y * z + x * z + x * y) < k * (3 * (y * z)) :=
    mul_lt_mul_of_pos_left (by omega) hk
  have : 5 * x < 3 * k := by
    have : (5 * x) * (y * z) < (3 * k) * (y * z) := by nlinarith [he]
    exact (mul_lt_mul_iff_of_pos_right (mul_pos hy hz)).mp this
  exact ⟨hk, ha, this, hd⟩

/-- A positive lower bound on the integer residual bounds the third denominator. -/
private theorem residual_bound {k x y z d : ℤ} (h : Sol k x y z)
    (_hd : 0 < d) (hle : d ≤ (5 * x - k) * y - k * x) :
    d * (5 * x - k) * z ≤ (k * x) * (k * x + d) := by
  have hb := basic_bounds h
  have hz : 0 < z := lt_trans h.1 (lt_trans h.2.1 h.2.2.1)
  have he : ((5 * x - k) * y - k * x) * z = k * x * y := by
    nlinarith [h.2.2.2]
  have hf : ((5 * x - k) * y - k * x) * ((5 * x - k) * z - k * x) =
      (k * x) ^ 2 := by
    linear_combination (5 * x - k) * he
  have hfpos : 0 < (5 * x - k) * z - k * x := by
    have hp : 0 < (k * x) ^ 2 := by have := h.1; have := hb.1; positivity
    exact (mul_pos_iff_of_pos_left hb.2.2.2).mp (hf ▸ hp)
  have := mul_le_mul_of_nonneg_right hle (le_of_lt hfpos)
  nlinarith [hf]

private theorem same_x_antitone {k x y z v w : ℤ}
    (h : Sol k x y z) (h' : Sol k x v w) (hy : y ≤ v) : w ≤ z := by
  have hb := basic_bounds h
  have hz : 0 < z := lt_trans h.1 (lt_trans h.2.1 h.2.2.1)
  have hw : 0 < w := by have := h'.1; have := h'.2.1; have := h'.2.2.1; omega
  have e : ((5 * x - k) * y - k * x) * z = k * x * y := by
    nlinarith [h.2.2.2]
  have e' : ((5 * x - k) * v - k * x) * w = k * x * v := by
    nlinarith [h'.2.2.2]
  have eq : ((5 * x - k) * y - k * x) * (z - w) =
      ((5 * x - k) * w - k * x) * (v - y) := by
    linear_combination e - e'
  have ha : 0 < (5 * x - k) * w - k * x := by
    have eb := (basic_bounds h').2.2.2
    nlinarith [mul_pos (show 0 < 5 * x - k by omega) (show 0 < w - v by have := h'.2.2.1; omega)]
  have : 0 ≤ ((5 * x - k) * y - k * x) * (z - w) := by
    rw [eq]
    exact mul_nonneg (le_of_lt ha) (by omega)
  have := (mul_nonneg_iff_of_pos_left hb.2.2.2).mp this
  omega

/-- Beyond the midpoint, the strict order supplies a stronger residual bound. -/
private theorem far_bound {k x y z : ℤ} (h : Sol k x y z)
    (hfar : 2 * k ≤ 5 * x) : 25 * z ≤ 2 * k * (2 * k + 5) := by
  have hb := basic_bounds h
  have hx := h.1
  have hk := hb.1
  have hy := h.2.1
  let a := 5 * x - k
  let b := k * x
  have ha : 0 < a := by dsimp [a]; omega
  have hbpos : 0 < b := mul_pos hb.1 hx
  have hd : a ≤ (5 * x - k) * y - k * x := by
    have hp := mul_nonneg (show 0 ≤ 5 * x - 2 * k by omega) (le_of_lt hx)
    have hp' := mul_nonneg (le_of_lt ha) (show 0 ≤ y - x - 1 by omega)
    dsimp [a] at *
    nlinarith
  have bound : a * a * z ≤ b * (b + a) := residual_bound h ha hd
  have ht : 0 ≤ 2 * k * a - 5 * b := by
    have := mul_nonneg (le_of_lt hb.1) (show 0 ≤ 5 * x - 2 * k by omega)
    dsimp [a, b]
    nlinarith
  have hp := mul_nonneg ht
    (show 0 ≤ 2 * k * a + 5 * b + 5 * a by positivity)
  have ha2 : 0 < a * a := mul_pos ha ha
  nlinarith

/-- Before the midpoint, the residual upper bound decreases with the first denominator. -/
private theorem near_bound {k x y z l d W : ℤ} (h : Sol k x y z)
    (hl : k < 5 * l) (hlx : l ≤ x) (hx : 5 * x ≤ 2 * k)
    (hd : 0 < d) (he : d ≤ (5 * x - k) * y - k * x)
    (hend : (k * l) * (k * l + d) ≤ d * (5 * l - k) * W) : z ≤ W := by
  have hb := basic_bounds h
  have hlpos : 0 < l := by omega
  have ax : 0 < 5 * x - k := by omega
  have al : 0 < 5 * l - k := by omega
  have hr := residual_bound h hd he
  have ht : 0 ≤ k * (x + l) - 5 * x * l + d := by
    have := mul_nonneg (show 0 ≤ 2 * k - 5 * x by omega) (le_of_lt hlpos)
    have := mul_nonneg (le_of_lt hb.1) (show 0 ≤ x - l by omega)
    nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg k) (show 0 ≤ x - l by omega)) ht
  have hm := mul_le_mul_of_nonneg_right hend (le_of_lt ax)
  have hn := mul_le_mul_of_nonneg_right hr (le_of_lt al)
  have hc : 0 < d * (5 * l - k) * (5 * x - k) := by positivity
  have hc' : d * (5 * l - k) * (5 * x - k) * z ≤
      d * (5 * l - k) * (5 * x - k) * W := by
    nlinarith only [hp, hm, hn]
  exact (mul_le_mul_iff_of_pos_left hc).mp hc'

/-- Residual numerator eight cannot have denominator gap one: that would give a square
congruent to three modulo four. -/
private theorem residual_eight_gap {k x y z : ℤ} (h : Sol k x y z)
    (ha : 5 * x - k = 8) : 2 ≤ (5 * x - k) * y - k * x := by
  have hd := (basic_bounds h).2.2.2
  by_contra hbad
  have he : (5 * x - k) * y - k * x = 1 := by omega
  have he' : k ^ 2 + 5 = 8 * (5 * y - k) := by nlinarith
  have hm : k ^ 2 % 8 = 3 := by omega
  rcases Int.even_or_odd k with heven | hodd
  · obtain ⟨t, ht⟩ := heven
    have heq : k ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
    omega
  · have := Int.sq_mod_four_eq_one_of_odd hodd
    omega


private theorem later_zero {q x y z : ℤ} (hq : 1 ≤ q) (h : Sol (5 * q) x y z)
    (hl : q + 2 ≤ x) : z ≤ q * (q + 1) * (q * (q + 1) + 1) := by
  let W := q * (q + 1) * (q * (q + 1) + 1)
  have hf : 2 * (5 * q) * (2 * (5 * q) + 5) ≤ 25 * W := by
    dsimp [W]
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 1 := ⟨q - 1, by omega, by ring⟩
    apply le_of_sub_nonneg
    ring_nf
    positivity
  by_cases hfar : 2 * (5 * q) ≤ 5 * x
  · have := far_bound h hfar
    dsimp [W] at hf
    omega
  · apply near_bound h (l := q + 2) (d := 5) (by omega) hl (by omega) (by norm_num)
    · have hd := (basic_bounds h).2.2.2
      have he : (5 * x - 5 * q) * y - 5 * q * x = 5 * ((x - q) * y - q * x) := by ring
      omega
    · obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 1 := ⟨q - 1, by omega, by ring⟩
      apply le_of_sub_nonneg
      ring_nf
      positivity

private theorem later_three {q x y z W : ℤ} (hq : 2 ≤ q)
    (h : Sol (5 * q + 3) x y z) (hl : q + 2 ≤ x)
    (hW : ((5 * q + 3) * (q + 1)) * ((5 * q + 3) * (q + 1) + 2) ≤ 4 * W) : z ≤ W := by
  have hf : 8 * (5 * q + 3) * (2 * (5 * q + 3) + 5) ≤
      25 * (((5 * q + 3) * (q + 1)) * ((5 * q + 3) * (q + 1) + 2)) := by
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 2 := ⟨q - 2, by omega, by ring⟩
    apply le_of_sub_nonneg
    ring_nf
    positivity
  by_cases hfar : 2 * (5 * q + 3) ≤ 5 * x
  · have := far_bound h hfar
    nlinarith
  · apply near_bound h (l := q + 2) (d := 1) (by omega) hl (by omega) (by norm_num)
    · have := (basic_bounds h).2.2.2; omega
    · have hend : 4 * (((5 * q + 3) * (q + 2)) * ((5 * q + 3) * (q + 2) + 1)) ≤
          7 * (((5 * q + 3) * (q + 1)) * ((5 * q + 3) * (q + 1) + 2)) := by
        obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 2 := ⟨q - 2, by omega, by ring⟩
        apply le_of_sub_nonneg
        ring_nf
        positivity
      nlinarith only [hend, hW]

private theorem later_four {q x y z : ℤ} (hq : 0 ≤ q)
    (h : Sol (5 * q + 4) x y z) (hl : q + 2 ≤ x) :
    z ≤ ((5 * q + 4) * (q + 1)) * ((5 * q + 4) * (q + 1) + 1) := by
  have hf : 2 * (5 * q + 4) * (2 * (5 * q + 4) + 5) ≤
      25 * (((5 * q + 4) * (q + 1)) * ((5 * q + 4) * (q + 1) + 1)) := by
    apply le_of_sub_nonneg
    ring_nf
    positivity
  by_cases hfar : 2 * (5 * q + 4) ≤ 5 * x
  · have := far_bound h hfar
    nlinarith
  · apply near_bound h (l := q + 2) (d := 1) (by omega) hl (by omega) (by norm_num)
    · have := (basic_bounds h).2.2.2; omega
    · apply le_of_sub_nonneg
      ring_nf
      positivity

private theorem later_two_coprime {q x y z W : ℤ} (hq : 1 ≤ q)
    (h : Sol (5 * q + 2) x y z) (hl : q + 2 ≤ x)
    (hW : ((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 1) ≤ 3 * W) : z ≤ W := by
  have hf : 6 * (5 * q + 2) * (2 * (5 * q + 2) + 5) ≤
      25 * (((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 1)) := by
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 1 := ⟨q - 1, by omega, by ring⟩
    apply le_of_sub_nonneg
    ring_nf
    positivity
  by_cases hfar : 2 * (5 * q + 2) ≤ 5 * x
  · have := far_bound h hfar
    nlinarith
  · apply near_bound h (l := q + 2) (d := 1) (by omega) hl (by omega) (by norm_num)
    · have := (basic_bounds h).2.2.2; omega
    · have hend : 3 * (((5 * q + 2) * (q + 2)) * ((5 * q + 2) * (q + 2) + 1)) ≤
          8 * (((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 1)) := by
        obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 1 := ⟨q - 1, by omega, by ring⟩
        apply le_of_sub_nonneg
        ring_nf
        positivity
      nlinarith only [hend, hW]

private theorem later_two_divisible {q x y z W : ℤ} (hq : 11 ≤ q)
    (h : Sol (5 * q + 2) x y z) (hl : q + 2 ≤ x)
    (hW : ((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 3) ≤ 9 * W) : z ≤ W := by
  have hf : 18 * (5 * q + 2) * (2 * (5 * q + 2) + 5) ≤
      25 * (((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 3)) := by
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 11 := ⟨q - 11, by omega, by ring⟩
    apply le_of_sub_nonneg
    ring_nf
    positivity
  by_cases hfar : 2 * (5 * q + 2) ≤ 5 * x
  · have := far_bound h hfar
    nlinarith
  · by_cases heq : x = q + 2
    · subst x
      have he := residual_eight_gap h (by ring)
      have hb := residual_bound h (by norm_num : (0 : ℤ) < 2) he
      have hend : 9 * (((5 * q + 2) * (q + 2)) * ((5 * q + 2) * (q + 2) + 2)) ≤
          16 * (((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 3)) := by
        obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 11 := ⟨q - 11, by omega, by ring⟩
        apply le_of_sub_nonneg
        ring_nf
        positivity
      nlinarith only [hend, hW, hb]
    · apply near_bound h (l := q + 3) (d := 1) (by omega) (by omega) (by omega) (by norm_num)
      · have := (basic_bounds h).2.2.2; omega
      · have hend : 9 * (((5 * q + 2) * (q + 3)) * ((5 * q + 2) * (q + 3) + 1)) ≤
            13 * (((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 3)) := by
          obtain ⟨t, ht, rfl⟩ : ∃ t : ℤ, 0 ≤ t ∧ q = t + 11 := ⟨q - 11, by omega, by ring⟩
          apply le_of_sub_nonneg
          ring_nf
          positivity
        nlinarith only [hend, hW]

-- Small branches split only x; each remaining pair y,z is bounded by the general estimate.
private theorem small_2 {x y z : ℤ} (h : Sol 2 x y z) : z ≤ 1 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 1 ≤ x := by omega
  have hxu : x ≤ 1 := by omega
  interval_cases x
  · have he : 4 ≤ (5 * 1 - 2) * y - 2 * 1 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 4) he
    norm_num at this
    omega

private theorem small_3 {x y z : ℤ} (h : Sol 3 x y z) : z ≤ 6 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 1 ≤ x := by omega
  have hxu : x ≤ 1 := by omega
  interval_cases x
  · have he : 1 ≤ (5 * 1 - 3) * y - 3 * 1 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 1) he
    norm_num at this
    omega

private theorem small_8 {x y z : ℤ} (h : Sol 8 x y z) : z ≤ 72 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 2 ≤ x := by omega
  have hxu : x ≤ 4 := by omega
  interval_cases x
  · have he : 2 ≤ (5 * 2 - 8) * y - 8 * 2 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 2) he
    norm_num at this
    omega
  · have he : 4 ≤ (5 * 3 - 8) * y - 8 * 3 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 4) he
    norm_num at this
    omega
  · have he : 28 ≤ (5 * 4 - 8) * y - 8 * 4 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 28) he
    norm_num at this
    omega

private theorem small_12 {x y z : ℤ} (h : Sol 12 x y z) : z ≤ 156 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 3 ≤ x := by omega
  have hxu : x ≤ 7 := by omega
  interval_cases x
  · have he : 3 ≤ (5 * 3 - 12) * y - 12 * 3 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 3) he
    norm_num at this
    omega
  · have he : 8 ≤ (5 * 4 - 12) * y - 12 * 4 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 8) he
    norm_num at this
    omega
  · have he : 18 ≤ (5 * 5 - 12) * y - 12 * 5 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 18) he
    norm_num at this
    omega
  · have he : 54 ≤ (5 * 6 - 12) * y - 12 * 6 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 54) he
    norm_num at this
    omega
  · have he : 100 ≤ (5 * 7 - 12) * y - 12 * 7 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 100) he
    norm_num at this
    omega

-- Small branches split only x; each remaining pair y,z is bounded by the general estimate.
private theorem small_27 {x y z : ℤ} (h : Sol 27 x y z) : z ≤ 2970 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 6 ≤ x := by omega
  have hxu : x ≤ 16 := by omega
  interval_cases x
  · have he : 3 ≤ (5 * 6 - 27) * y - 27 * 6 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 3) he
    norm_num at this
    omega
  · have he : 3 ≤ (5 * 7 - 27) * y - 27 * 7 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 3) he
    norm_num at this
    omega
  · have he : 5 ≤ (5 * 8 - 27) * y - 27 * 8 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 5) he
    norm_num at this
    omega
  · have he : 9 ≤ (5 * 9 - 27) * y - 27 * 9 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 9) he
    norm_num at this
    omega
  · have he : 6 ≤ (5 * 10 - 27) * y - 27 * 10 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 6) he
    norm_num at this
    omega
  · have he : 39 ≤ (5 * 11 - 27) * y - 27 * 11 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 39) he
    norm_num at this
    omega
  · have he : 105 ≤ (5 * 12 - 27) * y - 27 * 12 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 105) he
    norm_num at this
    omega
  · have he : 181 ≤ (5 * 13 - 27) * y - 27 * 13 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 181) he
    norm_num at this
    omega
  · have he : 267 ≤ (5 * 14 - 27) * y - 27 * 14 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 267) he
    norm_num at this
    omega
  · have he : 363 ≤ (5 * 15 - 27) * y - 27 * 15 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 363) he
    norm_num at this
    omega
  · have he : 469 ≤ (5 * 16 - 27) * y - 27 * 16 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 469) he
    norm_num at this
    omega

private theorem small_42 {x y z : ℤ} (h : Sol 42 x y z) : z ≤ 16002 := by
  have hb := basic_bounds h
  have hx := h.1
  have hy := h.2.1
  have hxl : 9 ≤ x := by omega
  have hxu : x ≤ 25 := by omega
  interval_cases x
  · have he : 3 ≤ (5 * 9 - 42) * y - 42 * 9 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 3) he
    norm_num at this
    omega
  · have he : 4 ≤ (5 * 10 - 42) * y - 42 * 10 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 4) he
    norm_num at this
    omega
  · have he : 6 ≤ (5 * 11 - 42) * y - 42 * 11 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 6) he
    norm_num at this
    omega
  · have he : 18 ≤ (5 * 12 - 42) * y - 42 * 12 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 18) he
    norm_num at this
    omega
  · have he : 6 ≤ (5 * 13 - 42) * y - 42 * 13 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 6) he
    norm_num at this
    omega
  · have he : 28 ≤ (5 * 14 - 42) * y - 42 * 14 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 28) he
    norm_num at this
    omega
  · have he : 30 ≤ (5 * 15 - 42) * y - 42 * 15 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 30) he
    norm_num at this
    omega
  · have he : 12 ≤ (5 * 16 - 42) * y - 42 * 16 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 12) he
    norm_num at this
    omega
  · have he : 60 ≤ (5 * 17 - 42) * y - 42 * 17 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 60) he
    norm_num at this
    omega
  · have he : 156 ≤ (5 * 18 - 42) * y - 42 * 18 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 156) he
    norm_num at this
    omega
  · have he : 262 ≤ (5 * 19 - 42) * y - 42 * 19 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 262) he
    norm_num at this
    omega
  · have he : 378 ≤ (5 * 20 - 42) * y - 42 * 20 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 378) he
    norm_num at this
    omega
  · have he : 504 ≤ (5 * 21 - 42) * y - 42 * 21 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 504) he
    norm_num at this
    omega
  · have he : 640 ≤ (5 * 22 - 42) * y - 42 * 22 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 640) he
    norm_num at this
    omega
  · have he : 786 ≤ (5 * 23 - 42) * y - 42 * 23 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 786) he
    norm_num at this
    omega
  · have he : 942 ≤ (5 * 24 - 42) * y - 42 * 24 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 942) he
    norm_num at this
    omega
  · have he : 1108 ≤ (5 * 25 - 42) * y - 42 * 25 := by omega
    have := residual_bound h (by norm_num : (0 : ℤ) < 1108) he
    norm_num at this
    omega

private def First (k x y z : ℤ) : Prop :=
  Sol k x y z ∧ ∀ u v w, Sol k u v w →
    x < u ∨ x = u ∧ (y < v ∨ y = v ∧ z ≤ w)

private theorem maximal_of_candidate {k x y z u v w : ℤ} (hfirst : First k x y z)
    (hcan : Sol k u v w) (hu : 5 * (u - 1) ≤ k)
    (hlater : ∀ a b c, Sol k a b c → u < a → c ≤ w) :
    ∀ a b c, Sol k a b c → c ≤ z := by
  have hb := basic_bounds hfirst.1
  have hc := hfirst.2 u v w hcan
  have hxu : x = u := by omega
  subst u
  have hW : w ≤ z := same_x_antitone hfirst.1 hcan (by omega)
  intro a b c hs
  have hc' := hfirst.2 a b c hs
  by_cases he : x = a
  · subst a
    exact same_x_antitone hfirst.1 hs (by omega)
  · exact le_trans (hlater a b c hs (by omega)) hW

private theorem construct_one {k u B : ℤ} (hu : 0 < u) (huB : u ≤ B) (hB : 2 ≤ B)
    (he : (5 * u - k) * B = k * u) : Sol k u (B + 1) (B * (B + 1)) := by
  refine ⟨hu, by omega, ?_, ?_⟩
  · nlinarith
  · linear_combination (B + 1) ^ 2 * he

private theorem construct_gap_one {k u v : ℤ} (hu : 0 < u) (huv : u < v)
    (hb : 2 ≤ k * u) (he : (5 * u - k) * v = k * u + 1) :
    Sol k u v (k * u * v) := by
  refine ⟨hu, huv, ?_, ?_⟩
  · nlinarith
  · linear_combination k * u * v * he

private theorem candidate_three {q : ℤ} (hq : 2 ≤ q) :
    ∃ v w, Sol (5 * q + 3) (q + 1) v w ∧
      ((5 * q + 3) * (q + 1)) * ((5 * q + 3) * (q + 1) + 2) ≤ 4 * w := by
  let b := (5 * q + 3) * (q + 1)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith [sq_nonneg q]
  by_cases heven : b % 2 = 0
  · let B := b / 2
    have hB : 2 * B = b := by dsimp [B]; omega
    have hB2 : 2 ≤ B := by dsimp [b] at *; nlinarith [sq_nonneg q]
    have huB : q + 1 ≤ B := by dsimp [b] at *; nlinarith [sq_nonneg q]
    refine ⟨B + 1, B * (B + 1), construct_one (by omega) huB hB2 ?_, ?_⟩
    · dsimp [b] at hB; nlinarith
    · change b * (b + 2) ≤ 4 * (B * (B + 1))
      nlinarith [hB]
  · let v := (b + 1) / 2
    have hv : 2 * v = b + 1 := by dsimp [v]; omega
    have huv : q + 1 < v := by dsimp [b] at *; nlinarith [sq_nonneg q]
    refine ⟨v, b * v, construct_gap_one (by omega) huv hb ?_, ?_⟩
    · dsimp [b] at hv; nlinarith
    · change b * (b + 2) ≤ 4 * (b * v)
      nlinarith [sq_nonneg b]

private theorem candidate_two_divisible {q : ℤ} (hq : 1 ≤ q)
    (hr : ((5 * q + 2) * (q + 1)) % 3 = 0) :
    ∃ v w, Sol (5 * q + 2) (q + 1) v w ∧
      ((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 3) ≤ 9 * w := by
  let b := (5 * q + 2) * (q + 1)
  let B := b / 3
  have hB : 3 * B = b := by dsimp [B, b]; omega
  have hB2 : 2 ≤ B := by dsimp [b] at *; nlinarith [sq_nonneg q]
  have huB : q + 1 ≤ B := by dsimp [b] at *; nlinarith [sq_nonneg q]
  refine ⟨B + 1, B * (B + 1), construct_one (by omega) huB hB2 ?_, ?_⟩
  · dsimp [b] at hB; nlinarith
  · change b * (b + 3) ≤ 9 * (B * (B + 1))
    nlinarith [hB]

private theorem candidate_two_coprime {q : ℤ} (hq : 1 ≤ q)
    (hr : ((5 * q + 2) * (q + 1)) % 3 = 2) :
    ∃ v w, Sol (5 * q + 2) (q + 1) v w ∧
      ((5 * q + 2) * (q + 1)) * ((5 * q + 2) * (q + 1) + 1) ≤ 3 * w := by
  let b := (5 * q + 2) * (q + 1)
  let v := (b + 1) / 3
  have hb : 2 ≤ b := by dsimp [b]; nlinarith [sq_nonneg q]
  have hv : 3 * v = b + 1 := by dsimp [v, b]; omega
  have huv : q + 1 < v := by dsimp [b] at *; nlinarith [sq_nonneg q]
  refine ⟨v, b * v, construct_gap_one (by omega) huv hb ?_, ?_⟩
  · dsimp [b] at hv; nlinarith
  · change b * (b + 1) ≤ 3 * (b * v)
    nlinarith [hv]

private theorem first_maximal {k x y z : ℤ} (hfirst : First k x y z) (hk : k % 5 ≠ 1) :
    ∀ a b c, Sol k a b c → c ≤ z := by
  have hb := basic_bounds hfirst.1
  let q := k / 5
  have hq : 0 ≤ q := by dsimp [q]; omega
  have hres : k % 5 = 0 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hres with hr | hr | hr | hr
  · have hke : k = 5 * q := by dsimp [q]; omega
    rw [hke] at hfirst ⊢
    have hq1 : 1 ≤ q := by omega
    have hcan : Sol (5 * q) (q + 1) (q * (q + 1) + 1)
        (q * (q + 1) * (q * (q + 1) + 1)) := by
      apply construct_one (by omega) (by nlinarith [sq_nonneg q]) (by nlinarith [sq_nonneg q])
      ring
    apply maximal_of_candidate hfirst hcan (by omega)
    intro a b c hs ha
    exact later_zero hq1 hs (by omega)
  · have hke : k = 5 * q + 2 := by dsimp [q]; omega
    rw [hke] at hfirst ⊢
    by_cases hq0 : q = 0
    · rw [hq0] at hfirst
      have hz := small_2 hfirst.1
      have hx := hfirst.1.1
      have hy := hfirst.1.2.1
      have hzz := hfirst.1.2.2.1
      omega
    have hq1 : 1 ≤ q := by omega
    have hmod : ((5 * q + 2) * (q + 1)) % 3 = 0 ∨
        ((5 * q + 2) * (q + 1)) % 3 = 2 := by
      have hqr : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
      rcases hqr with hqr | hqr | hqr <;>
        norm_num [Int.add_emod, Int.mul_emod, hqr]
    rcases hmod with hmod | hmod
    · by_cases hlarge : 11 ≤ q
      · obtain ⟨v, w, hcan, hW⟩ := candidate_two_divisible hq1 hmod
        apply maximal_of_candidate hfirst hcan (by omega)
        intro a b c hs ha
        exact later_two_divisible hlarge hs (by omega) hW
      · have hqu : q ≤ 10 := by omega
        interval_cases q <;> norm_num at hmod
        all_goals norm_num at hfirst ⊢
        · exact maximal_of_candidate hfirst (by norm_num [Sol] : Sol 12 3 13 156)
            (by norm_num) (fun a b c hs _ => small_12 hs)
        · exact maximal_of_candidate hfirst (by norm_num [Sol] : Sol 27 6 55 2970)
            (by norm_num) (fun a b c hs _ => small_27 hs)
        · exact maximal_of_candidate hfirst (by norm_num [Sol] : Sol 42 9 127 16002)
            (by norm_num) (fun a b c hs _ => small_42 hs)
    · obtain ⟨v, w, hcan, hW⟩ := candidate_two_coprime hq1 hmod
      apply maximal_of_candidate hfirst hcan (by omega)
      intro a b c hs ha
      exact later_two_coprime hq1 hs (by omega) hW
  · have hke : k = 5 * q + 3 := by dsimp [q]; omega
    rw [hke] at hfirst ⊢
    by_cases hlarge : 2 ≤ q
    · obtain ⟨v, w, hcan, hW⟩ := candidate_three hlarge
      apply maximal_of_candidate hfirst hcan (by omega)
      intro a b c hs ha
      exact later_three hlarge hs (by omega) hW
    · have hqu : q ≤ 1 := by omega
      interval_cases q <;> norm_num at hfirst ⊢
      · exact maximal_of_candidate hfirst (by norm_num [Sol] : Sol 3 1 2 6)
          (by norm_num) (fun a b c hs _ => small_3 hs)
      · exact maximal_of_candidate hfirst (by norm_num [Sol] : Sol 8 2 9 72)
          (by norm_num) (fun a b c hs _ => small_8 hs)
  · have hke : k = 5 * q + 4 := by dsimp [q]; omega
    rw [hke] at hfirst ⊢
    have hcan : Sol (5 * q + 4) (q + 1) ((5 * q + 4) * (q + 1) + 1)
        (((5 * q + 4) * (q + 1)) * ((5 * q + 4) * (q + 1) + 1)) := by
      apply construct_one (by omega) (by nlinarith [sq_nonneg q]) (by nlinarith [sq_nonneg q])
      ring
    apply maximal_of_candidate hfirst hcan (by omega)
    intro a b c hs ha
    exact later_four hq hs (by omega)

/-- Strictly increasing positive natural solutions of the integer equation. -/
def IsSolution (k x y z : ℕ) : Prop :=
  0 < x ∧ x < y ∧ y < z ∧ 5 * x * y * z = k * (y * z + x * z + x * y)

/-- A solution preceding every other solution in the full lexicographic order. -/
def IsLexFirst (k x y z : ℕ) : Prop :=
  IsSolution k x y z ∧ ∀ u v w, IsSolution k u v w →
    x < u ∨ x = u ∧ (y < v ∨ y = v ∧ z ≤ w)

/-- If a solution has larger third coordinate than the lexicographically first solution,
then the parameter is one modulo five. No converse or universal solvability is asserted. -/
theorem first_maximum_separation_mod_five {k x y z : ℕ} (hfirst : IsLexFirst k x y z)
    (hlarger : ∃ u v w, IsSolution k u v w ∧ z < w) : k % 5 = 1 := by
  by_contra hne
  have hf : First (k : ℤ) x y z := by
    refine ⟨?_, ?_⟩
    · have hs := hfirst.1
      dsimp [IsSolution] at hs
      dsimp [Sol]
      exact_mod_cast hs
    · intro a b c hs
      have ha := le_of_lt hs.1
      have hb := le_of_lt (lt_trans hs.1 hs.2.1)
      have hc := le_of_lt (lt_trans hs.1 (lt_trans hs.2.1 hs.2.2.1))
      lift a to ℕ using ha with a
      lift b to ℕ using hb with b
      lift c to ℕ using hc with c
      have hn : IsSolution k a b c := by
        dsimp [Sol] at hs
        dsimp [IsSolution]
        exact_mod_cast hs
      exact_mod_cast hfirst.2 a b c hn
  obtain ⟨a, b, c, hs, hc⟩ := hlarger
  have hs' : Sol (k : ℤ) a b c := by
    dsimp [IsSolution] at hs
    dsimp [Sol]
    exact_mod_cast hs
  have hm : (k : ℤ) % 5 ≠ 1 := by exact_mod_cast hne
  have hbound := first_maximal hf hm a b c hs'
  have hcn : c ≤ z := by exact_mod_cast hbound
  omega

#print axioms first_maximum_separation_mod_five

end D5.S3.Arith.Congruence.EgyptianFiveFirstMaximum
