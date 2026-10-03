/- GID: D5/S3/Arith/ShortIntervals/TripleProductSumRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/ShortIntervals/TripleProductSumRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal triple products in a short positive integer interval force equal sums. -/

import Mathlib.Tactic

namespace D5.S3.Arith.ShortIntervals.TripleProductSumRigidity

/-- Six integer rows in an interval of width below the square-root threshold have
    equal sums whenever their triple products agree. Rows may repeat. -/
theorem triple_product_sum_rigidity
    (m h a b c d e f : ℤ)
    (hm : 0 < m) (hh : 0 ≤ h) (hshort : h ^ 2 < m)
    (ha : m ≤ a ∧ a ≤ m + h) (hb : m ≤ b ∧ b ≤ m + h)
    (hc : m ≤ c ∧ c ≤ m + h) (hd : m ≤ d ∧ d ≤ m + h)
    (he : m ≤ e ∧ e ≤ m + h) (hf : m ≤ f ∧ f ≤ m + h)
    (hprod : a * b * c = d * e * f) : a + b + c = d + e + f := by
  by_cases hzero : h = 0
  · omega
  have hone : 1 ≤ h := by omega
  have h_le_sq : h ≤ h ^ 2 := by nlinarith only [hone]
  have h_lt_m : h < m := lt_of_le_of_lt h_le_sq hshort
  have mh_sq : m * h ^ 2 < m ^ 2 := by
    nlinarith only [mul_lt_mul_of_pos_left hshort hm]
  have h_cube : h ^ 3 < m ^ 2 := by
    calc
      h ^ 3 = h * h ^ 2 := by ring
      _ < m * m := mul_lt_mul h_lt_m hshort.le (by positivity) hm.le
      _ = m ^ 2 := by ring
  have anchored : ∀ x y z : ℤ,
      m ≤ x ∧ x ≤ m + h → m ≤ y ∧ y ≤ m + h → m ≤ z ∧ z ≤ m + h →
      x ≤ y → x ≤ z →
      0 ≤ (x + y + z) ^ 3 - 27 * (x * y * z) ∧
        (x + y + z) ^ 3 - 27 * (x * y * z) < 26 * m ^ 2 := by
    intro x y z hx hy hz hxy hxz
    let r := y - x
    let s := z - x
    have hr : 0 ≤ r := by dsimp [r]; omega
    have hs : 0 ≤ s := by dsimp [s]; omega
    have hrh : r ≤ h := by dsimp [r]; omega
    have hsh : s ≤ h := by dsimp [s]; omega
    have hxpos : 0 < x := lt_of_lt_of_le hm hx.1
    have q_nonneg : 0 ≤ r ^ 2 - r * s + s ^ 2 := by
      nlinarith only [sq_nonneg (r - s), mul_nonneg hr hs]
    have q_bound : r ^ 2 - r * s + s ^ 2 ≤ h ^ 2 := by
      rcases le_total r s with hrs | hsr
      · have ss : s ^ 2 ≤ h ^ 2 := by gcongr
        nlinarith only [ss, mul_nonneg hr (sub_nonneg.mpr hrs)]
      · have rr : r ^ 2 ≤ h ^ 2 := by gcongr
        nlinarith only [rr, mul_nonneg hs (sub_nonneg.mpr hsr)]
    have identity : (x + y + z) ^ 3 - 27 * (x * y * z) =
        9 * x * (r ^ 2 - r * s + s ^ 2) + (r + s) ^ 3 := by
      dsimp [r, s]
      ring
    constructor
    · rw [identity]
      positivity
    · calc
        (x + y + z) ^ 3 - 27 * (x * y * z) =
            9 * x * (r ^ 2 - r * s + s ^ 2) + (r + s) ^ 3 := identity
        _ ≤ 9 * (m + h) * h ^ 2 + (2 * h) ^ 3 := by gcongr <;> omega
        _ = 9 * m * h ^ 2 + 17 * h ^ 3 := by ring
        _ < 26 * m ^ 2 := by linarith only [mh_sq, h_cube]
  have defect_bounds : ∀ x y z : ℤ,
      m ≤ x ∧ x ≤ m + h → m ≤ y ∧ y ≤ m + h → m ≤ z ∧ z ≤ m + h →
      0 ≤ (x + y + z) ^ 3 - 27 * (x * y * z) ∧
        (x + y + z) ^ 3 - 27 * (x * y * z) < 26 * m ^ 2 := by
    intro x y z hx hy hz
    rcases le_total x y with hxy | hyx
    · rcases le_total x z with hxz | hzx
      · exact anchored x y z hx hy hz hxy hxz
      · simpa only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
          using anchored z x y hz hx hy hzx (le_trans hzx hxy)
    · rcases le_total y z with hyz | hzy
      · simpa only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
          using anchored y x z hy hx hz hyx hyz
      · simpa only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
          using anchored z x y hz hx hy (le_trans hzy hyx) hzy
  have cube_gap : ∀ u v : ℤ, 3 * m ≤ u → u < v → 27 * m ^ 2 < v ^ 3 - u ^ 3 := by
    intro u v hu huv
    have step : u + 1 ≤ v := by omega
    have upos : 0 < u := by omega
    have cubes : (u + 1) ^ 3 ≤ v ^ 3 := by gcongr
    have squares : (3 * m) ^ 2 ≤ u ^ 2 := by gcongr
    nlinarith only [cubes, squares, upos]
  obtain ⟨defect_left_nonneg, defect_left_lt⟩ := defect_bounds a b c ha hb hc
  obtain ⟨defect_right_nonneg, defect_right_lt⟩ := defect_bounds d e f hd he hf
  rcases lt_trichotomy (a + b + c) (d + e + f) with hlt | heq | hgt
  · have gap := cube_gap (a + b + c) (d + e + f) (by omega) hlt
    rw [← hprod] at defect_right_lt
    have msq : 0 ≤ m ^ 2 := sq_nonneg m
    linarith only [gap, defect_left_nonneg, defect_right_lt, msq]
  · exact heq
  · have gap := cube_gap (d + e + f) (a + b + c) (by omega) hgt
    rw [hprod] at defect_left_lt
    have msq : 0 ≤ m ^ 2 := sq_nonneg m
    linarith only [gap, defect_right_nonneg, defect_left_lt, msq]

end D5.S3.Arith.ShortIntervals.TripleProductSumRigidity
