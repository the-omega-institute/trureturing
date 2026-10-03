/- GID: D5/S3/Arith/ShortIntervals/ThreeRowSquareRootLock
   generality: G
   mirror-B: D5/B/S3/Arith/ShortIntervals/ThreeRowSquareRootLock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-hull cubic norms force positive offsets and the next odd integer quotient. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace D5.S3.Arith.ShortIntervals.ThreeRowSquareRootLock

theorem three_row_square_root_lock
    (S k : ℤ) (h l b c d Q P epsilon : ℝ)
    (hEven : Even S) (hScale : 8 ≤ S) (hOdd : Odd k)
    (hWidth : 0 ≤ h ∧ h ≤ (S : ℝ) - 2)
    (hZero : l ≤ 0 ∧ 0 ≤ l + h)
    (hB : l ≤ b ∧ b ≤ l + h)
    (hC : l ≤ c ∧ c ≤ l + h)
    (hD : l ≤ d ∧ d ≤ l + h)
    (hAbsB : 1 ≤ |b|) (hAbsC : 1 ≤ |c|) (hAbsD : 1 ≤ |d|)
    (hQpos : 0 < Q) (hPpos : 0 < P)
    (hQ : Q ^ 2 = ((S : ℝ) ^ 2 + b) * ((S : ℝ) ^ 2 + c) *
      ((S : ℝ) ^ 2 + d))
    (hP : P ^ 2 = b * c * d)
    (hEpsilon : epsilon = 1 ∨ epsilon = -1)
    (hLink : Q + epsilon * P = (S : ℝ) ^ 2 * (k : ℝ)) :
    0 < b ∧ 0 < c ∧ 0 < d ∧ k = S + 1 := by
  let scale : ℝ := S
  let N : ℝ := scale ^ 2
  have hScaleReal : 8 ≤ scale := by
    dsimp [scale]
    exact_mod_cast hScale
  have scale_pos : 0 < scale := by linarith
  have N_pos : 0 < N := pow_pos scale_pos 2
  have scale_lt_N : scale < N := by
    dsimp [N]
    nlinarith only [hScaleReal, sq_nonneg (scale - 4)]
  change 0 ≤ h ∧ h ≤ scale - 2 at hWidth
  have h_nonneg : 0 ≤ h := hWidth.1
  change Q ^ 2 = (N + b) * (N + c) * (N + d) at hQ
  change Q + epsilon * P = N * (k : ℝ) at hLink
  have hull_bound : ∀ x : ℝ, l ≤ x → x ≤ l + h → |x| ≤ h := by
    intro x hxlo hxhi
    rw [abs_le]
    constructor <;> linarith [hZero.1, hZero.2]
  have bound_b := hull_bound b hB.1 hB.2
  have bound_c := hull_bound c hC.1 hC.2
  have bound_d := hull_bound d hD.1 hD.2
  have hPbound : P ^ 2 ≤ h ^ 3 := by
    calc
      P ^ 2 = |b| * |c| * |d| := by
        rw [← abs_mul, ← abs_mul, ← hP, abs_of_nonneg (sq_nonneg P)]
      _ ≤ h * h * h := by gcongr
      _ = h ^ 3 := by ring
  have hCube : h ^ 3 < scale ^ 3 := by
    gcongr
    linarith [hWidth.2]
  have hScaleCube : scale ^ 3 < ((3 / 8 : ℝ) * N) ^ 2 := by
    have hMargin : 0 < scale ^ 3 * (9 * scale - 64) :=
      mul_pos (pow_pos scale_pos 3) (by linarith)
    dsimp [N]
    nlinarith only [hMargin]
  have hPsmall : P < (3 / 8 : ℝ) * N := by
    nlinarith only [hPbound, hCube, hScaleCube, hPpos, N_pos]
  have sign_bound : ∀ x : ℝ, 1 ≤ |x| → x ≤ -1 ∨ 1 ≤ x := by
    intro x hx
    rcases le_total x 0 with hneg | hpos
    · rw [abs_of_nonpos hneg] at hx
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hpos] at hx
      exact Or.inr hx
  have negative_case : ∀ x y z : ℝ,
      l ≤ x → x ≤ l + h → l ≤ y → y ≤ l + h → l ≤ z → z ≤ l + h →
      x ≤ -1 → y ≤ -1 → 1 ≤ z →
      Q ^ 2 = (N + x) * (N + y) * (N + z) → P ^ 2 = x * y * z → False := by
    intro x y z hxlo hxhi hylo hyhi hzlo hzhi hx hy hz hQnorm hPnorm
    let magnitude := max (-x) (-y)
    have hxmag : -x ≤ magnitude := le_max_left _ _
    have hymag : -y ≤ magnitude := le_max_right _ _
    have magnitude_pos : 0 < magnitude := by linarith
    have joint_hull : magnitude + z ≤ h := by
      rcases le_total (-x) (-y) with hxy | hyx
      · simp only [magnitude, max_eq_right hxy]
        linarith
      · simp only [magnitude, max_eq_left hyx]
        linarith
    have mag_le_h : magnitude ≤ h := by linarith
    have z_le_h : z ≤ h := by linarith
    have base_nonneg : 0 ≤ N - magnitude := by linarith [hWidth.2]
    have shifted_x : 0 ≤ N + x := by linarith
    have shifted_y : 0 ≤ N + y := by linarith
    have shifted_z : 0 ≤ N + z := by linarith
    have q_lower_sq : (scale * (N - magnitude)) ^ 2 ≤ Q ^ 2 := by
      calc
        (scale * (N - magnitude)) ^ 2 = (N - magnitude) * (N - magnitude) * N := by
          dsimp [N]
          ring
        _ ≤ (N + x) * (N + y) * (N + z) := by gcongr <;> linarith
        _ = Q ^ 2 := hQnorm.symm
    have q_lower : scale * (N - magnitude) ≤ Q := by
      nlinarith only [q_lower_sq, hQpos,
        mul_nonneg scale_pos.le base_nonneg]
    have xy_bound : x * y ≤ magnitude * magnitude := by
      calc
        x * y = (-x) * (-y) := by ring
        _ ≤ magnitude * magnitude := by gcongr; linarith
    have p_upper_sq : P ^ 2 ≤ (magnitude * z) ^ 2 := by
      calc
        P ^ 2 = x * y * z := hPnorm
        _ ≤ magnitude * magnitude * z := mul_le_mul_of_nonneg_right xy_bound (by linarith)
        _ ≤ magnitude * magnitude * (z * z) := by gcongr; nlinarith only [hz]
        _ = (magnitude * z) ^ 2 := by ring
    have p_upper : P ≤ magnitude * z := by
      nlinarith only [p_upper_sq, hPpos, mul_pos magnitude_pos (by linarith : 0 < z)]
    have charge_bound : magnitude * (scale + z) < N := by
      have hmul := mul_le_mul_of_nonneg_right
        (show magnitude ≤ scale - z - 2 by linarith [hWidth.2])
        (show 0 ≤ scale + z by linarith)
      have hmargin : 0 < 2 * scale + z ^ 2 + 2 * z := by positivity
      dsimp [N]
      nlinarith only [hmul, hmargin]
    have lower : N * (scale - 1) < Q - P := by
      nlinarith only [q_lower, p_upper, charge_bound]
    have q_upper_sq : Q ^ 2 ≤ N * N * (N + z) := by
      rw [hQnorm]
      gcongr <;> linarith
    have upper_comparison : N * N * (N + z) < (N * scale + N / 2) ^ 2 := by
      have hmargin : 0 < N * N * (scale + 1 / 4 - z) :=
        mul_pos (mul_pos N_pos N_pos) (by linarith [hWidth.2])
      dsimp [N] at *
      nlinarith only [hmargin]
    have q_upper : Q < N * scale + N / 2 := by
      have hpositive : 0 < N * scale + N / 2 := by positivity
      nlinarith only [q_upper_sq, upper_comparison, hpositive, hQpos]
    have linked_lower : N * (scale - 1) < Q + epsilon * P := by
      rcases hEpsilon with rfl | rfl <;> nlinarith only [lower, hPpos]
    have linked_upper : Q + epsilon * P < N * (scale + 1) := by
      rcases hEpsilon with rfl | rfl <;> nlinarith only [q_upper, hPsmall, hPpos, N_pos]
    rw [hLink] at linked_lower linked_upper
    have k_lower := (mul_lt_mul_iff_right₀ N_pos).mp linked_lower
    have k_upper := (mul_lt_mul_iff_right₀ N_pos).mp linked_upper
    dsimp [scale] at k_lower k_upper
    have k_lower_int : S - 1 < k := by exact_mod_cast k_lower
    have k_upper_int : k < S + 1 := by exact_mod_cast k_upper
    have k_eq : k = S := by omega
    rcases hEven with ⟨evenHalf, hEven⟩
    rcases hOdd with ⟨oddHalf, hOdd⟩
    omega
  have product_pos : 0 < b * c * d := by rw [← hP]; positivity
  have all_positive : 0 < b ∧ 0 < c ∧ 0 < d := by
    rcases sign_bound b hAbsB with hb | hb <;>
      rcases sign_bound c hAbsC with hc | hc <;>
      rcases sign_bound d hAbsD with hd | hd
    · have hbc : 0 ≤ b * c := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      have := mul_nonpos_of_nonneg_of_nonpos hbc (show d ≤ 0 by linarith)
      linarith
    · exact (negative_case b c d hB.1 hB.2 hC.1 hC.2 hD.1 hD.2 hb hc hd hQ hP).elim
    · exact (negative_case b d c hB.1 hB.2 hD.1 hD.2 hC.1 hC.2 hb hd hc
        (by nlinarith only [hQ]) (by nlinarith only [hP])).elim
    · have hbc : b * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have := mul_nonpos_of_nonpos_of_nonneg hbc (show 0 ≤ d by linarith)
      linarith
    · exact (negative_case c d b hC.1 hC.2 hD.1 hD.2 hB.1 hB.2 hc hd hb
        (by nlinarith only [hQ]) (by nlinarith only [hP])).elim
    · have hbc : b * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have := mul_nonpos_of_nonpos_of_nonneg hbc (show 0 ≤ d by linarith)
      linarith
    · have hbc : 0 ≤ b * c := mul_nonneg (by linarith) (by linarith)
      have := mul_nonpos_of_nonneg_of_nonpos hbc (show d ≤ 0 by linarith)
      linarith
    · exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨b_pos, c_pos, d_pos⟩ := all_positive
  have d_lt_N : d < N := by
    have dh : d ≤ h := (abs_le.mp bound_d).2
    linarith [hWidth.2]
  have root_d_sq := Real.sq_sqrt d_pos.le
  have root_d_nonneg := Real.sqrt_nonneg d
  have root_d_lt : Real.sqrt d < scale := by
    change d < scale ^ 2 at d_lt_N
    nlinarith only [root_d_sq, root_d_nonneg, d_lt_N, scale_pos]
  have amgm : 2 * P ≤ Real.sqrt d * (b + c) := by
    have hdiscriminant := mul_nonneg d_pos.le (sq_nonneg (b - c))
    have hsqrt : (Real.sqrt d * (b + c)) ^ 2 = d * (b + c) ^ 2 := by
      rw [mul_pow, root_d_sq]
    have hsquare : (2 * P) ^ 2 ≤ (Real.sqrt d * (b + c)) ^ 2 := by
      nlinarith only [hP, hdiscriminant, hsqrt]
    have hpositive : 0 ≤ Real.sqrt d * (b + c) := by positivity
    nlinarith only [hsquare, hpositive, hPpos]
  have root_gap : 2 * scale * P < N * (b + c + d) := by
    have hfirst := mul_le_mul_of_nonneg_left amgm scale_pos.le
    have hsecond := mul_lt_mul_of_pos_right root_d_lt (show 0 < b + c by positivity)
    have hthird := mul_lt_mul_of_pos_left hsecond scale_pos
    have hfourth := mul_pos N_pos d_pos
    dsimp [N] at *
    nlinarith only [hfirst, hthird, hfourth]
  have q_gap_sq : (N * scale + P) ^ 2 < Q ^ 2 := by
    have hbracket : 0 < N * (b + c + d) + (b * c + b * d + c * d) - 2 * scale * P := by
      have : 0 < b * c + b * d + c * d := by positivity
      linarith
    have hmul := mul_pos N_pos hbracket
    dsimp [N] at *
    nlinarith only [hmul, hQ, hP]
  have q_gap : N * scale < Q - P := by
    have hpositive : 0 < N * scale + P := by positivity
    nlinarith only [q_gap_sq, hpositive, hQpos]
  have q_cube : Q ^ 2 < (N + scale) ^ 3 := by
    calc
      Q ^ 2 = (N + b) * (N + c) * (N + d) := hQ
      _ ≤ (N + h) * (N + h) * (N + h) := by
        gcongr <;> linarith [(abs_le.mp bound_b).2, (abs_le.mp bound_c).2,
          (abs_le.mp bound_d).2]
      _ = (N + h) ^ 3 := by ring
      _ < (N + scale) ^ 3 := by gcongr; linarith [hWidth.1, hWidth.2]
  have polynomial_margin : 0 < 16 * scale ^ 2 - 23 * scale - 64 := by
    nlinarith only [hScaleReal, sq_nonneg (scale - 8)]
  have polynomial_bound : (N + scale) ^ 3 < (N * scale + (13 / 8 : ℝ) * N) ^ 2 := by
    have hmul := mul_pos (pow_pos scale_pos 3) polynomial_margin
    dsimp [N]
    nlinarith only [hmul]
  have q_upper : Q < N * scale + (13 / 8 : ℝ) * N := by
    have hpositive : 0 < N * scale + (13 / 8 : ℝ) * N := by positivity
    nlinarith only [q_cube, polynomial_bound, hpositive, hQpos]
  have linked_lower : N * scale < Q + epsilon * P := by
    rcases hEpsilon with rfl | rfl <;> nlinarith only [q_gap, hPpos]
  have linked_upper : Q + epsilon * P < N * (scale + 2) := by
    rcases hEpsilon with rfl | rfl <;> nlinarith only [q_upper, hPsmall, hPpos, N_pos]
  rw [hLink] at linked_lower linked_upper
  have k_lower := (mul_lt_mul_iff_right₀ N_pos).mp linked_lower
  have k_upper := (mul_lt_mul_iff_right₀ N_pos).mp linked_upper
  dsimp [scale] at k_lower k_upper
  have k_lower_int : S < k := by exact_mod_cast k_lower
  have k_upper_int : k < S + 2 := by exact_mod_cast k_upper
  exact ⟨b_pos, c_pos, d_pos, by omega⟩

end D5.S3.Arith.ShortIntervals.ThreeRowSquareRootLock
