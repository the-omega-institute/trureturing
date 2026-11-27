import D5.S3.Quantum.Semigroups.WuCubicEntropyRemainders
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import OmegaBuild.Commands

/-! The scalar logarithmic remainder in Wu's cold cubic localization
(`proof.txt`, §§5.1, 6.1, 7.1). -/

compile_only_with_mathlib

set_option autoImplicit false

namespace WuCubicColdLogBounds

/-- Wu's scalar entropy remainder centered at one. -/
noncomputable def J (z : ℝ) : ℝ :=
  z ^ 3 / 3 - z ^ 3 * Real.log z - 1 / 3

@[simp] theorem J_zero : J 0 = -(1 / 3) := by norm_num [J]

@[simp] theorem J_one : J 1 = 0 := by norm_num [J, Real.log_one]

private theorem J_nonpos {z : ℝ} (hz : 0 ≤ z) : J z ≤ 0 := by
  have h := InformationTheory.klFun_nonneg (pow_nonneg hz 3)
  calc
    J z = -(InformationTheory.klFun (z ^ 3)) / 3 := by
      simp only [J, InformationTheory.klFun_apply, Real.log_pow, Nat.cast_ofNat]
      ring
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (by norm_num)

private theorem abs_J_le_of_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    |J z| ≤ (3 / 2) * (z - 1) ^ 2 * (z + 1) := by
  rcases hz.eq_or_lt with rfl | hz
  · norm_num
  rw [abs_of_nonpos (J_nonpos hz.le)]
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hz) (pow_nonneg hz.le 3)
  have hzSq : z ^ 2 ≤ z := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hz1 hz.le
  calc
    -J z ≤ (z - 1) ^ 2 * (z ^ 2 + (2 * z + 1) / 3) := by
      unfold J
      nlinarith only [h]
    _ ≤ (z - 1) ^ 2 * ((3 / 2) * (z + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith [hzSq, hz1]) (sq_nonneg _)
    _ = _ := by ring

private theorem abs_J_le_of_one_le_of_le_two {z : ℝ} (hz1 : 1 ≤ z) (hz2 : z ≤ 2) :
    |J z| ≤ (3 / 2) * (z - 1) ^ 2 * (z + 1) := by
  have hz : 0 ≤ z := by linarith
  have htaylor :=
    D5.S3.Quantum.Semigroups.WuCubicEntropyRemainders.cubic_entropy_remainder_le
      (x := z) (g := 1) (by linarith) (by norm_num)
  rw [one_pow, div_one, Real.log_pow] at htaylor
  norm_num at htaylor
  have hsq : (z - 1) ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by linarith) (by linarith)
  rw [abs_of_nonpos (J_nonpos hz)]
  calc
    -J z ≤ (z - 1) ^ 2 * ((3 / 2) * z + (z - 1) ^ 2 / 2) := by
      unfold J
      nlinarith only [htaylor]
    _ ≤ (z - 1) ^ 2 * ((3 / 2) * (z + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsq]) (sq_nonneg _)
    _ = _ := by ring

private theorem abs_J_le_of_le_two {z : ℝ} (hz : 0 ≤ z) (hz2 : z ≤ 2) :
    |J z| ≤ (3 / 2) * (z - 1) ^ 2 * (z + 1) := by
  rcases le_total z 1 with hz1 | hz1
  · exact abs_J_le_of_le_one hz hz1
  · exact abs_J_le_of_one_le_of_le_two hz1 hz2

/-- The bound used for the second cold localization at `U = 1/256`. -/
theorem abs_J_le_three_halves {z : ℝ} (hz : 0 ≤ z) (hzmax : z ≤ 6 / 5) :
    |J z| ≤ (3 / 2) * (z - 1) ^ 2 * (z + 1) :=
  abs_J_le_of_le_two hz (by linarith)

private noncomputable def weight (z : ℝ) : ℝ := (z - 1) ^ 2 * (z + 1)

private theorem abs_J_le_of_log_cap {a z L : ℝ}
    (ha : 2 ≤ a) (haz : a ≤ z) (hlog : Real.log z ≤ L) (hL : 1 / 3 ≤ L)
    (hcap : a ^ 3 * (L - 1 / 3) + 1 / 3 ≤ (5 / 2) * weight a) :
    |J z| ≤ (5 / 2) * weight z := by
  have ha0 : 0 ≤ a := by linarith
  have hz0 : 0 ≤ z := ha0.trans haz
  have ha1 : 0 < a - 1 := by linarith
  have hza1 : a - 1 ≤ z - 1 := by linarith
  have ha2 : 0 ≤ a ^ 2 - 1 := sub_nonneg.mpr
    ((by norm_num : (1 : ℝ) ≤ 2 ^ 2).trans (pow_le_pow_left₀ (by norm_num) ha 2))
  have hDa : 0 < weight a := mul_pos (pow_pos ha1 2) (by linarith)
  have hD : weight a ≤ weight z :=
    mul_le_mul (pow_le_pow_left₀ ha1.le hza1 2) (by linarith)
      (by linarith) (sq_nonneg _)
  -- Cross-multiply the ratio comparison using weight z = (z - 1) * (z^2 - 1).
  have hratio : z ^ 3 * weight a ≤ weight z * a ^ 3 := by
    have hfirst : (a - 1) * z ≤ (z - 1) * a := by nlinarith only [haz]
    have hsecond : (a ^ 2 - 1) * z ^ 2 ≤ (z ^ 2 - 1) * a ^ 2 := by
      nlinarith only [pow_le_pow_left₀ ha0 haz 2]
    calc
      z ^ 3 * weight a = ((a - 1) * z) * ((a ^ 2 - 1) * z ^ 2) := by
        unfold weight
        ring
      _ ≤ ((z - 1) * a) * ((z ^ 2 - 1) * a ^ 2) :=
        mul_le_mul hfirst hsecond (mul_nonneg ha2 (sq_nonneg _))
          (mul_nonneg (ha1.le.trans hza1) ha0)
      _ = weight z * a ^ 3 := by
        unfold weight
        ring
  rw [abs_of_nonpos (J_nonpos hz0)]
  apply le_of_mul_le_mul_left _ hDa
  calc
    weight a * (-J z) = z ^ 3 * weight a * (Real.log z - 1 / 3) + weight a / 3 := by
      unfold J
      ring
    _ ≤ z ^ 3 * weight a * (L - 1 / 3) + weight a / 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hlog _)
          (mul_nonneg (pow_nonneg hz0 3) hDa.le)) (le_refl _)
    _ ≤ weight z * a ^ 3 * (L - 1 / 3) + weight z / 3 :=
      add_le_add (mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hL))
        (div_le_div_of_nonneg_right hD (by norm_num))
    _ = weight z * (a ^ 3 * (L - 1 / 3) + 1 / 3) := by ring
    _ ≤ weight z * ((5 / 2) * weight a) :=
      mul_le_mul_of_nonneg_left hcap (hDa.le.trans hD)
    _ = weight a * ((5 / 2) * weight z) := by ring

/-- The bound used for the first cold localization at `U = 1/256`. -/
theorem abs_J_le_five_halves {z : ℝ} (hz : 0 ≤ z) (hzmax : z ≤ 8) :
    |J z| ≤ (5 / 2) * (z - 1) ^ 2 * (z + 1) := by
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hlog3 : Real.log 3 ≤ 9 / 8 := by linarith only [Real.log_three_lt_d9]
  have hlog4 : Real.log 4 ≤ 7 / 5 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog2]
  have hlog6 : Real.log 6 ≤ 73 / 40 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith only [hlog2, hlog3]
  have hlog8 : Real.log 8 ≤ 21 / 10 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog2]
  by_cases hz2 : z ≤ 2
  · calc
      |J z| ≤ (3 / 2) * (z - 1) ^ 2 * (z + 1) := abs_J_le_of_le_two hz hz2
      _ ≤ (5 / 2) * (z - 1) ^ 2 * (z + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)) (by linarith)
  have hzpos : 0 < z := by linarith
  suffices |J z| ≤ (5 / 2) * weight z by simpa [weight, mul_assoc] using this
  by_cases hz3 : z ≤ 3
  · exact abs_J_le_of_log_cap (a := 2) (by norm_num) (not_le.mp hz2).le
      ((Real.log_le_log hzpos hz3).trans hlog3) (by norm_num) (by norm_num [weight])
  by_cases hz4 : z ≤ 4
  · exact abs_J_le_of_log_cap (a := 3) (by norm_num) (not_le.mp hz3).le
      ((Real.log_le_log hzpos hz4).trans hlog4) (by norm_num) (by norm_num [weight])
  by_cases hz6 : z ≤ 6
  · exact abs_J_le_of_log_cap (a := 4) (by norm_num) (not_le.mp hz4).le
      ((Real.log_le_log hzpos hz6).trans hlog6) (by norm_num) (by norm_num [weight])
  exact abs_J_le_of_log_cap (a := 6) (by norm_num) (not_le.mp hz6).le
    ((Real.log_le_log hzpos hzmax).trans hlog8) (by norm_num) (by norm_num [weight])

/-- The scalar difference `f(z) - s(z)` used in cold localization. -/
noncomputable def coldScalar (C e u z : ℝ) : ℝ :=
  C * z ^ 3 * (1 + e / 3 - e * Real.log z) + 2 * u ^ 3 * z ^ 3 - (z ^ 2 + z)

/-- The entropy tangent before completing the square. Either logarithmic bound
can supply `hJ`, with its corresponding coefficient `K`. -/
theorem cold_tangent_ge {C e u z K : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hC : 1 - 2 * u ≤ C) (hz : 0 ≤ z)
    (hK : 0 ≤ K) (hJ : |J z| ≤ K * (z - 1) ^ 2 * (z + 1)) :
    (1 - 4 * u - K * e) * (z - 1) ^ 2 * (z + 1) +
      3 * (C + 2 * u ^ 3 - 1) * (z - 1) ≤ coldScalar C e u z - coldScalar C e u 1 := by
  let A : ℝ := C + 2 * u ^ 3 - 1
  have hA : -(2 * u) ≤ A := by
    dsimp [A]
    linarith only [hC, pow_nonneg hu 3]
  have hweight : 0 ≤ weight z := mul_nonneg (sq_nonneg _) (by linarith)
  have hquad : -(4 * u) * weight z ≤ A * ((z - 1) ^ 2 * (z + 2)) := by
    have hle : (z - 1) ^ 2 * (z + 2) ≤ 2 * weight z := by
      calc
        (z - 1) ^ 2 * (z + 2) ≤ (z - 1) ^ 2 * (2 * (z + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ = 2 * weight z := by
          unfold weight
          ring
    calc
      -(4 * u) * weight z = -(2 * u) * (2 * weight z) := by ring
      _ ≤ -(2 * u) * ((z - 1) ^ 2 * (z + 2)) :=
        mul_le_mul_of_nonpos_left hle (by linarith)
      _ ≤ A * ((z - 1) ^ 2 * (z + 2)) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (sq_nonneg _) (by linarith))
  have hent : -(e * K) * weight z ≤ C * e * J z := by
    have hneg : -(K * weight z) ≤ J z := by
      have h := (abs_le.mp hJ).1
      simpa only [weight, mul_assoc] using h
    calc
      -(e * K) * weight z = e * (-(K * weight z)) := by ring
      _ ≤ (C * e) * (-(K * weight z)) :=
        mul_le_mul_of_nonpos_right
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 he)
          (neg_nonpos.mpr (mul_nonneg hK hweight))
      _ ≤ C * e * J z := mul_le_mul_of_nonneg_left hneg (mul_nonneg hC0 he)
  calc
    _ = weight z + (-(4 * u) * weight z + -(e * K) * weight z) +
        3 * A * (z - 1) := by
      dsimp [weight, A]
      ring
    _ ≤ weight z + (A * ((z - 1) ^ 2 * (z + 2)) + C * e * J z) +
        3 * A * (z - 1) := add_le_add (add_le_add (le_refl _) (add_le_add hquad hent)) (le_refl _)
    _ = coldScalar C e u z - coldScalar C e u 1 := by
      simp only [weight, A, J, coldScalar, Real.log_one]
      ring

end WuCubicColdLogBounds
