/- GID: D5/S3/Fourier/ThetaDerivativeBounds
   generality: G
   mirror-B: D5/B/S3/Fourier/ThetaDerivativeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small-parameter theta derivative bounds by Fourier moments and Gaussian pairing. -/

import D5.S3.Analytic.Polynomial.DiagonalPadeWindow
import D5.S3.Fourier.ThetaGaussianPairing

/-! # Small-parameter theta derivative bounds -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace D5.S3.Fourier.PlanarTheta
noncomputable section

/-- The real Fourier expansion of the one-dimensional theta function. -/
def thetaFourier (s b : ℝ) : ℝ :=
  1 + 2 * ∑' k : ℕ, Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
    Real.cos (2 * Real.pi * ((k : ℝ) + 1) * b)

/-- The positive-frequency sine series in the theta derivative. -/
def thetaSine (s b : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
    Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)

/-- Every positive-frequency polynomial Gaussian moment converges. -/
lemma gaussian_moment {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ j *
      Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) := by
  have h := HurwitzKernelBounds.summable_f_nat j 1 hs
  convert h using 1
  ext k
  dsimp [HurwitzKernelBounds.f_nat]
  congr 2
  ring

/-- The positive cosine Gaussian series converges at every real translation. -/
lemma cos_summable {s : ℝ} (hs : 0 < s) (b : ℝ) :
    Summable (fun k : ℕ => Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * ((k : ℝ) + 1) * b)) := by
  have h := gaussian_moment hs 0
  simp only [pow_zero, one_mul] at h
  apply h.of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private lemma sine_summable {s : ℝ} (hs : 0 < s) (b : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) *
      Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
      Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)) := by
  have h := gaussian_moment hs 1
  simp only [pow_one] at h
  apply h.of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

/-- Differentiation is justified by a summable uniform first Gaussian moment. -/
theorem hasDerivAt_thetaFourier {s : ℝ} (hs : 0 < s) (b : ℝ) :
    HasDerivAt (thetaFourier s) (-4 * Real.pi * thetaSine s b) b := by
  let g (k : ℕ) (z : ℝ) := Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
    Real.cos (2 * Real.pi * ((k : ℝ) + 1) * z)
  let g' (k : ℕ) (z : ℝ) := (-2 * Real.pi) * (((k : ℝ) + 1) *
    Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
    Real.sin (2 * Real.pi * ((k : ℝ) + 1) * z))
  have hd (k : ℕ) (z : ℝ) : HasDerivAt (g k) (g' k z) z := by
    convert (((hasDerivAt_id z).const_mul (2 * Real.pi * ((k : ℝ) + 1))).cos).const_mul
      (Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) using 1 <;> dsimp [g, g'] <;> ring
  have hm : Summable (fun k : ℕ => (2 * Real.pi) *
      (((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2))) := by
    simpa only [pow_one] using (gaussian_moment hs 1).mul_left (2 * Real.pi)
  have hb (k : ℕ) (z : ℝ) : ‖g' k z‖ ≤ (2 * Real.pi) *
      (((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) := by
    dsimp [g']
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left (Real.abs_sin_le_one
      (2 * Real.pi * ((k : ℝ) + 1) * z))
      (show 0 ≤ 2 * Real.pi * (((k : ℝ) + 1) *
        Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) by positivity)]
  have h := hasDerivAt_tsum hm hd hb (cos_summable hs b) b
  convert (h.const_mul 2).const_add 1 using 1
  · rfl
  · dsimp [g']
    rw [tsum_mul_left]
    dsimp [thetaSine]
    ring

private lemma tail_summable {s : ℝ} (hs : 0 < s) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * s * (((k : ℝ) + 2) ^ 2 - 1))) := by
  have h := (summable_nat_add_iff 1).mpr (gaussian_moment hs 2)
  convert h.mul_right (Real.exp (Real.pi * s)) using 1
  ext k
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The entire deviation from the first sine mode is controlled by the normalized tail. -/
theorem thetaSine_first_mode {s : ℝ} (hs : 0 < s) (b : ℝ) :
    |thetaSine s b - Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b)| ≤
      Real.exp (-Real.pi * s) * |Real.sin (2 * Real.pi * b)| * gaussianTail s := by
  have hs0 : 0 < s := by linarith
  let a := Real.exp (-Real.pi * s) * |Real.sin (2 * Real.pi * b)|
  let term (k : ℕ) := ((k : ℝ) + 2) *
    Real.exp (-Real.pi * s * ((k : ℝ) + 2) ^ 2) *
    Real.sin (2 * Real.pi * ((k : ℝ) + 2) * b)
  have hsin (k : ℕ) : |Real.sin (2 * Real.pi * ((k : ℝ) + 2) * b)| ≤
      ((k : ℝ) + 2) * |Real.sin (2 * Real.pi * b)| := by
    have h := Real.abs_sin_sum_le (Finset.range (k + 2))
      (fun _ : ℕ => 2 * Real.pi * b)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using h
  have he (k : ℕ) : Real.exp (-Real.pi * s * ((k : ℝ) + 2) ^ 2) =
      Real.exp (-Real.pi * s) *
        Real.exp (-Real.pi * s * (((k : ℝ) + 2) ^ 2 - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb (k : ℕ) : ‖term k‖ ≤ a * (((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * s * (((k : ℝ) + 2) ^ 2 - 1))) := by
    dsimp [term]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (show 0 ≤ (k : ℝ) + 2 by positivity)]
    calc
      _ ≤ (((k : ℝ) + 2) * Real.exp (-Real.pi * s * ((k : ℝ) + 2) ^ 2)) *
          (((k : ℝ) + 2) * |Real.sin (2 * Real.pi * b)|) :=
        mul_le_mul_of_nonneg_left (hsin k) (by positivity)
      _ = _ := by rw [he]; dsimp [a]; ring
  have hmajor := (tail_summable hs).mul_left a
  have hnorm : Summable (fun k => ‖term k‖) :=
    hmajor.of_nonneg_of_le (fun k => norm_nonneg _) hb
  have hsplit : thetaSine s b - Real.exp (-Real.pi * s) *
      Real.sin (2 * Real.pi * b) = ∑' k : ℕ, term k := by
    have h := (sine_summable hs0 b).sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_mul,
      one_pow] at h
    dsimp [thetaSine]
    rw [← h]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, mul_one]
    change (Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b) +
      ∑' k : ℕ, term k) - Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b) = _
    ring
  rw [hsplit]
  calc
    _ ≤ ∑' k : ℕ, ‖term k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, a * (((k : ℝ) + 2) ^ 2 *
        Real.exp (-Real.pi * s * (((k : ℝ) + 2) ^ 2 - 1))) :=
      hnorm.tsum_le_tsum hb hmajor
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The first mode controls the derivative for every translation, with its sign on the
open half-period. -/
theorem thetaFourier_derivative_bounds {s : ℝ} (hs : 0 < s) (b : ℝ) :
    |deriv (thetaFourier s) b| ≤
      4 * Real.pi * Real.exp (-Real.pi * s) * |Real.sin (2 * Real.pi * b)| *
        (1 + gaussianTail s) ∧
    (0 ≤ b → b ≤ 1 / 2 →
      4 * Real.pi * Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b) *
        (1 - gaussianTail s) ≤ -deriv (thetaFourier s) b) := by
  have hs0 : 0 < s := hs
  have he := thetaSine_first_mode hs b
  rw [(hasDerivAt_thetaFourier hs0 b).deriv]
  constructor
  · have htri : |thetaSine s b| ≤
        |thetaSine s b - Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b)| +
          |Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b)| := by
      simpa using abs_add_le
        (thetaSine s b - Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b))
        (Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b))
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at htri
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_le_mul_of_nonneg_left (he.trans (le_refl _)) Real.pi_pos.le,
      mul_le_mul_of_nonneg_left htri Real.pi_pos.le]
  · intro hb hb'
    have hsin : 0 ≤ Real.sin (2 * Real.pi * b) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    rw [abs_of_nonneg hsin] at he
    have hlo := (abs_le.mp he).1
    nlinarith [mul_le_mul_of_nonneg_left hlo Real.pi_pos.le]

private lemma gaussian_moment_comparison (u : ℝ) :
    u * Real.exp (-u) ≤ (2 * Real.exp (-1)) * Real.exp (-u / 2) := by
  have h := mul_le_mul_of_nonneg_right
    (Real.mul_exp_neg_le_exp_neg_one (u / 2))
    (show 0 ≤ 2 * Real.exp (-u / 2) by positivity)
  have he : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (u / 2) * (Real.exp (-u / 2) * Real.exp (-u / 2)) * 2 := by rw [he]; ring
    _ = (u / 2 * Real.exp (-(u / 2))) * (2 * Real.exp (-u / 2)) := by
      rw [neg_div]
      ring
    _ ≤ Real.exp (-1) * (2 * Real.exp (-u / 2)) := h
    _ = _ := by ring

/-- The translation derivative is controlled by a theta value at half the parameter. -/
theorem thetaFourier_derivative_control {s : ℝ} (hs : 0 < s) (b : ℝ) :
    |deriv (thetaFourier s) b| ≤
      (4 * Real.exp (-1) / s) * (thetaFourier (s / 2) 0 - 1) * |Real.sin (2 * Real.pi * b)| := by
  let f (k : ℕ) := ((k : ℝ) + 1) ^ 2 *
    Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)
  let g (k : ℕ) := Real.exp (-Real.pi * (s / 2) * ((k : ℝ) + 1) ^ 2)
  have hp : 0 < Real.pi * s := mul_pos Real.pi_pos hs
  have hf : Summable f := gaussian_moment hs 2
  have hg : Summable g := by
    simpa only [pow_zero, one_mul] using gaussian_moment (by positivity : 0 < s / 2) 0
  have hm (k : ℕ) : f k ≤ (2 * Real.exp (-1) * (Real.pi * s)⁻¹) * g k := by
    have h := gaussian_moment_comparison (Real.pi * s * ((k : ℝ) + 1) ^ 2)
    have he : -(Real.pi * s * ((k : ℝ) + 1) ^ 2) / 2 =
        -Real.pi * (s / 2) * ((k : ℝ) + 1) ^ 2 := by ring
    rw [he, show -(Real.pi * s * ((k : ℝ) + 1) ^ 2) =
      -Real.pi * s * ((k : ℝ) + 1) ^ 2 by ring] at h
    apply (mul_le_mul_iff_right₀ hp).mp
    dsimp [f, g]
    convert h using 1 <;> field_simp <;> ring
  have hm' := hf.tsum_le_tsum hm (hg.mul_left (2 * Real.exp (-1) * (Real.pi * s)⁻¹))
  rw [tsum_mul_left] at hm'
  have hb (k : ℕ) :
      ‖((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
        Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)‖ ≤
      |Real.sin (2 * Real.pi * b)| * f k := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity),
      abs_of_pos (Real.exp_pos _)]
    have hsin : |Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)| ≤
        ((k : ℝ) + 1) * |Real.sin (2 * Real.pi * b)| := by
      have h := Real.abs_sin_sum_le (Finset.range (k + 1))
        (fun _ : ℕ => 2 * Real.pi * b)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using h
    calc
      _ ≤ (((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) *
          (((k : ℝ) + 1) * |Real.sin (2 * Real.pi * b)|) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = _ := by dsimp [f]; ring
  have hnorm : Summable (fun k : ℕ =>
      ‖((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
        Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)‖) :=
    (hf.mul_left |Real.sin (2 * Real.pi * b)|).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hsum : |thetaSine s b| ≤ |Real.sin (2 * Real.pi * b)| * ∑' k : ℕ, f k := by
    calc
      _ ≤ ∑' k : ℕ,
          ‖((k : ℝ) + 1) * Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2) *
            Real.sin (2 * Real.pi * ((k : ℝ) + 1) * b)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' k : ℕ, |Real.sin (2 * Real.pi * b)| * f k :=
        hnorm.tsum_le_tsum hb (hf.mul_left _)
      _ = _ := tsum_mul_left
  have he : thetaFourier (s / 2) 0 = 1 + 2 * ∑' k : ℕ, g k := by
    simp [thetaFourier, g]
  rw [(hasDerivAt_thetaFourier hs b).deriv, abs_mul, abs_mul, abs_neg,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * Real.pi by positivity)
  have h2 := mul_le_mul_of_nonneg_left hm'
    (show 0 ≤ 4 * Real.pi * |Real.sin (2 * Real.pi * b)| by positivity)
  have hid : 4 * Real.pi * (2 * Real.exp (-1) * (Real.pi * s)⁻¹) = 8 * Real.exp (-1) / s := by
    field_simp [hs.ne', Real.pi_ne_zero]
    <;> ring
  rw [show 4 * Real.pi * |Real.sin (2 * Real.pi * b)| *
    ((2 * Real.exp (-1) * (Real.pi * s)⁻¹) * ∑' k : ℕ, g k) =
    (8 * Real.exp (-1) / s) * |Real.sin (2 * Real.pi * b)| * ∑' k : ℕ, g k by
      rw [← hid]; ring] at h2
  rw [he]
  calc
    _ ≤ 4 * Real.pi * |Real.sin (2 * Real.pi * b)| * ∑' k : ℕ, f k := by
      convert h1 using 1 <;> ring
    _ ≤ (8 * Real.exp (-1) / s) * |Real.sin (2 * Real.pi * b)| * ∑' k : ℕ, g k := h2
    _ = _ := by ring

private lemma complex_gaussian_term (s b : ℝ) (n : ℤ) :
    -(Real.pi : ℂ) * s * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I * b) * n =
    ((-Real.pi * s * (n : ℝ) ^ 2 : ℝ) : ℂ) +
      ((2 * Real.pi * (n : ℝ) * b : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

private lemma summable_complex_gaussian {s : ℝ} (hs : 0 < s) (b : ℝ) :
    Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * s * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I * b) * n)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hs 0
  simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] at h
  apply h.of_norm_bounded
  intro n
  rw [complex_gaussian_term, Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero]
  apply le_of_eq
  congr 1
  ring

/-- Pairing integer Fourier frequencies gives the positive-frequency theta expansion. -/
lemma real_fourier_int {s : ℝ} (hs : 0 < s) (b : ℝ) :
    (∑' n : ℤ, Real.exp (-Real.pi * s * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * (n : ℝ) * b)) = thetaFourier s b := by
  let f (n : ℤ) := Real.exp (-Real.pi * s * (n : ℝ) ^ 2) *
    Real.cos (2 * Real.pi * (n : ℝ) * b)
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    have hshift : Summable (fun n : ℕ =>
        Real.exp (-Real.pi * s * ((n : ℝ) + 1) ^ 2)) := by
      simpa only [pow_zero, one_mul] using gaussian_moment hs 0
    apply hshift.of_norm_bounded
    intro n
    dsimp [f]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have hneg : (fun n : ℕ => f (-(n + 1))) = (fun n : ℕ => f (n + 1)) := by
    funext n
    dsimp [f]
    simp only [Int.cast_neg, neg_sq, mul_neg, neg_mul, Real.cos_neg]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_add_one_of_neg_add_one hpos (hneg.symm ▸ hpos), hneg]
  have hnat : (∑' n : ℕ, f (n + 1)) =
      ∑' n : ℕ, Real.exp (-Real.pi * s * ((n : ℝ) + 1) ^ 2) *
        Real.cos (2 * Real.pi * ((n : ℝ) + 1) * b) := by
    apply tsum_congr
    intro n
    simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [hnat, show f 0 = 1 by simp [f], thetaFourier]
  ring

/-- The positive-frequency Fourier series is the positive real translated Gaussian sum. -/
theorem thetaFourier_poisson {s : ℝ} (hs : 0 < s) (b : ℝ) :
    thetaFourier s b = (Real.sqrt s)⁻¹ *
      ∑' n : ℤ, Real.exp (-Real.pi / s * ((n : ℝ) - b) ^ 2) := by
  have h := D5.S3.Analytic.Polynomial.DiagonalPadeWindow.gaussian_poisson
    (mul_pos Real.pi_pos hs) (2 * Real.pi * b)
  have he : (fun n : ℤ => Complex.exp
      (↑(-(Real.pi * s) * (n : ℝ) ^ 2) + ↑((n : ℝ) * (2 * Real.pi * b)) *
        Complex.I)) = (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * s * (n : ℂ) ^ 2 +
          2 * Real.pi * (Complex.I * b) * n)) := by
    funext n
    rw [complex_gaussian_term]
    congr 1 <;> push_cast <;> ring
  rw [he] at h
  have hleft : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * s * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I * b) * n)).re = thetaFourier s b := by
    rw [Complex.re_tsum (summable_complex_gaussian hs b)]
    convert real_fourier_int hs b using 1
    apply tsum_congr
    intro n
    rw [complex_gaussian_term, Complex.exp_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
  have hh := congrArg Complex.re h
  rw [hleft, Complex.ofReal_re] at hh
  have hr : Real.pi * s / Real.pi = s := by field_simp
  have hb : 2 * Real.pi * b / (2 * Real.pi) = b := by field_simp
  rw [hr, hb, one_div] at hh
  simpa only [neg_div] using hh

/-- At zero translation the reciprocal parameter exchanges the two Gaussian sums. -/
theorem thetaFourier_zero_duality {s : ℝ} (hs : 0 < s) :
    thetaFourier s 0 = (Real.sqrt s)⁻¹ * thetaFourier s⁻¹ 0 := by
  have h := real_fourier_int (inv_pos.mpr hs) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [thetaFourier_poisson hs 0, ← h]
  congr 1
  apply tsum_congr
  intro n
  simp only [sub_zero]
  congr 1

/-- A translated Gaussian sum can be differentiated term by term on the whole real line. -/
theorem hasDerivAt_gaussianTranslate {a : ℝ} (ha : 0 < a) (b : ℝ) :
    HasDerivAt (fun z => ∑' n : ℤ, Real.exp (-a * (z - n) ^ 2))
      (∑' n : ℤ, (-2 * a * (b - n)) * Real.exp (-a * (b - n) ^ 2)) b := by
  let M := |b| + 1
  let A (n : ℤ) := Real.exp (-Real.pi *
    (a / Real.pi * (n : ℝ) ^ 2 - 2 * (a * M / Real.pi) * |(n : ℝ)|))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h0 : Summable A := by
    simpa only [pow_zero, one_mul, Int.cast_abs] using
      summable_pow_mul_jacobiTheta₂_term_bound (a * M / Real.pi) hT 0
  have h1 : Summable (fun n : ℤ => |(n : ℝ)| * A n) := by
    simpa only [pow_one, Int.cast_abs] using
      summable_pow_mul_jacobiTheta₂_term_bound (a * M / Real.pi) hT 1
  have hu : Summable (fun n : ℤ => 2 * a * (|(n : ℝ)| + M) * A n) := by
    convert (h1.add (h0.mul_left M)).mul_left (2 * a) using 1
    ext n
    ring
  have he (n : ℤ) (z : ℝ) (hz : |z| ≤ M) :
      Real.exp (-a * (z - n) ^ 2) ≤ A n := by
    have hnz : (n : ℝ) * z ≤ |(n : ℝ)| * M := by
      calc
        _ ≤ |(n : ℝ) * z| := le_abs_self _
        _ = |(n : ℝ)| * |z| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have heq : -Real.pi * (a / Real.pi * (n : ℝ) ^ 2 -
        2 * (a * M / Real.pi) * |(n : ℝ)|) =
        -a * ((n : ℝ) ^ 2 - 2 * M * |(n : ℝ)|) := by
      field_simp
      <;> ring
    rw [heq]
    have hsq : (n : ℝ) ^ 2 - 2 * M * |(n : ℝ)| ≤ (z - n) ^ 2 := by
      nlinarith [sq_nonneg z]
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  let g (n : ℤ) (z : ℝ) := Real.exp (-a * (z - n) ^ 2)
  let g' (n : ℤ) (z : ℝ) := (-2 * a * (z - n)) * g n z
  have hd (n : ℤ) (z : ℝ) : HasDerivAt (g n) (g' n z) z := by
    convert ((((hasDerivAt_id z).sub_const (n : ℝ)).pow 2).const_mul (-a)).exp using 1
    · rfl
    · dsimp [g, g']
      ring
  have hb (n : ℤ) (z : ℝ) (hz : z ∈ Set.Ioo (b - 1) (b + 1)) :
      ‖g' n z‖ ≤ 2 * a * (|(n : ℝ)| + M) * A n := by
    have hzM : |z| ≤ M := by
      apply abs_le.mpr
      dsimp [M]
      constructor <;> linarith [hz.1, hz.2, le_abs_self b, neg_abs_le b]
    have habs : |z - (n : ℝ)| ≤ |(n : ℝ)| + M := by
      have ht := abs_add_le z (-(n : ℝ))
      simp only [abs_neg] at ht
      change |z - (n : ℝ)| ≤ _ at ht
      linarith
    dsimp [g', g]
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_pos ha, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left habs (by positivity))
      (he n z hzM) (Real.exp_pos _).le (by positivity)
  have hbm : b ∈ Set.Ioo (b - 1) (b + 1) := by constructor <;> linarith
  have hg : Summable (fun n : ℤ => g n b) :=
    h0.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
      (fun n => he n b (by dsimp [M]; linarith))
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo _ _).isPreconnected (fun n z _ => hd n z) hb hbm hg hbm

/-- The derivative of the Fourier theta function equals the signed Gaussian force sum. -/
theorem thetaFourier_derivative_gaussian {s : ℝ} (hs : 0 < s) (b : ℝ) :
    deriv (thetaFourier s) b = -(2 * Real.pi / (s * Real.sqrt s)) *
      ∑' n : ℤ, (b - n) * Real.exp (-Real.pi / s * (b - n) ^ 2) := by
  have hd := (hasDerivAt_gaussianTranslate (div_pos Real.pi_pos hs) b).const_mul
    ((Real.sqrt s)⁻¹)
  have hf : (fun z => (Real.sqrt s)⁻¹ *
      ∑' n : ℤ, Real.exp (-(Real.pi / s) * (z - n) ^ 2)) = thetaFourier s := by
    funext z
    rw [thetaFourier_poisson hs z]
    congr 1
    apply tsum_congr
    intro n
    congr 1
    ring
  rw [hf] at hd
  rw [hd.deriv]
  have he : (∑' n : ℤ, (-2 * (Real.pi / s) * (b - n)) *
      Real.exp (-(Real.pi / s) * (b - n) ^ 2)) = (-2 * Real.pi / s) *
      ∑' n : ℤ, (b - n) * Real.exp (-Real.pi / s * (b - n) ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [neg_div]
    ring
  rw [he]
  ring

private lemma thetaFourier_zero_le_two {r : ℝ} (hr : 1 ≤ r) :
    thetaFourier r 0 ≤ 2 := by
  have hr0 : 0 < r := by linarith
  let q := Real.exp (-Real.pi * r)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hpr : 3 < Real.pi * r := by
    have h := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have hq : q < 1 / 4 := by
    have he := Real.add_one_le_exp (Real.pi * r)
    dsimp [q]
    rw [show -Real.pi * r = -(Real.pi * r) by ring, Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hb := HurwitzKernelBounds.F_nat_zero_le (a := 1) (by norm_num) hr0
  have he : HurwitzKernelBounds.F_nat 0 1 r =
      ∑' k : ℕ, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * r) := by
    unfold HurwitzKernelBounds.F_nat
    apply tsum_congr
    intro k
    simp only [HurwitzKernelBounds.f_nat, pow_zero, one_mul]
  rw [he, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))] at hb
  norm_num only [one_pow, mul_one] at hb
  have hsum : (∑' k : ℕ, Real.exp (-Real.pi * r * ((k : ℝ) + 1) ^ 2)) ≤
      q / (1 - q) := by
    simpa only [mul_right_comm (-Real.pi)] using hb
  have hfrac : q / (1 - q) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
    linarith
  simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  linarith

/-- Uniform upper control at every translation and a positive lower control on a half-period. -/
theorem thetaFourier_small_derivative_bounds {s : ℝ} (hs : 0 < s) (hs' : s ≤ Real.pi / 6)
    (b : ℝ) :
    |deriv (thetaFourier s) b| ≤ 6 / (s * Real.sqrt s) * |Real.sin (2 * Real.pi * b)| ∧
    (0 ≤ b → b ≤ 1 / 2 →
      (3 / (10 * s * Real.sqrt s)) * Real.exp (-Real.pi / (4 * s)) *
        Real.sin (2 * Real.pi * b) ≤ -deriv (thetaFourier s) b) := by
  have hsr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hhalf : 0 < s / 2 := by positivity
  have hr : 1 ≤ (s / 2)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hhalf).mpr
    linarith [Real.pi_lt_four]
  have hz := thetaFourier_zero_le_two hr
  have hroot : (Real.sqrt (s / 2))⁻¹ ≤ (3 / 2) / Real.sqrt s := by
    rw [Real.sqrt_div hs.le, inv_div]
    apply div_le_div_of_nonneg_right _ hsr.le
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hzero : thetaFourier (s / 2) 0 ≤ 3 / Real.sqrt s := by
    rw [thetaFourier_zero_duality hhalf]
    calc
      _ ≤ (Real.sqrt (s / 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      _ ≤ ((3 / 2) / Real.sqrt s) * 2 := mul_le_mul_of_nonneg_right hroot (by norm_num)
      _ = _ := by ring
  have hzero' : thetaFourier (s / 2) 0 - 1 ≤ 3 / Real.sqrt s := by linarith
  constructor
  · have hnonneg : 0 ≤ thetaFourier (s / 2) 0 - 1 := by
      have hn : 0 ≤ ∑' k : ℕ, Real.exp (-Real.pi * (s / 2) * ((k : ℝ) + 1) ^ 2) :=
        tsum_nonneg (fun k => (Real.exp_pos _).le)
      simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
      linarith
    have hcoef : 4 * Real.exp (-1) / s ≤ 2 / s := by
      have he : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact (div_le_iff₀ (Real.exp_pos 1)).mpr
          (by linarith [Real.add_one_le_exp (1 : ℝ)])
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    have h := (thetaFourier_derivative_control hs b).trans
      (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right hcoef hnonneg).trans
          (mul_le_mul_of_nonneg_left hzero' (by positivity : 0 ≤ 2 / s)))
        (abs_nonneg _))
    convert h using 1 <;> field_simp <;> ring
  · intro hb hb'
    have ha : 6 ≤ Real.pi / s := by
      apply (le_div_iff₀ hs).mpr
      linarith
    have hf := gaussian_force_lower ha hb hb'
    have hcoeff : 0 ≤ 2 * Real.pi / (s * Real.sqrt s) := by positivity
    have h := mul_le_mul_of_nonneg_left hf hcoeff
    rw [thetaFourier_derivative_gaussian hs b]
    have hforce : (∑' n : ℤ, (b - n) *
        Real.exp (-Real.pi / s * (b - n) ^ 2)) = gaussianForce (Real.pi / s) b := by
      unfold gaussianForce
      apply tsum_congr
      intro n
      congr 2
      ring
    rw [hforce]
    have he : 2 * Real.pi / (s * Real.sqrt s) *
        (3 / (20 * Real.pi) * Real.exp (-(Real.pi / s) / 4) *
          Real.sin (2 * Real.pi * b)) =
        3 / (10 * s * Real.sqrt s) * Real.exp (-Real.pi / (4 * s)) *
          Real.sin (2 * Real.pi * b) := by
      rw [show -(Real.pi / s) / 4 = -Real.pi / (4 * s) by ring]
      field_simp [hs.ne', hsr.ne', Real.pi_ne_zero]
      <;> ring
    rw [he] at h
    nlinarith only [h]

end
end D5.S3.Fourier.PlanarTheta
