/- GID: D5/S3/Fourier/ThetaShearMonotonicity
   generality: G
   mirror-B: D5/B/S3/Fourier/ThetaShearMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict sign of the Fourier shear series by domination of its first row. -/

import D5.S3.Fourier.ThetaDerivativeBounds

/-! # Domination of the first shear row -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Fourier.PlanarTheta
noncomputable section

private lemma sin_nat_mul_bound (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * ((k : ℝ) + 1) * x)| ≤
      ((k : ℝ) + 1) * |Real.sin (2 * Real.pi * x)| := by
  have h := Real.abs_sin_sum_le (Finset.range (k + 1))
    (fun _ : ℕ => 2 * Real.pi * x)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using h

private lemma derivative_uniform_bound {s : ℝ} (hs : 0 < s) (b : ℝ) :
    |deriv (thetaFourier s) b| ≤ |(4 * Real.exp (-1) / s) * thetaFourier (s / 2) 0| := by
  have h := thetaFourier_derivative_control hs b
  have hc : (4 * Real.exp (-1) / s) * (thetaFourier (s / 2) 0 - 1) ≤
      (4 * Real.exp (-1) / s) * thetaFourier (s / 2) 0 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h := h.trans (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul (le_abs_self ((4 * Real.exp (-1) / s) *
      thetaFourier (s / 2) 0)) (Real.abs_sin_le_one (2 * Real.pi * b))
        (abs_nonneg _) (abs_nonneg _))

private lemma weighted_derivative_summable {s v : ℝ} (hs : 0 < s)
    (hv : 0 < v) (x : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) *
      Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) *
      deriv (thetaFourier s) (((k : ℝ) + 1) * x)) := by
  let B := |(4 * Real.exp (-1) / s) * thetaFourier (s / 2) 0|
  apply ((gaussian_moment hv 1).mul_right B).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity),
    abs_of_pos (Real.exp_pos _)]
  simpa only [pow_one] using mul_le_mul_of_nonneg_left (derivative_uniform_bound hs _)
    (show 0 ≤ ((k : ℝ) + 1) *
      Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) by positivity)

private theorem weighted_derivative_neg {s v x A B : ℝ} (hs : 0 < s)
    (hv : 1 / 2 ≤ v) (hx : 0 < x) (hx' : x < 1 / 2) (hB : 0 ≤ B)
    (hlower : A * Real.sin (2 * Real.pi * x) ≤ -deriv (thetaFourier s) x)
    (hupper : ∀ b : ℝ, |deriv (thetaFourier s) b| ≤ B * |Real.sin (2 * Real.pi * b)|)
    (hmargin : B * gaussianTail v < A) :
    (∑' k : ℕ, ((k : ℝ) + 1) *
      Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) *
      deriv (thetaFourier s) (((k : ℝ) + 1) * x)) < 0 := by
  have hv0 : 0 < v := by linarith
  have hsin : 0 < Real.sin (2 * Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  let C := Real.exp (-Real.pi * v) * Real.sin (2 * Real.pi * x)
  have hC : 0 < C := by dsimp [C]; positivity
  let f (k : ℕ) := ((k : ℝ) + 1) *
    Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) *
    deriv (thetaFourier s) (((k : ℝ) + 1) * x)
  have hf : Summable f := weighted_derivative_summable hs hv0 x
  have hfirst : f 0 ≤ -A * C := by
    have h := mul_le_mul_of_nonneg_left hlower (Real.exp_pos (-Real.pi * v)).le
    dsimp [f, C]
    norm_num only [Nat.cast_zero, zero_add, one_pow, mul_one, one_mul]
    nlinarith only [h]
  have hmajor (k : ℕ) : f (k + 1) ≤ B * C * (((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) := by
    have hd := hupper (((k : ℝ) + 2) * x)
    have hn := sin_nat_mul_bound x (k + 1)
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
      abs_of_pos hsin] at hn
    simp only [mul_assoc (2 * Real.pi) ((k : ℝ) + 2) x] at hn
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hn hB)
    have hh := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd')
      (show 0 ≤ ((k : ℝ) + 2) *
        Real.exp (-Real.pi * v * ((k : ℝ) + 2) ^ 2) by positivity)
    have he : Real.exp (-Real.pi * v * ((k : ℝ) + 2) ^ 2) =
        Real.exp (-Real.pi * v) *
          Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    convert hh using 1 <;> rw [he] <;> dsimp [C] <;> ring
  have htail : (∑' k : ℕ, f (k + 1)) ≤ B * C * gaussianTail v := by
    calc
      _ ≤ ∑' k : ℕ, B * C * (((k : ℝ) + 2) ^ 2 *
          Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) :=
        ((summable_nat_add_iff 1).mpr hf).tsum_le_tsum hmajor
          ((gaussian_tail_bound hv).1.mul_left (B * C))
      _ = _ := by rw [tsum_mul_left]; rfl
  have ht := mul_lt_mul_of_pos_right hmargin hC
  change (∑' k : ℕ, f k) < 0
  rw [← hf.sum_add_tsum_nat_add 1, Finset.sum_range_one]
  nlinarith only [hfirst, htail, ht]


private lemma thetaFourier_even (s b : ℝ) : thetaFourier s (-b) = thetaFourier s b := by
  simp only [thetaFourier, mul_neg, Real.cos_neg]

private lemma poisson_row {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (x : ℝ) (n : ℤ) :
    (∑' m : ℤ, Real.exp (-Real.pi * t * Q x y (m, n))) =
      Real.sqrt (y / t) * (Real.exp (-Real.pi * (t * y) * (n : ℝ) ^ 2) *
        thetaFourier (y / t) ((n : ℝ) * x)) := by
  have hs : 0 < y / t := div_pos hy ht
  have hsz : Real.sqrt (y / t) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hgaussian : (∑' m : ℤ, Real.exp (-Real.pi / (y / t) *
      ((m : ℝ) + (n : ℝ) * x) ^ 2)) =
      Real.sqrt (y / t) * thetaFourier (y / t) ((n : ℝ) * x) := by
    rw [← thetaFourier_even (y / t) ((n : ℝ) * x), thetaFourier_poisson hs]
    simp only [sub_neg_eq_add]
    rw [mul_inv_cancel_left₀ hsz]
  calc
    _ = ∑' m : ℤ, Real.exp (-Real.pi * (t * y) * (n : ℝ) ^ 2) *
        Real.exp (-Real.pi / (y / t) * ((m : ℝ) + (n : ℝ) * x) ^ 2) := by
      apply tsum_congr
      intro m
      rw [← Real.exp_add]
      congr 1
      dsimp [Q]
      field_simp [ht.ne', hy.ne']
      <;> ring
    _ = _ := by rw [tsum_mul_left, hgaussian]; ring

private lemma fourier_rows_summable {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * (t * y) * (n : ℝ) ^ 2) *
      thetaFourier (y / t) ((n : ℝ) * x)) := by
  have hs : Real.sqrt (y / t) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hy ht)).ne'
  have h := ((summable t x ht hy).prod_symm.prod).mul_left
    (Real.sqrt (y / t))⁻¹
  convert h using 1
  ext n
  change _ = (Real.sqrt (y / t))⁻¹ *
    ∑' m : ℤ, Real.exp (-Real.pi * t * Q x y (m, n))
  rw [poisson_row ht hy x n, inv_mul_cancel_left₀ hs]

private lemma positive_rows_summable {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (x : ℝ) :
    Summable (fun k : ℕ => Real.exp (-Real.pi * (t * y) * ((k : ℝ) + 1) ^ 2) *
      thetaFourier (y / t) (((k : ℝ) + 1) * x)) := by
  have h := (fourier_rows_summable ht hy x).comp_injective
    (show Function.Injective (fun k : ℕ => (k : ℤ) + 1) from by
      intro a b hab
      exact_mod_cast add_right_cancel hab)
  simpa only [Function.comp_def, Int.cast_add, Int.cast_natCast, Int.cast_one] using h

private lemma fourier_rows {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (x : ℝ) :
    F t x y = Real.sqrt (y / t) *
      ∑' n : ℤ, Real.exp (-Real.pi * (t * y) * (n : ℝ) ^ 2) *
        thetaFourier (y / t) ((n : ℝ) * x) := by
  have h := (summable t x ht hy).prod_symm
  calc
    _ = ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * Q x y (p.2, p.1)) := by
      exact ((Equiv.prodComm ℤ ℤ).tsum_eq
        (fun p : ℤ × ℤ => Real.exp (-Real.pi * t * Q x y p))).symm
    _ = ∑' n : ℤ, ∑' m : ℤ, Real.exp (-Real.pi * t * Q x y (m, n)) := h.tsum_prod
    _ = _ := by simp_rw [poisson_row ht hy x]; rw [tsum_mul_left]

/-- Pairing the positive and negative Poisson rows isolates the zero row. -/
private theorem shear_positive_rows {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (x : ℝ) :
    F t x y = Real.sqrt (y / t) * (thetaFourier (y / t) 0 +
      2 * ∑' k : ℕ, Real.exp (-Real.pi * (t * y) * ((k : ℝ) + 1) ^ 2) *
        thetaFourier (y / t) (((k : ℝ) + 1) * x)) := by
  let f (n : ℤ) := Real.exp (-Real.pi * (t * y) * (n : ℝ) ^ 2) *
    thetaFourier (y / t) ((n : ℝ) * x)
  have hp : Summable (fun k : ℕ => f (k + 1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      positive_rows_summable ht hy x
  have heven : (fun k : ℕ => f (-(k + 1))) = (fun k : ℕ => f (k + 1)) := by
    funext k
    dsimp [f]
    simp only [Int.cast_neg, neg_sq, neg_mul, thetaFourier_even]
  rw [fourier_rows ht hy x]
  change Real.sqrt (y / t) * (∑' n : ℤ, f n) = _
  have hzero : f 0 = thetaFourier (y / t) 0 := by simp [f]
  have hpositive : (∑' k : ℕ, f (k + 1)) =
      ∑' k : ℕ, Real.exp (-Real.pi * (t * y) * ((k : ℝ) + 1) ^ 2) *
        thetaFourier (y / t) (((k : ℝ) + 1) * x) := by
    apply tsum_congr
    intro k
    simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [tsum_of_add_one_of_neg_add_one hp (heven.symm ▸ hp), heven, hzero]
  simp_rw [hpositive]
  ring

/-- The shear derivative is the convergent derivative of the positive Poisson rows.
The premise concerns the Fourier parameter, not the temperature alone. -/
private theorem hasDerivAt_shear_fourier {t y : ℝ} (ht : 0 < t) (hy : 0 < y)
    (x : ℝ) :
    HasDerivAt (fun z => F t z y)
      (2 * Real.sqrt (y / t) * ∑' k : ℕ, ((k : ℝ) + 1) *
        Real.exp (-Real.pi * (t * y) * ((k : ℝ) + 1) ^ 2) *
        deriv (thetaFourier (y / t)) (((k : ℝ) + 1) * x)) x := by
  let s := y / t
  let v := t * y
  let B := |(4 * Real.exp (-1) / s) * thetaFourier (s / 2) 0|
  let g (k : ℕ) (z : ℝ) := Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) *
    thetaFourier s (((k : ℝ) + 1) * z)
  let g' (k : ℕ) (z : ℝ) := ((k : ℝ) + 1) *
    Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) *
    deriv (thetaFourier s) (((k : ℝ) + 1) * z)
  have hs0 : 0 < s := div_pos hy ht
  have hv0 : 0 < v := mul_pos ht hy
  have hd (k : ℕ) (z : ℝ) : HasDerivAt (g k) (g' k z) z := by
    have h := ((hasDerivAt_thetaFourier hs0 (((k : ℝ) + 1) * z)).comp z
      ((hasDerivAt_id z).const_mul ((k : ℝ) + 1))).const_mul
        (Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2))
    rw [← (hasDerivAt_thetaFourier hs0 (((k : ℝ) + 1) * z)).deriv] at h
    convert h using 1 <;> dsimp [g, g'] <;> ring
  have hm : Summable (fun k : ℕ => B * (((k : ℝ) + 1) *
      Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2))) := by
    have hn : Summable (fun n : ℕ => (n : ℝ) *
        Real.exp (-Real.pi * (v * (n : ℝ) ^ 2))) := by
      simpa only [Function.comp_def, pow_one, Int.cast_natCast, Nat.abs_cast, mul_zero,
        zero_mul, sub_zero] using
        (summable_pow_mul_jacobiTheta₂_term_bound 0 hv0 1).comp_injective
          (fun a b : ℕ => Int.ofNat_inj.mp)
    have hshift := (summable_nat_add_iff 1).mpr hn
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hshift.mul_left B
  have hb (k : ℕ) (z : ℝ) : ‖g' k z‖ ≤ B * (((k : ℝ) + 1) *
      Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2)) := by
    have hB := derivative_uniform_bound hs0 (((k : ℝ) + 1) * z)
    dsimp [g']
    rw [abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity),
      abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ ((k : ℝ) + 1) *
        Real.exp (-Real.pi * v * ((k : ℝ) + 1) ^ 2) by positivity)
    simpa only [mul_comm B] using h
  have h := hasDerivAt_tsum hm hd hb (positive_rows_summable ht hy x) x
  convert ((h.const_mul 2).const_add (thetaFourier s 0)).const_mul
    (Real.sqrt (y / t)) using 1
  · funext z
    exact shear_positive_rows ht hy z
  · dsimp [g', s, v]
    ring

private theorem shear_derivative_neg_ge_one {t y x : ℝ} (ht : 1 ≤ t)
    (hy : Real.sqrt 3 / 2 ≤ y) (hx : 0 < x) (hx' : x < 1 / 2) :
    deriv (fun z => F t z y) x < 0 := by
  have ht0 : 0 < t := by linarith
  have hc : 1 / 2 < Real.sqrt 3 / 2 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < y / t := div_pos hy0 ht0
  have hv : 1 / 2 ≤ t * y := by
    have hm := mul_le_mul_of_nonneg_right ht hy0.le
    linarith
  rw [(hasDerivAt_shear_fourier ht0 hy0 x).deriv]
  apply mul_neg_of_pos_of_neg (by positivity)
  by_cases hs : 1 / 2 ≤ y / t
  · have hsN : 0 ≤ gaussianTail (y / t) := by unfold gaussianTail; positivity
    apply weighted_derivative_neg
      (A := (4 * Real.pi * Real.exp (-Real.pi * (y / t))) *
        (1 - gaussianTail (y / t)))
      (B := (4 * Real.pi * Real.exp (-Real.pi * (y / t))) *
        (1 + gaussianTail (y / t))) hs0 hv hx hx' (by positivity)
      (by convert (thetaFourier_derivative_bounds hs0 x).2 hx.le hx'.le using 1 <;> ring)
      (fun b => by convert (thetaFourier_derivative_bounds hs0 b).1 using 1 <;> ring)
    have hsT := (gaussian_tail_bound hs).2.2
    have hvT := (gaussian_tail_bound hv).2.2
    have hvN : 0 ≤ gaussianTail (t * y) := by unfold gaussianTail; positivity
    have hm : (1 + gaussianTail (y / t)) * gaussianTail (t * y) <
        1 - gaussianTail (y / t) := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 15 - gaussianTail (y / t) by linarith)
        (show 0 ≤ 1 / 15 - gaussianTail (t * y) by linarith)]
    have h := mul_lt_mul_of_pos_left hm
      (show 0 < 4 * Real.pi * Real.exp (-Real.pi * (y / t)) by positivity)
    nlinarith only [h]
  · have hs' : y / t ≤ 1 / 2 := (lt_of_not_ge hs).le
    have hysq : 3 / 4 ≤ y ^ 2 := by
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_nonneg (3 : ℝ),
        mul_nonneg (show 0 ≤ y - Real.sqrt 3 / 2 from sub_nonneg.mpr hy)
          (show 0 ≤ y + Real.sqrt 3 / 2 by positivity)]
    have hvs : 3 / (4 * (y / t)) ≤ t * y := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * (y / t))).mpr
      have he : t * y * (4 * (y / t)) = 4 * y ^ 2 := by
        field_simp [ht0.ne']
        <;> ring
      linarith
    have hsPi : y / t ≤ Real.pi / 6 := by linarith [Real.pi_gt_three]
    apply weighted_derivative_neg hs0 hv hx hx' (by positivity)
      ((thetaFourier_small_derivative_bounds hs0 hsPi x ).2 hx.le hx'.le)
      (fun b => (thetaFourier_small_derivative_bounds hs0 hsPi b).1)
    have htail := gaussian_tail_scaled_bound hs0 hsPi hvs
    have hexp : Real.exp (Real.pi / (4 * (y / t))) * gaussianTail (t * y) < 1 / 32 :=
      htail.trans (by norm_num)
    have he := mul_lt_mul_of_pos_right hexp
      (Real.exp_pos (-Real.pi / (4 * (y / t))))
    have hcancel : Real.exp (Real.pi / (4 * (y / t))) *
        Real.exp (-Real.pi / (4 * (y / t))) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have hnorm : gaussianTail (t * y) <
        1 / 32 * Real.exp (-Real.pi / (4 * (y / t))) := by
      calc
        _ = (Real.exp (Real.pi / (4 * (y / t))) * gaussianTail (t * y)) *
            Real.exp (-Real.pi / (4 * (y / t))) := by rw [mul_right_comm, hcancel]; ring
        _ < _ := he
    have hm := mul_lt_mul_of_pos_left hnorm
      (show 0 < 6 / ((y / t) * Real.sqrt (y / t)) by positivity)
    have hc : 6 / ((y / t) * Real.sqrt (y / t)) *
        (1 / 32 * Real.exp (-Real.pi / (4 * (y / t)))) <
        3 / (10 * (y / t) * Real.sqrt (y / t)) *
          Real.exp (-Real.pi / (4 * (y / t))) := by
      have hpos : 0 < Real.exp (-Real.pi / (4 * (y / t))) /
          ((y / t) * Real.sqrt (y / t)) := by positivity
      field_simp
      nlinarith
    exact hm.trans hc

/-- The shear derivative is strictly negative throughout the open reduced half-strip. -/
theorem shear_derivative_neg {t y x : ℝ} (ht : 0 < t)
    (hy : Real.sqrt 3 / 2 ≤ y) (hx : 0 < x) (hx' : x < 1 / 2) :
    deriv (fun z => F t z y) x < 0 := by
  by_cases ht1 : 1 ≤ t
  · exact shear_derivative_neg_ge_one ht1 hy hx hx'
  · have hc : 0 < Real.sqrt 3 / 2 := by positivity
    have hy0 : 0 < y := hc.trans_le hy
    have hinv : 1 ≤ t⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ ht).mpr
      linarith
    have hd := (hasDerivAt_shear t⁻¹ x (inv_pos.mpr ht) hy0).differentiableAt.hasDerivAt
    have he : (fun z => t⁻¹ * F t⁻¹ z y) = (fun z => F t z y) := by
      funext z
      exact (temperature_duality t z ht hy0).symm
    have h := hd.const_mul t⁻¹
    rw [he] at h
    rw [h.deriv]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr ht)
      (shear_derivative_neg_ge_one hinv hy hx hx')

/-- The right edge minimizes theta on every horizontal reduced half-strip, uniquely. -/
theorem shear_minimum {t y x : ℝ} (ht : 0 < t) (hy : Real.sqrt 3 / 2 ≤ y)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    F t (1 / 2) y ≤ F t x y ∧
      (F t x y = F t (1 / 2) y ↔ x = 1 / 2) := by
  have hy0 : 0 < y := (by positivity : 0 < Real.sqrt 3 / 2).trans_le hy
  have ha : StrictAntiOn (fun z => F t z y) (Set.Icc 0 (1 / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro z hz
      exact (hasDerivAt_shear t z ht hy0).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact shear_derivative_neg ht hy hz.1 hz.2
  have hright : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) := by constructor <;> norm_num
  have hleft : x ∈ Set.Icc 0 (1 / 2) := ⟨hx, hx'⟩
  constructor
  · rcases lt_or_eq_of_le hx' with h | h
    · exact (ha hleft hright h).le
    · rw [h]
  · constructor
    · intro he
      by_contra hn
      have hlt : x < 1 / 2 := lt_of_le_of_ne hx' hn
      have h := ha hleft hright hlt
      linarith
    · intro h
      rw [h]

end
end D5.S3.Fourier.PlanarTheta
