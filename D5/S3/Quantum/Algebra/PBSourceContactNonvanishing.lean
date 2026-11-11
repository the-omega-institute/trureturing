/- GID: D5/S3/Quantum/Algebra/PBSourceContactNonvanishing
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBSourceContactNonvanishing
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Basic]
   utility: none
   digest: The original two-coordinate PB contact equations control both signed sources. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.PBSourceContactNonvanishing

abbrev Vec := Fin 2 → ℂ

def pairing (u v : Vec) : ℂ := star (u 0) * v 0 + star (u 1) * v 1

def spectral (x y : ℝ) : ℂ := x + Complex.I * y

def cMap (u : Vec) : Vec := ![u 0, 2 * u 1]

def hMap (h : ℝ) (u : Vec) : Vec :=
  ![2 * u 0 + h * u 1, h * u 0 + 4 * u 1]

def graphColumn (h x y : ℝ) (u p : Vec) : Vec :=
  ![(spectral x y + 2) * p 0 + Complex.I * (3 * u 0 + 2 * h * u 1),
    (spectral x y + 1) * p 1 + Complex.I * (h * u 0 + 12 * u 1)]

def actorColumn (x y : ℝ) (p : Vec) : Vec :=
  ![Complex.I * (1 - spectral x y) * p 0,
    Complex.I * (1 - spectral x y / 2) * p 1]

def sourceVector (r : ℝ) : Vec := ![((Real.sqrt 2)⁻¹ : ℝ), (r : ℂ)]

/-- The unchanged complete contact equations on the actual two-dimensional actor.
The two complex source coordinates retain the same fixed source vector. -/
structure Contact (h r x y : ℝ) (u p q a : Vec) (η : ℂ) : Prop where
  source_sign : r = 1 ∨ r = -1
  small : |h| < 1
  imaginary : 1 < |y|
  unit : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1
  first_real : (pairing u p).im = 0
  second_real : (pairing (cMap u) q).im = 0
  mixed : pairing u q = pairing p (cMap u)
  graph : q = graphColumn h x y u p
  actor : a = actorColumn x y p
  source : ∀ j, a j - hMap h u j + spectral x y / 2 * cMap (cMap u) j =
    η * sourceVector r j

def beta (h : ℝ) (u : Vec) : ℝ :=
  3 * ‖u 0‖ ^ 2 + 12 * ‖u 1‖ ^ 2 + 3 * h * (star (u 0) * u 1).re

def residual (h x y : ℝ) (u : Vec) : ℂ :=
  (3 / 2 : ℂ) * (1 - spectral x y)⁻¹ * (‖u 0‖ ^ 2 : ℝ) +
    h * (1 - spectral x y)⁻¹ * (star (u 0) * u 1) +
    2 * h * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)

def sourceReadout (r x y : ℝ) (u : Vec) : ℂ :=
  star (u 0) * (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ) +
    star (u 1) * (2 - spectral x y)⁻¹ * (2 * r)

def numerator (h x y : ℝ) (u : Vec) : ℂ :=
  -((‖u 0‖ ^ 2 + 8 * ‖u 1‖ ^ 2 : ℝ) : ℂ) / 2 - residual h x y u -
    Complex.I * (beta h u / y : ℝ)

private theorem graph_pairing (h x y : ℝ) (u p : Vec) :
    pairing u (graphColumn h x y u p) =
      (spectral x y + 3) * pairing u p - pairing u (cMap p) +
        Complex.I * ((beta h u : ℂ) +
          Complex.I * (h * (star (u 0) * u 1).im : ℝ)) := by
  apply Complex.ext <;>
    simp [pairing, graphColumn, cMap, beta, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem pairing_swap (u p : Vec) :
    pairing p (cMap u) = star (pairing u (cMap p)) := by
  simp [pairing, cMap, map_add, map_mul]
  ring

private theorem mass (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) :
    pairing u p = (-(beta h u / y) : ℝ) := by
  have hy : y ≠ 0 := by
    intro hz
    have hi := H.imaginary
    simp [hz] at hi
  have he := congrArg Complex.im H.mixed
  rw [H.graph, graph_pairing, pairing_swap] at he
  simp [spectral, Complex.mul_im, H.first_real] at he
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [neg_div]
    apply (eq_div_iff hy).mpr
    linarith
  · simpa using H.first_real

private theorem denominator_ne (j x y : ℝ) (hy : y ≠ 0) :
    (j : ℂ) - spectral x y ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp [spectral] at hi
  exact hy hi

private theorem source_columns (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) (hy : y ≠ 0) :
    p 0 = -Complex.I * ((1 / 2 : ℂ) * u 0 +
      (1 - spectral x y)⁻¹ * ((3 / 2 : ℂ) * u 0 + h * u 1) +
      η * (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ)) ∧
    p 1 = -Complex.I * (4 * u 1 +
      (2 - spectral x y)⁻¹ * (2 * h * u 0) +
      η * (2 - spectral x y)⁻¹ * (2 * r)) := by
  have h0 := H.source 0
  have h1 := H.source 1
  rw [H.actor] at h0 h1
  simp [actorColumn, hMap, cMap, sourceVector] at h0 h1
  constructor
  · field_simp [denominator_ne 1 x y hy]
    linear_combination -Complex.I * h0
  · field_simp [denominator_ne 2 x y hy]
    linear_combination -2 * Complex.I * h1

private theorem source_balance (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) (hy : y ≠ 0) :
    η * sourceReadout r x y u = numerator h x y u := by
  obtain ⟨h0, h1⟩ := source_columns h r x y u p q a η H hy
  have he : pairing u p = -Complex.I *
      (((‖u 0‖ ^ 2 + 8 * ‖u 1‖ ^ 2 : ℝ) : ℂ) / 2 +
        residual h x y u + η * sourceReadout r x y u) := by
    rw [pairing, h0, h1]
    apply Complex.ext <;>
      simp [residual, sourceReadout, Complex.sq_norm, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [mass h r x y u p q a η H] at he
  dsimp [numerator]
  linear_combination Complex.I * he

private theorem resolvent_norm (j x y : ℝ) (hy : y ≠ 0) :
    |y| * ‖((j : ℂ) - spectral x y)⁻¹‖ ≤ 1 := by
  have hn : 0 < ‖(j : ℂ) - spectral x y‖ :=
    norm_pos_iff.mpr (denominator_ne j x y hy)
  have hi : |y| ≤ ‖(j : ℂ) - spectral x y‖ := by
    simpa [spectral] using Complex.abs_im_le_norm ((j : ℂ) - spectral x y)
  rw [norm_inv, ← div_eq_mul_inv]
  exact (div_le_one hn).mpr hi

private theorem resolvent_imaginary (j x y : ℝ) :
    0 ≤ y * (((j : ℂ) - spectral x y)⁻¹).im := by
  rw [Complex.inv_im]
  simp only [spectral, Complex.sub_im, Complex.ofReal_im, Complex.add_im,
    Complex.mul_im, Complex.I_re, Complex.ofReal_re, Complex.I_im,
    zero_mul, one_mul, zero_add, sub_zero, zero_sub, neg_neg]
  rw [← mul_div_assoc]
  exact div_nonneg (mul_self_nonneg y) (Complex.normSq_nonneg _)

private theorem cross_bound (h x y : ℝ) (u : Vec) (hy : y ≠ 0) :
    -(3 * |h| * (‖u 0‖ * ‖u 1‖)) ≤
      y * (h * (1 - spectral x y)⁻¹ * (star (u 0) * u 1) +
        2 * h * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)).im := by
  have hb (j : ℝ) (z : ℂ) :
      |y| * ‖(h : ℂ) * ((j : ℂ) - spectral x y)⁻¹ * z‖ ≤ |h| * ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [resolvent_norm j x y hy, norm_nonneg z, abs_nonneg h]
  have h0 := hb 1 (star (u 0) * u 1)
  have h1 := hb 2 (star (u 1) * u 0)
  simp only [norm_mul, norm_star] at h0 h1
  have hi0 := Complex.abs_im_le_norm
    ((h : ℂ) * (1 - spectral x y)⁻¹ * (star (u 0) * u 1))
  have hi1 := Complex.abs_im_le_norm
    ((h : ℂ) * (2 - spectral x y)⁻¹ * (star (u 1) * u 0))
  have ha0 := neg_abs_le (y *
    ((h : ℂ) * (1 - spectral x y)⁻¹ * (star (u 0) * u 1)).im)
  have ha1 := neg_abs_le (y *
    ((h : ℂ) * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)).im)
  rw [abs_mul] at ha0 ha1
  have hh0 := mul_le_mul_of_nonneg_left hi0 (abs_nonneg y)
  have hh1 := mul_le_mul_of_nonneg_left hi1 (abs_nonneg y)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero] at *
  nlinarith

private theorem numerator_lower (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) (hy : y ≠ 0) :
    3 + 9 * ‖u 1‖ ^ 2 - 3 * |h| ≤ -y * (numerator h x y u).im := by
  have hz : ‖u 0‖ * ‖u 1‖ ≤ 1 / 2 := by
    nlinarith [sq_nonneg (‖u 0‖ - ‖u 1‖), H.unit]
  have hv : |(star (u 0) * u 1).re| ≤ ‖u 0‖ * ‖u 1‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (star (u 0) * u 1)
  have hvh : -(|h| * (‖u 0‖ * ‖u 1‖)) ≤ h * (star (u 0) * u 1).re := by
    have ha := neg_abs_le (h * (star (u 0) * u 1).re)
    rw [abs_mul] at ha
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg h)]
  have hc := cross_bound h x y u hy
  have hr := resolvent_imaginary 1 x y
  have hn : -y * (numerator h x y u).im =
      beta h u + (3 / 2) * ‖u 0‖ ^ 2 * y * ((1 - spectral x y)⁻¹).im +
      y * ((h : ℂ) * (1 - spectral x y)⁻¹ * (star (u 0) * u 1) +
        2 * h * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)).im := by
    simp [numerator, residual, Complex.mul_im]
    field_simp [hy]
    ring
  rw [hn]
  dsimp [beta]
  nlinarith [sq_nonneg ‖u 0‖, H.unit, abs_nonneg h,
    mul_nonneg (sq_nonneg ‖u 0‖) hr]

private theorem readout_upper (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) (hy : y ≠ 0) :
    |y| * ‖sourceReadout r x y u‖ ≤ 3 / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : |r| = 1 := by
    rcases H.source_sign with hr | hr <;> rw [hr] <;> norm_num
  have h0 : |y| * ‖star (u 0) * (1 - spectral x y)⁻¹ *
      ((Real.sqrt 2)⁻¹ : ℝ)‖ ≤ ‖u 0‖ / Real.sqrt 2 := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hs]
    have hR := mul_le_mul_of_nonneg_right (resolvent_norm 1 x y hy)
      (mul_nonneg (norm_nonneg (u 0)) (inv_nonneg.mpr hs.le))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hR
  have h1 : |y| * ‖star (u 1) * (2 - spectral x y)⁻¹ * (2 * r)‖ ≤
      2 * ‖u 1‖ := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, hr]
    norm_num
    have hR := mul_le_mul_of_nonneg_right (resolvent_norm 2 x y hy)
      (show 0 ≤ 2 * ‖u 1‖ by positivity)
    nlinarith
  have hc : ‖u 0‖ / Real.sqrt 2 + 2 * ‖u 1‖ ≤ 3 / Real.sqrt 2 := by
    apply (le_div_iff₀ hs).mpr
    have hsa : (Real.sqrt 2) ^ 2 * ‖u 0‖ ^ 2 = 2 * ‖u 0‖ ^ 2 :=
      congrArg (fun t : ℝ => t * ‖u 0‖ ^ 2) hs2
    have hsb : (Real.sqrt 2) ^ 2 * ‖u 1‖ ^ 2 = 2 * ‖u 1‖ ^ 2 :=
      congrArg (fun t : ℝ => t * ‖u 1‖ ^ 2) hs2
    have he : (‖u 0‖ / Real.sqrt 2 + 2 * ‖u 1‖) * Real.sqrt 2 =
        ‖u 0‖ + 2 * Real.sqrt 2 * ‖u 1‖ := by field_simp; ring
    rw [he]
    nlinarith [sq_nonneg (2 * Real.sqrt 2 * ‖u 0‖ - ‖u 1‖), H.unit,
      norm_nonneg (u 0), norm_nonneg (u 1)]
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (star (u 0) * (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ))
      (star (u 1) * (2 - spectral x y)⁻¹ * (2 * r))) (abs_nonneg y)
  dsimp [sourceReadout]
  linarith

/-- Quantitative nonvanishing for every original contact, both fixed source signs,
both signs of the imaginary parameter, and both actor axes. -/
theorem original_contact_nonvanishing (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) :
    sourceReadout r x y u ≠ 0 ∧
      Real.sqrt 2 * (1 + 3 * ‖u 1‖ ^ 2 - |h|) ≤ ‖η‖ ∧ 0 < ‖η‖ := by
  have hy : y ≠ 0 := by
    intro hz
    have hi := H.imaginary
    simp [hz] at hi
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl := numerator_lower h r x y u p q a η H hy
  have hu := readout_upper h r x y u p q a η H hy
  have hb := source_balance h r x y u p q a η H hy
  have hn : -y * (numerator h x y u).im ≤ |y| * ‖numerator h x y u‖ := by
    have ha := neg_le_abs (y * (numerator h x y u).im)
    rw [abs_mul] at ha
    nlinarith [mul_le_mul_of_nonneg_left
      (Complex.abs_im_le_norm (numerator h x y u)) (abs_nonneg y)]
  have hp : 0 < 3 + 9 * ‖u 1‖ ^ 2 - 3 * |h| := by
    nlinarith [H.small, sq_nonneg ‖u 1‖]
  have hd : sourceReadout r x y u ≠ 0 := by
    intro hz
    have hzN : numerator h x y u = 0 := by simpa [hz] using hb.symm
    simp [hzN] at hl
    linarith
  rw [← hb, norm_mul] at hn
  have huη := mul_le_mul_of_nonneg_left hu (norm_nonneg η)
  have hc : 3 + 9 * ‖u 1‖ ^ 2 - 3 * |h| ≤ (‖η‖ * 3) / Real.sqrt 2 := by
    nlinarith
  have he := (le_div_iff₀ hs).mp hc
  refine ⟨hd, ?_, ?_⟩
  · nlinarith
  · have hp' : 0 < Real.sqrt 2 * (1 + 3 * ‖u 1‖ ^ 2 - |h|) := by
      apply mul_pos hs
      nlinarith
    nlinarith

end D5.S3.Quantum.Algebra.PBSourceContactNonvanishing
