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
  have hy : y ≠ 0 := by intro hz; simp [hz] at H
  have he := congrArg Complex.im H.mixed
  rw [H.graph, graph_pairing, pairing_swap] at he
  simp [spectral, Complex.mul_im, H.first_real] at he
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    apply (eq_neg_iff_add_eq_zero).mpr
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
  simp only [actorColumn, hMap, cMap, sourceVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] at h0 h1
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
    field_simp
    ring
  rw [hn]
  dsimp [beta]
  nlinarith [sq_nonneg ‖u 0‖, H.unit, abs_nonneg h,
    mul_nonneg (sq_nonneg ‖u 0‖) hr]

end D5.S3.Quantum.Algebra.PBSourceContactNonvanishing
