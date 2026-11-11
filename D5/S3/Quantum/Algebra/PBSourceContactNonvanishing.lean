/- GID: D5/S3/Quantum/Algebra/PBSourceContactNonvanishing
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBSourceContactNonvanishing
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Basic]
   utility: none
   digest: The original two-coordinate PB contact equations control both signed sources. -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! Quantitative nonvanishing on the original actual actor contact. -/

@[expose] public section

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
    norm_num [hz] at hi
  have he := congrArg Complex.im H.mixed
  rw [H.graph, graph_pairing, pairing_swap] at he
  simp [spectral, Complex.mul_im, H.first_real] at he
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [← neg_div]
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
  have hd0 : (1 : ℂ) - spectral x y ≠ 0 := denominator_ne 1 x y hy
  have hd1 : (2 : ℂ) - spectral x y ≠ 0 := denominator_ne 2 x y hy
  have hp0 : (1 - spectral x y) * p 0 =
      -Complex.I * ((2 - spectral x y / 2) * u 0 + h * u 1 +
        η * ((Real.sqrt 2)⁻¹ : ℝ)) := by
    linear_combination (norm := ring_nf) -Complex.I * h0
    simp [Complex.I_sq]
  have hp1 : (2 - spectral x y) * p 1 =
      -Complex.I * ((8 - 4 * spectral x y) * u 1 + 2 * h * u 0 + 2 * η * r) := by
    linear_combination (norm := ring_nf) -2 * Complex.I * h1
    simp [Complex.I_sq]
  constructor
  · apply mul_left_cancel₀ hd0
    rw [hp0]
    field_simp [hd0]
    ring
  · apply mul_left_cancel₀ hd1
    rw [hp1]
    field_simp [hd1]
    ring

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
  push_cast at he ⊢
  linear_combination (norm := ring_nf) -Complex.I * he
  simp [Complex.I_sq]
  ring

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

private theorem imaginary_lower (y : ℝ) (z : ℂ) : -(|y| * ‖z‖) ≤ y * z.im := by
  have ha := neg_abs_le (y * z.im)
  rw [abs_mul] at ha
  have hb := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (abs_nonneg y)
  linarith

private theorem cross_bound (h x y : ℝ) (u : Vec) (hy : y ≠ 0) :
    -(3 * |h| * (‖u 0‖ * ‖u 1‖)) ≤
      y * (h * (1 - spectral x y)⁻¹ * (star (u 0) * u 1) +
        2 * h * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)).im := by
  have hb (j : ℝ) (z : ℂ) :
      |y| * ‖(h : ℂ) * ((j : ℂ) - spectral x y)⁻¹ * z‖ ≤ |h| * ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = (|y| * ‖((j : ℂ) - spectral x y)⁻¹‖) * (|h| * ‖z‖) := by ring
      _ ≤ 1 * (|h| * ‖z‖) := mul_le_mul_of_nonneg_right
        (resolvent_norm j x y hy) (mul_nonneg (abs_nonneg h) (norm_nonneg z))
      _ = _ := one_mul _
  let z0 := (h : ℂ) * (1 - spectral x y)⁻¹ * (star (u 0) * u 1)
  let z1 := (h : ℂ) * (2 - spectral x y)⁻¹ * (star (u 1) * u 0)
  have h0 : |y| * ‖z0‖ ≤ |h| * (‖u 0‖ * ‖u 1‖) := by
    simpa only [z0, norm_mul, norm_star, Complex.ofReal_one] using hb 1 (star (u 0) * u 1)
  have h1 : |y| * ‖z1‖ ≤ |h| * (‖u 1‖ * ‖u 0‖) := by
    simpa only [z1, norm_mul, norm_star, Complex.ofReal_ofNat] using hb 2 (star (u 1) * u 0)
  have hi0 := imaginary_lower y z0
  have hi1 := imaginary_lower y z1
  have he : (h : ℂ) * (1 - spectral x y)⁻¹ * (star (u 0) * u 1) +
      2 * h * (2 - spectral x y)⁻¹ * (star (u 1) * u 0) = z0 + 2 * z1 := by
    dsimp [z0, z1]
    ring
  rw [he]
  have him : (z0 + 2 * z1).im = z0.im + 2 * z1.im := by
    simp [Complex.mul_im]
  rw [him]
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
    norm_num [numerator, residual, Complex.mul_im, ← Complex.ofReal_pow]
    field_simp [hy]
    ring
  rw [hn]
  have hr' : 0 ≤ y * ((1 - spectral x y)⁻¹).im := by
    simpa only [Complex.ofReal_one] using hr
  have hz' := mul_le_mul_of_nonneg_left hz (show 0 ≤ 6 * |h| by positivity)
  unfold beta
  nlinarith [sq_nonneg ‖u 0‖, H.unit, abs_nonneg h,
    mul_nonneg (sq_nonneg ‖u 0‖) hr']

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
    simpa [norm_inv, mul_comm, mul_left_comm, mul_assoc] using hR
  have hc : ‖u 0‖ / Real.sqrt 2 + 2 * ‖u 1‖ ≤ 3 / Real.sqrt 2 := by
    apply (le_div_iff₀ hs).mpr
    have hsa : (Real.sqrt 2) ^ 2 * ‖u 0‖ ^ 2 = 2 * ‖u 0‖ ^ 2 :=
      congrArg (fun t : ℝ => t * ‖u 0‖ ^ 2) hs2
    have hsb : (Real.sqrt 2) ^ 2 * ‖u 1‖ ^ 2 = 2 * ‖u 1‖ ^ 2 :=
      congrArg (fun t : ℝ => t * ‖u 1‖ ^ 2) hs2
    have he : (‖u 0‖ / Real.sqrt 2 + 2 * ‖u 1‖) * Real.sqrt 2 =
        ‖u 0‖ + 2 * Real.sqrt 2 * ‖u 1‖ := by field_simp
    rw [he]
    nlinarith [sq_nonneg (2 * Real.sqrt 2 * ‖u 0‖ - ‖u 1‖), H.unit,
      norm_nonneg (u 0), norm_nonneg (u 1)]
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (star (u 0) * (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ))
      (star (u 1) * (2 - spectral x y)⁻¹ * (2 * r))) (abs_nonneg y)
  rw [mul_add] at ht
  exact ht.trans ((add_le_add h0 h1).trans hc)

/-- Quantitative nonvanishing for every original contact, both fixed source signs,
both signs of the imaginary parameter, and both actor axes. -/
theorem original_contact_nonvanishing (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) :
    sourceReadout r x y u ≠ 0 ∧
      Real.sqrt 2 * (1 + 3 * ‖u 1‖ ^ 2 - |h|) ≤ ‖η‖ ∧ 0 < ‖η‖ := by
  have hy : y ≠ 0 := by
    intro hz
    have hi := H.imaginary
    norm_num [hz] at hi
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
  have heN : ‖numerator h x y u‖ = ‖η‖ * ‖sourceReadout r x y u‖ := by
    rw [← hb, norm_mul]
  rw [heN] at hn
  have huη := mul_le_mul_of_nonneg_left hu (norm_nonneg η)
  have hc : 3 + 9 * ‖u 1‖ ^ 2 - 3 * |h| ≤ (‖η‖ * 3) / Real.sqrt 2 := by
    calc
      _ ≤ -y * (numerator h x y u).im := hl
      _ ≤ |y| * (‖η‖ * ‖sourceReadout r x y u‖) := hn
      _ = ‖η‖ * (|y| * ‖sourceReadout r x y u‖) := by ring
      _ ≤ ‖η‖ * (3 / Real.sqrt 2) := huη
      _ = _ := by ring
  have he := (le_div_iff₀ hs).mp hc
  refine ⟨hd, ?_, ?_⟩
  · nlinarith
  · have hp' : 0 < Real.sqrt 2 * (1 + 3 * ‖u 1‖ ^ 2 - |h|) := by
      apply mul_pos hs
      nlinarith
    nlinarith

def pFormula (h x y : ℝ) (r : ℝ) (u : Vec) (η : ℂ) : Vec := ![
  -Complex.I * ((1 / 2 : ℂ) * u 0 +
    (1 - spectral x y)⁻¹ * ((3 / 2 : ℂ) * u 0 + h * u 1) +
    η * (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ)),
  -Complex.I * (4 * u 1 +
    (2 - spectral x y)⁻¹ * (2 * h * u 0) +
    η * (2 - spectral x y)⁻¹ * (2 * r))]

def qFormula (h x y : ℝ) (u p : Vec) : Vec := graphColumn h x y u p

def aFormula (x y : ℝ) (p : Vec) : Vec := actorColumn x y p

def reducedMass (h y : ℝ) (u p : Vec) : Prop :=
  pairing u p = (-(beta h u / y) : ℝ)

def reducedReal (h x y : ℝ) (u p : Vec) : Prop :=
  2 * (pairing u (cMap p)).re + (x + 3) * beta h u / y +
      h * (star (u 0) * u 1).im = 0

def reducedImag (h x y : ℝ) (u p : Vec) : Prop :=
  (spectral x y * pairing u (cMap p)).im +
      (3 * ‖u 0‖ ^ 2 + 24 * ‖u 1‖ ^ 2 +
        4 * h * (star (u 0) * u 1).re) = 0

private theorem cMap_graph_pairing (h x y : ℝ) (u p : Vec) :
    pairing (cMap u) (graphColumn h x y u p) =
      spectral x y * pairing u (cMap p) + 2 * pairing u p +
        Complex.I * ((3 * ‖u 0‖ ^ 2 + 24 * ‖u 1‖ ^ 2 +
          4 * h * (star (u 0) * u 1).re : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [pairing, graphColumn, cMap, Complex.sq_norm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem pFormula_eq_source_columns (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) (hy : y ≠ 0) :
    p = pFormula h x y r u η := by
  obtain ⟨h0, h1⟩ := source_columns h r x y u p q a η H hy
  funext j
  fin_cases j
  · simpa [pFormula] using h0
  · simpa [pFormula] using h1

private theorem source_of_pFormula (h r x y : ℝ) (u : Vec) (η : ℂ)
    (hy : y ≠ 0) :
    ∀ j, (aFormula x y (pFormula h x y r u η)) j - hMap h u j +
      spectral x y / 2 * cMap (cMap u) j = η * sourceVector r j := by
  intro j
  fin_cases j
  · have hp : (1 - spectral x y) * pFormula h x y r u η 0 =
        -Complex.I * ((2 - spectral x y / 2) * u 0 + h * u 1 +
          η * ((Real.sqrt 2)⁻¹ : ℝ)) := by
      change (1 - spectral x y) * (-Complex.I *
        ((1 / 2 : ℂ) * u 0 + (1 - spectral x y)⁻¹ *
          ((3 / 2 : ℂ) * u 0 + h * u 1) + η *
          (1 - spectral x y)⁻¹ * ((Real.sqrt 2)⁻¹ : ℝ))) = _
      have hi : (1 - spectral x y) * (1 - spectral x y)⁻¹ = (1 : ℂ) :=
        mul_inv_cancel₀ (denominator_ne 1 x y hy)
      calc
        _ = -Complex.I * ((1 - spectral x y) * ((1 / 2 : ℂ) * u 0) +
            ((1 - spectral x y) * (1 - spectral x y)⁻¹) *
              ((3 / 2 : ℂ) * u 0 + h * u 1) +
            η * ((1 - spectral x y) * (1 - spectral x y)⁻¹) *
              ((Real.sqrt 2)⁻¹ : ℝ)) := by ring
        _ = _ := by rw [hi]; ring
    simp [aFormula, actorColumn, hMap, cMap, sourceVector, Complex.I_sq]
    linear_combination (norm := ring_nf) Complex.I * hp
    rw [Complex.I_sq]
    push_cast
    ring
  · have hp : (2 - spectral x y) * pFormula h x y r u η 1 =
        -Complex.I * ((8 - 4 * spectral x y) * u 1 +
          2 * h * u 0 + 2 * η * r) := by
      change (2 - spectral x y) * (-Complex.I *
        (4 * u 1 + (2 - spectral x y)⁻¹ * (2 * h * u 0) +
          η * (2 - spectral x y)⁻¹ * (2 * r))) = _
      have hi : (2 - spectral x y) * (2 - spectral x y)⁻¹ = (1 : ℂ) :=
        mul_inv_cancel₀ (denominator_ne 2 x y hy)
      calc
        _ = -Complex.I * ((2 - spectral x y) * (4 * u 1) +
            ((2 - spectral x y) * (2 - spectral x y)⁻¹) *
              (2 * h * u 0) + η * ((2 - spectral x y) *
              (2 - spectral x y)⁻¹) * (2 * r)) := by ring
        _ = _ := by rw [hi]; ring
    simp [aFormula, actorColumn, hMap, cMap, sourceVector, Complex.I_sq]
    linear_combination (norm := ring_nf) (Complex.I / 2) * hp
    rw [Complex.I_sq]
    ring

theorem contact_iff_reduced (h r x y : ℝ) (u : Vec) (η : ℂ)
    (hr : r = 1 ∨ r = -1) (hh : |h| < 1) (hy : 1 < |y|)
    (hu : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1) :
    Contact h r x y u (pFormula h x y r u η)
      (qFormula h x y u (pFormula h x y r u η))
      (aFormula x y (pFormula h x y r u η)) η ↔
      reducedMass h y u (pFormula h x y r u η) ∧
      reducedReal h x y u (pFormula h x y r u η) ∧
      reducedImag h x y u (pFormula h x y r u η) ∧
      η * sourceReadout r x y u = numerator h x y u := by
  constructor
  · intro H
    have hmass := mass h r x y u (pFormula h x y r u η)
      (qFormula h x y u (pFormula h x y r u η))
      (aFormula x y (pFormula h x y r u η)) η H
    have hbal := source_balance h r x y u (pFormula h x y r u η)
      (qFormula h x y u (pFormula h x y r u η))
      (aFormula x y (pFormula h x y r u η)) η H
      (by
        intro hz
        have hi := H.imaginary
        rw [hz] at hi
        norm_num at hi)
    have hm := congrArg Complex.re H.mixed
    rw [H.graph, graph_pairing, pairing_swap u (pFormula h x y r u η)] at hm
    have hs := H.second_real
    rw [H.graph, cMap_graph_pairing] at hs
    refine ⟨hmass, ?_, ?_, hbal⟩
    · simp [spectral, Complex.mul_re, Complex.mul_im, hmass] at hm
      have hswap :
          (pairing (pFormula h x y r u η) (cMap u)).re =
            (pairing u (cMap (pFormula h x y r u η))).re := by
        rw [pairing_swap]
        simp
      simp [reducedReal, Complex.mul_im]
      linear_combination (norm := ring_nf) -hm
    · simp [reducedImag, Complex.mul_re, Complex.mul_im, H.first_real] at hs
      push_cast at hs
      norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hs
      simpa [reducedImag, pow_two, Complex.mul_re, Complex.mul_im, H.first_real] using hs
  · rintro ⟨hmass, hreal, himag, hbal⟩
    change pairing u (pFormula h x y r u η) = ↑(-(beta h u / y)) at hmass
    refine {
      source_sign := hr
      small := hh
      imaginary := hy
      unit := hu
      first_real := ?_
      second_real := ?_
      mixed := ?_
      graph := rfl
      actor := rfl
      source := source_of_pFormula h r x y u η (by
        intro hz
        have hi := hy
        rw [hz] at hi
        norm_num at hi) }
    · have hi := congrArg Complex.im hmass
      simpa using hi
    · change (pairing (cMap u)
        (graphColumn h x y u (pFormula h x y r u η))).im = 0
      rw [cMap_graph_pairing]
      have hi : (spectral x y *
          pairing u (cMap (pFormula h x y r u η))).im +
          (3 * ‖u 0‖ ^ 2 + 24 * ‖u 1‖ ^ 2 +
            4 * h * (star (u 0) * u 1).re) = 0 := by
        simpa [reducedImag] using himag
      have hpim : (pairing u (pFormula h x y r u η)).im = 0 := by
        have hi' := congrArg Complex.im hmass
        simpa using hi'
      norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hi
      simpa [pow_two, Complex.mul_re, Complex.mul_im, hpim] using hi
    · change pairing u (graphColumn h x y u (pFormula h x y r u η)) =
        pairing (pFormula h x y r u η) (cMap u)
      rw [graph_pairing, pairing_swap u (pFormula h x y r u η)]
      have hmass' : pairing u (pFormula h x y r u η) =
          (-(beta h u / y) : ℂ) := by exact_mod_cast hmass
      have hswap :
          (pairing (pFormula h x y r u η) (cMap u)).re =
            (pairing u (cMap (pFormula h x y r u η))).re := by
        rw [pairing_swap]
        simp
      rw [hmass']
      apply Complex.ext
      · simp [spectral, Complex.mul_re, Complex.mul_im]
        simp [reducedReal, Complex.mul_im] at hreal
        linear_combination (norm := ring_nf) -hreal
      · have hy0 : y ≠ 0 := by
          intro hz
          norm_num [hz] at hy
        simp [spectral, Complex.mul_re, Complex.mul_im, mul_div_cancel₀ _ hy0]
        ring

theorem contact_reduction (h r x y : ℝ) (u p q a : Vec) (η : ℂ)
    (H : Contact h r x y u p q a η) :
    p = pFormula h x y r u η ∧
      sourceReadout r x y u ≠ 0 ∧
      reducedMass h y u (pFormula h x y r u η) ∧
      reducedReal h x y u (pFormula h x y r u η) ∧
      reducedImag h x y u (pFormula h x y r u η) ∧
      η * sourceReadout r x y u = numerator h x y u := by
  have hy : y ≠ 0 := by
    intro hz
    have hi := H.imaginary
    rw [hz] at hi
    norm_num at hi
  have hp := pFormula_eq_source_columns h r x y u p q a η H hy
  have hq : q = qFormula h x y u (pFormula h x y r u η) := by
    simpa [qFormula, hp] using H.graph
  have ha : a = aFormula x y (pFormula h x y r u η) := by
    simpa [aFormula, hp] using H.actor
  have H' : Contact h r x y u (pFormula h x y r u η)
      (qFormula h x y u (pFormula h x y r u η))
      (aFormula x y (pFormula h x y r u η)) η := by
    simpa [hp, hq, ha] using H
  have hr := H.source_sign
  have hh := H.small
  have hy' := H.imaginary
  have hu := H.unit
  have hred := (contact_iff_reduced h r x y u η hr hh hy' hu).mp H'
  have hD := (original_contact_nonvanishing h r x y u p q a η H).1
  exact ⟨hp, hD, hred.1, hred.2.1, hred.2.2.1, hred.2.2.2⟩

end D5.S3.Quantum.Algebra.PBSourceContactNonvanishing
