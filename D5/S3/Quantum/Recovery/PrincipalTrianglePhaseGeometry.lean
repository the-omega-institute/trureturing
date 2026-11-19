/- GID: D5/S3/Quantum/Recovery/PrincipalTrianglePhaseGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalTrianglePhaseGeometry
   mirror-E: none(waiver:principal-triangle-phase-geometry)
   anchors: []
   utility: none
   digest: The three-fibre phase cube forces an explicit triangle phase gap under Gram and block contraction bounds. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Triangle and plaquette phases of three paired orthonormal fibres. -/

namespace D5.S3.Quantum.Recovery.PrincipalTrianglePhase

section

namespace RTPhaseCube

/-- If the phase lift on an eight-triangle cube has zero third difference and two
transverse plaquettes of size at least (4t), some phase has size at least (2t). -/
theorem transverse_phase_cube
    (t x000 x001 x010 x011 x100 x101 x110 x111 : ℝ)
    (cube : x000 - x001 - x010 + x011 - x100 + x101 + x110 - x111 = 0)
    (hij : 4 * t ≤ |x000 - x010 - x100 + x110|)
    (hik : 4 * t ≤ |x000 - x001 - x100 + x101|) :
    2 * t ≤ |x000| ∨ 2 * t ≤ |x001| ∨
    2 * t ≤ |x010| ∨ 2 * t ≤ |x011| ∨
    2 * t ≤ |x100| ∨ 2 * t ≤ |x101| ∨
    2 * t ≤ |x110| ∨ 2 * t ≤ |x111| := by
  by_contra! h
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  have b0 := abs_lt.mp h0
  have b1 := abs_lt.mp h1
  have b2 := abs_lt.mp h2
  have b3 := abs_lt.mp h3
  have b4 := abs_lt.mp h4
  have b5 := abs_lt.mp h5
  have b6 := abs_lt.mp h6
  have b7 := abs_lt.mp h7
  obtain ⟨b0l,b0u⟩ := b0
  obtain ⟨b1l,b1u⟩ := b1
  obtain ⟨b2l,b2u⟩ := b2
  obtain ⟨b3l,b3u⟩ := b3
  obtain ⟨b4l,b4u⟩ := b4
  obtain ⟨b5l,b5u⟩ := b5
  obtain ⟨b6l,b6u⟩ := b6
  obtain ⟨b7l,b7u⟩ := b7
  rw [le_abs] at hij hik
  rcases hij with hj | hj <;> rcases hik with hk | hk <;> linarith

end RTPhaseCube

end

section

namespace RTPhaseCube
open Real

/-- Below one period, a real number representing the zero circle phase is zero. -/
theorem eq_zero_of_circle_zero_short {x : ℝ} (hc : (x : Angle) = 0)
    (hx : |x| < 2 * π) : x = 0 := by
  obtain ⟨n, hn⟩ := Angle.coe_eq_zero_iff.mp hc
  rw [zsmul_eq_mul] at hn
  have hz : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hh : |(n : ℝ)| < 1 := by
    rw [← hn, abs_mul, abs_of_pos hz] at hx
    by_contra! hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hz.le]
  have nn : |n| < 1 := by exact_mod_cast hh
  have nz : n = 0 := by have hn2 := abs_lt.mp nn; omega
  simp [nz] at hn
  exact hn.symm

/-- The oriented triangle phases of three pairs obey the cube relation on the
circle, without a reality or branch hypothesis. -/
theorem triangle_cube_circle (a00 a01 a10 a11 b00 b01 b10 b11 c00 c01 c10 c11 : Angle) :
    let p000 := a00 + b00 - c00
    let p001 := a00 + b01 - c01
    let p010 := a01 + b10 - c00
    let p011 := a01 + b11 - c01
    let p100 := a10 + b00 - c10
    let p101 := a10 + b01 - c11
    let p110 := a11 + b10 - c10
    let p111 := a11 + b11 - c11
    p000 - p001 - p010 + p011 - p100 + p101 + p110 - p111 = 0 := by
  dsimp
  abel

/-- Eight short phase lifts satisfying the cube relation on the circle satisfy
it exactly on the real line. -/
theorem phase_cube_lift (x000 x001 x010 x011 x100 x101 x110 x111 : ℝ)
    (h0 : |x000| < π / 4) (h1 : |x001| < π / 4)
    (h2 : |x010| < π / 4) (h3 : |x011| < π / 4)
    (h4 : |x100| < π / 4) (h5 : |x101| < π / 4)
    (h6 : |x110| < π / 4) (h7 : |x111| < π / 4)
    (hc : (x000 : Angle) - x001 - x010 + x011 - x100 + x101 + x110 - x111 = 0) :
    x000 - x001 - x010 + x011 - x100 + x101 + x110 - x111 = 0 := by
  apply eq_zero_of_circle_zero_short
  · simpa only [Angle.coe_sub, Angle.coe_add] using hc
  · obtain ⟨h0l,h0u⟩ := abs_lt.mp h0
    obtain ⟨h1l,h1u⟩ := abs_lt.mp h1
    obtain ⟨h2l,h2u⟩ := abs_lt.mp h2
    obtain ⟨h3l,h3u⟩ := abs_lt.mp h3
    obtain ⟨h4l,h4u⟩ := abs_lt.mp h4
    obtain ⟨h5l,h5u⟩ := abs_lt.mp h5
    obtain ⟨h6l,h6u⟩ := abs_lt.mp h6
    obtain ⟨h7l,h7u⟩ := abs_lt.mp h7
    apply abs_lt.mpr
    constructor <;> linarith

/-- An angle block of given plaquette can be gauged to a checkerboard of
quarter-plaquette phases. The hypothesis lives on the circle, so this
does not assume a branch for the original four angles. -/
theorem checkerboard_gauge (u00 u01 u10 u11 : Angle) (d : ℝ)
    (h : u00 - u01 - u10 + u11 = (d : Angle)) :
    ∃ r0 r1 c0 c1 : Angle,
      u00 + r0 + c0 = (d / 4 : ℝ) ∧
      u01 + r0 + c1 = (- (d / 4) : ℝ) ∧
      u10 + r1 + c0 = (- (d / 4) : ℝ) ∧
      u11 + r1 + c1 = (d / 4 : ℝ) := by
  let v : Angle := ↑(d / 4 : ℝ)
  have hv : v + v + v + v = (d : Angle) := by
    dsimp [v]
    simp only [← Angle.coe_add]
    congr 1
    linarith
  refine ⟨0, -v - v + u00 - u10, v - u00, -v - u01, ?_, ?_, ?_, ?_⟩
  · change u00 + 0 + (v - u00) = v
    abel
  · rw [Angle.coe_neg]
    change u01 + 0 + (-v - u01) = -v
    abel
  · rw [Angle.coe_neg]
    change u10 + (-v - v + u00 - u10) + (v - u00) = -v
    abel
  · change u11 + (-v - v + u00 - u10) + (-v - u01) = v
    calc
      _ = (u00 - u01 - u10 + u11) - (v + v + v) := by abel
      _ = v := by rw [h, ← hv]; abel

end RTPhaseCube

end

section

namespace RTPhaseCube
open Real
set_option maxHeartbeats 1200000

/-- Numerical consequence of the all-ones contraction test after checkerboard
gauging. The four cross-overlap moduli are all at least a. -/
theorem plaquette_gap (a d u v w z : ℝ) (ha : 1 / 2 < a)
    (hd : |d| ≤ π) (hu : a ≤ u) (hv : a ≤ v) (hw : a ≤ w) (hz : a ≤ z)
    (test : (u + v + w + z) * cos (|d| / 4) ≤ 2) :
    4 * arccos (1 / (2 * a)) ≤ |d| := by
  have ha0 : 0 < a := by linarith
  have hd0 := abs_nonneg d
  have hc0 : 0 ≤ cos (|d| / 4) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hcap := (div_le_iff₀ (show (0 : ℝ) < 2 * a by positivity)).mpr (by linarith : (1 : ℝ) ≤ 1 * (2 * a))
  have hbot : -1 ≤ 1 / (2 * a) := by
    have hp : 0 ≤ (1 : ℝ) / (2 * a) := by positivity
    linarith
  have hcos := cos_arccos hbot hcap
  have hscale : 4 * a * cos (|d| / 4) ≤ 2 :=
    (mul_le_mul_of_nonneg_right (show 4 * a ≤ u + v + w + z by linarith) hc0).trans test
  by_contra! hh
  have hc : 1 / (2 * a) < cos (|d| / 4) := by
    rw [← hcos]
    have hleft : |d| / 4 ∈ Set.Icc (0 : ℝ) π := ⟨by positivity, by linarith [pi_pos]⟩
    have hright : arccos (1 / (2 * a)) ∈ Set.Icc (0 : ℝ) π :=
      ⟨arccos_nonneg _, arccos_le_pi _⟩
    exact strictAntiOn_cos hleft hright (by linarith)
  have hc' := (div_lt_iff₀ (show (0 : ℝ) < 2 * a by positivity)).mp hc
  nlinarith only [hscale, hc']

end RTPhaseCube

end

section

namespace RTPhaseCube
open Real
set_option maxHeartbeats 1200000

/-- A short sine combined with the negative-cosine exclusion fixes the
principal phase in the short positive-cosine interval. -/
theorem phase_short {θ u : ℝ} (hθ : 0 ≤ θ) (_hθ' : θ ≤ π / 4)
    (hu : |u| ≤ π) (hs : |sin u| < sin θ) (hc : -cos θ < cos u) :
    |u| < θ := by
  obtain ⟨hl, hh⟩ := abs_lt.mp hs
  have hsinSq : sin u ^ 2 < sin θ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < sin θ + sin u by linarith)]
  have hcSq : cos θ ^ 2 < cos u ^ 2 := by
    linarith [sin_sq_add_cos_sq u, sin_sq_add_cos_sq θ]
  have hc' : cos θ < cos u := by
    by_contra! hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ cos θ + cos u by linarith)]
  by_contra! hc''
  have h := cos_le_cos_of_nonneg_of_le_pi hθ hu hc''
  rw [cos_abs] at h
  exact (not_le_of_gt hc') h

noncomputable def baseAngle (a : ℝ) := arccos (1 / (2 * a))
noncomputable def cutoffAngle (a : ℝ) := min (2 * baseAngle a) (π / 4)

theorem cutoff_nonneg (a : ℝ) : 0 ≤ cutoffAngle a := by
  apply le_min
  · exact mul_nonneg (by norm_num) (arccos_nonneg _)
  · positivity

/-- Polynomial form of the cosine threshold needed by the normalized
3×3 Gram determinant. -/
theorem cutoff_cosine (a : ℝ) (ha : 1 / 2 < a) :
    0 ≤ cos (cutoffAngle a) ∧
    a * (1 - 2 * a ^ 2) ≤ 2 * a ^ 3 * cos (cutoffAngle a) := by
  have ha0 : 0 < a := by linarith
  have h0 : 0 ≤ cutoffAngle a := cutoff_nonneg a
  have ht : cutoffAngle a ≤ π / 4 := min_le_right _ _
  constructor
  · exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  · have hca : cutoffAngle a ≤ 2 * baseAngle a := min_le_left _ _
    have hl : baseAngle a < π / 2 :=
      arccos_lt_pi_div_two.mpr (div_pos one_pos (mul_pos (by norm_num) ha0))
    have hc := cos_le_cos_of_nonneg_of_le_pi h0 (show 2 * baseAngle a ≤ π by linarith) hca
    have hd : 0 < 2 * a := by positivity
    have hb : 1 / (2 * a) ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
    have hb' : -1 ≤ 1 / (2 * a) := by
      have h : 0 ≤ (1 : ℝ) / (2*a) := by positivity
      linarith
    have heq : 2 * a ^ 3 * cos (2 * baseAngle a) = a * (1 - 2 * a ^ 2) := by
      rw [cos_two_mul, baseAngle, cos_arccos hb' hb]
      field_simp [ne_of_gt ha0]
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hc (by positivity)

end RTPhaseCube

end

section

namespace RTPhaseBarrier

/-- A 3×3 normalized complex Gram determinant excludes a cross entry whose
real part opposite the fixed vertex, with the incident terms positive, is ≤-1/2. -/
theorem realPart_gt_neg_half
    {a x2 y z r : ℝ}
    (ha : 1/2 < a) (hx : a^2 ≤ x2) (hy : a ≤ y) (hz : a ≤ z)
    (hdet : 0 ≤ 1 - x2 - y^2 - z^2 + 2*y*z*r) :
    -(1/2:ℝ) < r := by
  by_contra! bad
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hau : 0 ≤ a := by linarith
  have hy2 : a^2 ≤ y^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y+a by positivity)]
  have hz2 : a^2 ≤ z^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ z+a by positivity)]
  have hyz : a^2 ≤ y*z := by
    simpa [pow_two] using mul_le_mul hy hz hau hy0
  have hneg := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hy0 hz0) (show 2*r+1 ≤ 0 by linarith)
  have hasa : (1/2:ℝ)^2 < a^2 := by
    nlinarith [mul_pos (show 0 < a-1/2 by linarith) (show 0 < a+1/2 by positivity)]
  nlinarith

/-- Compress a contraction to the real uniform test vector. The supplied scalar
inequality is exactly the sum of the four real parts bounded by two. -/
theorem localImagSq
    {a : ℝ} {r s y z : Fin 4 → ℝ}
    (ha : 1/2 < a)
    (hx : ∀ i, a^2 ≤ (r i)^2 + (s i)^2)
    (hy : ∀ i, a ≤ y i) (hz : ∀ i, a ≤ z i)
    (hdet : ∀ i, 0 ≤ 1 - ((r i)^2+(s i)^2) - (y i)^2 - (z i)^2 + 2*y i*z i*r i)
    (hu : r 0 + r 1 + r 2 + r 3 ≤ 2) :
    ∃ i, -(1/2:ℝ) < r i ∧ r i ≤ 1/2 ∧ a^2-1/4 ≤ (s i)^2 := by
  have hmin : ∃ i : Fin 4, r i ≤ 1/2 := by
    by_contra! h
    linarith [h 0, h 1, h 2, h 3]
  obtain ⟨i, hi⟩ := hmin
  have hn := realPart_gt_neg_half ha (hx i) (hy i) (hz i) (hdet i)
  refine ⟨i, hn, hi, ?_⟩
  nlinarith [hx i, mul_nonneg (show 0 ≤ r i+1/2 by linarith) (show 0 ≤ 1/2-r i by linarith)]

/-- The sine squared of the normalized phase, written without division by any
potentially zero entry. The claimed entry has modulus at least a > 1/2. -/
theorem phaseSq
    {a : ℝ} {r s y z : Fin 4 → ℝ}
    (ha : 1/2 < a)
    (hx : ∀ i, a^2 ≤ (r i)^2 + (s i)^2)
    (hy : ∀ i, a ≤ y i) (hz : ∀ i, a ≤ z i)
    (hdet : ∀ i, 0 ≤ 1 - ((r i)^2+(s i)^2) - (y i)^2 - (z i)^2 + 2*y i*z i*r i)
    (hu : r 0 + r 1 + r 2 + r 3 ≤ 2) :
    ∃ i, 1-1/(4*a^2) ≤ (s i)^2 / ((r i)^2 + (s i)^2) := by
  obtain ⟨i, hneg, hpos, _⟩ := localImagSq ha hx hy hz hdet hu
  have happ : 0 < 4*a^2 := by positivity
  have hden : 0 < (r i)^2 + (s i)^2 := lt_of_lt_of_le (by positivity) (hx i)
  have hr : (r i)^2 ≤ 1/4 := by
    nlinarith [mul_nonneg (show 0 ≤ r i+1/2 by linarith) (show 0 ≤ 1/2-r i by linarith)]
  have hh := mul_nonneg (le_of_lt happ) (sub_nonneg.mpr hr)
  have hratio : (r i)^2 / ((r i)^2+(s i)^2) ≤ 1/(4*a^2) := by
    apply (div_le_iff₀ hden).2
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ happ).2
    nlinarith [hx i]
  have hsum : (r i)^2 / ((r i)^2+(s i)^2) + (s i)^2 / ((r i)^2+(s i)^2) = 1 := by
    rw [← add_div, div_self (ne_of_gt hden)]
  exact ⟨i, by linarith⟩

/-- For the full cube argument, any cosine at most minus the claimed
positive threshold contradicts a single 3×3 determinant. The hypothesis
on q packages q ≥ cos(2 acos(1/(2a))) without division. -/
theorem no_negative_cosine
    {a x y z c q : ℝ}
    (ha : 1/2 < a) (ha1 : a ≤ 1)
    (hx : a ≤ x) (hy : a ≤ y) (hz : a ≤ z)
    (hdet : 0 ≤ 1-x^2-y^2-z^2+2*x*y*z*c)
    (hq0 : 0 ≤ q) (hq : a*(1-2*a^2) ≤ 2*a^3*q) :
    -q < c := by
  by_contra! hbad
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := ha0.trans hx
  have hy0 : 0 ≤ y := ha0.trans hy
  have hz0 : 0 ≤ z := ha0.trans hz
  have hx2 : a^2 ≤ x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x+a by positivity)]
  have hy2 : a^2 ≤ y^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y+a by positivity)]
  have hz2 : a^2 ≤ z^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ z+a by positivity)]
  have haprod : a^3 ≤ x*y*z := by
    simpa [pow_succ] using mul_le_mul (mul_le_mul hx hy ha0 hx0) hz ha0 (mul_nonneg hx0 hy0)
  have hterm : x*y*z*c ≤ -(a^3*q) := by
    calc
      x*y*z*c ≤ x*y*z*(-q) := mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = -(x*y*z*q) := by ring
      _ ≤ -(a^3*q) := neg_le_neg (mul_le_mul_of_nonneg_right haprod hq0)
  have hfac : 0 < (2*a-1)*(1+a-a^2) := by
    apply mul_pos (by linarith)
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  nlinarith

/-- Sharp scalar threshold: q can be cos(3 acos(1/(2a))) when
that cosine is nonnegative, by the triple-angle identity. -/
theorem not_cosine_lt_neg_triple_threshold
    {a x y z c q : ℝ}
    (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) (hz : a ≤ z)
    (hdet : 0 ≤ 1-x^2-y^2-z^2+2*x*y*z*c)
    (hq0 : 0 ≤ q) (hq : 1-3*a^2 ≤ 2*a^3*q) :
    -q ≤ c := by
  by_contra! hbad
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have hx2 : a^2 ≤ x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x+a by positivity)]
  have hy2 : a^2 ≤ y^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y+a by positivity)]
  have hz2 : a^2 ≤ z^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ z+a by positivity)]
  have haprod : a^3 ≤ x*y*z := by
    simpa [pow_succ] using mul_le_mul (mul_le_mul hx hy ha.le hx0.le) hz ha.le (mul_nonneg hx0.le hy0.le)
  have hterm : x*y*z*c < -(a^3*q) := by
    calc
      x*y*z*c < x*y*z*(-q) := mul_lt_mul_of_pos_left hbad (by positivity)
      _ = -(x*y*z*q) := by ring
      _ ≤ -(a^3*q) := neg_le_neg (mul_le_mul_of_nonneg_right haprod hq0)
  linarith



/-- Determinant of the phase-gauged triple anchored at the third vertex. -/
theorem gauged_det_re (u : ℂ) (y z : ℝ) :
    (Matrix.det !![(1 : ℂ), u, (y : ℂ);
                   star u, 1, (z : ℂ);
                   (y : ℂ), (z : ℂ), 1]).re =
       1-(u.re^2+u.im^2)-y^2-z^2+2*y*z*u.re := by
  rw [Matrix.det_fin_three]
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re]
  ring

/-- Uniform-vector contraction test, expressed as a bound on row sum norms. -/
theorem uniform_entry_real_sum
    (u₀₀ u₀₁ u₁₀ u₁₁ : ℂ)
    (htest : (u₀₀+u₀₁).re^2 + (u₀₀+u₀₁).im^2 +
             (u₁₀+u₁₁).re^2 + (u₁₀+u₁₁).im^2 ≤ 2) :
    u₀₀.re + u₀₁.re + u₁₀.re + u₁₁.re ≤ 2 := by
  simp only [Complex.add_re, Complex.add_im] at htest
  by_contra! hb
  nlinarith [sq_nonneg (u₀₀.im+u₀₁.im), sq_nonneg (u₁₀.im+u₁₁.im),
    sq_nonneg (u₀₀.re+u₀₁.re - (u₁₀.re+u₁₁.re)),
    mul_pos (show 0 < u₀₀.re+u₀₁.re+u₁₀.re+u₁₁.re - 2 by linarith)
      (show 0 < u₀₀.re+u₀₁.re+u₁₀.re+u₁₁.re + 2 by linarith)]

/-- Raw cyclic product is the only non-real datum in the determinant. -/
theorem cyclic_det_re (u v w : ℂ) :
    (Matrix.det !![(1 : ℂ), u, star w;
                   star u, 1, v;
                   w, star v, 1]).re =
       1-(u.re^2+u.im^2)-(v.re^2+v.im^2)-(w.re^2+w.im^2)+2*(u*v*w).re := by
  rw [Matrix.det_fin_three]
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re]
  ring

/-- Complex local theorem suitable for a phase-gauged 2×2 block.
`u` is lexicographically flattened; `y,z` are the real, positive
couplings of each row/column to the fixed third coordinate. -/
theorem local_gauged_complex_phase_sq
    {a : ℝ} (ha : 1/2 < a) (u : Fin 4 → ℂ) (y z : Fin 4 → ℝ)
    (hu : ∀ i, a^2 ≤ (u i).re^2 + (u i).im^2)
    (hy : ∀ i, a ≤ y i) (hz : ∀ i, a ≤ z i)
    (hp : ∀ i, 0 ≤
      (Matrix.det !![(1 : ℂ), u i, (y i : ℂ);
                     star (u i), 1, (z i : ℂ);
                     (y i : ℂ), (z i : ℂ), 1]).re)
    (htest : (u 0+u 1).re^2 + (u 0+u 1).im^2 +
             (u 2+u 3).re^2 + (u 2+u 3).im^2 ≤ 2) :
    ∃ i, 1-1/(4*a^2) ≤ (u i).im^2 / ((u i).re^2 + (u i).im^2) := by
  have h := uniform_entry_real_sum (u 0) (u 1) (u 2) (u 3) htest
  exact phaseSq (r := fun i => (u i).re) (s := fun i => (u i).im)
    ha hu hy hz (fun i => by simpa only [gauged_det_re] using hp i) h

/-- Construct the two row and two column corrections balancing a plaquette.
Applying any corrections used here is diagonal-unitary multiplication in
polar form. -/
theorem balance_plaquette (a b c d : ℝ) :
    let p := (a-b-c+d)/4
    ∃ r₀ r₁ s₀ s₁ : ℝ,
      a+r₀+s₀ = p ∧ b+r₀+s₁ = -p ∧
      c+r₁+s₀ = -p ∧ d+r₁+s₁ = p := by
  dsimp only
  let p := (a-b-c+d)/4
  refine ⟨0, a-c-2*p, p-a, -p-b, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [p] <;> ring

end RTPhaseBarrier

end

section

namespace RTPhaseCube
open Real
set_option maxHeartbeats 1200000

/-- Three-fibre phase obstruction, at the exact scalar interface. `det` is
triangle Gram PSD, `circle` is the phase cocycle, and the two contrast
hypotheses are the numerical output of the gauged block contractions. -/
theorem phase_obstruction
    (a : ℝ) (ha : 1 / 2 < a) (ha1 : a ≤ 1)
    (p x y z : Fin 8 → ℝ)
    (principal : ∀ i, |p i| ≤ π)
    (hx : ∀ i, a ≤ x i) (hy : ∀ i, a ≤ y i) (hz : ∀ i, a ≤ z i)
    (det : ∀ i, 0 ≤ 1 - (x i)^2 - (y i)^2 - (z i)^2 +
      2 * x i * y i * z i * cos (p i))
    (circle : (p 0 : Angle) - (p 1 : Angle) - (p 2 : Angle) + (p 3 : Angle) -
      (p 4 : Angle) + (p 5 : Angle) + (p 6 : Angle) - (p 7 : Angle) = 0)
    (face1 : |p 0 - p 2 - p 4 + p 6| ≤ π → 4 * baseAngle a ≤ |p 0 - p 2 - p 4 + p 6|)
    (face2 : |p 0 - p 1 - p 4 + p 5| ≤ π → 4 * baseAngle a ≤ |p 0 - p 1 - p 4 + p 5|) :
    ∃ i, sin (cutoffAngle a) ≤ |sin (p i)| := by
  by_contra! h
  have hcu : cutoffAngle a ≤ π / 4 := min_le_right _ _
  have hct : cutoffAngle a ≤ 2 * baseAngle a := min_le_left _ _
  obtain ⟨hq0, hq⟩ := cutoff_cosine a ha
  have all : ∀ i, |p i| < cutoffAngle a := fun i =>
    phase_short (cutoff_nonneg a) hcu (principal i) (h i)
      (RTPhaseBarrier.no_negative_cosine ha ha1 (hx i) (hy i) (hz i) (det i) hq0 hq)
  have b (i : Fin 8) := (all i).trans_le hcu
  have eq := phase_cube_lift (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)
    (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) circle
  have d1 : |p 0 - p 2 - p 4 + p 6| ≤ π := by
    obtain ⟨l0,u0⟩ := abs_lt.mp (b 0)
    obtain ⟨l2,u2⟩ := abs_lt.mp (b 2)
    obtain ⟨l4,u4⟩ := abs_lt.mp (b 4)
    obtain ⟨l6,u6⟩ := abs_lt.mp (b 6)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have d2 : |p 0 - p 1 - p 4 + p 5| ≤ π := by
    obtain ⟨l0,u0⟩ := abs_lt.mp (b 0)
    obtain ⟨l1,u1⟩ := abs_lt.mp (b 1)
    obtain ⟨l4,u4⟩ := abs_lt.mp (b 4)
    obtain ⟨l5,u5⟩ := abs_lt.mp (b 5)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases transverse_phase_cube (baseAngle a) (p 0) (p 1) (p 2) (p 3)
      (p 4) (p 5) (p 6) (p 7) eq (face1 d1) (face2 d2) with h0|h1|h2|h3|h4|h5|h6|h7
  · exact (not_le_of_gt ((all 0).trans_le hct)) h0
  · exact (not_le_of_gt ((all 1).trans_le hct)) h1
  · exact (not_le_of_gt ((all 2).trans_le hct)) h2
  · exact (not_le_of_gt ((all 3).trans_le hct)) h3
  · exact (not_le_of_gt ((all 4).trans_le hct)) h4
  · exact (not_le_of_gt ((all 5).trans_le hct)) h5
  · exact (not_le_of_gt ((all 6).trans_le hct)) h6
  · exact (not_le_of_gt ((all 7).trans_le hct)) h7

/-- Interface from the oriented edge phases and the actual uniform-vector
block tests. Modulus data in the tests may be kept separately from the
triangle determinant's magnitudes; the final Gram consumer identifies them. -/
theorem phase_obstruction_from_edge_tests
    (a : ℝ) (ha : 1 / 2 < a) (ha1 : a ≤ 1)
    (p x y z : Fin 8 → ℝ)
    (principal : ∀ i, |p i| ≤ π)
    (hx : ∀ i, a ≤ x i) (hy : ∀ i, a ≤ y i) (hz : ∀ i, a ≤ z i)
    (det : ∀ i, 0 ≤ 1 - (x i)^2 - (y i)^2 - (z i)^2 +
      2 * x i * y i * z i * cos (p i))
    (A B C : Fin 2 → Fin 2 → Angle)
    (p0 : (p 0 : Angle) = A 0 0 + B 0 0 - C 0 0)
    (p1 : (p 1 : Angle) = A 0 0 + B 0 1 - C 0 1)
    (p2 : (p 2 : Angle) = A 0 1 + B 1 0 - C 0 0)
    (p3 : (p 3 : Angle) = A 0 1 + B 1 1 - C 0 1)
    (p4 : (p 4 : Angle) = A 1 0 + B 0 0 - C 1 0)
    (p5 : (p 5 : Angle) = A 1 0 + B 0 1 - C 1 1)
    (p6 : (p 6 : Angle) = A 1 1 + B 1 0 - C 1 0)
    (p7 : (p 7 : Angle) = A 1 1 + B 1 1 - C 1 1)
    (f g : Fin 4 → ℝ) (hf : ∀ i, a ≤ f i) (hg : ∀ i, a ≤ g i)
    (test1 : (f 0 + f 1 + f 2 + f 3) * cos (|p 0 - p 2 - p 4 + p 6| / 4) ≤ 2)
    (test2 : (g 0 + g 1 + g 2 + g 3) * cos (|p 0 - p 1 - p 4 + p 5| / 4) ≤ 2) :
    ∃ i, sin (cutoffAngle a) ≤ |sin (p i)| := by
  apply phase_obstruction a ha ha1 p x y z principal hx hy hz det
  · rw [p0, p1, p2, p3, p4, p5, p6, p7]
    exact triangle_cube_circle (A 0 0) (A 0 1) (A 1 0) (A 1 1)
      (B 0 0) (B 0 1) (B 1 0) (B 1 1) (C 0 0) (C 0 1) (C 1 0) (C 1 1)
  · intro h
    exact plaquette_gap a _ _ _ _ _ ha h (hf 0) (hf 1) (hf 2) (hf 3) test1
  · intro h
    exact plaquette_gap a _ _ _ _ _ ha h (hg 0) (hg 1) (hg 2) (hg 3) test2

end RTPhaseCube

end

section

namespace RTPhaseCube
open Real Complex
set_option maxHeartbeats 1200000

def triangleProduct (u v w : ℂ) := u * v * star w

theorem triangleProduct_phase {u v w : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (arg (triangleProduct u v w) : Angle) = (arg u : Angle) + arg v - arg w := by
  unfold triangleProduct
  rw [Complex.star_def, arg_mul_coe_angle (mul_ne_zero hu hv) ((map_ne_zero (starRingEnd ℂ)).mpr hw),
    arg_mul_coe_angle hu hv, arg_conj_coe_angle, sub_eq_add_neg]

theorem complex_det_to_scalar (u v w : ℂ)
    (h : 0 ≤ (Matrix.det !![(1 : ℂ), u, w;
        star u, 1, v;
        star w, star v, 1]).re) :
    0 ≤ 1 - ‖u‖ ^ 2 - ‖v‖ ^ 2 - ‖w‖ ^ 2
      + 2 * ‖u‖ * ‖v‖ * ‖w‖ * Real.cos (arg (triangleProduct u v w)) := by
  have he := RTPhaseBarrier.cyclic_det_re u v (star w)
  rw [star_star] at he
  rw [he] at h
  have hn : ‖triangleProduct u v w‖ = ‖u‖ * ‖v‖ * ‖w‖ := by
    simp [triangleProduct]
  have hr := norm_mul_cos_arg (triangleProduct u v w)
  rw [hn] at hr
  rw [show 2 * ‖u‖ * ‖v‖ * ‖w‖ * Real.cos (arg (triangleProduct u v w)) =
      2 * (triangleProduct u v w).re by rw [← hr]; ring]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simpa only [triangleProduct, Complex.normSq_apply, pow_two,
    Complex.star_def, Complex.conj_re, Complex.conj_im, neg_mul_neg] using h

end RTPhaseCube

end

section

namespace RTPhaseBarrier

noncomputable def cis (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)

theorem cis_add (s t : ℝ) : cis (s+t) = cis s * cis t := by
  simp [cis, add_mul, Complex.exp_add]

theorem norm_cis (t : ℝ) : ‖cis t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

theorem cis_re (t : ℝ) : (cis t).re = Real.cos t := by
  simp [cis, Complex.exp_mul_I, Complex.mul_re, Complex.cos_ofReal_re]

theorem cis_congr_angle {s t : ℝ} (h : (s : Real.Angle) = t) :
    cis s = cis t := by
  have hcos := congrArg Real.Angle.cos h
  have hsin := congrArg Real.Angle.sin h
  rw [Real.Angle.cos_coe, Real.Angle.cos_coe] at hcos
  rw [Real.Angle.sin_coe, Real.Angle.sin_coe] at hsin
  simp [cis, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]

theorem re_abs_le_norm (u : ℂ) : |u.re| ≤ ‖u‖ := by
  exact Complex.abs_re_le_norm u

theorem real_sum_of_complex_contraction
    (u v w z : ℂ) (h : ‖u+v‖^2 + ‖w+z‖^2 ≤ 2) :
    u.re+v.re+w.re+z.re ≤ 2 := by
  have hav : (u+v).re ≤ ‖u+v‖ := le_trans (le_abs_self _) (re_abs_le_norm _)
  have hbv : (w+z).re ≤ ‖w+z‖ := le_trans (le_abs_self _) (re_abs_le_norm _)
  have hs : ‖u+v‖ + ‖w+z‖ ≤ 2 := by
    by_contra! bad
    nlinarith [sq_nonneg (‖u+v‖-‖w+z‖),
      mul_pos (show 0 < ‖u+v‖+‖w+z‖-2 by linarith) (show 0 < ‖u+v‖+‖w+z‖+2 by linarith)]
  simp only [Complex.add_re] at hav hbv
  linarith

/-- The modulus of the uniform-vector test after balancing a plaquette.
The phases are lifted reals only for the proof, and the hypothesis retains
a modulo-2π equality through `cis`. -/
theorem plaquette_cos_bound
    (u v w z : ℂ) (d : ℝ)
    (hcontract : ∀ x y : ℂ,
      ‖u*x+v*y‖^2 + ‖w*x+z*y‖^2 ≤ ‖x‖^2 + ‖y‖^2)
    (hphase : cis (u.arg-v.arg-w.arg+z.arg) = cis d) :
    (‖u‖+‖v‖+‖w‖+‖z‖)*Real.cos (d/4) ≤ 2 := by
  let p := d/4
  let r := u.arg-w.arg-2*p
  let s := p-u.arg
  let t := -p-v.arg
  have Hraw := hcontract (cis s) (cis t)
  rw [norm_cis, norm_cis] at Hraw
  have H : ‖cis 0 * (u*cis s+v*cis t)‖^2 + ‖cis r*(w*cis s+z*cis t)‖^2 ≤ 2 := by
    simpa [Complex.norm_mul, norm_cis, one_add_one_eq_two] using Hraw
  rw [mul_add, mul_add] at H
  have valid (q : ℂ) (a b : ℝ) :
      cis a * (q * cis b) = (‖q‖ : ℂ) * cis (a+q.arg+b) := by
    rw [cis_add, cis_add]
    have hq : (‖q‖ : ℂ) * cis q.arg = q := Complex.norm_mul_exp_arg_mul_I q
    calc
      cis a * (q * cis b) = (‖q‖ : ℂ) * (cis a * cis q.arg * cis b) := by
        conv_lhs => rw [← hq]
        ring
      _ = _ := rfl
  have h₁ : 0 + u.arg + s = p := by dsimp [s]; ring
  have h₂ : 0 + v.arg + t = -p := by dsimp [t]; ring
  have h₃ : r + w.arg + s = -p := by dsimp [r,s]; ring
  have h₄ : r+w.arg+s = -p := h₃
  have h₅ : r+z.arg+t = (u.arg-v.arg-w.arg+z.arg)-3*p := by dsimp [r,t]; ring
  rw [valid, valid, valid, valid, h₁, h₂, h₃, h₅, sub_eq_add_neg, cis_add, hphase, ← cis_add] at H
  have hd : d + -(3*p) = p := by dsimp [p]; ring
  rw [hd] at H
  have hsum := real_sum_of_complex_contraction _ _ _ _ H
  simp [Complex.mul_re, cis_re, Real.cos_neg] at hsum
  dsimp [p] at hsum
  linarith

theorem plaquette_abs_cos_bound
    (u v w z : ℂ) (d : ℝ)
    (hcontract : ∀ x y : ℂ,
      ‖u*x+v*y‖^2 + ‖w*x+z*y‖^2 ≤ ‖x‖^2 + ‖y‖^2)
    (hphase : (u.arg : Real.Angle) - v.arg - w.arg + z.arg = (d : Real.Angle)) :
    (‖u‖+‖v‖+‖w‖+‖z‖)*Real.cos (|d|/4) ≤ 2 := by
  have hc : Real.cos (|d|/4) = Real.cos (d/4) := by
    rcases le_or_gt 0 d with hn | hp
    · rw [abs_of_nonneg hn]
    · rw [abs_of_neg hp, neg_div, Real.cos_neg]
  rw [hc]
  apply plaquette_cos_bound u v w z d hcontract
  apply cis_congr_angle
  simpa only [Real.Angle.coe_add, Real.Angle.coe_sub] using hphase

end RTPhaseBarrier

end

section

namespace RTPhaseCube
open Real Complex
set_option maxHeartbeats 1600000

/-- Direct six-vector coordinate shell: three cross blocks, their actual
scalar-vector contraction tests, and their eight principal determinants. -/
theorem three_fibre_complex_phase
    (m : ℝ) (hm : 1 / 2 < m) (hm1 : m ≤ 1)
    (A B C : Fin 2 → Fin 2 → ℂ)
    (ha : ∀ i j, m ≤ ‖A i j‖) (hb : ∀ j k, m ≤ ‖B j k‖) (hc : ∀ i k, m ≤ ‖C i k‖)
    (testA : ∀ x y : ℂ,
      ‖A 0 0 * x + A 0 1 * y‖ ^ 2 + ‖A 1 0 * x + A 1 1 * y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2)
    (testC : ∀ x y : ℂ,
      ‖C 0 0 * x + C 0 1 * y‖ ^ 2 + ‖C 1 0 * x + C 1 1 * y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2)
    (psd : ∀ i j k, 0 ≤
      (Matrix.det !![(1 : ℂ), A i j, C i k;
        star (A i j), 1, B j k;
        star (C i k), star (B j k), 1]).re) :
    ∃ i j k, Real.sin (cutoffAngle m) ≤ |Real.sin (arg (triangleProduct (A i j) (B j k) (C i k)))| := by
  let ii : Fin 8 → Fin 2 := ![0,0,0,0,1,1,1,1]
  let jj : Fin 8 → Fin 2 := ![0,0,1,1,0,0,1,1]
  let kk : Fin 8 → Fin 2 := ![0,1,0,1,0,1,0,1]
  let p (s : Fin 8) := arg (triangleProduct (A (ii s) (jj s)) (B (jj s) (kk s)) (C (ii s) (kk s)))
  have pne {u : ℂ} (h : m ≤ ‖u‖) : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at h
    linarith
  have ph (s : Fin 8) : (p s : Angle) =
      (arg (A (ii s) (jj s)) : Angle) + arg (B (jj s) (kk s)) - arg (C (ii s) (kk s)) :=
    triangleProduct_phase (pne (ha _ _)) (pne (hb _ _)) (pne (hc _ _))
  have main := phase_obstruction m hm hm1 p
    (fun s => ‖A (ii s) (jj s)‖) (fun s => ‖B (jj s) (kk s)‖) (fun s => ‖C (ii s) (kk s)‖)
    (fun _ => abs_le.mpr ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩)
    (fun _ => ha _ _) (fun _ => hb _ _) (fun _ => hc _ _)
    (fun _ => complex_det_to_scalar _ _ _ (psd _ _ _))
  have p0 : (p 0 : Angle) = (arg (A 0 0) : Angle) + arg (B 0 0) - arg (C 0 0) := ph 0
  have p1 : (p 1 : Angle) = (arg (A 0 0) : Angle) + arg (B 0 1) - arg (C 0 1) := ph 1
  have p2 : (p 2 : Angle) = (arg (A 0 1) : Angle) + arg (B 1 0) - arg (C 0 0) := ph 2
  have p3 : (p 3 : Angle) = (arg (A 0 1) : Angle) + arg (B 1 1) - arg (C 0 1) := ph 3
  have p4 : (p 4 : Angle) = (arg (A 1 0) : Angle) + arg (B 0 0) - arg (C 1 0) := ph 4
  have p5 : (p 5 : Angle) = (arg (A 1 0) : Angle) + arg (B 0 1) - arg (C 1 1) := ph 5
  have p6 : (p 6 : Angle) = (arg (A 1 1) : Angle) + arg (B 1 0) - arg (C 1 0) := ph 6
  have p7 : (p 7 : Angle) = (arg (A 1 1) : Angle) + arg (B 1 1) - arg (C 1 1) := ph 7
  have circ :
      (p 0 : Angle) - (p 1 : Angle) - (p 2 : Angle) + (p 3 : Angle) -
      (p 4 : Angle) + (p 5 : Angle) + (p 6 : Angle) - (p 7 : Angle) = 0 := by
    rw [p0,p1,p2,p3,p4,p5,p6,p7]
    abel
  have f1 (hd : |p 0 - p 2 - p 4 + p 6| ≤ π) :
      4 * baseAngle m ≤ |p 0 - p 2 - p 4 + p 6| := by
    have hph : (arg (A 0 0) : Angle) - arg (A 0 1) - arg (A 1 0) + arg (A 1 1) =
        ((p 0 - p 2 - p 4 + p 6 : ℝ) : Angle) := by
      rw [Angle.coe_add,Angle.coe_sub,Angle.coe_sub,p0,p2,p4,p6]
      abel
    exact plaquette_gap m _ _ _ _ _ hm hd (ha _ _) (ha _ _) (ha _ _) (ha _ _)
      (RTPhaseBarrier.plaquette_abs_cos_bound _ _ _ _ _ testA hph)
  have f2 (hd : |p 0 - p 1 - p 4 + p 5| ≤ π) :
      4 * baseAngle m ≤ |p 0 - p 1 - p 4 + p 5| := by
    let d := p 0 - p 1 - p 4 + p 5
    have hph : (arg (C 0 0) : Angle) - arg (C 0 1) - arg (C 1 0) + arg (C 1 1) =
        ((-d : ℝ) : Angle) := by
      dsimp only [d]
      rw [Angle.coe_neg,Angle.coe_add,Angle.coe_sub,Angle.coe_sub,p0,p1,p4,p5]
      abel
    have H := RTPhaseBarrier.plaquette_abs_cos_bound _ _ _ _ _ testC hph
    rw [abs_neg] at H
    exact plaquette_gap m _ _ _ _ _ hm hd (hc _ _) (hc _ _) (hc _ _) (hc _ _) H
  obtain ⟨s, hs⟩ := main circ f1 f2
  exact ⟨ii s,jj s,kk s,hs⟩

end RTPhaseCube

end

end D5.S3.Quantum.Recovery.PrincipalTrianglePhase
