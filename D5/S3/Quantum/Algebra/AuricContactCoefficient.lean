/- GID: D5/S3/Quantum/Algebra/AuricContactCoefficient
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/AuricContactCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=algebraic-identity; basis=consumer=D5/S3/Quantum/Algebra/AuricContactCoefficient.lemma_46_3
   digest: Explicit coefficient identities at the cost-centre t=1/4 in the Auric contact model. -/

module

public import Mathlib

/-! The coefficient calculation in Lemma 46.3 is kept over `ℂ`, with the source
    coordinates `x` and `y` represented by the real and imaginary parts of
    `ell = x + y I`.  The helper definitions are consumed by the single
    theorem below, so the displayed identities remain the reusable source. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.AuricContactCoefficient

open Complex

def ell (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

def ellBar (x y : ℝ) : ℂ := (x : ℂ) - (y : ℂ) * I

def fOne (x y : ℝ) : ℂ :=
  6 * ((x - 1 : ℝ) : ℂ) * (1 - ell x y) *
    (((1 / x : ℝ) : ℂ) + I * ((1 / y : ℝ) : ℂ))

def fOneFactored (x y : ℝ) : ℂ :=
  -6 * I * ((x - 1 : ℝ) : ℂ) * ellBar x y * (ell x y - 1) /
    ((x * y : ℝ) : ℂ)

def chiZero (x y : ℝ) : ℂ := ((-3 * (x + 1) / (2 * y) : ℝ) : ℂ)

def kappaZero (x y : ℝ) : ℂ := ((-3 * (x + 1) / (2 * x) : ℝ) : ℂ)

def gZero (x y : ℝ) : ℂ :=
  I * (1 - ell x y / 2) * (chiZero x y - I * kappaZero x y)

def gZeroFactored (x y : ℝ) : ℂ :=
  3 * I * ((x + 1 : ℝ) : ℂ) * ellBar x y * (ell x y - 2) /
    (4 * ((x * y : ℝ) : ℂ))

def alphaCenter (x y : ℝ) : ℂ := ((3 * (x - 1) / y : ℝ) : ℂ)

def fCenter (x y : ℝ) : ℂ :=
  I * (1 - ell x y) * (alphaCenter x y + I * (-3)) - (2 - ell x y / 2)

def fCenterClosed (x y : ℝ) : ℂ :=
  (((x - 4) / 2 : ℝ) : ℂ) -
    I * (((5 * y ^ 2 + 6 * (x - 1) ^ 2) / (2 * y) : ℝ) : ℂ)

def chiCenter (x y : ℝ) : ℂ := ((-3 * (x + 1) / y : ℝ) : ℂ)

def gCenter (x y : ℝ) : ℂ :=
  I * (1 - ell x y / 2) * (chiCenter x y - I * (-3)) -
    (4 - 2 * ell x y) * ((1 / 4 : ℝ) : ℂ)

def gCenterClosed (x y : ℝ) : ℂ :=
  (ell x y - 2) * (2 + 3 * I * (((x + 1) / (2 * y) : ℝ) : ℂ))

def beta (t : ℝ) : ℝ := 3 * (1 + 4 * t)

def zeta (t : ℝ) : ℝ := 4 * t

def chi (x y t : ℝ) : ℂ := ((-(x + 1) * beta t / (2 * y) : ℝ) : ℂ)

def kappa (x y t : ℝ) : ℂ :=
  (((-3 + 12 * t - x * (3 + 12 * t)) / (2 * x) : ℝ) : ℂ)

def g (x y t : ℝ) : ℂ :=
  I * (1 - ell x y / 2) * (chi x y t - I * kappa x y t) -
    (4 - 2 * ell x y) * (t : ℂ)

def gClosed (x y t : ℝ) : ℂ :=
  -(2 - ell x y) / 4 *
    (((3 + 5 * zeta t - 3 * (zeta t - 1) / x : ℝ) : ℂ) +
      I * (((beta t * (x + 1) / y : ℝ) : ℂ)))

private lemma fOne_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    fOne x y = fOneFactored x y := by
  apply Complex.ext <;> simp [fOne, fOneFactored, ell, Complex.mul_re, Complex.mul_im,
    ellBar, Complex.div_re, Complex.div_im, hx, hy] <;> field_simp <;> ring

private lemma gZero_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    gZero x y = gZeroFactored x y := by
  apply Complex.ext <;> simp [gZero, gZeroFactored, chiZero, kappaZero, ell,
    ellBar, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, hx, hy] <;>
    field_simp <;> ring

private lemma fCenter_eq (x y : ℝ) (hy : y ≠ 0) :
    fCenter x y = fCenterClosed x y := by
  apply Complex.ext <;> simp [fCenter, fCenterClosed, alphaCenter, ell,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, hy,
    ← Complex.ofReal_pow] <;>
    field_simp <;> ring

private lemma gCenter_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    gCenter x y = gCenterClosed x y := by
  apply Complex.ext <;> simp [gCenter, gCenterClosed, chiCenter, ell,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, hx, hy] <;>
    field_simp <;> ring

private lemma g_eq (x y t : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    g x y t = gClosed x y t := by
  apply Complex.ext <;> simp [g, gClosed, chi, kappa, beta, zeta, ell,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, hx, hy] <;>
    field_simp <;> ring

private lemma fCenter_ne_zero {x y : ℝ} (hy : y ^ 2 > 1) :
    fCenter x y ≠ 0 := by
  have hy0 : y ≠ 0 := by nlinarith
  have hnum : 0 < 5 * y ^ 2 + 6 * (x - 1) ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  intro h
  have hi := congrArg im h
  rw [fCenter_eq x y hy0] at hi
  simp [fCenterClosed, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, ← Complex.ofReal_pow] at hi
  rcases hi with hnum0 | hyzero
  · exact (ne_of_gt hnum) hnum0
  · exact hy0 hyzero

private lemma ell_sub_two_ne_zero {x y : ℝ} (hy : y ^ 2 > 1) :
    ell x y - 2 ≠ 0 := by
  have hy0 : y ≠ 0 := by nlinarith
  intro h
  have hi := congrArg im h
  simp [ell] at hi
  exact hy0 hi

private lemma gCenter_closed_factor_ne_zero {x y : ℝ} (hy : y ^ 2 > 1) :
    2 + 3 * I * (((x + 1) / (2 * y) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg re h
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] at hr

theorem lemma_46_3 {x y t : ℝ} (hx : x ≠ 0) (hy : y ^ 2 > 1) :
    fOne x y = fOneFactored x y ∧
      gZero x y = gZeroFactored x y ∧
      fCenter x y = fCenterClosed x y ∧
      gCenter x y = gCenterClosed x y ∧
      fCenter x y ≠ 0 ∧
      gCenter x y ≠ 0 ∧
      g x y t = gClosed x y t := by
  have hy0 : y ≠ 0 := by nlinarith
  refine ⟨fOne_eq x y hx hy0, gZero_eq x y hx hy0, fCenter_eq x y hy0,
    gCenter_eq x y hx hy0, fCenter_ne_zero hy, ?_, g_eq x y t hx hy0⟩
  rw [gCenter_eq x y hx hy0, gCenterClosed]
  exact mul_ne_zero (ell_sub_two_ne_zero hy) (gCenter_closed_factor_ne_zero hy)

#print axioms lemma_46_3

end D5.S3.Quantum.Algebra.AuricContactCoefficient
