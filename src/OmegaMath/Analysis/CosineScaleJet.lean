import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! Omega original.

Quantitative separation by a complex cosine and its first dilation derivative. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Omega.CosineScaleJet

/-- The even cosine coordinate. -/
def value (z : ℂ) : ℂ := 2 * Complex.cos z

/-- The first derivative with respect to the dilation parameter at one. -/
def scaleJet (z : ℂ) : ℂ := deriv (fun t : ℂ => value (t * z)) 1

theorem scaleJet_eq (z : ℂ) :
    scaleJet z = -2 * z * Complex.sin z := by
  have h := (((Complex.hasDerivAt_cos (1 * z)).comp 1
    ((hasDerivAt_id (1 : ℂ)).mul_const z)).const_mul 2).deriv
  change deriv (fun t : ℂ => 2 * Complex.cos (t * z)) 1 = _
  rw [h]
  simp only [one_mul]
  ring

private theorem value_im (z : ℂ) :
    (value z).im = -2 * Real.sin z.re * Real.sinh z.im := by
  unfold value
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem scaleJet_im (z : ℂ) :
    (scaleJet z).im = -2 * (z.re * Real.cos z.re * Real.sinh z.im +
      z.im * Real.sin z.re * Real.cosh z.im) := by
  rw [scaleJet_eq, Complex.sin_eq]
  simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- A quantitative lower bound for the joint imaginary-coordinate energy.
The bound retains both the real-axis and imaginary-axis degeneracies. -/
theorem separation (z : ℂ) :
    4 * z.re ^ 2 * z.im ^ 2 ≤
      (z.re ^ 2 + 1 + Real.cosh z.im ^ 2) *
        ((value z).im ^ 2 + (scaleJet z).im ^ 2) := by
  by_cases hy : z.im = 0
  · simp only [hy, zero_pow (by decide : 2 ≠ 0), mul_zero, Real.cosh_zero]
    positivity
  let x := z.re
  let y := z.im
  let s := Real.sinh y
  let A := (value z).im
  let B := (scaleJet z).im
  let r := y * Real.cosh y / s
  have hsne : s ≠ 0 := Real.sinh_ne_zero.mpr hy
  have hab : |y| ≤ |s| := by
    rw [show |s| = Real.sinh |y| from Real.abs_sinh y]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg y)
  have hs : y ^ 2 ≤ s ^ 2 := by
    nlinarith [sq_abs y, sq_abs s, abs_nonneg y, abs_nonneg s]
  have hrabs : |r| ≤ Real.cosh y := by
    calc
      |r| = (|y| / |s|) * Real.cosh y := by
        dsimp [r]
        rw [abs_div, abs_mul, abs_of_pos (Real.cosh_pos y)]
        ring
      _ ≤ 1 * Real.cosh y :=
        mul_le_mul_of_nonneg_right
          ((div_le_one (abs_pos.mpr hsne)).mpr hab) (Real.cosh_pos y).le
      _ = Real.cosh y := one_mul _
  have hr : r ^ 2 ≤ Real.cosh y ^ 2 := by
    nlinarith [sq_abs r, Real.cosh_pos y, abs_nonneg r]
  have hA : A = -2 * Real.sin x * s := value_im z
  have hB : B = -2 * (x * Real.cos x * s + y * Real.sin x * Real.cosh y) :=
    scaleJet_im z
  have hres : B - r * A = -2 * x * Real.cos x * s := by
    rw [hA, hB]
    dsimp [r]
    field_simp [hsne] <;> ring
  have hid : x ^ 2 * A ^ 2 + (B - r * A) ^ 2 = 4 * x ^ 2 * s ^ 2 := by
    rw [hres, hA]
    calc
      _ = 4 * x ^ 2 * s ^ 2 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
  have htri : (B - r * A) ^ 2 ≤ (1 + r ^ 2) * (A ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (A + r * B)]
  change 4 * x ^ 2 * y ^ 2 ≤
    (x ^ 2 + 1 + Real.cosh y ^ 2) * (A ^ 2 + B ^ 2)
  calc
    4 * x ^ 2 * y ^ 2 ≤ 4 * x ^ 2 * s ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = x ^ 2 * A ^ 2 + (B - r * A) ^ 2 := hid.symm
    _ ≤ x ^ 2 * A ^ 2 + (1 + r ^ 2) * (A ^ 2 + B ^ 2) :=
      add_le_add_left htri _
    _ ≤ x ^ 2 * A ^ 2 + (1 + Real.cosh y ^ 2) * (A ^ 2 + B ^ 2) := by
      gcongr <;> exact hr
    _ ≤ (x ^ 2 + 1 + Real.cosh y ^ 2) * (A ^ 2 + B ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg B)]

/-- The value and first scale jet are simultaneously real exactly on the two axes. -/
theorem real_iff_axes (z : ℂ) :
    ((value z).im = 0 ∧ (scaleJet z).im = 0) ↔ z.re = 0 ∨ z.im = 0 := by
  constructor
  · rintro ⟨hA, hB⟩
    have h := separation z
    rw [hA, hB] at h
    have hz : (z.re * z.im) ^ 2 = 0 := by nlinarith [sq_nonneg (z.re * z.im)]
    exact mul_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    rw [value_im, scaleJet_im]
    rcases h with h | h <;> simp [h]

end Omega.CosineScaleJet
