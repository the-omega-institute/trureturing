/- GID: D5/S3/CharacterSums/DirichletTriangleExplicit
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletTriangleExplicit
   mirror-E: none(waiver:conditional-dirichlet-consumer)
   anchors: []
   utility: none
   digest: Centered zero kernels for the triangular Dirichlet explicit formula. -/

import D5.S3.CharacterSums.DirichletCompletion
import D5.S3.CharacterSums.DirichletTrianglePerron
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology BigOperators FourierTransform
open D5.S3.CharacterSums.DirichletCompletion
open D5.S3.Analytic.Resolvent.EntireLogDerivDifference

namespace D5.S3.CharacterSums.DirichletTriangleExplicit

/-- The three absolutely convergent pieces are kept together at every zero. -/
def zeroKernel (ρ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) +
    3 / ((x : ℂ) * (ρ + 1) * (2 - ρ))

/-- Each distinct zero is weighted by its actual analytic multiplicity. -/
def zeroTriangle {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑' ρ : {z : ℂ // completion χ z = 0},
    (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * zeroKernel ρ.1 x

private theorem endpoint_nonzero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    completion χ 0 ≠ 0 ∧ completion χ (-1) ≠ 0 ∧ completion χ 2 ≠ 0 := by
  exact ⟨completion_ne_zero_of_re_le_zero hχ (by norm_num),
    completion_ne_zero_of_re_le_zero hχ (by norm_num),
    completion_ne_zero_of_one_le_re χ (.inl hne) (by norm_num)⟩

private theorem difference {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {a s : ℂ}
    (ha : completion χ a ≠ 0) (hs : completion χ s ≠ 0) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) *
        ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹))
      (logDeriv (completion χ) s - logDeriv (completion χ) a) :=
  entire_logDeriv_difference_hasSum (differentiable_completion χ hne)
    (by norm_num : (3 / 2 : ℝ) < 2)
    (fun z => (completion_power_growth hχ hne z).le) ha hs

private theorem zero_denominators {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (ρ : {z : ℂ // completion χ z = 0}) :
    ρ.1 ≠ 0 ∧ ρ.1 + 1 ≠ 0 ∧ 2 - ρ.1 ≠ 0 := by
  have hr := completion_zero_strip hχ ρ.2
  constructor
  · intro h; rw [h] at hr; norm_num at hr
  constructor
  · intro h; have he := congrArg Complex.re h; simp at he; linarith [hr.1]
  · intro h; have he := congrArg Complex.re h; simp at he; linarith [hr.2]

private theorem coefficient_hasSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1)))
      (logDeriv (completion χ) (-1) - logDeriv (completion χ) 0) := by
  have he := difference hχ hne (endpoint_nonzero hχ hne).1
    (endpoint_nonzero hχ hne).2.1
  convert he using 1
  funext ρ
  obtain ⟨h0, h1, h2⟩ := zero_denominators hχ ρ
  field_simp
  <;> ring

private theorem constant_hasSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * (2 / (ρ.1 * (2 - ρ.1))))
      (logDeriv (completion χ) 2 - logDeriv (completion χ) 0) := by
  have he := difference hχ hne (endpoint_nonzero hχ hne).1
    (endpoint_nonzero hχ hne).2.2
  convert he using 1
  funext ρ
  obtain ⟨h0, h1, h2⟩ := zero_denominators hχ ρ
  field_simp
  <;> ring

private theorem inverse_hasSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * (3 / ((ρ.1 + 1) * (2 - ρ.1))))
      (logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) := by
  have he := difference hχ hne (endpoint_nonzero hχ hne).2.1
    (endpoint_nonzero hχ hne).2.2
  convert he using 1
  funext ρ
  obtain ⟨h0, h1, h2⟩ := zero_denominators hχ ρ
  field_simp
  <;> ring

private def zeroSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  ∑' ρ : {z : ℂ // completion χ z = 0},
    (analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1)) *
      Complex.exp ((y : ℂ) * ρ.1)

private theorem zeroSeries_term_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (y : ℝ) (ρ : {z : ℂ // completion χ z = 0}) :
    ‖(analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1)) *
      Complex.exp ((y : ℂ) * ρ.1)‖ ≤
        ‖(analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))‖ *
          Real.exp (max y 0) := by
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hr := completion_zero_strip hχ ρ.2
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_left hy]; nlinarith [hr.2]
  · rw [max_eq_right hy.le]; nlinarith [hr.1]

private theorem zeroSeries_summable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (y : ℝ) :
    Summable (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1)) *
        Complex.exp ((y : ℂ) * ρ.1)) :=
  Summable.of_norm_bounded
    ((coefficient_hasSum hχ hne).summable.norm.mul_right (Real.exp (max y 0)))
    (zeroSeries_term_bound hχ y)

private theorem zeroTriangle_exp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (y : ℝ) :
    zeroTriangle χ (Real.exp y) = zeroSeries χ y -
      (logDeriv (completion χ) 2 - logDeriv (completion χ) 0) +
      (logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) /
        (Real.exp y : ℂ) := by
  have h0 := constant_hasSum hχ hne
  have h1 := (inverse_hasSum hχ hne).div_const (Real.exp y : ℂ)
  have he := ((zeroSeries_summable hχ hne y).hasSum.sub h0).add h1
  have ht (ρ : {z : ℂ // completion χ z = 0}) :
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * zeroKernel ρ.1 (Real.exp y) =
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1)) *
          Complex.exp ((y : ℂ) * ρ.1) -
        (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * (2 / (ρ.1 * (2 - ρ.1))) +
        ((analyticOrderNatAt (completion χ) ρ.1 : ℂ) *
          (3 / ((ρ.1 + 1) * (2 - ρ.1)))) / (Real.exp y : ℂ) := by
    rw [zeroKernel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne')]
    rw [← Complex.ofReal_log (Real.exp_nonneg y), Real.log_exp]
    ring
  exact (he.congr (fun ρ => (ht ρ).symm)).tsum_eq

end D5.S3.CharacterSums.DirichletTriangleExplicit
