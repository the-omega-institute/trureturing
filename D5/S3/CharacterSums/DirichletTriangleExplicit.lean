/- GID: D5/S3/CharacterSums/DirichletTriangleExplicit
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletTriangleExplicit
   mirror-E: none(waiver:conditional-dirichlet-consumer)
   anchors: []
   utility: none
   digest: Centered zero kernels for the triangular Dirichlet explicit formula. -/

import D5.S3.CharacterSums.DirichletCompletion
import D5.S3.CharacterSums.DirichletTrianglePerron
import D5.S3.CharacterSums.DirichletTriangleExplicitGamma
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual completion divisor is counted once, with its analytic multiplicity. -/

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
    (fun z => (completion_power_growth hne z (.inr hχ)).le) ha hs

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
  rw [show -1 - ρ.1 = -(ρ.1 + 1) by ring]
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
  rw [show -1 - ρ.1 = -(ρ.1 + 1) by ring]
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
    rw [zeroKernel, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne')]
    rw [← Complex.ofReal_log (Real.exp_nonneg y), Real.log_exp]
    field_simp
    <;> ring
  exact (he.congr_fun ht).tsum_eq

private theorem zeroSeries_continuous {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Continuous (zeroSeries χ) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hc : ContinuousOn (zeroSeries χ) (Iic (y + 1)) := by
    apply continuousOn_tsum (fun ρ => (by fun_prop))
      ((coefficient_hasSum hχ hne).summable.norm.mul_right (Real.exp (max (y + 1) 0)))
    intro ρ t ht
    exact (zeroSeries_term_bound hχ t ρ).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (max_le_max_right 0 ht))
        (norm_nonneg _))
  exact hc.continuousAt (Iic_mem_nhds (by linarith))

private theorem zeroSeries_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (y : ℝ) :
    ‖zeroSeries χ y‖ ≤
      (∑' ρ : {z : ℂ // completion χ z = 0},
        ‖(analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))‖) *
          Real.exp (max y 0) :=
  tsum_of_norm_bounded
    (((coefficient_hasSum hχ hne).summable.norm.hasSum).mul_right _)
    (zeroSeries_term_bound hχ y)

private theorem zeroSeries_laplace_integrable {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * zeroSeries χ y) (Ioi 0) := by
  let M : ℝ := ∑' ρ : {z : ℂ // completion χ z = 0},
    ‖(analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))‖
  have hb := (integrableOn_exp_mul_Ioi (by linarith : 1 - s.re < 0) 0).const_mul M
  refine hb.mono' ((show Continuous (fun y : ℝ => Complex.exp (-s * y)) by
    fun_prop).mul (zeroSeries_continuous hχ hne)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  calc
    ‖Complex.exp (-s * y) * zeroSeries χ y‖ =
        Real.exp (-s.re * y) * ‖zeroSeries χ y‖ := by simp [norm_mul, Complex.norm_exp]
    _ ≤ Real.exp (-s.re * y) * (M * Real.exp y) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [max_eq_left (show 0 ≤ y from (show 0 < y from hy).le)]
          using zeroSeries_bound hχ hne y)
        (Real.exp_nonneg _)
    _ = M * Real.exp ((1 - s.re) * y) := by
      rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private theorem zeroSeries_laplace_hasSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      ((analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))) /
        (s - ρ.1))
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * zeroSeries χ y) := by
  have hc : Set.Countable (Set.univ : Set {z : ℂ // completion χ z = 0}) := by
    convert (coefficient_hasSum hχ hne).summable.countable_support using 1
    ext ρ
    simp only [Set.mem_univ, Function.mem_support, true_iff]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      ((completion_zero_order χ hne ρ.1).2.mp ρ.2)))
      (mul_ne_zero (zero_denominators hχ ρ).1 (zero_denominators hχ ρ).2.1)
  letI : Countable {z : ℂ // completion χ z = 0} := Set.countable_univ_iff.mp hc
  let c := fun ρ : {z : ℂ // completion χ z = 0} =>
    (analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))
  let f := fun (ρ : {z : ℂ // completion χ z = 0}) (y : ℝ) =>
    c ρ * Complex.exp ((ρ.1 - s) * y)
  let b := fun (ρ : {z : ℂ // completion χ z = 0}) (y : ℝ) =>
    ‖c ρ‖ * Real.exp ((1 - s.re) * y)
  have hf : ∀ ρ, AEStronglyMeasurable (f ρ) (volume.restrict (Ioi 0)) := by
    intro ρ
    exact (show Continuous (f ρ) by dsimp [f]; fun_prop).aestronglyMeasurable
  have hb : ∀ ρ, ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ‖f ρ y‖ ≤ b ρ y := by
    intro ρ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    dsimp only [f, b]
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hr := completion_zero_strip hχ ρ.2
    nlinarith [hr.2, (show 0 < y from hy)]
  have hbs : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), Summable (fun ρ => b ρ y) :=
    ae_of_all _ (fun y => (coefficient_hasSum hχ hne).summable.norm.mul_right _)
  have hbi : Integrable (fun y => ∑' ρ, b ρ y) (volume.restrict (Ioi 0)) := by
    simpa only [b, tsum_mul_right] using
      (integrableOn_exp_mul_Ioi (by linarith : 1 - s.re < 0) 0).const_mul
        (∑' ρ, ‖c ρ‖)
  have hlim : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0),
      HasSum (fun ρ => f ρ y) (Complex.exp (-s * y) * zeroSeries χ y) := by
    apply ae_of_all
    intro y
    convert ((zeroSeries_summable hχ hne y).hasSum.mul_left
      (Complex.exp (-s * y))) using 1
    funext ρ
    dsimp only [f, c]
    rw [show (ρ.1 - s) * (y : ℂ) = -s * y + y * ρ.1 by ring, Complex.exp_add]
    · ring
    · rfl
  have he := hasSum_integral_of_dominated_convergence b hf hb hbs hbi hlim
  convert he using 1
  funext ρ
  dsimp only [f, c]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by
    simp only [Complex.sub_re]
    linarith [(completion_zero_strip hχ ρ.2).2])]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show ρ.1 - s = -(s - ρ.1) by ring]
  have hsr : s - ρ.1 ≠ 0 := by
    intro h; have hr := congrArg Complex.re h; simp at hr
    linarith [(completion_zero_strip hχ ρ.2).2]
  field_simp
  <;> ring

private theorem zeroSeries_laplace {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * zeroSeries χ y) =
      (logDeriv (completion χ) s + s * logDeriv (completion χ) (-1) -
        (s + 1) * logDeriv (completion χ) 0) / (s * (s + 1)) := by
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hs1 : s + 1 ≠ 0 := by
    intro he; have hr := congrArg Complex.re he; simp at hr; linarith
  have he := ((difference hχ hne (endpoint_nonzero hχ hne).1
    (completion_ne_zero_of_one_le_re χ (.inl hne) hs.le)).add
      ((coefficient_hasSum hχ hne).mul_left s)).div_const (s * (s + 1))
  have ht (ρ : {z : ℂ // completion χ z = 0}) :
      ((analyticOrderNatAt (completion χ) ρ.1 : ℂ) *
          ((s - ρ.1)⁻¹ - (0 - ρ.1)⁻¹) +
        s * ((analyticOrderNatAt (completion χ) ρ.1 : ℂ) /
          (ρ.1 * (ρ.1 + 1)))) / (s * (s + 1)) =
      ((analyticOrderNatAt (completion χ) ρ.1 : ℂ) / (ρ.1 * (ρ.1 + 1))) /
        (s - ρ.1) := by
    obtain ⟨h0, h1, h2⟩ := zero_denominators hχ ρ
    have hsr : s - ρ.1 ≠ 0 := by
      intro h; have hr := congrArg Complex.re h; simp at hr
      linarith [(completion_zero_strip hχ ρ.2).2]
    field_simp
    <;> ring
  have hvalue := (he.congr_fun (fun ρ => (ht ρ).symm)).unique
    (zeroSeries_laplace_hasSum hχ hne hs)
  rw [← hvalue]
  congr 1
  ring

private theorem constant_integrable (v : ℂ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * v) (Ioi 0) :=
  (exp_integrable hs).mul_const v

private theorem constant_laplace (v : ℂ) {s : ℂ} (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * v) = v / s := by
  rw [integral_mul_const, exp_integral hs]
  ring

private theorem inverse_exp (v s : ℂ) (y : ℝ) :
    Complex.exp (-s * y) * (v / (Real.exp y : ℂ)) =
      Complex.exp (-(s + 1) * y) * v := by
  rw [Complex.ofReal_exp, div_eq_mul_inv, ← Complex.exp_neg]
  rw [← mul_assoc, mul_right_comm, ← Complex.exp_add]
  congr 2
  ring

private theorem inverse_integrable (v : ℂ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (v / (Real.exp y : ℂ))) (Ioi 0) := by
  simpa only [inverse_exp] using
    constant_integrable v (s := s + 1) (by simp only [Complex.add_re, Complex.one_re]; linarith)

private theorem inverse_laplace (v : ℂ) {s : ℂ} (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
      (v / (Real.exp y : ℂ))) = v / (s + 1) := by
  simp_rw [inverse_exp]
  exact constant_laplace v (by simp only [Complex.add_re, Complex.one_re]; linarith)

private theorem zeroTriangle_continuous {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Continuous (fun y : ℝ => zeroTriangle χ (Real.exp y)) := by
  have he : (fun y : ℝ => zeroTriangle χ (Real.exp y)) =
      (fun y : ℝ => zeroSeries χ y -
        (logDeriv (completion χ) 2 - logDeriv (completion χ) 0) +
        (logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) /
          (Real.exp y : ℂ)) := funext (zeroTriangle_exp hχ hne)
  rw [he]
  exact ((zeroSeries_continuous hχ hne).sub continuous_const).add
    (continuous_const.div (Complex.continuous_ofReal.comp Real.continuous_exp)
      (fun y => Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'))

private theorem zeroTriangle_laplace_integrable {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * zeroTriangle χ (Real.exp y))
      (Ioi 0) := by
  have he : (fun y : ℝ => Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) =
      (fun y : ℝ => Complex.exp (-s * y) * zeroSeries χ y -
        Complex.exp (-s * y) *
          (logDeriv (completion χ) 2 - logDeriv (completion χ) 0) +
        Complex.exp (-s * y) *
          ((logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) /
            (Real.exp y : ℂ))) := by
    funext y
    rw [zeroTriangle_exp hχ hne]
    ring
  rw [he]
  exact ((zeroSeries_laplace_integrable hχ hne hs).sub
    (constant_integrable _ (zero_lt_one.trans hs))).add
    (inverse_integrable _ (zero_lt_one.trans hs))

private theorem zeroTriangle_laplace {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) =
      (logDeriv (completion χ) s - logDeriv (completion χ) 2) / (s * (s + 1)) := by
  have he : (fun y : ℝ => Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) =
      (fun y : ℝ => Complex.exp (-s * y) * zeroSeries χ y -
        Complex.exp (-s * y) *
          (logDeriv (completion χ) 2 - logDeriv (completion χ) 0) +
        Complex.exp (-s * y) *
          ((logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) /
            (Real.exp y : ℂ))) := by
    funext y
    rw [zeroTriangle_exp hχ hne]
    ring
  rw [he, integral_add
    (f := fun y : ℝ => Complex.exp (-s * y) * zeroSeries χ y -
      Complex.exp (-s * y) *
        (logDeriv (completion χ) 2 - logDeriv (completion χ) 0))
    (g := fun y : ℝ => Complex.exp (-s * y) *
      ((logDeriv (completion χ) 2 - logDeriv (completion χ) (-1)) /
        (Real.exp y : ℂ)))
    ((zeroSeries_laplace_integrable hχ hne hs).sub
      (constant_integrable _ (zero_lt_one.trans hs)))
    (inverse_integrable _ (zero_lt_one.trans hs)),
    integral_sub
      (f := fun y : ℝ => Complex.exp (-s * y) * zeroSeries χ y)
      (g := fun y : ℝ => Complex.exp (-s * y) *
        (logDeriv (completion χ) 2 - logDeriv (completion χ) 0))
      (zeroSeries_laplace_integrable hχ hne hs)
      (constant_integrable _ (zero_lt_one.trans hs)),
    zeroSeries_laplace hχ hne hs,
    constant_laplace _ (zero_lt_one.trans hs), inverse_laplace _ (zero_lt_one.trans hs)]
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hs1 : s + 1 ≠ 0 := by
    intro he; have hr := congrArg Complex.re he; simp at hr; linarith
  field_simp
  <;> ring

open D5.S3.CharacterSums.DirichletTrianglePerron
open D5.S3.Weil.Mertens.IntegratedExplicit

private theorem from_laplace {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (f : ℝ → ℂ)
    (hi : ∀ t : ℝ, IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) * f y)
      (Ioi 0))
    (hc : ∀ y : ℝ, 0 < y → ContinuousAt f y)
    (hL : ∀ t : ℝ, t ≠ 0 →
      (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * f y) =
        -logDeriv χ.LFunction (transformLine t) /
          (transformLine t * (transformLine t + 1)))
    {y : ℝ} (hy : 0 < y) : f y = characterTriangle χ (Real.exp y) := by
  let g : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
    (fun v => Complex.exp (-(2 : ℂ) * v) * f v)
  have hgi : Integrable g := by
    change Integrable ((Ioi (0 : ℝ)).indicator
      (fun v : ℝ => Complex.exp (-(2 : ℂ) * v) * f v))
    rw [integrable_indicator_iff measurableSet_Ioi]
    simpa only [transformLine, zero_mul, mul_zero, Complex.ofReal_zero, zero_add,
      add_zero] using hi 0
  have hgc : ContinuousAt g y := by
    have he : g =ᶠ[𝓝 y] (fun v : ℝ => Complex.exp (-(2 : ℂ) * v) * f v) := by
      filter_upwards [Ioi_mem_nhds hy] with v hv
      exact Set.indicator_of_mem hv _
    exact ((by fun_prop : ContinuousAt (fun v : ℝ => Complex.exp (-(2 : ℂ) * v)) y).mul
      (hc y hy)).congr_of_eventuallyEq he
  have hgF (t : ℝ) : 𝓕 g t =
      ∫ v : ℝ in Ioi 0, Complex.exp (-transformLine t * v) * f v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have he : (fun v : ℝ => Complex.exp ((-2 * Real.pi * v * t : ℝ) * I) * g v) =
        (Ioi (0 : ℝ)).indicator
          (fun v => Complex.exp (-transformLine t * v) * f v) := by
      funext v
      by_cases hv : v ∈ Ioi (0 : ℝ)
      · simp only [g, Set.indicator_of_mem hv, ← mul_assoc, ← Complex.exp_add]
        congr 2
        dsimp only [transformLine]
        push_cast
        ring
      · simp only [g, Set.indicator_of_notMem hv, mul_zero]
    rw [he, integral_indicator measurableSet_Ioi]
  have hFa : 𝓕 g =ᵐ[volume]
      (fun t : ℝ => trianglePerronIntegrand χ 1 2 (2 * Real.pi * t)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    rw [hgF t, hL t ht]
    simp only [trianglePerronIntegrand, Complex.ofReal_one, one_cpow, mul_one,
      transformLine, Complex.ofReal_ofNat]
  have hp : 0 < 2 * Real.pi := by positivity
  have hFi : Integrable (𝓕 g) :=
    ((trianglePerronIntegrand_integrable χ (x := 1) (c := 2) (by norm_num)
      (by norm_num)).comp_mul_left' hp.ne').congr hFa.symm
  have hinv := hgi.fourierInv_fourier_eq hFi hgc
  rw [Real.fourierInv_eq'] at hinv
  simp only [Real.inner_apply, smul_eq_mul] at hinv
  have hphase (t : ℝ) :
      Complex.exp (((2 * Real.pi * (t * y) : ℝ) : ℂ) * I) *
        trianglePerronIntegrand χ 1 2 (2 * Real.pi * t) =
      Complex.exp (-(2 : ℂ) * y) *
        trianglePerronIntegrand χ (Real.exp y) 2 (2 * Real.pi * t) := by
    have he : Complex.exp (-(2 : ℂ) * y) *
        (Real.exp y : ℂ) ^ ((2 : ℂ) + (2 * Real.pi * t : ℝ) * I) =
        Complex.exp (((2 * Real.pi * (t * y) : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg y), Real.log_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [trianglePerronIntegrand]
    simp only [Complex.ofReal_one, one_cpow, mul_one, Complex.ofReal_ofNat]
    rw [← he]
    ring
  have heq : (∫ t : ℝ, Complex.exp (((2 * Real.pi * (t * y) : ℝ) : ℂ) * I) *
      𝓕 g t) = Complex.exp (-(2 : ℂ) * y) *
        (∫ t : ℝ, trianglePerronIntegrand χ (Real.exp y) 2 (2 * Real.pi * t)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hFa] with t ht
    rw [ht, hphase]
  rw [heq] at hinv
  have hchange : (∫ t : ℝ, trianglePerronIntegrand χ (Real.exp y) 2
      (2 * Real.pi * t)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, trianglePerronIntegrand χ (Real.exp y) 2 t) := by
    simpa only [abs_of_pos (inv_pos.mpr hp), Complex.real_smul, one_div] using
      Measure.integral_comp_mul_left (trianglePerronIntegrand χ (Real.exp y) 2)
        (2 * Real.pi)
  have hper : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, trianglePerronIntegrand χ (Real.exp y) 2 t) =
        characterTriangle χ (Real.exp y) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_inv, one_div] using
      (characterTriangle_perron χ (Real.exp_pos y).le (by norm_num : (1 : ℝ) < 2)).symm
  rw [hchange, hper] at hinv
  change Complex.exp (-(2 : ℂ) * y) * characterTriangle χ (Real.exp y) =
    g y at hinv
  rw [show g y = Complex.exp (-(2 : ℂ) * y) * f y from
    Set.indicator_of_mem hy _] at hinv
  exact (mul_left_cancel₀ (Complex.exp_ne_zero _) hinv).symm

private theorem zeroTriangle_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : zeroTriangle χ 1 = 0 := by
  have he : (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * zeroKernel ρ.1 1) =
        (fun _ => (0 : ℂ)) := by
    funext ρ
    obtain ⟨h0, h1, h2⟩ := zero_denominators hχ ρ
    simp only [zeroKernel, Complex.ofReal_one, one_cpow]
    field_simp
    <;> ring
  change (∑' ρ : {z : ℂ // completion χ z = 0},
    (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * zeroKernel ρ.1 1) = 0
  rw [he]
  exact tsum_zero

/-- The exact triangular explicit formula uses the centered actual zero divisor. -/
theorem characterTriangle_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    characterTriangle χ x = -zeroTriangle χ x -
      (1 - (x : ℂ)⁻¹) * logDeriv χ.LFunction 2 + parityCorrection χ x := by
  classical
  rcases eq_or_lt_of_le hx with rfl | hx
  · rw [zeroTriangle_one hχ, parityCorrection_one]
    simp [characterTriangle]
  let l : ℂ := logDeriv χ.LFunction 2
  let f : ℝ → ℂ := fun y => -zeroTriangle χ (Real.exp y) - l +
    l / (Real.exp y : ℂ) + parityCorrection χ (Real.exp y)
  have hi (t : ℝ) : IntegrableOn
      (fun y : ℝ => Complex.exp (-transformLine t * y) * f y) (Ioi 0) := by
    have he : (fun y : ℝ => Complex.exp (-transformLine t * y) * f y) =
        (fun y : ℝ => -(Complex.exp (-transformLine t * y) * zeroTriangle χ (Real.exp y)) -
          Complex.exp (-transformLine t * y) * l +
          Complex.exp (-transformLine t * y) * (l / (Real.exp y : ℂ)) +
          Complex.exp (-transformLine t * y) * parityCorrection χ (Real.exp y)) := by
      funext y
      dsimp only [f]
      ring
    rw [he]
    exact ((((zeroTriangle_laplace_integrable hχ hne (by simp :
      1 < (transformLine t).re)).neg).sub (constant_integrable l (by simp))).add
        (inverse_integrable l (by simp))).add
          (parityCorrection_laplace_integrable χ (by simp))
  have hc (y : ℝ) (hy : 0 < y) : ContinuousAt f y := by
    exact ((((zeroTriangle_continuous hχ hne).continuousAt.neg).sub
      continuousAt_const).add (continuousAt_const.div
        (Complex.continuous_ofReal.comp Real.continuous_exp).continuousAt
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'))).add
          ((parityCorrection_continuousOn χ).continuousAt (Ici_mem_nhds hy))
  have hL (t : ℝ) (ht : t ≠ 0) :
      (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * f y) =
        -logDeriv χ.LFunction (transformLine t) /
          (transformLine t * (transformLine t + 1)) := by
    let s := transformLine t
    have hs : 1 < s.re := by simp [s]
    have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
    have hs1 : s + 1 ≠ 0 := by
      intro he; have hh := congrArg Complex.re he; norm_num [s] at hh
    have he : (fun y : ℝ => Complex.exp (-s * y) * f y) =
        (fun y : ℝ => -(Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) -
          Complex.exp (-s * y) * l + Complex.exp (-s * y) * (l / (Real.exp y : ℂ)) +
          Complex.exp (-s * y) * parityCorrection χ (Real.exp y)) := by
      funext y
      dsimp only [f]
      ring
    change (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * f y) = _
    rw [he, integral_add
      (f := fun y : ℝ => -(Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) -
        Complex.exp (-s * y) * l + Complex.exp (-s * y) * (l / (Real.exp y : ℂ)))
      (g := fun y : ℝ => Complex.exp (-s * y) * parityCorrection χ (Real.exp y))
      ((((zeroTriangle_laplace_integrable hχ hne hs).neg).sub
        (constant_integrable l (zero_lt_one.trans hs))).add
          (inverse_integrable l (zero_lt_one.trans hs)))
      (parityCorrection_laplace_integrable χ (zero_lt_one.trans hs)),
      integral_add
        (f := fun y : ℝ => -(Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) -
          Complex.exp (-s * y) * l)
        (g := fun y : ℝ => Complex.exp (-s * y) * (l / (Real.exp y : ℂ)))
        (((zeroTriangle_laplace_integrable hχ hne hs).neg).sub
          (constant_integrable l (zero_lt_one.trans hs)))
        (inverse_integrable l (zero_lt_one.trans hs)),
      integral_sub
        (f := fun y : ℝ => -(Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)))
        (g := fun y : ℝ => Complex.exp (-s * y) * l)
        (zeroTriangle_laplace_integrable hχ hne hs).neg
        (constant_integrable l (zero_lt_one.trans hs)),
      show (∫ y : ℝ in Ioi 0, -(Complex.exp (-s * y) * zeroTriangle χ (Real.exp y))) =
        -(∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * zeroTriangle χ (Real.exp y)) by
          simp only [neg_mul, integral_neg],
      zeroTriangle_laplace hχ hne hs, constant_laplace l (zero_lt_one.trans hs),
      inverse_laplace l (zero_lt_one.trans hs), parityCorrection_laplace χ ht,
      completion_logDeriv χ (zero_lt_one.trans hs)
        (χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs.le) (.inr hne),
      completion_logDeriv χ (s := 2) (by norm_num)
        (χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by norm_num)) (.inr hne)]
    simp only [parity, l, s]
    dsimp only [s] at hs0 hs1
    have hd : transformLine t + transformLine t ^ 2 ≠ 0 := by
      rw [show transformLine t + transformLine t ^ 2 =
        transformLine t * (transformLine t + 1) by ring]
      exact mul_ne_zero hs0 hs1
    field_simp [hs0, hs1, hd]
    <;> ring
  have hv := from_laplace χ f hi hc hL (Real.log_pos hx)
  rw [Real.exp_log (by linarith : 0 < x)] at hv
  rw [← hv]
  dsimp only [f, l]
  rw [Real.exp_log (by linarith : 0 < x)]
  ring

end D5.S3.CharacterSums.DirichletTriangleExplicit
