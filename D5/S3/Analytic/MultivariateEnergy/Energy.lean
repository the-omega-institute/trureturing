/- GID: D5/S3/Analytic/MultivariateEnergy/Energy
   generality: G
   mirror-B: D5/B/S3/Analytic/MultivariateEnergy/Energy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Bilinear, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.Algebra.Order.Star.Real]
   utility: none
   digest: Cubic spherical energies and the positive averaged matrix Gram kernel. -/

import D5.S3.Analytic.MultivariateEnergy.Moments
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! Moment reduction for the three-input centered matrix family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace D5.S3.Analytic.MultivariateEnergy.Energy
open Defs Moments
attribute [local fun_prop] Moments.continuous_A

private lemma integral_linear_A {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (f : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ℝ) :
    (∫ x, f (A x) ∂μ) = f (Q μ) :=
  f.toContinuousLinearMap.integral_comp_comm (integrable_A μ)

private lemma integral_L_right {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (B : Matrix (Fin d) (Fin d) ℝ) :
    (∫ x, trace (B * A x) ∂μ) = trace (B * Q μ) :=
  integral_linear_A μ ((traceLinearMap (Fin d) ℝ ℝ).comp (mulLeftLinearMap (Fin d) ℝ B))

private lemma integral_L_left {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (B : Matrix (Fin d) (Fin d) ℝ) :
    (∫ x, trace (A x * B) ∂μ) = trace (Q μ * B) :=
  integral_linear_A μ ((traceLinearMap (Fin d) ℝ ℝ).comp (mulRightLinearMap (Fin d) ℝ B))

private lemma integral_T_middle {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (B C : Matrix (Fin d) (Fin d) ℝ) :
    (∫ x, trace (B * A x * C) ∂μ) = trace (B * Q μ * C) :=
  integral_linear_A μ ((traceLinearMap (Fin d) ℝ ℝ).comp
    ((mulRightLinearMap (Fin d) ℝ C).comp (mulLeftLinearMap (Fin d) ℝ B)))

private lemma integral_cons {d n : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (f : (Fin (n + 1) → S d) → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂Measure.pi (fun _ => μ)) =
      ∫ x, ∫ y : Fin n → S d, f (Fin.cons x y) ∂Measure.pi (fun _ => μ) ∂μ := by
  calc
    _ = ∫ w : S d × (Fin n → S d), f (Fin.cons w.1 w.2)
        ∂μ.prod (Measure.pi (fun _ => μ)) := by
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    _ = _ := integral_prod _
      ((hf.comp (by fun_prop)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

private lemma integral_three {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (f : (Fin 3 → S d) → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂Measure.pi (fun _ => μ)) =
      ∫ x, ∫ y, ∫ z, f ![x, y, z] ∂μ ∂μ ∂μ := by
  rw [integral_cons μ f hf]
  congr 1
  funext x
  rw [integral_cons μ (fun y : Fin 2 → S d => f (Fin.cons x y)) (hf.comp (by fun_prop))]
  congr 1
  funext y
  rw [integral_cons μ (fun z : Fin 1 → S d => f (Fin.cons x (Fin.cons y z)))
    (hf.comp (by fun_prop))]
  congr 1
  funext z
  rw [Measure.pi_of_empty]
  simp only [integral_dirac]
  congr 1

private lemma integral_expr {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ]
    (β : ℝ) (f g h t : S d → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (ht : Continuous t) :
    (∫ x, β / 3 * (f x + g x + h x) - t x ∂μ) =
      β / 3 * ((∫ x, f x ∂μ) + (∫ x, g x ∂μ) + (∫ x, h x ∂μ)) - ∫ x, t x ∂μ := by
  have hi {f : S d → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (f := fun x => β / 3 * (f x + g x + h x))
    (g := t) ((hi ((hf.add hg).add hh)).const_mul _) (hi ht),
    integral_const_mul,
    integral_add (f := fun x => f x + g x) (g := h) (hi (hf.add hg)) (hi hh),
    integral_add (f := f) (g := g) (hi hf) (hi hg)]

/-- For three inputs, all probability-measure energy depends only on the centered matrix moment. -/
theorem energy_family_eq (d : ℕ) (β : ℝ) (μ : Measure (S d)) [IsProbabilityMeasure μ] :
    energy (familyKernel d β) μ = β * trace (Q μ * Q μ) - trace (Q μ * Q μ * Q μ) := by
  have hc : Continuous (familyKernel d β) := by
    unfold familyKernel
    unfold L T
    fun_prop
  rw [energy, integral_three μ _ hc]
  have hz (x y : S d) :
      (∫ z, familyKernel d β ![x,y,z] ∂μ) =
      β / 3 * (L x y + trace (A x * Q μ) + trace (A y * Q μ)) -
        trace (A x * A y * Q μ) := by
    simp only [familyKernel]
    change (∫ z, β / 3 * (L x y + L x z + L y z) - T x y z ∂μ) = _
    rw [integral_expr μ β (fun _ => L x y) (fun z => L x z) (fun z => L y z)
      (fun z => T x y z) continuous_const (by unfold L; fun_prop)
      (by unfold L; fun_prop) (by unfold T; fun_prop)]
    simp only [integral_const, probReal_univ, one_smul, L, T, integral_L_right]
  simp_rw [hz]
  have hy (x : S d) :
      (∫ y, β / 3 * (L x y + trace (A x * Q μ) + trace (A y * Q μ)) -
        trace (A x * A y * Q μ) ∂μ) =
      β / 3 * (trace (A x * Q μ) + trace (A x * Q μ) + trace (Q μ * Q μ)) -
        trace (A x * Q μ * Q μ) := by
    rw [integral_expr]
    · simp only [L, integral_L_right, integral_L_left, integral_T_middle,
        integral_const, probReal_univ, one_smul]
    all_goals try unfold L
    all_goals fun_prop (disch := exact continuous_A d)
  simp_rw [hy]
  rw [integral_expr]
  · simp only [Matrix.mul_assoc, integral_L_left, integral_const, probReal_univ, one_smul]
    ring
  all_goals fun_prop (disch := exact continuous_A d)

/-- Averaging one input leaves exactly a positive multiple of the matrix feature pairing. -/
theorem avgKernel_family_eq (d : ℕ) [NeZero d] (β : ℝ) (x y : S d) :
    avgKernel (familyKernel d β) x y = β / 3 * L x y := by
  have he : (fun z : Fin 1 → S d =>
      familyKernel d β (Fin.append (m := 1) (n := 2) z ![x,y])) =
      fun z => β / 3 * (L (z 0) x + L (z 0) y + L x y) - T (z 0) x y := by
    funext z
    simp [familyKernel, Fin.append, Fin.addCases]
  unfold avgKernel
  rw [he]
  rw [integral_comp_eval (μ := fun _ : Fin 1 => sigma d) (i := 0)
    (f := fun z : S d => β / 3 * (L z x + L z y + L x y) - T z x y)
    (by apply Continuous.aestronglyMeasurable; unfold L T; fun_prop)]
  rw [integral_expr (sigma d) β (fun z => L z x) (fun z => L z y)
    (fun _ => L x y) (fun z => T z x y) (by unfold L; fun_prop)
    (by unfold L; fun_prop) continuous_const (by unfold T; fun_prop)]
  simp only [L, T, Matrix.mul_assoc, integral_L_left, integral_const,
    probReal_univ, one_smul, Q, integral_A_eq_zero, Matrix.zero_mul, trace_zero,
    zero_add, sub_zero]

private lemma Q_symmetric {d : ℕ} (μ : Measure (S d)) [IsFiniteMeasure μ] :
    (Q μ).IsSymm := by
  ext i j
  unfold Q
  simp only [transpose_apply]
  rw [eval_integral (fun k => (integrable_A μ).eval k),
    eval_integral (fun k => ((integrable_A μ).eval j).eval k),
    eval_integral (fun k => (integrable_A μ).eval k),
    eval_integral (fun k => ((integrable_A μ).eval i).eval k)]
  congr 1
  funext x
  simp [A, mul_comm, eq_comm]

/-- The averaged kernel is positive on differences of arbitrary finite measures. -/
theorem isCondPosDef_family (d : ℕ) [NeZero d] (β : ℝ) (hβ : 0 ≤ β) :
    IsCondPosDef (avgKernel (familyKernel d β)) := by
  intro μ₁ μ₂ hμ₁ hμ₂ _
  letI := hμ₁
  letI := hμ₂
  simp_rw [avgKernel_family_eq, integral_const_mul, L, integral_L_right, integral_L_left]
  have hs : (Q μ₁ - Q μ₂).IsHermitian := by
    rw [isHermitian_iff_isSymm]
    exact (Q_symmetric μ₁).sub (Q_symmetric μ₂)
  have hp := (posSemidef_conjTranspose_mul_self (Q μ₁ - Q μ₂)).trace_nonneg
  rw [hs.eq] at hp
  have he : trace ((Q μ₁ - Q μ₂) * (Q μ₁ - Q μ₂)) =
      trace (Q μ₁ * Q μ₁) - 2 * trace (Q μ₁ * Q μ₂) + trace (Q μ₂ * Q μ₂) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, trace_sub]
    rw [trace_mul_comm (Q μ₂) (Q μ₁)]
    ring
  rw [he] at hp
  nlinarith [mul_nonneg (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 3)) hp]

end D5.S3.Analytic.MultivariateEnergy.Energy
