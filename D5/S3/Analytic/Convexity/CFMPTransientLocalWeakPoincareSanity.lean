import D5.S3.Analytic.Convexity.CFMPTransientLocalWeakPoincare
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Transient source-only sanity consumers. None has been run. -/

set_option autoImplicit false

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology NNReal

namespace LocalWeakPoincareSanity

/-- In one real dimension every actual linear derivative is symmetric. -/
theorem real_clm_symmetric (A : ℝ →L[ℝ] ℝ) (u v : ℝ) :
    inner ℝ (A u) v = inner ℝ u (A v) := by
  have hu : A u = u * A 1 := by simpa only [smul_eq_mul, mul_one] using A.map_smul u 1
  have hv : A v = v * A 1 := by simpa only [smul_eq_mul, mul_one] using A.map_smul v 1
  rw [Real.inner_apply, Real.inner_apply, hu, hv]
  ring

/-- The conclusion applies at the kink itself, despite failure of a pointwise
derivative hypothesis there. Rademacher supplies actual a.e. derivatives. -/
theorem norm_field_at_zero :
    ∃ r : ℝ, 0 < r ∧ ball (0 : ℝ) r ⊆ (univ : Set ℝ) ∧
      ∃ Q : ℝ → ℝ, Q 0 = 0 ∧
        ∀ z ∈ ball (0 : ℝ) r, HasFDerivAt Q (innerSL ℝ ‖z‖) z := by
  have hL : LipschitzWith 1 (fun x : ℝ ↦ ‖x‖) := lipschitzWith_one_norm
  apply LocalWeakPoincare.exists_local_normalized_primitive isOpen_univ
    hL.lipschitzOnWith ?_ 0 (mem_univ _)
  rw [Measure.restrict_univ]
  filter_upwards [hL.ae_differentiableAt (μ := volume)] with x hx
  exact ⟨fderiv ℝ (fun y : ℝ ↦ ‖y‖) x, hx.hasFDerivAt, real_clm_symmetric _⟩

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ ‖x‖) 0 :=
  not_differentiableAt_norm_zero ℝ

/-- A nonzero constant field, zero Lipschitz constant, and a disconnected source set. -/
theorem zero_lipschitz_disconnected :
    ∃ r : ℝ, 0 < r ∧ ball (-2 : ℝ) r ⊆ (ball (-2) 1 ∪ ball 2 1) ∧
      ∃ Q : ℝ → ℝ, Q (-2) = 0 ∧
        ∀ z ∈ ball (-2 : ℝ) r, HasFDerivAt Q (innerSL ℝ (3 : ℝ)) z := by
  apply LocalWeakPoincare.exists_local_normalized_primitive
    (isOpen_ball.union isOpen_ball)
    (G := fun _ : ℝ ↦ (3 : ℝ)) (K := 0)
    (LipschitzWith.const (3 : ℝ)).lipschitzOnWith ?_ (-2)
    (Or.inl (mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  exact Filter.Eventually.of_forall fun z ↦
    ⟨0, hasFDerivAt_const (3 : ℝ) z, by intro u v; simp⟩

/-- No `Nontrivial E` hypothesis can be hidden in the final theorem. -/
theorem dimension_zero :
    ∃ r : ℝ, 0 < r ∧ ball (0 : EuclideanSpace ℝ (Fin 0)) r ⊆ univ ∧
      ∃ Q : EuclideanSpace ℝ (Fin 0) → ℝ, Q 0 = 0 ∧
        ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin 0)) r,
          HasFDerivAt Q (innerSL ℝ (0 : EuclideanSpace ℝ (Fin 0))) z := by
  apply LocalWeakPoincare.exists_local_normalized_primitive isOpen_univ
    (G := fun _ : EuclideanSpace ℝ (Fin 0) ↦ 0) (K := 0)
    (LipschitzWith.const (0 : EuclideanSpace ℝ (Fin 0))).lipschitzOnWith ?_ 0 (mem_univ _)
  exact Filter.Eventually.of_forall fun z ↦
    ⟨0, hasFDerivAt_const (0 : EuclideanSpace ℝ (Fin 0)) z, by intro u v; simp⟩

end LocalWeakPoincareSanity
