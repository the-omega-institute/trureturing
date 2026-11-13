import D5.S3.Quantum.Foundation.OriginalBallScale
import Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight

/-! Complete original telescope with its actual scalar comparison readout.
Whole-family intervention, sensitivity and observational dependence are separate obligations. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.OriginalBallScale

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalBallScale
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.RegularAnchorHeight
open scoped RealInnerProductSpace

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P z => comparison P.cone P.unit z.1 z.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    (∀ s t : pure C u, comparison C u s t = comparison C u t s) →
    ∀ (p : pure C u) (a : ExclusionChart C u p),
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
      (BudgetFeasible b v (1 / (2*t)) ∧
        (∀ M, BudgetFeasible b v M → 1 / (2*t) ≤ M) ∧ extensionBudget b v = 1 / (2*t)) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : P.V →ₗ[ℝ] ℝ,
        confirms C u q e ∧ (∀ z, e (b.param z) = 1-t+t*⟪v,z⟫) ∧
        ∀ z, ‖z‖ ≤ 1 → O.readout () P (q, b.param z) = 1-t+t*⟪v,z⟫

abbrev sourceScope : Prop := type_of% (@original_common_chart_scale.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_common_chart_scale.{v})

end Reg.D5.S3.Quantum.Foundation.OriginalBallScale
