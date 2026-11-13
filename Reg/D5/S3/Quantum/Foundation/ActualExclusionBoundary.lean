import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.ActualExclusionBoundary

/-! The source-family bridge preserves the original cone, whole base and all
whole exclusions. A lawful raw source selection and a validated four-slot
registration remain unavailable; see issue 29762. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Foundation.ActualExclusionBoundary

open Set
open _root_.D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces ActualExclusionBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

structure Inputs where
  V : Type u
  normed : NormedAddCommGroup V
  scalar : NormedSpace ℝ V
  finite : FiniteDimensional ℝ V
  C : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  closed : IsClosed (C : Set V)
  strict : ∀ x ∈ C, x ≠ 0 → 0 < unit x
  generating : Submodule.span ℝ (C : Set V) = ⊤
  balls : exclusionBalls C unit

attribute [instance] Inputs.normed Inputs.scalar Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := pure P.C P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P p => exclusion P.C P.unit p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    (∀ x ∈ intrinsicFrontier ℝ (base P.C P.unit),
      ∃ p : pure P.C P.unit, x ∈ R.readout () P p) ∧
    ∀ x ∈ base P.C P.unit, ∀ y ∈ base P.C P.unit,
      midpoint ℝ x y ∈ intrinsicFrontier ℝ (base P.C P.unit) ↔
        ∃ p : pure P.C P.unit, x ∈ R.readout () P p ∧ y ∈ R.readout () P p

abbrev source_scope := type_of%
  (@_root_.D5.S3.Quantum.Foundation.ActualExclusionBoundary.original_boundary_cover_and_midpoint.{u})

theorem source_bridge : source_scope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    exact @h P.V P.normed P.scalar P.finite P.C P.unit
      P.closed P.strict P.generating P.balls
  · intro h V normed scalar finite C unit closed strict generating balls
    exact h ⟨V, normed, scalar, finite, C, unit, closed, strict, generating, balls⟩

theorem actual_positive : arena.{u}.Law actual :=
  source_bridge.mp @_root_.D5.S3.Quantum.Foundation.ActualExclusionBoundary.original_boundary_cover_and_midpoint

end Reg.D5.S3.Quantum.Foundation.ActualExclusionBoundary
