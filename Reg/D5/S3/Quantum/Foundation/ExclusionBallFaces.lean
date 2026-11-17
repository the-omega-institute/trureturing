import D5.S3.Quantum.Foundation.ExclusionBallFaces
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Complete original telescope reconstruction through original exclusion readouts.
Whole-family variation, sensitivity, observational dependence and source selection
remain necessary for a four-slot Contract registration. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.ExclusionBallFaces

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type u
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => exclusion P.cone P.unit x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    (∀ p : pure C u,
      (O.readout () P p).Nontrivial ∧ IsCompact (O.readout () P p) ∧
      Convex ℝ (O.readout () P p) ∧ IsExposed ℝ (base C u) (O.readout () P p) ∧
      IsExtreme ℝ (base C u) (O.readout () P p) ∧ O.readout () P p ≠ base C u ∧
      ∃ f, confirms C u p f ∧ O.readout () P p = {x | x ∈ base C u ∧ f x = 0}) ∧
    (∀ F : Set P.V, F.Nonempty → Convex ℝ F → IsExtreme ℝ (base C u) F →
      F ≠ base C u →
      (∃ p : pure C u, F = {(p : P.V)}) ∨ ∃ p : pure C u, F = O.readout () P p) ∧
    (pairProper C u →
      (∀ p q : pure C u, p ≠ q → ∃ r : pure C u,
        pairBase C u p q = O.readout () P r) ∧ wholePairBalls C u)

abbrev sourceScope : Prop := type_of% (@exclusion_ball_faces.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u hc hu hs hB
    exact h (@Inputs.mk V add space finite C u) hc hu hs hB

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exclusion_ball_faces.{u})

end Reg.D5.S3.Quantum.Foundation.ExclusionBallFaces
