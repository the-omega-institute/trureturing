import D5.S3.Quantum.Foundation.PositiveComplementaryProjections
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Original VII105.5 observation on the complete original family.
Sensitivity, observational dependence and exact source selection remain
additional registration obligations. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.PositiveComplementaryProjections

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.CommonPositiveExtension
open _root_.D5.S3.Quantum.Foundation.PositiveComplementaryProjections
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P _ =>
∃ a : pure P.cone P.unit → (P.V →ₗ[ℝ] ℝ),
      (∀ p : pure P.cone P.unit, common P.cone P.unit p (a p)) ∧
      (∀ (p : pure P.cone P.unit) f, common P.cone P.unit p f → f = a p) ∧
      (∀ (p : pure P.cone P.unit) (b : ExclusionChart P.cone P.unit p),
        ∃ Λ : (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (P.V →ₗ[ℝ] ℝ),
          ExtensionLaws b (a p) Λ ∧
          (restriction b).comp Λ = LinearMap.id ∧
          PointLaws P.cone P.unit p (a p) (primal (Λ.comp (restriction b))) (Λ.comp (restriction b)) ∧
          ∀ (c : ExclusionChart P.cone P.unit p)
            (Γ : (EuclideanSpace ℝ (Fin c.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (P.V →ₗ[ℝ] ℝ)),
            PositiveLift c Γ → Λ.comp (restriction b) = Γ.comp (restriction c)) ∧
      ∀ F : PointedCone.Face P.cone, ∃ T R,
        ComplementaryPair P.cone P.unit T R ∧ positiveImage P.cone T = (F : Set P.V)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    exclusionBalls P.cone P.unit → weakPair P.cone P.unit → O.readout () P ()

abbrev sourceScope : Prop := type_of% (@whole_positive_projections.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hB hW

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@whole_positive_projections.{v})

abbrev pendingEvidence := Registration arena.{v} sourceScope.{v}

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.PositiveComplementaryProjections
