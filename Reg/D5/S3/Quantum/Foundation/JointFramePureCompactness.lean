import D5.S3.Quantum.Foundation.JointFramePureCompactness
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original-domain reconstruction and positive laws for both conclusions.
Whole-family variation, sensitivity, actual observational dependence and lawful
source selection remain unsupplied. No complete four-slot registration is declared. -/

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.JointFramePureCompactness

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.JointFramePureCompactness
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
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => x ∈ pure P.cone P.unit) (fun e => nomatch e)

namespace Closed

abbrev sourceScope : Prop := type_of% (@pure_closed_of_joint_completion.{u})

def arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    pureJointCompletion P.cone P.unit → pointBallIncidence P.cone P.unit →
    IsClosed {x | O.readout () P x}

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C unit
    exact h (@Inputs.mk V add space finite C unit)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@pure_closed_of_joint_completion.{u})

end Closed

namespace Compact

abbrev sourceScope : Prop := type_of% (@pure_compact_of_joint_completion.{u})

def arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    pureJointCompletion P.cone P.unit → pointBallIncidence P.cone P.unit →
    IsCompact {x | O.readout () P x}

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C unit
    exact h (@Inputs.mk V add space finite C unit)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@pure_compact_of_joint_completion.{u})

end Compact

end Reg.D5.S3.Quantum.Foundation.JointFramePureCompactness
