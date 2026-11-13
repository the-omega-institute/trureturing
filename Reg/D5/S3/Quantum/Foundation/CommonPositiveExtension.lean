import D5.S3.Quantum.Foundation.CommonPositiveExtension
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The complete original telescope and common-extension observation.
Whole-family intervention, observational dependence and exact enrolled
source-selection evidence are additional registration obligations. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.CommonPositiveExtension

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.CommonPositiveExtension
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
      (∀ (p : pure P.cone P.unit) g, confirms P.cone P.unit p g → ConfirmationNormalForm a p g) ∧
      ∀ (p : pure P.cone P.unit) (b : ExclusionChart P.cone P.unit p),
        Set.BijOn (restriction b) (zeroPositive P.cone P.unit p) {h | ballPositive h} ∧
        ∃! Λ, ExtensionLaws b (a p) Λ) (fun e => nomatch e)

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    exclusionBalls P.cone P.unit → weakPair P.cone P.unit → O.readout () P ()

abbrev sourceScope : Prop := type_of% (@whole_positive_extension.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hB hW

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@whole_positive_extension.{v})

/-- Conditional failure of erasure at every admissible original input; this
alone supplies no whole-family sensitivity or enrollment evidence. -/
theorem erased_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit) (hW : weakPair P.cone P.unit) :
    ¬ arena.{v}.Law erased.{v} := fun h => h P hc hs hg hB hW

abbrev pendingEvidence := Registration arena.{v} sourceScope.{v}

def arcActual : Realization signature.{v} :=
  realize signature (fun _ P _ =>
    ∃ a : pure P.cone P.unit → (P.V →ₗ[ℝ] ℝ),
      (∀ p : pure P.cone P.unit, common P.cone P.unit p (a p)) ∧
      (∀ (p : pure P.cone P.unit) f, common P.cone P.unit p f → f = a p) ∧ ArcFamily a)
    (fun e => nomatch e)

abbrev arcSourceScope : Prop := type_of% (@whole_arc_effect.{v})

theorem arc_source_bridge : arcSourceScope.{v} ↔ arena.{v}.Law arcActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hB hW

theorem arc_actual_positive : arena.{v}.Law arcActual.{v} :=
  arc_source_bridge.mp (@whole_arc_effect.{v})

abbrev arcPendingEvidence := Registration arena.{v} arcSourceScope.{v}

#print axioms source_bridge
#print axioms actual_positive
#print axioms erased_negative
#print axioms arc_source_bridge
#print axioms arc_actual_positive

end Reg.D5.S3.Quantum.Foundation.CommonPositiveExtension
