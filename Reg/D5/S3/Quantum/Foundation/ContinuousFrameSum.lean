import D5.S3.Quantum.Foundation.ContinuousFrameSum
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original telescopes for all three public source theorems.
The source bridges and actual laws are proved. Whole-family intervention,
sensitivity and observational dependence remain required for enrollment. -/

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Foundation.ContinuousFrameSum

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.ContinuousFrameSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  balls : exclusionBalls cone unit

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := Unit
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def compactOutcome (P : Inputs.{v}) : Prop := IsCompact (pure P.cone P.unit)

def continuousOutcome (P : Inputs.{v}) : Prop :=
  (weakPair P.cone P.unit →
  IsClosed {s : pure P.cone P.unit × pure P.cone P.unit |
    excludes P.cone P.unit s.1 s.2} ∧
  Continuous (sumVector P.balls) ∧
  (∀ p q : pure P.cone P.unit, excludes P.cone P.unit p q →
    sumVector P.balls p = sumVector P.balls q) ∧
  (commonCenter P.balls ↔ ∃ U : P.V, ∀ p : pure P.cone P.unit, sumVector P.balls p = U)) ∧
  (pairProper P.cone P.unit → commonCenter P.balls)

def interiorOutcome (P : Inputs.{v}) : Prop :=
  weakPair P.cone P.unit ∧ ∃ U : P.V,
    (∀ p : pure P.cone P.unit, sumVector P.balls p = U) ∧
    (1/3 : ℝ) • U ∈ intrinsicInterior ℝ (base P.cone P.unit) ∧
    U ∈ interior (P.cone : Set P.V)

def actual : Realization signature.{v} :=
  realize signature (fun i P _ => if i = 0 then compactOutcome P
    else if i = 1 then continuousOutcome P else interiorOutcome P)
    (fun e => nomatch e)

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev compactArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → weakPair P.cone P.unit →
    O.readout 0 P ()

abbrev continuousArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    O.readout 1 P ()

abbrev interiorArena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → commonCenter P.balls →
    O.readout 2 P ()

abbrev compactSource : Prop := type_of% (@original_pure_compact.{v})
abbrev continuousSource : Prop := type_of% (@original_continuous_frame_sum.{v})
abbrev interiorSource : Prop := type_of% (@common_center_interior.{v})

theorem compact_source_bridge : compactSource.{v} ↔ compactArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
      (hB := P.balls)
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u hB) hc hs hg hW

theorem continuous_source_bridge : continuousSource.{v} ↔ continuousArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
      (hB := P.balls)
  · intro h V add space finite nontrivial C u hc hs hg hB
    exact h (@Inputs.mk V add space finite nontrivial C u hB) hc hs hg

theorem interior_source_bridge : interiorSource.{v} ↔ interiorArena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
      (hB := P.balls)
  · intro h V add space finite nontrivial C u hc hs hg hB hG
    exact h (@Inputs.mk V add space finite nontrivial C u hB) hc hs hg hG

theorem compact_positive : compactArena.{v}.Law actual.{v} :=
  compact_source_bridge.mp (@original_pure_compact.{v})

theorem continuous_positive : continuousArena.{v}.Law actual.{v} :=
  continuous_source_bridge.mp (@original_continuous_frame_sum.{v})

theorem interior_positive : interiorArena.{v}.Law actual.{v} :=
  interior_source_bridge.mp (@common_center_interior.{v})

theorem erased_compact_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hW : weakPair P.cone P.unit) :
    ¬ compactArena.{v}.Law erased.{v} := by
  intro h
  exact h P hc hs hg hW

theorem erased_continuous_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) :
    ¬ continuousArena.{v}.Law erased.{v} := by
  intro h
  exact h P hc hs hg

theorem erased_interior_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤) (hG : commonCenter P.balls) :
    ¬ interiorArena.{v}.Law erased.{v} := by
  intro h
  exact h P hc hs hg hG

abbrev compactPending := Registration compactArena.{v} compactSource.{v}
abbrev continuousPending := Registration continuousArena.{v} continuousSource.{v}
abbrev interiorPending := Registration interiorArena.{v} interiorSource.{v}

#print axioms compact_source_bridge
#print axioms continuous_source_bridge
#print axioms interior_source_bridge
#print axioms compact_positive
#print axioms continuous_positive
#print axioms interior_positive

end Reg.D5.S3.Quantum.Foundation.ContinuousFrameSum
