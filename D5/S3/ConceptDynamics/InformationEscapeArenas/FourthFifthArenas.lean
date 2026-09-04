/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed arenas expose context-selected meanings and causal intervention separation. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-09-04):
   * Repository searches for `LegacyPrimitiveRealization`, the two source theorem
     names, and their state structures found no existing realization layer.
   * The frozen `IsBinaryFixedMeaning`, `Int`, and `CF` definitions are imported
     and used verbatim rather than reproved or repackaged.
   * Pinned Mathlib's finite product and finite function instances supply the
     explicit eight-context and sixteen-model arena structures. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas

open D5.S3.ConceptDynamics.InformationEscape

namespace ContextSource
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint

section
set_option backward.isDefEq.respectTransparency.types false

private def contextEquiv :
    BinaryInterpretationContext ≃ Bool × Bool × Bool where
  toFun c := (c.readerAdmission, c.background, c.evaluationGoal)
  invFun bits :=
    { text := ()
      readerAdmission := bits.1
      background := bits.2.1
      evaluationGoal := bits.2.2
      interpretationRule := () }
  left_inv := by rintro ⟨⟨⟩, admission, background, goal, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨admission, background, goal⟩; rfl

def contextFintype : Fintype BinaryInterpretationContext :=
  Fintype.ofEquiv _ contextEquiv.symm

def contextDecidableEq : DecidableEq BinaryInterpretationContext :=
  fun left right =>
    decidable_of_iff (contextEquiv left = contextEquiv right) contextEquiv.injective.eq_iff

inductive ContextReadout
  | text
  | interpretationRule
  | readerAdmission
  | background
  | evaluationGoal
  | falseMeaning
  | trueMeaning
  deriving DecidableEq, Fintype

end

def contextSignature : PrimitiveSignature BinaryInterpretationContext where
  Index := ContextReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .text | .interpretationRule => Unit
    | .readerAdmission | .background | .evaluationGoal | .falseMeaning | .trueMeaning => Bool
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis
    | .falseMeaning | .trueMeaning => .admit
    | _ => .cut
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Bool
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def contextArena : PrimitiveLawArena where
  toArena :=
    { State := BinaryInterpretationContext
      stateFintype := contextFintype
      stateDecidableEq := contextDecidableEq }
  signature := contextSignature
  Law := fun r =>
    r.readout .text (r.anchor false) = r.readout .text (r.anchor true) ∧
    r.readout .interpretationRule (r.anchor false) =
      r.readout .interpretationRule (r.anchor true) ∧
    r.readout .readerAdmission (r.anchor false) ≠
      r.readout .readerAdmission (r.anchor true) ∧
    r.readout .background (r.anchor false) ≠ r.readout .background (r.anchor true) ∧
    r.readout .evaluationGoal (r.anchor false) ≠
      r.readout .evaluationGoal (r.anchor true) ∧
    r.readout .falseMeaning (r.anchor false) = true ∧
    r.readout .trueMeaning (r.anchor true) = true ∧
    (r.readout .readerAdmission (r.anchor false),
      r.readout .background (r.anchor false),
      r.readout .evaluationGoal (r.anchor false)) ≠
    (r.readout .readerAdmission (r.anchor true),
      r.readout .background (r.anchor true),
      r.readout .evaluationGoal (r.anchor true))

end ContextSource

namespace InterventionSource
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

section
set_option backward.isDefEq.respectTransparency.types false

private def modelEquiv :
    DeterministicBoolSCM ≃ Bool × Bool × Bool × Bool where
  toFun model :=
    (model.outcome false false, model.outcome false true,
      model.outcome true false, model.outcome true true)
  invFun bits :=
    ⟨fun exogenous treatment =>
      if exogenous then (if treatment then bits.2.2.2 else bits.2.2.1)
      else if treatment then bits.2.1 else bits.1⟩
  left_inv := by
    rintro ⟨outcome⟩
    apply congrArg DeterministicBoolSCM.mk
    funext e t
    cases e <;> cases t <;> rfl
  right_inv := by rintro ⟨a, b, c, d⟩; simp

def modelFintype : Fintype DeterministicBoolSCM :=
  Fintype.ofEquiv _ modelEquiv.symm

def modelDecidableEq : DecidableEq DeterministicBoolSCM :=
  fun left right =>
    decidable_of_iff (modelEquiv left = modelEquiv right) modelEquiv.injective.eq_iff

inductive ModelReadout
  | intervention
  | counterfactual
  deriving DecidableEq, Fintype

end

def interventionSignature : PrimitiveSignature DeterministicBoolSCM where
  Index := ModelReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .intervention => Bool -> Bool -> Nat
    | .counterfactual => Bool -> Bool -> Bool -> Bool
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def interventionArena : PrimitiveLawArena where
  toArena :=
    { State := DeterministicBoolSCM
      stateFintype := modelFintype
      stateDecidableEq := modelDecidableEq }
  signature := interventionSignature
  Law := fun r => exists M N : DeterministicBoolSCM,
    r.readout .intervention M = r.readout .intervention N ∧
      r.readout .counterfactual M ≠ r.readout .counterfactual N

end InterventionSource

end D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
