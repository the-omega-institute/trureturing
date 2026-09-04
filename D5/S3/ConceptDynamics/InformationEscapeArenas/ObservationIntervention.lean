/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation and intervention separation is a law of two typed CUT readouts. -/

import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Data.Fintype.Pi

/- Library-search audit trail (2026-09-04): exact repository hits `Obs`, `Int`,
   the two named models, and the frozen separation theorem are imported and reused.
   Mathlib finite function instances support the explicit source-structure equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

instance : DecidableEq CausalDirection := by
  intro x y
  cases x <;> cases y
  · exact isTrue rfl
  · exact isFalse (fun h => CausalDirection.noConfusion h)
  · exact isFalse (fun h => CausalDirection.noConfusion h)
  · exact isTrue rfl

instance : Fintype CausalDirection where
  elems := {CausalDirection.xCausesY, CausalDirection.yCausesX}
  complete := by intro d; cases d <;> simp

/-- Source SCMs are exactly a direction and two unary Boolean tables. -/
def scmEquiv : DeterministicBoolSCM ≃
    CausalDirection × (Bool -> Bool) × (Bool -> Bool) where
  toFun model := (model.direction, model.root, model.child)
  invFun data := { direction := data.1, root := data.2.1, child := data.2.2 }
  left_inv := by intro model; cases model; rfl
  right_inv := by intro data; cases data; rfl

instance : Fintype DeterministicBoolSCM :=
  Fintype.ofEquiv (CausalDirection × (Bool -> Bool) × (Bool -> Bool)) scmEquiv.symm
instance : DecidableEq DeterministicBoolSCM := scmEquiv.decidableEq

/-- Observation and intervention CUT roles. -/
inductive ObservationReadout
  | observation
  | intervention
  deriving DecidableEq

instance : Fintype ObservationReadout where
  elems := {.observation, .intervention}
  complete := by intro i; cases i <;> simp

/-- Typed signature of observational and interventional behavior. -/
abbrev observationInterventionSignature : PrimitiveSignature DeterministicBoolSCM where
  Index := ObservationReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .observation => Bool -> Bool × Bool
    | .intervention => Bool -> Bool -> Bool × Bool
  outputDecidableEq
    | .observation => inferInstance
    | .intervention => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The exact proposition proved by the frozen source theorem. -/
def ObservationInterventionStatement : Prop :=
  ∃ M N : DeterministicBoolSCM, Obs M = Obs N /\ Int M ≠ Int N

/-- Equal observation but unequal intervention, stated through realization slots. -/
def observationInterventionArena : PrimitiveLawArena where
  toArena := Arena.ofFintype DeterministicBoolSCM
  signature := observationInterventionSignature
  Law := fun r => ∃ M N,
    r.readout .observation M = r.readout .observation N /\
      r.readout .intervention M ≠ r.readout .intervention N

end D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
