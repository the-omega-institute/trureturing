import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit

namespace Reg.Support.LegacyRelations.System
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit

/-- Retain the original Fin 1 role, Stage carrier, Nat output and engine census. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Stage
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Fin 0
  finiteAnchor := inferInstance

def toLegacy (r : Realization signature) :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization
      _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature where
  readout i := r.readout i ()
  anchor i := r.anchor i ()

/-- The Unit parameter changes no realization: both directions are inverse. -/
def fromLegacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature) :
    Realization signature :=
  realize signature (fun i _ => r.readout i) (fun i _ => r.anchor i)

theorem to_from_legacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.signature) :
    toLegacy (fromLegacy r) = r := by
  cases r
  rfl

theorem from_to_legacy (r : Realization signature) : fromLegacy (toLegacy r) = r := by
  cases r with
  | mk readout anchor =>
    congr 1 <;> funext i p <;> cases p <;> rfl

def arena : Arena := ⟨signature, fun r =>
  _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.Law (toLegacy r)⟩

def actual : Realization signature :=
  realize signature (fun _ _ stage => (censusCatalog stage).uniqueCaptureCount (0 : Fin 1))
    (fun i => Fin.elim0 i)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun i => Fin.elim0 i)

theorem full_law_transport (r : Realization signature) :
    arena.Law r ↔
      _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.Law (toLegacy r) := Iff.rfl

theorem bridge : SystemStatement ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h.1 true
  have different : (0 : Nat) ≠ systemReadout true := by decide
  exact different bad

theorem variation : Variation arena actual :=
  ⟨engine_census_self_application, rejected, rejected_law⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    exact (h (@Subsingleton.elim (Fin 1) inferInstance j i)).elim
  · intro i
    exact Fin.elim0 i

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  change systemReadout false ≠ systemReadout true
  decide

def registration : Registration arena SystemStatement where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

#print axioms registration
end Reg.Support.LegacyRelations.System
