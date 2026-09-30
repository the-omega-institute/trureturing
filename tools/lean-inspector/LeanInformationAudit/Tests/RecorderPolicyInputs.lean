import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates

/-! Recorder-only fixture, compiled as a `Reg` module is: it imports the
Interface package and D5, never the implementation. Both registrations below
are syntactically valid and violate an admission rule owned by the report
(IE-C011 reserved judge-output names; the P1 rigid zero-universe arena gate).
Compiling this module is the evidence that the recorder records them without
error; `RecorderPolicyBoundary` shows that the report rejects them. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.RecorderPolicyInputs

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def realization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

/-- An author theorem spelled with a reserved judge-output suffix. -/
theorem reserved.__catalog_irredundant : True := trivial

theorem reservedBridge : LegacyPrimitiveRealization arena True realization where
  equivalence := iff_of_true trivial trivial

register_information_theorem reserved.__catalog_irredundant in arena
  primitives realization.toPrimitiveBundle
  realization reservedBridge

/-- A law arena in universe 1: outside the rigid zero-universe P1 gate. -/
def highArena : PrimitiveLawArena.{1,0,0} where
  toArena := Arena.ofFintype (ULift.{1} Bool)
  signature := {
    Index := Fin 0, indexFintype := inferInstance, indexDecidableEq := inferInstance
    Output := fun _ => Bool, outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut, readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0, anchorFintype := inferInstance, anchorDecidableEq := inferInstance }
  Law _ := True

theorem lifted (x : Bool) : x.not.not = x := Bool.not_not _

register_information_theorem lifted
  via (D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
    (fun x : Bool => x.not.not) (fun x => x)) in highArena

end LeanInformationAudit.Tests.RecorderPolicyInputs
