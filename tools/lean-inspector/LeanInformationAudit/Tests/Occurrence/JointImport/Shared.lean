import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Occurrence.JointImport

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Fin 1
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

instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def readout : PrimitiveRealization arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

theorem shared : True := trivial
theorem bridge : LegacyPrimitiveRealization arena True readout := ⟨Iff.rfl⟩

end LeanInformationAudit.Tests.Occurrence.JointImport
