import D5.S3.ConceptDynamics.CIRPT.SemanticIntegrity
import LeanInformationAudit.SealCommand

/-! T-CIRPT-016: a closed truth readout has no unique object capture. -/

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.CirptClosedTruth

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
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

def closedTruthRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => true
  anchor := Fin.elim0

information_theorem closedTruthTheorem
  in arena
  primitives closedTruthRealization
  : arena.Law closedTruthRealization := by trivial

example (x y : arena.State) :
    (cutKernel (fun _ : arena.State => true)).relation x y := by
  exact closed_truth_readout_has_universal_kernel true x y

private def fixtureCatalog : Catalog arena.toArena :=
  Catalog.ofVector ![closedTruthTheorem.__information_unit]

example : fixtureCatalog.uniqueCaptureCount (0 : Fin 1) = 0 := by decide

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.CirptClosedTruth.closedTruthTheorem arena
LeanInformationAudit.Tests.CirptClosedTruth.arena full 2 without 2 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.CirptClosedTruth
