import LeanInformationAudit.Syntax

open Lean
open LeanInformationAudit
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

def probeArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Bool
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

local instance : DecidableEq probeArena.State :=
  probeArena.toArena.stateDecidableEq

def probeRealization : PrimitiveRealization probeArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem probeTheorem
  in probeArena
  primitives probeRealization
  : probeArena.Law probeRealization := by
    trivial

end LeanInformationAudit.Tests
