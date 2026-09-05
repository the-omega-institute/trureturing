import LeanInformationAudit.SealCommand

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SplitCanonicalArenaCatalog

set_option linter.style.longLine false

def objectArena : Arena := Arena.ofFintype (Bool × Bool)

def lawArena : PrimitiveLawArena where
  toArena := objectArena
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

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def fstRealization : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

def sndRealization : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state.2
  anchor := Fin.elim0

information_theorem fstTheorem
  in lawArena
  object_arena objectArena
  catalog left
  primitives fstRealization
  : lawArena.Law fstRealization := by trivial

information_theorem sndTheorem
  in lawArena
  object_arena objectArena
  catalog right
  primitives sndRealization
  : lawArena.Law sndRealization := by trivial

expect_information_occurrence fstTheorem
  in objectArena
  from "LeanInformationAudit.Tests.SplitCanonicalArenaCatalog"

expect_information_occurrence sndTheorem
  in objectArena
  from "LeanInformationAudit.Tests.SplitCanonicalArenaCatalog"

/-- error: IE-C024 SplitCanonicalArenaCatalog root=LeanInformationAudit.Tests.SplitCanonicalArenaCatalog arena=LeanInformationAudit.Tests.SplitCanonicalArenaCatalog.objectArena catalogs=["left","right"] -/
#guard_msgs (error) in
#seal_information_theory

#print axioms
  fstTheorem.«LeanInformationAudit.Tests.SplitCanonicalArenaCatalog/LeanInformationAudit.Tests.SplitCanonicalArenaCatalog.objectArena/left».__primitive_realization
#print axioms
  fstTheorem.«LeanInformationAudit.Tests.SplitCanonicalArenaCatalog/LeanInformationAudit.Tests.SplitCanonicalArenaCatalog.objectArena/left».__information_unit
#print axioms
  sndTheorem.«LeanInformationAudit.Tests.SplitCanonicalArenaCatalog/LeanInformationAudit.Tests.SplitCanonicalArenaCatalog.objectArena/right».__primitive_realization
#print axioms
  sndTheorem.«LeanInformationAudit.Tests.SplitCanonicalArenaCatalog/LeanInformationAudit.Tests.SplitCanonicalArenaCatalog.objectArena/right».__information_unit

end LeanInformationAudit.Tests.SplitCanonicalArenaCatalog
