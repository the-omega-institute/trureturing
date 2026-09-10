import LeanInformationAudit.SealCommand

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.AliasSplitCatalog

set_option linter.style.longLine false

def objectArena : Arena := Arena.ofFintype (Bool × Bool)

def cloneArena := objectArena
abbrev abbreviatedArena := cloneArena
@[reducible] def chainedArena := abbreviatedArena

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
  object_arena chainedArena
  catalog right
  primitives sndRealization
  : lawArena.Law sndRealization := by trivial

expect_information_occurrence fstTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.AliasSplitCatalog"

expect_information_occurrence sndTheorem
  in chainedArena
  from "LeanInformationAudit.Tests.Occurrence.AliasSplitCatalog"

/-- error: IE-C024 SplitCanonicalArenaCatalog root=LeanInformationAudit.Tests.Occurrence.AliasSplitCatalog arena=LeanInformationAudit.Tests.AliasSplitCatalog.objectArena catalogs=["left","right"] -/
#guard_msgs (error) in
#seal_information_theory

/-- error: IE-C002 DuplicateRegistration object_arena=LeanInformationAudit.Tests.AliasSplitCatalog.objectArena theorem_name=LeanInformationAudit.Tests.AliasSplitCatalog.fstTheorem registration_modules=["LeanInformationAudit.Tests.Occurrence.AliasSplitCatalog"] count=2 -/
#guard_msgs (error) in
information_theorem fstTheorem
  in lawArena
  object_arena chainedArena
  catalog duplicate
  primitives fstRealization
  : lawArena.Law fstRealization := by trivial


end LeanInformationAudit.Tests.AliasSplitCatalog
