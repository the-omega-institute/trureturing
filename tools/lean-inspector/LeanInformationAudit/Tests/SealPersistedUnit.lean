import LeanInformationAudit.SealCommand

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealPersistedUnit

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

def fixtureRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => !state
  anchor := Fin.elim0

theorem target : arena.Law fixtureRealization := by trivial

def customPersistedUnit : TheoremUnit arena.toArena :=
  { «primitives» := fixtureRealization.toPrimitiveBundle
    Statement := arena.Law fixtureRealization
    proof := target }

run_cmd registerValidatedEntry {
  theoremName := `LeanInformationAudit.Tests.SealPersistedUnit.target
  unitName := `LeanInformationAudit.Tests.SealPersistedUnit.customPersistedUnit
  arenaName := `LeanInformationAudit.Tests.SealPersistedUnit.arena
  realizationName := `LeanInformationAudit.Tests.SealPersistedUnit.fixtureRealization
}

#seal_information_theory

#check target.__lowers_escape
#check arena.__catalog_irredundant
#print axioms target.__lowers_escape
#print axioms target.__escape_enriched
#print axioms arena.__catalog_irredundant

end LeanInformationAudit.Tests.SealPersistedUnit
