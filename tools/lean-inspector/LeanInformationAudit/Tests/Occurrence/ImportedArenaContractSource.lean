import LeanInformationAudit.Tests.Occurrence.ImportedArenaAlignmentSource

open D5.S3.ConceptDynamics.InformationEscape

namespace ImportedContractProbe

-- A pure source supplier: none of these spellings has registration side effects.
def arena : Arena := Arena.ofFintype Bool
def expectedAlias : Arena := arena
def expectedCopy : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq
def sourceAlias : Arena := arena
def sourceCopy : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq
def baselineAlias : Arena := arena
def baselineCopy : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq
def expectationAlias : Arena := arena
def expectationCopy : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq

-- Independently authored contract inputs, never registration-derived.
def expectedGroupedAlias : Arena := (QualityGrouped.hold ()) {
  State := arena.State, stateFintype := arena.stateFintype,
  stateDecidableEq := arena.stateDecidableEq }
def expectedGroupedCopy : Arena := (QualityGrouped.holdCopy ()) arena
def sourceGroupedAlias : Arena := (QualityGrouped.hold ()) {
  State := arena.State, stateFintype := arena.stateFintype,
  stateDecidableEq := arena.stateDecidableEq }
def sourceGroupedCopy : Arena := (QualityGrouped.holdCopy ()) arena
def baselineGroupedAlias : Arena := (QualityGrouped.hold ()) {
  State := arena.State, stateFintype := arena.stateFintype,
  stateDecidableEq := arena.stateDecidableEq }
def baselineGroupedCopy : Arena := (QualityGrouped.holdCopy ()) arena

def missingEvidence : Arena := arena

def lawArena : PrimitiveLawArena where
  toArena := arena
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

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def readout : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

theorem target : True := trivial
theorem bridge : LegacyPrimitiveRealization lawArena True readout := ⟨Iff.rfl⟩

end ImportedContractProbe
