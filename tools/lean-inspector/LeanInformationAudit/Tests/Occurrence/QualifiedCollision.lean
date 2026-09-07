import LeanInformationAudit.SealCommand

open LeanInformationAudit
open Lean
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.QualifiedCollision

set_option linter.style.longLine false

/-- error: IE-C026 MissingMaximalCatalog root=fixtureRoot arena=fixtureArena occurrences=[] -/
#guard_msgs (error) in
run_cmd do
  let result : Except String CatalogId :=
    validateMaximalCatalog `fixtureRoot `fixtureArena #[]
  match result with
  | .ok _ =>
      throwError "empty occurrence set produced a maximal catalog"
      pure ()
  | .error message =>
      throwError message
      pure ()

def object : Arena := Arena.ofFintype Bool
def «object/catalog» : Arena := Arena.ofFintype Bool

def lawA : PrimitiveLawArena where
  toArena := object
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

def lawB : PrimitiveLawArena where
  toArena := «object/catalog»
  signature := lawA.signature
  Law := fun _ => True

local instance : DecidableEq lawA.State := lawA.toArena.stateDecidableEq
local instance : DecidableEq lawB.State := lawB.toArena.stateDecidableEq

def realizationA : PrimitiveRealization lawA.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

def realizationB : PrimitiveRealization lawB.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

theorem shared : True := trivial

theorem legacyA : LegacyPrimitiveRealization lawA True realizationA where
  equivalence := Iff.rfl

theorem legacyB : LegacyPrimitiveRealization lawB True realizationB where
  equivalence := Iff.rfl

register_information_theorem shared
  in lawA
  object_arena object
  catalog «catalog/y»
  primitives realizationA.toPrimitiveBundle
  realization legacyA

/-- error: IE-C025 QualifiedNameCollision root=LeanInformationAudit.Tests.Occurrence.QualifiedCollision catalog=y generated_name=LeanInformationAudit.Tests.QualifiedCollision.shared.LeanInformationAudit.Tests.Occurrence.QualifiedCollision/LeanInformationAudit.Tests.QualifiedCollision.object/«catalog/y».__information_unit occurrences=["LeanInformationAudit.Tests.QualifiedCollision.object/LeanInformationAudit.Tests.QualifiedCollision.shared","LeanInformationAudit.Tests.QualifiedCollision.«object/catalog»/LeanInformationAudit.Tests.QualifiedCollision.shared"] -/
#guard_msgs (error) in
run_cmd do
  let env <- getEnv
  let existing <- match InformationRegistry.entries env |>.find? fun entry =>
      entry.theoremName == `LeanInformationAudit.Tests.QualifiedCollision.shared with
    | some entry => pure entry
    | none => throwError "missing first collision owner"
  let prospective : InformationRegistryEntry := {
    theoremName := existing.theoremName
    unitName := existing.unitName
    arenaName := `LeanInformationAudit.Tests.QualifiedCollision.lawB
    realizationName := existing.realizationName
    catalogId := `y
    registrationModuleName := env.header.mainModule
    objectArenaName := `LeanInformationAudit.Tests.QualifiedCollision.«object/catalog»
    localRegistrationNames := false
  }
  let owners := qualifiedNameCollisionEntries (InformationRegistry.entries env)
    existing.unitName prospective
  throwError (qualifiedNameCollisionError env.header.mainModule `y
    existing.unitName owners)
  pure ()

end LeanInformationAudit.Tests.QualifiedCollision
