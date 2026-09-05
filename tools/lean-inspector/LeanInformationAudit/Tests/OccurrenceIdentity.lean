import LeanInformationAudit.SealCommand

open Lean
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.OccurrenceIdentity

set_option linter.style.longLine false

def objectA : Arena := Arena.ofFintype Bool
def objectB : Arena := Arena.ofFintype Bool

def lawA : PrimitiveLawArena where
  toArena := objectA
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
  toArena := objectB
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

theorem sharedTheorem : True := trivial

theorem legacyA : LegacyPrimitiveRealization lawA True realizationA where
  equivalence := Iff.rfl

theorem legacyB : LegacyPrimitiveRealization lawB True realizationB where
  equivalence := Iff.rfl

register_information_theorem sharedTheorem
  in lawA
  object_arena objectA
  catalog boolA
  primitives realizationA.toPrimitiveBundle
  realization legacyA

register_information_theorem sharedTheorem
  in lawB
  object_arena objectB
  catalog boolB
  primitives realizationB.toPrimitiveBundle
  realization legacyB

/-- error: IE-C002 DuplicateRegistration:
LeanInformationAudit.Tests.OccurrenceIdentity.sharedTheorem -/
#guard_msgs (error) in
register_information_theorem sharedTheorem
  in lawA
  object_arena objectA
  catalog duplicateSpellingDoesNotMatter
  primitives realizationA.toPrimitiveBundle
  realization legacyA

#seal_information_theory output "/tmp/lean-information-audit-occurrence-identity.json"

/-- info: occurrence-qualified companions and diagnostic address projection passed -/
#guard_msgs (info) in
run_cmd do
  let env <- getEnv
  let root := env.header.mainModule
  let theoremName := `LeanInformationAudit.Tests.OccurrenceIdentity.sharedTheorem
  let first := catalogQualifiedName root
    `LeanInformationAudit.Tests.OccurrenceIdentity.objectA `boolA theoremName
    "__lowers_escape"
  let second := catalogQualifiedName root
    `LeanInformationAudit.Tests.OccurrenceIdentity.objectB `boolB theoremName
    "__lowers_escape"
  if first == second || !env.contains first || !env.contains second then
    throwError "missing distinct occurrence-qualified companions"
  let contents <- Lean.Elab.Command.liftIO <|
    IO.FS.readFile "/tmp/lean-information-audit-occurrence-identity.json"
  let json <- match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError message
  let classes <- match Json.getObjVal? json "kernel_address_coincidence_classes" >>=
      Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let some coincidence := classes[0]?
    | throwError "missing address coincidence class"
  let diagnosticOnly <- match Json.getObjVal? coincidence "diagnostic_only" >>=
      Json.getBool? with
    | .ok value => pure value
    | .error message => throwError message
  let occurrences <- match Json.getObjVal? coincidence "occurrences" >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  unless classes.size == 1 && diagnosticOnly && occurrences.size == 2 do
    throwError "address coincidence escaped diagnostic-only projection"
  logInfo "occurrence-qualified companions and diagnostic address projection passed"

/-- error: IE-C030 KernelAddressUsedAsSemanticEvidence root=LeanInformationAudit.Tests.OccurrenceIdentity catalog=boolA address=sha256:fixture consumer=arena-grouping -/
#guard_msgs (error) in
run_cmd do
  match rejectKernelAddressSemanticUse
      `LeanInformationAudit.Tests.OccurrenceIdentity `boolA
      "sha256:fixture" "arena-grouping" with
  | .ok () => pure ()
  | .error message => throwError message

#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__primitive_realization
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__primitive_realization
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__information_unit
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__information_unit
#print axioms
  objectA.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__information_catalog
#print axioms
  objectB.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__information_catalog
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__lowers_escape
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__escape_enriched
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__lowers_escape
#print axioms
  sharedTheorem.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__escape_enriched
#print axioms
  objectA.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectA/boolA».__catalog_irredundant
#print axioms
  objectB.«LeanInformationAudit.Tests.OccurrenceIdentity/LeanInformationAudit.Tests.OccurrenceIdentity.objectB/boolB».__catalog_irredundant

end LeanInformationAudit.Tests.OccurrenceIdentity
