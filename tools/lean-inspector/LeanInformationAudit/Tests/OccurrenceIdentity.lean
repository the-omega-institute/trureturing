import LeanInformationAudit.SealCommand

open Lean
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.OccurrenceIdentity

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

/-- info: occurrence-qualified companions are distinct -/
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
  logInfo "occurrence-qualified companions are distinct"

/-- error: IE-C030 KernelAddressUsedAsSemanticEvidence root=LeanInformationAudit.Tests.OccurrenceIdentity catalog=boolA address=sha256:fixture consumer=arena-grouping -/
#guard_msgs (error) in
run_cmd do
  match rejectKernelAddressSemanticUse
      `LeanInformationAudit.Tests.OccurrenceIdentity `boolA
      "sha256:fixture" "arena-grouping" with
  | .ok () => pure ()
  | .error message => throwError message

end LeanInformationAudit.Tests.OccurrenceIdentity
