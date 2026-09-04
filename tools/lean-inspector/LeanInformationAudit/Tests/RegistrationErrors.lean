import LeanInformationAudit.Syntax

open Lean
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.RegistrationErrors

set_option autoImplicit false
set_option relaxedAutoImplicit false

def fixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

def fixtureSignature : PrimitiveSignature fixtureArena.State where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def fixtureLawArena : PrimitiveLawArena where
  toArena := fixtureArena
  signature := fixtureSignature
  Law := fun _ => True

local instance : DecidableEq fixtureLawArena.State :=
  fixtureLawArena.toArena.stateDecidableEq

def fixtureRealization : PrimitiveRealization fixtureLawArena.signature where
  readout := fun i x => bif i then x.2 else x.1
  anchor := Fin.elim0

def fixtureBundle :=
  fixtureRealization.toPrimitiveBundle

information_theorem nativeExample
  in fixtureLawArena
  primitives fixtureRealization
  : fixtureLawArena.Law fixtureRealization := by
    trivial

example : nativeExample.__information_unit.primitives =
    fixtureRealization.toPrimitiveBundle := rfl

/-- error: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.unrelatedNative -/
#guard_msgs (error) in
information_theorem unrelatedNative
  in fixtureLawArena
  primitives fixtureRealization
  : 2 + 2 = 4 := by
    rfl

def alternativeRealization : PrimitiveRealization fixtureLawArena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

theorem nativeBundleTarget : fixtureLawArena.Law fixtureRealization :=
  trivial

def mismatchedNativeBundleUnit : TheoremUnit fixtureLawArena.toArena :=
  { «primitives» := alternativeRealization.toPrimitiveBundle
    Statement := fixtureLawArena.Law fixtureRealization
    proof := nativeBundleTarget }

/-- info: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.nativeBundleTarget -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
      theoremName := `LeanInformationAudit.Tests.RegistrationErrors.nativeBundleTarget
      unitName :=
        `LeanInformationAudit.Tests.RegistrationErrors.mismatchedNativeBundleUnit
      arenaName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
      realizationName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureRealization
    }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "mismatched native bundle passed validation"

theorem nativeLawMismatchTarget : 2 + 2 = 4 :=
  rfl

def nativeLawMismatchUnit : TheoremUnit fixtureLawArena.toArena :=
  { «primitives» := fixtureRealization.toPrimitiveBundle
    Statement := 2 + 2 = 4
    proof := nativeLawMismatchTarget }

/-- info: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.nativeLawMismatchTarget -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
      theoremName :=
        `LeanInformationAudit.Tests.RegistrationErrors.nativeLawMismatchTarget
      unitName := `LeanInformationAudit.Tests.RegistrationErrors.nativeLawMismatchUnit
      arenaName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
      realizationName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureRealization
    }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "unrelated native law passed validation"

theorem legacyExample : True :=
  trivial

theorem legacyRealization :
    LegacyPrimitiveRealization fixtureLawArena True fixtureRealization where
  equivalence := Iff.rfl

register_information_theorem legacyExample
  in fixtureLawArena
  primitives fixtureBundle
  realization legacyRealization

namespace ImportedFixture

theorem importedExample : True :=
  trivial

theorem importedRealization :
    LegacyPrimitiveRealization fixtureLawArena True fixtureRealization where
  equivalence := Iff.rfl

end ImportedFixture

open ImportedFixture

register_information_theorem importedExample
  in fixtureLawArena
  primitives fixtureBundle
  realization importedRealization

theorem definitionBackedTarget : True :=
  trivial

set_option linter.defProp false in
def definitionBackedRealization :
    LegacyPrimitiveRealization fixtureLawArena True fixtureRealization where
  equivalence := Iff.rfl

/-- error: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.definitionBackedTarget -/
#guard_msgs (error) in
register_information_theorem definitionBackedTarget
  in fixtureLawArena
  primitives fixtureBundle
  realization definitionBackedRealization

/-- error: IE-C002 DuplicateRegistration:
LeanInformationAudit.Tests.RegistrationErrors.legacyExample -/
#guard_msgs (error) in
register_information_theorem legacyExample
  in fixtureLawArena
  primitives fixtureBundle
  realization legacyRealization

set_option linter.style.nameCheck false in
theorem generated.__lowers_escape : True :=
  trivial

theorem generatedRealization :
    LegacyPrimitiveRealization fixtureLawArena True fixtureRealization where
  equivalence := Iff.rfl

/-- error: IE-C011 GeneratedCertificateRegistered:
LeanInformationAudit.Tests.RegistrationErrors.generated.__lowers_escape -/
#guard_msgs (error) in
register_information_theorem generated.__lowers_escape
  in fixtureLawArena
  primitives fixtureBundle
  realization generatedRealization

theorem differentStatement : 1 = 1 :=
  rfl

theorem mismatchTarget : True :=
  trivial

theorem mismatchedRealization :
    LegacyPrimitiveRealization fixtureLawArena (1 = 1) fixtureRealization where
  equivalence := by simp [fixtureLawArena]

/-- error: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget -/
#guard_msgs (error) in
register_information_theorem mismatchTarget
  in fixtureLawArena
  primitives fixtureBundle
  realization mismatchedRealization

def mismatchedUnit : TheoremUnit (fixtureLawArena.toArena) :=
  { «primitives» := fixtureBundle
    Statement := 1 = 1
    proof := rfl }

/-- info: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
      theoremName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget
      unitName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchedUnit
      arenaName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
      realizationName := `LeanInformationAudit.Tests.RegistrationErrors.legacyRealization
    }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "mismatched theorem unit passed validation"

def notATheorem : Prop :=
  True

/-- info: IE-C001 UnregisteredTheoremUnit:
LeanInformationAudit.Tests.RegistrationErrors.notATheorem -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
    theoremName := `LeanInformationAudit.Tests.RegistrationErrors.notATheorem
    unitName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchedUnit
    arenaName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
    realizationName := `LeanInformationAudit.Tests.RegistrationErrors.legacyRealization
  }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "non-theorem declaration passed validation"

/-- info: IE-C003 ArenaResolutionFailed:
LeanInformationAudit.Tests.RegistrationErrors.missingArena -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
    theoremName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget
    unitName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchedUnit
    arenaName := `LeanInformationAudit.Tests.RegistrationErrors.missingArena
    realizationName := `LeanInformationAudit.Tests.RegistrationErrors.legacyRealization
  }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "missing arena passed validation"

theorem wrongUnitHead : True :=
  trivial

/-- info: IE-C006 StatementProofMismatch:
LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget -/
#guard_msgs in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) {
    theoremName := `LeanInformationAudit.Tests.RegistrationErrors.mismatchTarget
    unitName := `LeanInformationAudit.Tests.RegistrationErrors.wrongUnitHead
    arenaName := `LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
    realizationName := `LeanInformationAudit.Tests.RegistrationErrors.legacyRealization
  }
  match result with
  | .error message => logInfo message
  | .ok () => throwError "wrong theorem-unit type passed validation"

/-- error: IE-C001 UnregisteredTheoremUnit:
LeanInformationAudit.Tests.RegistrationErrors.unknownTheorem -/
#guard_msgs (error) in
register_information_theorem unknownTheorem
  in fixtureLawArena
  primitives fixtureBundle
  realization legacyRealization

end LeanInformationAudit.Tests.RegistrationErrors
