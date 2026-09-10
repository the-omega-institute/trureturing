import LeanInformationAudit.Tests.RegistrationGates.Positive
import LeanInformationAudit.Tests.RegistrationGates.Structural

open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace RegistrationProvenance

theorem proofSource : True := True.intro
theorem truth : True := proofSource
instance statementDecision : Decidable True := .isTrue True.intro
structure Certificate (theoremName : Name) where
  bit : Bool
def certificate : Certificate ``truth := ⟨false⟩
def identitySource : Name := ``truth
def viaTruth (_ : Unit) (x : Bool) : Bool := let _ := truth; x
def viaProof (_ : Unit) (x : Bool) : Bool := let _ := proofSource; x
def viaDecision (_ : Unit) (x : Bool) : Bool := if @decide True statementDecision then x else true
def viaCertificate (_ : Unit) (x : Bool) : Bool := if certificate.bit then true else x
def viaIdentity (_ : Unit) (x : Bool) : Bool := let _ := identitySource; x
def constantTruth (_ : Unit) (_ : Bool) : Bool := @decide True (.isTrue truth)
def clean (_ : Unit) (x : Bool) : Bool := x

def truthReads : PrimitiveRealization RegistrationPositive.arena.signature := ⟨viaTruth, Fin.elim0⟩
def cleanReads : PrimitiveRealization RegistrationPositive.arena.signature := ⟨clean, Fin.elim0⟩
local instance : DecidableEq RegistrationPositive.arena.State :=
  RegistrationPositive.arena.toArena.stateDecidableEq
theorem bridge : LegacyPrimitiveRealization RegistrationPositive.arena True truthReads :=
  ⟨⟨fun _ => rfl, fun _ => True.intro⟩⟩
register_information_theorem truth in RegistrationPositive.arena
  primitives truthReads.toPrimitiveBundle realization bridge
  variation RegistrationPositive.lawVariation sensitivity RegistrationPositive.slotSensitivity

-- Assertions are commands with named runtime failures, not elaboration failures.
elab "check_provenance " label:str " using " readout:ident " expects " reason:str : command => do
  Elab.Command.liftTermElabM do
    let env ← getEnv
    let n := `RegistrationProvenance ++ readout.getId
    let some entry := InformationRegistry.find? env ``truth | throwError "missing entry"
    let holder := n.str "fixtureRealization"
    let type := (env.find? ``truthReads).get!.type
    let .defnInfo template := (env.find? ``truthReads).get! | throwError "fixture template"
    let value := template.value.replace fun e =>
      if e == mkConst ``viaTruth then some (mkConst n) else none
    addDecl <| .defnDecl {
      name := holder, levelParams := [], type, value
      hints := .abbrev, safety := .safe }
    let actual ← RegistrationGates.validateFinite { entry with realizationName := holder }
    let ok := match actual with
      | none => reason.getString == "clean"
      | some message => message.startsWith "IE-C050 ClosedTruthReadout key=" &&
          (message.splitOn s!" reason={reason.getString} provenance=").length == 2 &&
          (message.splitOn "IE-C021").length == 1
    unless ok do throwError "[FAIL] {label.getString}: {actual}"
    logInfo m!"[PASS] {label.getString}"

check_provenance "TheoremTruth" using viaTruth expects "forbidden_dependency"
check_provenance "ProofConstant" using viaProof expects "forbidden_dependency"
check_provenance "StatementDecidable" using viaDecision expects "forbidden_dependency"
check_provenance "TheoremCertificate" using viaCertificate expects "forbidden_dependency"
check_provenance "StatementIdentity" using viaIdentity expects "forbidden_dependency"
check_provenance "CleanReadout" using clean expects "clean"
check_provenance "C050BeforeC021" using constantTruth expects "forbidden_dependency"

run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``truth | throwError "missing entry"
  let name := RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName
  let actual := (← getConstInfo name).value!
  let .lit (.strVal message) := actual | throwError "fixture metadata"
  unless message.startsWith "IE-C050 ClosedTruthReadout " do
    throwError "[FAIL] FinitePublished: {actual}"
  logInfo "[PASS] FinitePublished"

-- A real chain exceeds the fixed production fuel, with no recursive Lean definition.
run_cmd Elab.Command.liftTermElabM do
  let type := (← getConstInfo ``clean).type
  for i in [:5000] do
    let value := mkConst (if i == 0 then ``clean else `RegistrationProvenance.chain |>.num (i-1))
    addDecl <| .defnDecl {
      name := `RegistrationProvenance.chain |>.num i
      levelParams := [], type, value, hints := .abbrev, safety := .safe }
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.exhausted
    levelParams := [], type, value := mkConst (`RegistrationProvenance.chain |>.num 4999)
    hints := .abbrev, safety := .safe }
check_provenance "FuelExhaustion" using exhausted expects "incomplete_closure"

-- Unobtainable dependency, isolated to this synthetic environment.
run_cmd Elab.Command.liftTermElabM do
  addDecl <| .axiomDecl {
    name := `RegistrationProvenance.unavailable
    levelParams := [], type := (← getConstInfo ``clean).type, isUnsafe := false }
check_provenance "UnavailableDefinition" using unavailable expects "incomplete_closure"

-- The structural command stores a proof constant used by the readout.
def structuralRead (_ : Unit) (x : Nat) : Nat := let _ := proofSource; x
structural_theorem structuralTruth in RegistrationStructural.law
  realization ⟨structuralRead⟩ nondegeneracy RegistrationStructural.lawVariation
  sensitivity RegistrationStructural.slotSensitivity := by let _ := proofSource; rfl
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find?
    (·.theoremName == ``structuralTruth)).get!
  let actual ← RegistrationGates.validateStructural entry
  unless (actual.getD "").startsWith "IE-C050 ClosedTruthReadout " do
    throwError "[FAIL] StructuralForbidden: {actual}"
  let name := RegistrationGates.diagnosticName entry.unitConst entry.registrationModule
  unless (← getConstInfo name).value? == some (mkStrLit (actual.getD "")) do
    throwError "[FAIL] StructuralPublished"
  logInfo "[PASS] StructuralForbidden"
end RegistrationProvenance
