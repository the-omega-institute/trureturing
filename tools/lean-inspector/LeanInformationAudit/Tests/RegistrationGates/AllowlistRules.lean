import LeanInformationAudit.Tests.RegistrationGates.AllowlistRulesCore



open Lean LeanInformationAudit.RegistrationGates

namespace CorrectnessNominalResult

def signature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CorrectnessExternalRound4.StatementResult

def bare : LeanInformationAudit.StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨CorrectnessExternalRound4.valuedResult⟩
def eta : LeanInformationAudit.StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨fun index bit => CorrectnessExternalRound4.valuedResult index bit⟩
def literal : LeanInformationAudit.StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨fun (_ : Unit) bit => ⟨⟨rfl⟩, bit⟩⟩

def cleanSignature : LeanInformationAudit.StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CorrectnessExternalRound4.CleanResult
def clean : LeanInformationAudit.StructuralPrimitiveRealization ⟨Bool⟩ cleanSignature :=
  ⟨CorrectnessExternalRound4.cleanResult⟩
def cleanEta : LeanInformationAudit.StructuralPrimitiveRealization ⟨Bool⟩ cleanSignature :=
  ⟨fun index bit => CorrectnessExternalRound4.cleanResult index bit⟩

run_cmd Elab.Command.liftTermElabM do
  for alternative in [``eta, ``literal] do
    unless ← Meta.isDefEq (mkConst ``bare) (mkConst alternative) do
      throwError "[FAIL] NominalResultShape {alternative}"
  let env ← getEnv
  let some index := env.getModuleIdxFor? ``CorrectnessExternalRound4.valuedResult
    | throwError "[FAIL] NominalResultShape external module missing"
  logInfo m!"[PASS] NominalResultShape external={env.header.modules[index.toNat]!.module}"
  for (label, holder) in [("NominalBare", ``bare), ("NominalEta", ``eta),
      ("NominalLiteral", ``literal), ("NominalCleanBare", ``clean), ("NominalCleanEta", ``cleanEta)] do
    let result ← provenanceErrorCurrent env.header.mainModule `catalog ``AllowlistRules.target holder
    if holder == ``clean || holder == ``cleanEta then
      if result.isNone then logInfo m!"[PASS] {label}"
      else logError m!"[FAIL] {label}: {result}"
    else
      match result with
      | some message =>
        let expected := if holder == ``literal then "reason=forbidden_dependency"
          else "statement_mentioning_type"
        if message.startsWith "IE-C050 ClosedTruthReadout " && message.contains expected then
          logInfo m!"[PASS] {label}: {message}"
        else logError m!"[FAIL] {label}: unexpected {message}"
      | none => logError m!"[FAIL] {label}: false admission; missing IE-C050"

end CorrectnessNominalResult

open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape

namespace FunnelAttackA6


def statement : Prop := (137 : Nat) = 137
theorem target : statement := rfl

def targetFamily (f : statement → Type) : Type := Unit

def sortDomainRead (i : Unit) (s : Bool) : targetFamily (fun _ : statement => Bool) := ()

def sortDomainSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => targetFamily (fun _ : statement => Bool)
def sortDomainRealization : StructuralPrimitiveRealization
    ⟨Bool⟩ sortDomainSignature := ⟨sortDomainRead⟩

structure CachePayload where
  hidden : Unit → statement
  bit : Bool

def cacheRead (i : Unit) (s : Bool) : CachePayload :=
  { hidden := fun _ => rfl, bit := s }
def cacheSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CachePayload
def cacheRealization : StructuralPrimitiveRealization
    ⟨Bool⟩ cacheSignature := ⟨cacheRead⟩

inductive ActiveNominal where
  | base : ActiveNominal
  | mk (next : ActiveNominal) (hidden : statement) (bit : Bool) : ActiveNominal

def activeRead (i : Unit) (s : Bool) : ActiveNominal :=
  ActiveNominal.mk ActiveNominal.base rfl s
def activeSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ActiveNominal
def activeRealization : StructuralPrimitiveRealization
    ⟨Bool⟩ activeSignature := ⟨activeRead⟩

private def check (label : String) (realizationName : Name) : CoreM Unit := do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog ``FunnelAttackA6.target realizationName
  logInfo m!"[A6_RESULT] {label}: {result.getD "<none>"}"
  let some message := result | throwError "[FAIL] {label}: false admission"
  unless message.startsWith "IE-C050 ClosedTruthReadout " do
    throwError "[FAIL] {label}: unexpected {message}"
  logInfo m!"[PASS] {label}"

run_cmd Elab.Command.liftCoreM do
  check "cache-domain-hidden-body" ``cacheRealization
  check "active-nominal-hidden-field" ``activeRealization
  check "sort-family-hidden-domain" ``sortDomainRealization

end FunnelAttackA6

namespace NominalFieldFixtures
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
def ProofSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ProofResult
def ProofRealization : StructuralPrimitiveRealization ⟨Bool⟩ ProofSignature := ⟨proofResult⟩
def CleanProofSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CleanProofResult
def CleanProofRealization : StructuralPrimitiveRealization ⟨Bool⟩ CleanProofSignature := ⟨cleanProofResult⟩
def InstanceSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => InstanceResult
def InstanceRealization : StructuralPrimitiveRealization ⟨Bool⟩ InstanceSignature := ⟨instanceResult⟩
def CleanInstanceSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CleanInstanceResult
def CleanInstanceRealization : StructuralPrimitiveRealization ⟨Bool⟩ CleanInstanceSignature := ⟨cleanInstanceResult⟩
def UniverseSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => UniverseResult.{1}
def UniverseRealization : StructuralPrimitiveRealization ⟨Bool⟩ UniverseSignature := ⟨universeResult⟩
run_cmd Elab.Command.liftCoreM do
  for (label, holder, target, clean) in [
      ("NominalProofField", ``ProofRealization, ``AllowlistRules.target, false),
      ("NominalInstanceField", ``InstanceRealization, ``AllowlistRules.target, false),
      ("NominalUniverseField", ``UniverseRealization, ``AllowlistAttempt8Fixtures.universeTarget, false),
      ("NominalCleanProofField", ``CleanProofRealization, ``AllowlistRules.target, true),
      ("NominalCleanInstanceField", ``CleanInstanceRealization, ``AllowlistRules.target, true)] do
    let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog target holder
    if clean then
      if result.isNone then logInfo m!"[PASS] {label}"
      else logError m!"[FAIL] {label}: unexpected {result}"
    else
      match result with
      | some message =>
        if message.startsWith "IE-C050 ClosedTruthReadout " &&
            message.contains "statement_mentioning_type" then logInfo m!"[PASS] {label}: {message}"
        else logError m!"[FAIL] {label}: unexpected {message}"
      | none => logError m!"[FAIL] {label}: false admission; missing IE-C050"
end NominalFieldFixtures

namespace NominalFieldFixtures
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
theorem listedClassTarget : ∀ a b : Unit, a = b := by
  intro a b
  cases a
  cases b
  rfl
def listedClassSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PLift (Subsingleton Unit)
def listedClassRealization : StructuralPrimitiveRealization ⟨Bool⟩ listedClassSignature :=
  ⟨listedClassResult⟩
def cleanListedClassSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PLift (Subsingleton (Fin 1))
def cleanListedClassRealization : StructuralPrimitiveRealization ⟨Bool⟩ cleanListedClassSignature :=
  ⟨cleanListedClassResult⟩
run_cmd Elab.Command.liftCoreM do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``listedClassTarget ``listedClassRealization
  match result with
  | some message =>
    if message.startsWith "IE-C050 ClosedTruthReadout " &&
        message.contains "statement_mentioning_type" then
      logInfo m!"[PASS] NominalListedClassProof: {message}"
    else logError m!"[FAIL] NominalListedClassProof: unexpected {message}"
  | none => logError "[FAIL] NominalListedClassProof: false admission; missing IE-C050"
  let clean ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``listedClassTarget ``cleanListedClassRealization
  if clean.isNone then logInfo "[PASS] NominalCleanListedClassProof"
  else logError m!"[FAIL] NominalCleanListedClassProof: {clean}"
end NominalFieldFixtures

namespace ReadoutModeInvariant
open Lean
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  for userName in [
      `LeanInformationAudit.RegistrationGates.inputType,
      `LeanInformationAudit.RegistrationGates.occurrenceType,
      `LeanInformationAudit.RegistrationGates.caseFields,
      `LeanInformationAudit.RegistrationGates.typeFamilyArgument,
      `LeanInformationAudit.RegistrationGates.classifyOccurrence] do
    let some (_, info) := env.constants.toList.find? (fun (name, _) =>
      (privateToUserName? name).getD name == userName)
      | throwError "[FAIL] NoTypeClassificationModes: missing {userName}"
    Meta.forallTelescope info.type fun params _ => do
      for param in params do
        if (← Meta.inferType param) == mkConst ``Bool then
          throwError "[FAIL] NoTypeClassificationModes: {userName} has a Boolean mode"
  for userName in [
      `LeanInformationAudit.RegistrationGates.WalkState.typeChecks,
      `LeanInformationAudit.RegistrationGates.WalkState.cleanTypes] do
    let some (_, info) := env.constants.toList.find? (fun (name, _) =>
      (privateToUserName? name).getD name == userName)
      | throwError "[FAIL] NoTypeClassificationModes: missing {userName}"
    Meta.forallTelescope info.type fun _ result => do
      if (result.find? (· == mkConst ``Bool)).isSome then
        throwError "[FAIL] NoTypeClassificationModes: {userName} retains a mode in its data"
  logInfo "[PASS] NoTypeClassificationModes"
end ReadoutModeInvariant

-- Admission is guarded by the behavior/mutation pairs in this file and by
-- AllowlistBoundaries.NoSemanticNormalization. Diagnostic strings and counters
-- do not participate in an unrelated whole-source checksum.


namespace NominalFieldFixtures
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
def IndexedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => IndexedResult 137
def IndexedRealization : StructuralPrimitiveRealization ⟨Bool⟩ IndexedSignature := ⟨indexedResult⟩
def CleanIndexedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CleanIndexedResult 138
def CleanIndexedRealization : StructuralPrimitiveRealization ⟨Bool⟩ CleanIndexedSignature := ⟨cleanIndexedResult⟩
run_cmd Elab.Command.liftCoreM do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``AllowlistRules.target ``IndexedRealization
  match result with
  | some message =>
    if message.startsWith "IE-C050 ClosedTruthReadout " &&
        message.contains "statement_mentioning_type" then
      logInfo m!"[PASS] NominalIndexedProofField: {message}"
    else logError m!"[FAIL] NominalIndexedProofField: unexpected {message}"
  | none => logError "[FAIL] NominalIndexedProofField: false admission; missing IE-C050"
  let clean ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``AllowlistRules.target ``CleanIndexedRealization
  if clean.isNone then logInfo "[PASS] NominalCleanIndexedProofField"
  else logError m!"[FAIL] NominalCleanIndexedProofField: {clean}"
end NominalFieldFixtures

namespace NominalFieldFixtures
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
theorem recursiveTarget : (138 : Nat) = 138 := rfl
def RecursiveIndexedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => RecursiveIndexedResult 137
def RecursiveIndexedRealization : StructuralPrimitiveRealization ⟨Bool⟩ RecursiveIndexedSignature :=
  ⟨recursiveIndexedResult⟩
def CleanRecursiveIndexedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CleanRecursiveIndexedResult 137
def CleanRecursiveIndexedRealization : StructuralPrimitiveRealization ⟨Bool⟩ CleanRecursiveIndexedSignature :=
  ⟨cleanRecursiveIndexedResult⟩
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  for name in [``UniformIndexedResult, ``IndexedResult] do
    let some (.inductInfo info) := env.find? name | throwError "[FAIL] IndexFixtureShape"
    logInfo m!"IndexFixtureShape {name}: parameters={info.numParams}, indices={info.numIndices}"
  let result ← provenanceErrorCurrent env.header.mainModule `catalog
    ``recursiveTarget ``RecursiveIndexedRealization
  match result with
  | some message =>
    if message.startsWith "IE-C050 ClosedTruthReadout " &&
        message.contains "statement_mentioning_type" then
      logInfo m!"[PASS] NominalRecursiveIndexedProofField: {message}"
    else logError m!"[FAIL] NominalRecursiveIndexedProofField: unexpected {message}"
  | none => logError "[FAIL] NominalRecursiveIndexedProofField: false admission; missing IE-C050"
  let clean ← provenanceErrorCurrent env.header.mainModule `catalog
    ``recursiveTarget ``CleanRecursiveIndexedRealization
  if clean.isNone then logInfo "[PASS] NominalCleanRecursiveIndexedProofField"
  else logError m!"[FAIL] NominalCleanRecursiveIndexedProofField: {clean}"
end NominalFieldFixtures

namespace NominalFieldFixtures
open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
def LetIndexSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => IndexSelfResult 138
def LetIndexRealization : StructuralPrimitiveRealization ⟨Bool⟩ LetIndexSignature :=
  ⟨fun i bit => let n := 138; indexSelfBy n i bit⟩
def CleanLetIndexSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => IndexSelfResult 139
def CleanLetIndexRealization : StructuralPrimitiveRealization ⟨Bool⟩ CleanLetIndexSignature :=
  ⟨fun i bit => let n := 139; indexSelfBy n i bit⟩
run_cmd Elab.Command.liftCoreM do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``recursiveTarget ``LetIndexRealization
  match result with
  | some message =>
    if message.startsWith "IE-C050 ClosedTruthReadout " &&
        message.contains "statement_mentioning_type" then
      logInfo m!"[PASS] NominalLetIndexProofField: {message}"
    else logError m!"[FAIL] NominalLetIndexProofField: unexpected {message}"
  | none => logError "[FAIL] NominalLetIndexProofField: false admission; missing IE-C050"
  let clean ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog
    ``recursiveTarget ``CleanLetIndexRealization
  if clean.isNone then logInfo "[PASS] NominalCleanLetIndexProofField"
  else logError m!"[FAIL] NominalCleanLetIndexProofField: {clean}"
end NominalFieldFixtures


open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates

namespace CorrectnessRound5
open CorrectnessExternalRound5

def directSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => DirectIndexed 137
def directBare : StructuralPrimitiveRealization ⟨Bool⟩ directSignature := ⟨directRead⟩

-- These eliminators return the stored field. No independent proof of S is supplied.
def recoverIdentityProof : IdentityIndexed 137 → ((137 : Nat) = 137)
  | .mk _ proof _ => proof
def recoverSuccessorProof : SuccessorIndexed 138 → ((137 : Nat) = 137)
  | .mk _ proof _ => proof

def identitySignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => IdentityIndexed 137
def identityBare : StructuralPrimitiveRealization ⟨Bool⟩ identitySignature := ⟨identityRead⟩
def identityEta : StructuralPrimitiveRealization ⟨Bool⟩ identitySignature :=
  ⟨fun i bit => identityRead i bit⟩
def identityLiteral : StructuralPrimitiveRealization ⟨Bool⟩ identitySignature :=
  ⟨fun _ bit => .mk 137 rfl bit⟩

def successorSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => SuccessorIndexed 138
def successorBare : StructuralPrimitiveRealization ⟨Bool⟩ successorSignature := ⟨successorRead⟩
def successorEta : StructuralPrimitiveRealization ⟨Bool⟩ successorSignature :=
  ⟨fun i bit => successorRead i bit⟩
def successorLiteral : StructuralPrimitiveRealization ⟨Bool⟩ successorSignature :=
  ⟨fun _ bit => .mk 137 rfl bit⟩

def cleanIdentitySignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => IdentityIndexed 139
def cleanIdentity : StructuralPrimitiveRealization ⟨Bool⟩ cleanIdentitySignature := ⟨cleanIdentityRead⟩
def cleanSuccessorSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => SuccessorIndexed 140
def cleanSuccessor : StructuralPrimitiveRealization ⟨Bool⟩ cleanSuccessorSignature := ⟨cleanSuccessorRead⟩

run_cmd Elab.Command.liftTermElabM do
  for (bare, alternative) in [(``identityBare, ``identityEta), (``identityBare, ``identityLiteral),
      (``successorBare, ``successorEta), (``successorBare, ``successorLiteral)] do
    unless ← Meta.isDefEq (mkConst bare) (mkConst alternative) do
      throwError "[FAIL] ReopeningShape {bare} {alternative}"
    logInfo m!"[PASS] ReopeningShape {bare} = {alternative}"
  let env ← getEnv
  let some externalIndex := env.getModuleIdxFor? ``identityRead
    | throwError "[FAIL] ExternalShape: no imported owner"
  logInfo m!"[PASS] ExternalShape: {env.header.modules[externalIndex.toNat]!.module}"
  for name in [``IdentityIndexed, ``SuccessorIndexed] do
    let some (.inductInfo info) := env.find? name | throwError "missing inductive"
    logInfo m!"[SHAPE] {name}: parameters={info.numParams} indices={info.numIndices}"
  for name in [``IdentityIndexed.mk, ``SuccessorIndexed.mk] do
    logInfo m!"[SHAPE] {name}: {(env.find? name).map (·.type)}"
  for (label, holder, clean) in [
      ("DirectIndexBare", ``directBare, false),
      ("CompositeIdentityBare", ``identityBare, false),
      ("CompositeIdentityEta", ``identityEta, false),
      ("CompositeIdentityLiteral", ``identityLiteral, false),
      ("CompositeSuccessorBare", ``successorBare, false),
      ("CompositeSuccessorEta", ``successorEta, false),
      ("CompositeSuccessorLiteral", ``successorLiteral, false),
      ("CompositeIdentityClean", ``cleanIdentity, true),
      ("CompositeSuccessorClean", ``cleanSuccessor, true)] do
    let result ← provenanceErrorCurrent env.header.mainModule `catalog ``AllowlistRules.target holder
    logInfo m!"[OBSERVED] {label}: {result}"
    if !clean && result.isNone then
      logError m!"[FAIL] {label}: false admission; nominal proof field specializes to registered statement"
    else if clean && result.isSome then
      logError m!"[FAIL] {label}: unexpected rejection {result}"
    else logInfo m!"[PASS] {label}"
end CorrectnessRound5

namespace NumericMetadataFixtures
theorem orderTarget : (0 : Nat) ≤ 137 := Nat.zero_le 137
theorem strictOrderTarget : (0 : Nat) < 137 := by decide
def signature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => Fin 256
def bounded : StructuralPrimitiveRealization ⟨Bool⟩ signature := ⟨boundedRead⟩

run_cmd Elab.Command.liftCoreM do
  for (label, statement, clean) in [
      ("NumericMetadataClean", ``AllowlistRules.target, true),
      ("NatLeStatementFence", ``orderTarget, false),
      ("NatLtStatementFence", ``strictOrderTarget, false)] do
    let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog statement ``bounded
    if clean == result.isNone then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {result}"
end NumericMetadataFixtures


open Lean LeanInformationAudit LeanInformationAudit.RegistrationGates
namespace ReviewTestsA7

theorem target : (137 : Nat) = 137 := rfl

def signature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CorrectnessExternalRound4.StatementResult

def bare : StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨CorrectnessExternalRound4.valuedResult⟩
def eta : StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨fun index bit => CorrectnessExternalRound4.valuedResult index bit⟩
def literal : StructuralPrimitiveRealization ⟨Bool⟩ signature :=
  ⟨fun (_ : Unit) bit => ⟨⟨rfl⟩, bit⟩⟩

def cleanSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => CorrectnessExternalRound4.CleanResult
def clean : StructuralPrimitiveRealization ⟨Bool⟩ cleanSignature :=
  ⟨CorrectnessExternalRound4.cleanResult⟩
def cleanEta : StructuralPrimitiveRealization ⟨Bool⟩ cleanSignature :=
  ⟨fun index bit => CorrectnessExternalRound4.cleanResult index bit⟩

def nestedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ReviewTestsA7External.NestedResult
def nested : StructuralPrimitiveRealization ⟨Bool⟩ nestedSignature :=
  ⟨ReviewTestsA7External.nestedResult⟩
def cleanNestedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ReviewTestsA7External.CleanNestedResult
def cleanNested : StructuralPrimitiveRealization ⟨Bool⟩ cleanNestedSignature :=
  ⟨ReviewTestsA7External.cleanNestedResult⟩

def instanceSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ReviewTestsA7External.InstanceResult
def instanceReadout : StructuralPrimitiveRealization ⟨Bool⟩ instanceSignature :=
  ⟨ReviewTestsA7External.instanceResult⟩
def cleanInstanceSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => ReviewTestsA7External.CleanInstanceResult
def cleanInstance : StructuralPrimitiveRealization ⟨Bool⟩ cleanInstanceSignature :=
  ⟨ReviewTestsA7External.cleanInstanceResult⟩

run_cmd Elab.Command.liftTermElabM do
  for alternative in [``eta, ``literal] do
    unless ← Meta.isDefEq (mkConst ``bare) (mkConst alternative) do
      throwError "[FAIL] A7NominalShape: {alternative}"
  let env ← getEnv
  for name in [``CorrectnessExternalRound4.valuedResult,
      ``ReviewTestsA7External.nestedResult, ``ReviewTestsA7External.instanceResult] do
    let some index := env.getModuleIdxFor? name
      | throwError "[FAIL] A7ExternalShape: {name}"
    logInfo m!"[PASS] A7ExternalShape {name}: {env.header.modules[index.toNat]!.module}"
  let info ← getConstInfo ``ReviewTestsA7External.InstanceResult.mk
  Meta.forallTelescope info.type fun params _ => do
    let mut found := false
    for param in params do
      let decl ← param.fvarId!.getDecl
      if decl.binderInfo == .instImplicit && decl.type.isAppOf ``Inhabited then
        found := true
    unless found do throwError "[FAIL] A7InstanceBinderShape: missing Inhabited instance binder"
  logInfo "[PASS] A7NominalShape"
  logInfo "[PASS] A7InstanceBinderShape: Inhabited instance argument contains nominal proof record"

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  for (label, holder) in [("A7NominalBare", ``bare), ("A7NominalEta", ``eta),
      ("A7NominalLiteral", ``literal), ("A7NestedProofField", ``nested),
      ("A7KnownInstanceProofField", ``instanceReadout)] do
    let result ← provenanceErrorCurrent env.header.mainModule `catalog ``target holder
    logInfo m!"[OBSERVED] {label}: {result}"
    match result with
    | none => logError m!"[FAIL] {label}: false admission; missing IE-C050"
    | some message =>
      if message.startsWith "IE-C050 ClosedTruthReadout " then
        logInfo m!"[PASS] {label}: {message}"
      else logError m!"[FAIL] {label}: unexpected {message}"
  for (label, holder) in [("A7CleanBare", ``clean), ("A7CleanEta", ``cleanEta),
      ("A7CleanNested", ``cleanNested), ("A7CleanInstance", ``cleanInstance)] do
    let result ← provenanceErrorCurrent env.header.mainModule `catalog ``target holder
    if result.isNone then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: unexpected {result}"

end ReviewTestsA7

namespace ListMetadataFixtures
theorem existsTarget : ∃ k : Nat, k = 137 := ⟨137, rfl⟩
theorem notExistsTarget : ¬ (∃ k : Nat, k + 1 = 0) := by simp
theorem functionTarget : ∀ b ∈ ([0] : List Nat), 137 ≠ b := by simp
def rangeSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => UniqueRange
def rangeRealization : StructuralPrimitiveRealization ⟨Bool⟩ rangeSignature := ⟨uniqueRead⟩
def predicateSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PredicatePairwise
def predicateRealization : StructuralPrimitiveRealization ⟨Bool⟩ predicateSignature := ⟨predicateRead⟩
def literalSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => UniqueLiteral
def literalRealization : StructuralPrimitiveRealization ⟨Bool⟩ literalSignature := ⟨literalRead⟩
run_cmd Elab.Command.liftCoreM do
  for (label, statement, holder, clean) in [
      ("SymbolicNodupExistsClean", ``existsTarget, ``rangeRealization, true),
      ("SymbolicNodupNegExistsClean", ``notExistsTarget, ``rangeRealization, true),
      ("PairwisePredicatePayload", ``existsTarget, ``predicateRealization, false),
      ("NodupFunctionPayload", ``functionTarget, ``literalRealization, false)] do
    let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog statement holder
    if clean == result.isNone then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {result}"
end ListMetadataFixtures

namespace ListMetadataFixtures
def propositionSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PropositionUnique
def propositionRealization : StructuralPrimitiveRealization ⟨Bool⟩ propositionSignature :=
  ⟨propositionRead⟩
run_cmd Elab.Command.liftCoreM do
  let result ← provenanceErrorCurrent (← getEnv).header.mainModule
    `catalog ``existsTarget ``propositionRealization
  if result.isSome then logInfo "[PASS] PropositionNodupPayload"
  else logError "[FAIL] PropositionNodupPayload: list element hides the registered proposition"
end ListMetadataFixtures

namespace ListMetadataFixtures
def polymorphicSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => Bool
def polymorphicRealization : StructuralPrimitiveRealization ⟨Bool⟩ polymorphicSignature :=
  ⟨fun i bit => mapProofRead (fun n : Nat => n) [] .nil i bit⟩
def indexedSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => TypeIndexed Prop
def indexedRealization : StructuralPrimitiveRealization ⟨Bool⟩ indexedSignature :=
  ⟨indexedRead Prop rfl⟩
def letPropositionSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => LetPropositionUnique
def letPropositionRealization : StructuralPrimitiveRealization ⟨Bool⟩ letPropositionSignature :=
  ⟨letPropositionRead⟩
run_cmd Elab.Command.liftCoreM do
  for (label, statement, holder, clean) in [
      ("PolymorphicNodupExistsClean", ``existsTarget, ``polymorphicRealization, true),
      ("PolymorphicNodupNegExistsClean", ``notExistsTarget, ``polymorphicRealization, true),
      ("IndexedPropositionNodupPayload", ``existsTarget, ``indexedRealization, false),
      ("LetPropositionNodupPayload", ``existsTarget, ``letPropositionRealization, false)] do
    let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog statement holder
    if label == "IndexedPropositionNodupPayload" || label == "PropositionMemPayload" then
      logInfo m!"[LIST-DIAGNOSTIC] {label}: {result}"
    if clean == result.isNone then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {result}"
end ListMetadataFixtures

namespace ListMetadataFixtures
def enumMemRealization : StructuralPrimitiveRealization ⟨Bool⟩ polymorphicSignature :=
  ⟨fun i bit => enumMemRead .left (.tail _ (.head _)) i bit⟩
def propositionMemSignature : StructuralPrimitiveSignature where
  Index := Unit
  indexFintype := inferInstance
  Output := fun _ => PropositionMember
def propositionMemRealization : StructuralPrimitiveRealization ⟨Bool⟩ propositionMemSignature :=
  ⟨propositionMemRead⟩
run_cmd Elab.Command.liftCoreM do
  for (label, statement, holder, clean) in [
      ("EnumMemExistsClean", ``existsTarget, ``enumMemRealization, true),
      ("EnumMemNegExistsClean", ``notExistsTarget, ``enumMemRealization, true),
      ("PropositionMemPayload", ``existsTarget, ``propositionMemRealization, false)] do
    let result ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog statement holder
    if label == "IndexedPropositionNodupPayload" || label == "PropositionMemPayload" then
      logInfo m!"[LIST-DIAGNOSTIC] {label}: {result}"
    if clean == result.isNone then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {result}"
end ListMetadataFixtures
