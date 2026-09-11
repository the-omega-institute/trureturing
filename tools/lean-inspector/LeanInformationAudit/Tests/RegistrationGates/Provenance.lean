import LeanInformationAudit.Tests.RegistrationGates.Positive
import LeanInformationAudit.Tests.RegistrationGates.Structural
import LeanInformationAudit.Tests.RegistrationGates.P2Padding

open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace RegistrationProvenance

theorem proofSource : True ∧ True := ⟨True.intro, True.intro⟩
theorem numberProof (n : Nat) : n = n := rfl
theorem truth : True := let _ := numberProof 0; proofSource.1
instance statementDecision : Decidable True := .isTrue True.intro
structure Certificate (theoremName : Name) where
  bit : Bool
def certificate : Certificate ``truth := ⟨false⟩
def identitySource : Name := ``truth
def viaTruth (_ : Unit) (x : Bool) : Bool := let _ := truth; x
def viaAppliedProof (_ : Unit) (x : Bool) : Bool := let _ := numberProof 0; x
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
elab "check_provenance " label:str " using " readout:ident " expects " reason:str " for " theoremName:ident : command => do
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
    let entry := { entry with theoremName := `RegistrationProvenance ++ theoremName.getId }
    let actual ← tryCatchRuntimeEx
      (RegistrationGates.validateFinite { entry with realizationName := holder })
      (fun _ => throwError "[FAIL] {label.getString}: uncaught provenance exhaustion")
    let ok := match actual with
      | none => reason.getString == "clean"
      | some message => message.startsWith "IE-C050 ClosedTruthReadout key=" &&
          (message.splitOn s!" reason={reason.getString} provenance=").length == 2 &&
          (message.splitOn "IE-C021").length == 1
    if let some message := actual then
      let pieces := message.splitOn " provenance="
      let payload := pieces.getLast!
      let expectedKey := s!"key={entry.registrationModuleName}/{entry.effectiveCatalogId}/{entry.theoremName}"
      unless (message.splitOn expectedKey).length == 2 &&
          (message.splitOn s!"readout={n}").length == 2 do
        throwError "[FAIL] {label.getString}: diagnostic keys"
      if reason.getString == "incomplete_closure" then
        unless payload == "null" do throwError "[FAIL] {label.getString}: partial closure"
      else if let .ok json := Json.parse payload then
        if let .ok names := fromJson? (α := Array String) json then
          unless names == names.qsort (· < ·) && names.toList.eraseDups.length == names.size &&
              names.contains n.toString do throwError "[FAIL] {label.getString}: canonical closure"
        else throwError "[FAIL] {label.getString}: non-array closure"
      else throwError "[FAIL] {label.getString}: invalid JSON"
    unless ok do throwError "[FAIL] {label.getString}: {actual}"
    logInfo m!"[PASS] {label.getString}"

check_provenance "TheoremTruth" using viaTruth expects "forbidden_dependency" for truth
check_provenance "AppliedProof" using viaAppliedProof expects "forbidden_dependency" for truth
check_provenance "ProofConstant" using viaProof expects "forbidden_dependency" for truth
check_provenance "StatementDecidable" using viaDecision expects "forbidden_dependency" for truth
check_provenance "TheoremCertificate" using viaCertificate expects "forbidden_dependency" for truth
check_provenance "StatementIdentity" using viaIdentity expects "forbidden_dependency" for truth
check_provenance "CleanReadout" using clean expects "clean" for truth
check_provenance "C050BeforeC021" using constantTruth expects "forbidden_dependency" for truth

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
check_provenance "FuelExhaustion" using exhausted expects "incomplete_closure" for truth

-- Unobtainable dependency, isolated to this synthetic environment.
run_cmd Elab.Command.liftTermElabM do
  addDecl <| .axiomDecl {
    name := `RegistrationProvenance.unavailable
    levelParams := [], type := (← getConstInfo ``clean).type, isUnsafe := false }
check_provenance "UnavailableDefinition" using unavailable expects "incomplete_closure" for truth
noncomputable def unavailableAlias := unavailable
check_provenance "UnavailableAlias" using unavailableAlias expects "incomplete_closure" for truth

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
-- A complete clean closure is asserted independently of the collector.
run_cmd do
  let actual ← Elab.Command.liftCoreM <| RegistrationGates.readoutClosure (← getEnv) ``truth (mkConst ``clean)
  unless actual == (false, some #["Bool", "PUnit", "RegistrationProvenance.clean", "Unit"]) do
    throwError "[FAIL] CanonicalClosure: {repr actual}"
  logInfo "[PASS] CanonicalClosure"
run_cmd Elab.Command.liftTermElabM do
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.typeTruth, levelParams := []
    type := .letE `evidence (mkConst ``True) (mkConst ``truth)
      (← getConstInfo ``clean).type false
    value := mkConst ``clean, hints := .abbrev, safety := .safe }
check_provenance "TypeDependency" using typeTruth expects "forbidden_dependency" for truth

-- 65536 distinct leaves in a balanced term exhaust the expression budget
-- while using only a handful of constants; no time-based assertion is involved.
set_option maxHeartbeats 2000000 in
run_cmd Elab.Command.liftTermElabM do
  let mut layer := (List.range 65536).toArray.map mkNatLit
  while layer.size > 1 do
    layer := (List.range (layer.size / 2)).toArray.map fun i =>
      mkApp2 (mkConst ``Nat.add) layer[2*i]! layer[2*i+1]!
  let value := mkLambda `i .default (mkConst ``Unit) <|
    mkLambda `x .default (mkConst ``Bool) <|
      .letE `ignored (mkConst ``Nat) layer[0]! (.bvar 1) false
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.expressionExhausted
    levelParams := [], type := (← getConstInfo ``clean).type, value
    hints := .abbrev, safety := .safe }
check_provenance "ExpressionExhaustion" using expressionExhausted expects "incomplete_closure" for truth

abbrev boolArena : StructuralArena := ⟨Bool⟩
def boolLaw : StructuralPrimitiveLawArena boolArena where
  signature := ⟨Unit, inferInstance, fun _ => Bool⟩
  Law r := r.readout () false = true
def structuralCert : Certificate `RegistrationProvenance.structuralConstant := ⟨true⟩
structural_theorem structuralConstant in boolLaw
  realization ⟨fun _ _ => structuralCert.bit⟩ := rfl
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find?
    (·.theoremName == ``structuralConstant)).get!
  let actual ← RegistrationGates.validateStructural entry
  unless (actual.getD "").startsWith "IE-C050 ClosedTruthReadout " &&
      ((actual.getD "").splitOn " reason=forbidden_dependency provenance=").length == 2 do
    throwError "[FAIL] StructuralC050BeforeC021: {actual}"
  logInfo "[PASS] StructuralC050BeforeC021"
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``truth | throwError "missing entry"
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.statementDigest, levelParams := [], type := mkConst ``String
    value := mkStrLit entry.statementIdentity, hints := .abbrev, safety := .safe }
def viaDigest (_ : Unit) (x : Bool) : Bool := let _ := statementDigest; x
check_provenance "StatementDigest" using viaDigest expects "forbidden_dependency" for truth
def specificStatement : Prop := (137 : Nat) = 137
theorem specificTruth : specificStatement := rfl
noncomputable def genericDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (Classical.propDecidable specificStatement) then x else true
run_cmd do
  let (forbidden, closure) ← Elab.Command.liftCoreM <| RegistrationGates.readoutClosure (← getEnv)
    ``specificTruth (mkConst ``genericDecision)
  unless forbidden && closure.isSome do
    throwError "[FAIL] AppliedDecidable: {forbidden}, {closure.isSome}"
  logInfo "[PASS] AppliedDecidable"
noncomputable def parameterDecision (p : Prop) (_ : Bool) : Decidable p := Classical.propDecidable p
noncomputable def openDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (parameterDecision specificStatement x) then x else true
run_cmd do
  let (forbidden, closure) ← Elab.Command.liftCoreM <| RegistrationGates.readoutClosure (← getEnv)
    ``specificTruth (mkConst ``openDecision)
  unless forbidden && closure.isSome do throwError "[FAIL] OpenAppliedDecidable"
  logInfo "[PASS] OpenAppliedDecidable"
run_cmd do
  let env ← getEnv
  for (name, label) in [( ``RegistrationPositive.source, "CleanInlineFinite"),
      (``P2Padding.source, "CleanBranchReadout")] do
    let some entry := InformationRegistry.find? env name | throwError "missing fixture entry"
    let actual ← Elab.Command.liftCoreM <| RegistrationGates.provenanceError env entry.registrationModuleName
      entry.effectiveCatalogId entry.theoremName entry.realizationName
    if actual.isSome then logError m!"[FAIL] {label}: {actual}"
    else logInfo m!"[PASS] {label}"
run_cmd do
  let env ← getEnv
  let entry := ((structuralProvenanceEntries env).find?
    (·.theoremName == ``RegistrationStructural.positive)).get!
  let actual ← Elab.Command.liftCoreM <| RegistrationGates.provenanceError env entry.registrationModule
    entry.canonicalArena entry.theoremName entry.realizationConst
  unless actual.isNone do throwError "[FAIL] CleanInlineStructural: {actual}"
  logInfo "[PASS] CleanInlineStructural"
end RegistrationProvenance
