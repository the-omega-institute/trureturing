import LeanInformationAudit.Tests.RegistrationGates.Provenance

open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace RegistrationProvenance

theorem rawTruth : True := True.intro
def rawProofRead (_ : Unit) (x : Bool) : Bool := let _ := True.intro; x
check_provenance "RawProofTerm" using rawProofRead expects "forbidden_dependency" for rawTruth
theorem independentProof : True := True.intro
def independentRead (_ : Unit) (x : Bool) : Bool := let _ := independentProof; x
check_provenance "IndependentProofConstant" using independentRead expects "forbidden_dependency" for truth

abbrev Statement : Prop := True
theorem aliasHelper : Statement := True.intro
theorem aliasBridge : True := aliasHelper
theorem aliasRegistered : True := aliasBridge
def aliasRead (_ : Unit) (x : Bool) : Bool := let _ := aliasHelper; x
check_provenance "ProofAlias" using aliasRead expects "forbidden_dependency" for aliasRegistered
theorem deepHelper : True ∧ True := ⟨True.intro, True.intro⟩
theorem deepBridge : True := deepHelper.1
theorem deepRegistered : True := deepBridge
def deepRead (_ : Unit) (x : Bool) : Bool := let _ := deepHelper; x
check_provenance "TransitiveProofDependency" using deepRead expects "forbidden_dependency" for deepRegistered

def decisionProposition : Prop := (137 : Nat) + 0 = 137
example : decisionProposition = specificStatement := rfl
noncomputable def defeqDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide decisionProposition (Classical.propDecidable decisionProposition) then x else false
check_provenance "DefeqDecision" using defeqDecisionRead expects "unclassified_form" for specificTruth
noncomputable def unrelatedDecisionRead (_ : Unit) (x : Bool) : Bool :=
  if @decide (x = true) (Classical.propDecidable (x = true)) then x else false
check_provenance "UnrelatedBinderDecision" using unrelatedDecisionRead expects "unclassified_form" for specificTruth
check_provenance "AppliedDecidableFinite" using genericDecision expects "unclassified_form" for specificTruth

def computedKey : Name := Name.str (Name.mkSimple "RegistrationProvenance") "truth"
example : computedKey = ``truth := rfl
def computedCert : Certificate computedKey := ⟨true⟩
def computedRead (_ : Unit) (x : Bool) : Bool := cond computedCert.bit x true
check_provenance "ComputedName" using computedRead expects "clean" for truth
run_cmd Elab.Command.liftTermElabM do
  let info ← getConstInfo ``specificTruth
  let digest := Sha256.hex (toString info.type).toUTF8
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.computedDigest, levelParams := [], type := mkConst ``String
    value := mkApp2 (mkConst ``String.append) (mkStrLit "sha256:") (mkStrLit digest)
    hints := .abbrev, safety := .safe }
  unless ← Meta.isDefEq (mkConst `RegistrationProvenance.computedDigest)
      (mkStrLit (theoremStatementIdentity (← getEnv) ``specificTruth)) do
    throwError "fixture digest is not the registered identity"
def computedDigestRead (_ : Unit) (x : Bool) : Bool := let _ := computedDigest; x
check_provenance "ComputedDigest" using computedDigestRead expects "clean" for specificTruth

def registryRead (env : Environment) : String :=
  ((InformationRegistry.find? env computedKey).map (·.statementIdentity)).getD ""
def registryIdentityRead (_ : Unit) (x : Bool) : Bool := let _ := registryRead; x
run_cmd do
  let env ← getEnv
  unless registryRead env == theoremStatementIdentity env ``truth && !(registryRead env).isEmpty do
    throwError "fixture registry lookup does not return registered identity"
check_provenance "RegistryIdentity" using registryIdentityRead expects "forbidden_dependency" for truth
-- Both real command paths must publish IE-C050 for the escaped sources.
def aliasReads : PrimitiveRealization RegistrationPositive.arena.signature := ⟨aliasRead, Fin.elim0⟩
local instance : DecidableEq RegistrationPositive.arena.State :=
  RegistrationPositive.arena.toArena.stateDecidableEq
theorem aliasRealization : LegacyPrimitiveRealization RegistrationPositive.arena True aliasReads :=
  ⟨⟨fun _ => rfl, fun _ => True.intro⟩⟩
register_information_theorem aliasRegistered in RegistrationPositive.arena
  primitives aliasReads.toPrimitiveBundle realization aliasRealization
  variation RegistrationPositive.lawVariation sensitivity RegistrationPositive.slotSensitivity
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``aliasRegistered
    | throwError "missing registered fixture"
  let actual ← RegistrationGates.validateFinite entry
  let published := (← getConstInfo
    (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)).value!
  unless (actual.getD "").startsWith "IE-C050 ClosedTruthReadout " &&
      ((actual.getD "").splitOn "reason=forbidden_dependency").length == 2 &&
      published == mkStrLit (actual.getD "") do throwError "[FAIL] EscapeRegistrationFinite: {actual}"
  logInfo "[PASS] EscapeRegistrationFinite"
def structuralKey : Name := Name.str (Name.mkSimple "RegistrationProvenance") "escapedStructural"
def escapedCert : Certificate structuralKey := ⟨true⟩
def escapedRead (_ : Unit) (x : Nat) : Nat :=
  let _ := StatementKey.mk
  if escapedCert.bit then x else 0
structural_theorem escapedStructural in RegistrationStructural.law
  realization ⟨escapedRead⟩ nondegeneracy RegistrationStructural.lawVariation
  sensitivity RegistrationStructural.slotSensitivity := rfl
example : structuralKey = ``escapedStructural := rfl
run_cmd Elab.Command.liftTermElabM do
  let entry := ((structuralProvenanceEntries (← getEnv)).find?
    (·.theoremName == ``escapedStructural)).get!
  let actual ← RegistrationGates.validateStructural entry
  let published := (← getConstInfo
    (RegistrationGates.diagnosticName entry.unitConst entry.registrationModule)).value!
  unless (actual.getD "").startsWith "IE-C050 ClosedTruthReadout " &&
      ((actual.getD "").splitOn "reason=forbidden_dependency").length == 2 &&
      published == mkStrLit (actual.getD "") do throwError "[FAIL] EscapeRegistrationStructural: {actual}"
  logInfo "[PASS] EscapeRegistrationStructural"

-- The allowlist rejects this Classical decision without reducing its expensive argument.
def expensive : Nat → Nat
  | 0 => 1
  | n + 1 => expensive n + expensive n
theorem expensiveTruth : expensive 10000 = expensive 10000 := rfl
noncomputable def expensiveDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide (expensive 10000 = 0) (Classical.propDecidable _) then x else false
check_provenance "ClassicalExpensiveArgument" using expensiveDecision expects "unclassified_form" for expensiveTruth

def independentAliasRead (_ : Unit) (x : Bool) : Bool := let _ := aliasHelper; x
check_provenance "IndependentProofAlias" using independentAliasRead expects "forbidden_dependency" for truth

run_cmd Elab.Command.liftTermElabM do
  let type := (← getConstInfo ``truthReads).type
  for i in [:300] do
    let name := `RegistrationProvenance.forward |>.num i
    let prev := if i == 0 then ``truthReads else `RegistrationProvenance.forward |>.num (i-1)
    addDecl <| .defnDecl {
      name, levelParams := [], type, value := mkConst prev,
      hints := .abbrev, safety := .safe }
  let some entry := InformationRegistry.find? (← getEnv) ``truth | throwError "fixture"
  let actual ← RegistrationGates.validateFinite
    { entry with realizationName := `RegistrationProvenance.forward |>.num 299 }
  unless ((actual.getD "").splitOn "reason=incomplete_closure provenance=null").length == 2 do
    throwError "[FAIL] ForwardingExhaustion"
  logInfo "[PASS] ForwardingExhaustion"

run_cmd Elab.Command.liftTermElabM do
  let mut type := mkApp (mkConst ``Decidable) (.bvar 257)
  let mut value := mkApp (mkConst ``Classical.propDecidable) (.bvar 257)
  for _ in [:257] do
    type := mkForall `x .default (mkConst ``Bool) type
    value := mkLambda `x .default (mkConst ``Bool) value
  type := mkForall `p .default (.sort .zero) type
  value := mkLambda `p .default (.sort .zero) value
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.wideDecision, levelParams := [],
    type, value, hints := .abbrev, safety := .safe }
  let instanceTerm := mkAppN (mkConst `RegistrationProvenance.wideDecision)
    (#[mkConst ``specificStatement] ++ Array.replicate 257 (.bvar 0))
  let decision := mkApp2 (mkConst ``Decidable.decide) (mkConst ``specificStatement) instanceTerm
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.wideRead, levelParams := [],
    type := (← getConstInfo ``clean).type,
    value := mkLambda `i .default (mkConst ``Unit) (mkLambda `x .default (mkConst ``Bool) decision),
    hints := .abbrev, safety := .safe }
check_provenance "TypeArgumentExhaustion" using wideRead expects "unclassified_form" for specificTruth

run_cmd Elab.Command.liftTermElabM do
  for i in [:4100] do
    let name := `RegistrationProvenance.proofChain |>.num i
    let prev := if i == 0 then ``rawTruth else `RegistrationProvenance.proofChain |>.num (i-1)
    addDecl <| .thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst prev }
  addDecl <| .thmDecl {
    name := `RegistrationProvenance.proofBudgetTruth, levelParams := [],
    type := mkConst ``True, value := mkConst (`RegistrationProvenance.proofChain |>.num 4099) }
def proofBudgetRead (_ : Unit) (x : Bool) : Bool := let _ := proofBudgetTruth; x
check_provenance "ProofScanExhaustion" using proofBudgetRead expects "incomplete_closure" for specificTruth

end RegistrationProvenance
