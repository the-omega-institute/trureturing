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

-- Alias/type boundaries reject without tracing independent proof bodies or
-- claiming semantic equality with a differently written proposition.
abbrev Statement : Prop := True
theorem aliasHelper : Statement := True.intro
theorem aliasBridge : True := aliasHelper
theorem aliasRegistered : True := aliasBridge
def aliasRead (_ : Unit) (x : Bool) : Bool := let _ := aliasHelper; x
check_provenance "ProofAlias" using aliasRead expects "unclassified_form" for aliasRegistered
theorem deepHelper : True ∧ True := ⟨True.intro, True.intro⟩
theorem deepBridge : True := deepHelper.1
theorem deepRegistered : True := deepBridge
def deepRead (_ : Unit) (x : Bool) : Bool := let _ := deepHelper; x
check_provenance "TransitiveProofDependency" using deepRead expects "unclassified_form" for deepRegistered

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
-- The Environment argument exposes abstract Sigma/Subtype carriers and exhausts
-- the structural type walk. Incomplete takes precedence over the captured API.
check_provenance "RegistryIdentity" using registryIdentityRead expects "incomplete_closure" for truth
run_cmd Elab.Command.liftTermElabM do
  let actual ← RegistrationGates.templateArgumentsCurrent ``truth
    #[mkConst ``InformationRegistryEntry.statementIdentity] 524288
  unless actual matches .error "forbidden_dependency:dtr.argument_audit" do
    throwError "[FAIL] RegistryIdentityArgument: {repr actual}"
  logInfo "[PASS] RegistryIdentityArgument"
-- Both command paths assess declared arguments through the same evidence phase.
-- The generic fixture has no static proof or statement-specific body.
-- Fixed concrete interfaces are checked once at enrollment. Only the readout
-- function is supplied at each occurrence, with the same 524288-work limit.
def finiteSignature : PrimitiveSignature Bool where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def structuralSignature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Nat⟩

def finiteTemplate (f : Unit → Bool → Bool) : PrimitiveRealization finiteSignature :=
  ⟨f, Fin.elim0⟩
register_information_template finiteTemplate

def structuralTemplate (f : Unit → Nat → Nat) :
    StructuralPrimitiveRealization RegistrationStructural.arena structuralSignature := ⟨f⟩
register_information_template structuralTemplate

private def expectBinding (name : Name) (label : String) (reason : Option String) : Meta.MetaM Unit := do
  let rows ← TemplateBinding.assessJoined
  let some row := rows.find? (·.occurrence.key.theoremName == name)
    | throwError "setup: missing binding record {name}"
  let ok := match row.result, reason with
    | .declaredValidated _, none => true
    | .declaredUnresolved diagnostic, some reason =>
        diagnostic.contains s!"reason={reason}"
    | _, _ => false
  let actual := match row.result with
    | .declaredValidated _ => "validated"
    | .declaredUnresolved diagnostic => diagnostic
    | .undeclared => "undeclared"
  unless ok do throwError "[FAIL] {label}: {actual}"
  logInfo m!"[PASS] {label}"

def aliasReads : PrimitiveRealization RegistrationPositive.arena.signature :=
  finiteTemplate (fun i x => aliasRead i x)
local instance : DecidableEq RegistrationPositive.arena.State :=
  RegistrationPositive.arena.toArena.stateDecidableEq
theorem aliasRealization : LegacyPrimitiveRealization RegistrationPositive.arena True aliasReads :=
  ⟨⟨fun _ => rfl, fun _ => True.intro⟩⟩
register_information_theorem aliasRegistered in RegistrationPositive.arena
  readout via (finiteTemplate (fun i x => aliasRead i x))
  primitives aliasReads.toPrimitiveBundle realization aliasRealization
  variation RegistrationPositive.lawVariation sensitivity RegistrationPositive.slotSensitivity
run_cmd Elab.Command.liftTermElabM do
  expectBinding ``aliasRegistered "EscapeRegistrationFinite" (some "unclassified_form rule=E6.argument_identity")

information_theorem cleanFinite in RegistrationPositive.arena
  readout via (finiteTemplate (fun i x => clean i x))
  primitives (finiteTemplate (fun i x => clean i x))
  variation RegistrationPositive.lawVariation sensitivity RegistrationPositive.slotSensitivity
  : RegistrationPositive.arena.Law (finiteTemplate (fun i x => clean i x)) := rfl
run_cmd Elab.Command.liftTermElabM do
  expectBinding ``cleanFinite "DeclaredEscapeCleanFinite" none

def structuralKey : Name := Name.str (Name.mkSimple "RegistrationProvenance") "escapedStructural"
def escapedCert : Certificate structuralKey := ⟨true⟩
def escapedRead (_ : Unit) (x : Nat) : Nat :=
  let _ := StatementKey.mk
  if escapedCert.bit then x else 0
structural_theorem escapedStructural in RegistrationStructural.law
  readout via (structuralTemplate (fun i x => escapedRead i x))
  realization (structuralTemplate (fun i x => escapedRead i x)) nondegeneracy RegistrationStructural.lawVariation
  sensitivity RegistrationStructural.slotSensitivity := rfl
example : structuralKey = ``escapedStructural := rfl
run_cmd Elab.Command.liftTermElabM do
  expectBinding ``escapedStructural "EscapeRegistrationStructural" (some "forbidden_dependency rule=E6.registered_identity")

structural_theorem cleanStructural in RegistrationStructural.law
  readout via (structuralTemplate (fun _ x => x))
  realization (structuralTemplate (fun _ x => x))
  nondegeneracy RegistrationStructural.lawVariation
  sensitivity RegistrationStructural.slotSensitivity := rfl
run_cmd Elab.Command.liftTermElabM do
  expectBinding ``cleanStructural "DeclaredEscapeCleanStructural" none

-- The allowlist rejects this Classical decision without reducing its expensive argument.
def expensive : Nat → Nat
  | 0 => 1
  | n + 1 => expensive n + expensive n
theorem expensiveTruth : expensive 10000 = expensive 10000 := rfl
noncomputable def expensiveDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide (expensive 10000 = 0) (Classical.propDecidable _) then x else false
check_provenance "ClassicalExpensiveArgument" using expensiveDecision expects "unclassified_form" for expensiveTruth

def independentAliasRead (_ : Unit) (x : Bool) : Bool := let _ := aliasHelper; x
check_provenance "IndependentProofAlias" using independentAliasRead expects "unclassified_form" for truth

-- Retain the forwarding limit on the declared actual-extraction path. The
-- retired validateFinite fallback is not an invocation of this checker.
run_cmd Elab.Command.liftTermElabM do
  let some record := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``cleanFinite)
    | throwError "setup: missing forwarding occurrence"
  let some descriptor := record.descriptor | throwError "setup: missing forwarding descriptor"
  let type ← Meta.inferType descriptor
  for i in [:300] do
    let name := `RegistrationProvenance.forward |>.num i
    let value := if i == 0 then descriptor else
      mkConst (`RegistrationProvenance.forward |>.num (i-1))
    addDecl <| .defnDecl {
      name, levelParams := [], type, value,
      hints := .abbrev, safety := .safe }
  let claim : TemplateBindingClaim := {
    key := record.occurrence.key, arena := record.occurrence.arena,
    descriptor := some descriptor, owner := (← getEnv).header.mainModule }
  let shallow ← TemplateBinding.assess
    { record.occurrence with realizationName := `RegistrationProvenance.forward |>.num 0 } (some claim)
  unless shallow.result matches .declaredValidated _ do
    let message := match shallow.result with
      | .declaredUnresolved message => message
      | _ => "undeclared"
    throwError "[FAIL] ForwardingShallowControl: {message}"
  logInfo "[PASS] ForwardingShallowControl"
  let deep ← TemplateBinding.assess
    { record.occurrence with realizationName := `RegistrationProvenance.forward |>.num 299 } (some claim)
  let actual := match deep.result with
    | .declaredUnresolved message => message
    | .declaredValidated _ => "validated"
    | .undeclared => "undeclared"
  -- This chain exhausts cumulative identity work before the depth cap. The
  -- error must remain unresolved, with no certificate and no larger budget.
  unless actual.contains "reason=incomplete_closure rule=E7.type_identity" do
    throwError "[FAIL] ForwardingExhaustion: {actual}"
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
-- Proof implementation size is outside executable provenance. FuelExhaustion
-- and ExpressionExhaustion independently retain executable-work limits.
check_provenance "IndependentProofBodyErased" using proofBudgetRead expects "clean" for specificTruth

end RegistrationProvenance
