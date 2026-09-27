import LeanInformationAudit.Syntax
import InformationSourceFixture
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredArguments
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape

theorem target : (137 : Nat) = 137 := rfl
theorem identityTarget : ∀ x : Bool, x = x.not.not := fun x => (Bool.not_not x).symm
theorem independent : True := True.intro
def discardTarget (_ : (137 : Nat) = 137) : Arena := Arena.ofFintype Bool
def discardClean (_ : True) : Arena := Arena.ofFintype Bool
def nestedTarget := Option (Arena.State (discardTarget target))
def nestedClean := Option (Arena.State (discardClean independent))
def closedDecision (_ : Bool) : Bool := decide ((0 : Nat) < 24)
def recursiveArgument (n : Nat) : Bool := Nat.rec true (fun _ b => b) n
def identity (x : Bool) : Bool := x
noncomputable def localChoiceReadout (_ : Int) : Nat :=
  Classical.choice (show Nonempty Nat from ⟨0⟩)
def keep {p : Prop} (_ : p) (x : Bool) : Bool := x
def hidden (x : Bool) : Bool := let h := identityTarget; keep h x
def targetDecision : Decidable (∀ x : Bool, x = x.not.not) := .isTrue identityTarget
structure TargetCarrier where
  bit : Bool
  proof : (137 : Nat) = 137
def carrier : TargetCarrier := ⟨true, rfl⟩
class UnknownCarrier where
  bit : Bool
def unknown : UnknownCarrier := ⟨true⟩
def independentPair : Bool × Bool := (true, false)
def companion.__information_unit (x : Bool) : Bool := x
def proofOnly (_ : ∀ n : Int, True) : Bool := true

private def check (label : String) (argument : Expr) (expected : Option String)
    (work : Nat := 524288) (theoremName : Name := ``target) : MetaM Unit := do
  let saved ← getEnv
  let result ← RegistrationGates.templateArgumentsCurrent theoremName #[argument] work
  let actual := match result with
    | .ok _ => none
    | .error diagnostic => some diagnostic
  setEnv saved
  (if actual == expected then logInfo else logError) m!"[{if actual == expected then "PASS" else "FAIL"}] {label} result={repr actual}"

-- Independently typed arguments pass through the production entry used by
-- TemplateBinding.validate and P1. Every case restores the environment so
-- syntax-summary memoization cannot make the next oracle self-referential.
run_meta do
  let .defnInfo bad ← getConstInfo ``nestedTarget | throwError "setup"
  let .defnInfo clean ← getConstInfo ``nestedClean | throwError "setup"
  check "raw_carrier_target_proof_rejected" bad.value
    (some "forbidden_dependency:dtr.argument_audit")
  check "raw_carrier_clean_twin_accepted" clean.value none
  let .defnInfo closedDecisionInfo ← getConstInfo ``closedDecision | throwError "setup"
  let decisionResult ← RegistrationGates.templateArgumentsCurrent ``target #[closedDecisionInfo.value] 524288
  let rejected := match decisionResult with
    | .error s => s == "unclassified_form:E3.closed_decision"
    | _ => false
  (if rejected then logInfo else logError) m!"[{if rejected then "PASS" else "FAIL"}] argument_closed_decision_grammar_rejected result={repr decisionResult}"
  let .defnInfo recursiveInfo ← getConstInfo ``recursiveArgument | throwError "setup"
  check "argument_unsupported_nat_recursion_rejected" recursiveInfo.value
    (some "unclassified_form:E4.recursion:Nat.rec")
  let .defnInfo identityInfo ← getConstInfo ``identity | throwError "setup"
  check "independent_data_argument_accepted" identityInfo.value none
  check "infinite_carrier_type_accepted" (mkConst ``Int) none
  check "independent_infinite_readout_accepted" (mkConst ``Int.natAbs) none
  check "imported_name_alias_type_rejected" (mkConst ``InformationSourceFixture.NameAlias)
    (some "forbidden_dependency:E6.closed_identity")
  check "imported_name_alias_readout_rejected" (mkConst ``InformationSourceFixture.nameReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.nameReadout")
  check "imported_finite_alias_type_accepted" (mkConst ``InformationSourceFixture.BoolAlias) none
  check "imported_finite_alias_readout_rejected" (mkConst ``InformationSourceFixture.finiteReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.finiteReadout")
  check "imported_finite_composite_readout_rejected"
    (mkConst ``InformationSourceFixture.finiteCompositeReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.finiteCompositeReadout")
  check "imported_erased_carrier_readout_rejected" (mkConst ``InformationSourceFixture.erasedReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.erasedReadout")
  check "imported_alias_raw_argument_rejected"
    (mkApp (mkConst ``InformationSourceFixture.ErasedAlias) (mkConst ``Lean.Name))
    (some "forbidden_dependency:E6.closed_identity")
  check "imported_infinite_alias_type_accepted" (mkConst ``InformationSourceFixture.IntAlias) none
  check "judge_package_alias_readout_rejected" (mkConst ``InformationSourceFixture.aliasReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.aliasReadout")
  check "judge_package_composite_readout_rejected"
    (mkConst ``InformationSourceFixture.compositeReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.compositeReadout")
  check "judge_package_aliased_composite_readout_rejected"
    (mkConst ``InformationSourceFixture.aliasedCompositeReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.aliasedCompositeReadout")
  let metadataSource <- getConstInfo `InformationSourceFixture.metadataReadout
  unless metadataSource.type matches .mdata _ (.forallE ..) do
    throwError "setup: metadata must wrap the whole source function type"
  check "judge_package_metadata_function_readout_rejected"
    (mkConst `InformationSourceFixture.metadataReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.metadataReadout")
  check "independent_dictionary_alias_readout_rejected"
    (mkConst ``InformationSourceFixture.dictionaryReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.dictionaryReadout")
  check "class_only_readout_rejected"
    (mkConst ``InformationSourceFixture.classOnlyReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.classOnlyReadout")
  check "explicit_class_only_readout_rejected"
    (mkConst ``InformationSourceFixture.explicitClassOnlyReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.explicitClassOnlyReadout")
  check "aliased_class_only_readout_rejected"
    (mkConst ``InformationSourceFixture.aliasedClassOnlyReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.aliasedClassOnlyReadout")
  check "judge_package_class_and_infinite_readout_rejected"
    (mkConst ``InformationSourceFixture.classAndInfiniteReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.classAndInfiniteReadout")
  check "independent_output_only_readout_rejected" (mkConst ``InformationSourceFixture.outputOnlyReadout)
    (some "unclassified_form:E5.unsaturated_definition:InformationSourceFixture.outputOnlyReadout")
  check "local_unapplied_readout_rejected" (mkConst ``localChoiceReadout)
    (some "unclassified_form:E5.unsaturated_definition:LeanInformationAudit.Tests.DeclaredArguments.localChoiceReadout")
  let sourceInfo ← getConstInfo ``Int.natAbs
  let (_, sourceTypeWork) ← TemplateAudit.checkExtractionType ``target sourceInfo.type 524288
  unless sourceTypeWork < 524288 do throwError "independent source type exhausted work budget"
  unless ← TemplateAudit.checkIndependentInputCarrier ``target sourceInfo.type 524288 do
    throwError "[FAIL] independent_data_input_carrier"
  logInfo "[PASS] independent_data_input_carrier"
  let proofOnlyType := (← getConstInfo ``proofOnly).type
  if ← TemplateAudit.checkIndependentInputCarrier ``target proofOnlyType 524288 then
    throwError "[FAIL] proof_only_infinite_carrier_rejected"
  logInfo "[PASS] proof_only_infinite_carrier_rejected"
  let infiniteOutput ← mkArrow (mkConst ``Int) (mkConst ``Int)
  let equalityDictionary ← mkAppM ``Classical.decEq #[infiniteOutput]
  check "classical_equality_dictionary_data_rejected" equalityDictionary
    (some "unclassified_form:E2.dictionary_position:Classical.decEq")
  let dictionarySlot ← RegistrationGates.templateArgumentsCurrent ``target
    #[equalityDictionary] 524288 #[] #[true]
  let dictionarySlotAccepted : Bool := match dictionarySlot with
    | .ok _ => true
    | .error _ => false
  (if dictionarySlotAccepted then logInfo else logError)
    m!"[{if dictionarySlotAccepted then "PASS" else "FAIL"}] classical_equality_dictionary_slot_accepted result={repr dictionarySlot}"
  let boolDictionary <- mkAppM ``Classical.decEq #[mkConst ``Bool]
  check "classical_equality_application_data_rejected"
    (mkApp2 boolDictionary (mkConst ``Bool.true) (mkConst ``Bool.false))
    (some "unclassified_form:E2.dictionary_position:Classical.decEq")
  check "constructive_equality_dictionary_data_accepted" (mkConst ``instDecidableEqBool) none
  let signature := mkApp3 (mkConst
    ``D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutSignature)
    (mkConst ``Int) infiniteOutput equalityDictionary
  let resultType <- mkAppM ``PrimitiveRealization #[signature]
  let saved <- getEnv
  try
    let (dependencies, _) <- TemplateAudit.checkExtractionType ``target resultType 524288
    unless dependencies.any (fun dependency => dependency.name == ``Classical.decEq) do
      throwError "setup: classical dictionary dependency was not retained"
    logInfo "[PASS] infinite_function_equality_dictionary_type_accepted"
  catch error =>
    logError m!"[FAIL] infinite_function_equality_dictionary_type_accepted result={error.toMessageData}"
  setEnv saved
  check "independent_proof_and_dictionary_accepted" (mkConst ``independent) none
  check "object_projection_accepted"
    (.proj ``Prod 0 (mkConst ``independentPair)) none
  check "nonindex_numeric_encoding_rejected" (mkNatLit 0)
    (some "unclassified_form:E3.index_encoding:OfNat.ofNat")
  check "nonindex_numeric_literal_rejected" (.lit (.natVal 0))
    (some "unclassified_form:E3.nonindex_literal")
  check "bounded_admitted_arguments_accepted" (mkConst ``Bool.true) none
  check "argument_theorem_direct_rejected" (mkConst ``identityTarget)
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  let .defnInfo hiddenInfo ← getConstInfo ``hidden | throwError "setup"
  check "argument_theorem_helper_let_rejected" hiddenInfo.value
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  check "argument_theorem_instance_rejected" (mkConst ``targetDecision)
    (some "forbidden_dependency:dtr.argument_audit") 524288 ``identityTarget
  let type := (← getConstInfo ``target).type
  let proof ← mkEqRefl (mkNatLit 137)
  check "argument_statement_proof_rejected" proof
    (some "forbidden_dependency:dtr.argument_audit")
  let decision ← mkAppM ``Decidable.isTrue #[proof]
  unless (← inferType decision).isAppOfArity ``Decidable 1 do
    throwError "setup: expected a typed decision"
  check "argument_statement_decision_rejected" decision
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_statement_carrier_rejected" (mkConst ``carrier)
    (some "unclassified_form:E2.unknown_constant:LeanInformationAudit.Tests.DeclaredArguments.TargetCarrier")
  check "argument_certificate_projection_rejected" (mkConst ``InformationRegistryEntry.statementIdentity)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_generated_identity_rejected" (mkConst ``companion.__information_unit)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_statement_hash_rejected" (mkConst ``Sha256.hex)
    (some "forbidden_dependency:dtr.argument_audit")
  check "argument_unknown_carrier_rejected" (mkConst ``unknown)
    (some "unclassified_form:E2.unknown_constant:LeanInformationAudit.Tests.DeclaredArguments.UnknownCarrier")
  check "argument_exhaustion_incomplete" (mkConst ``Bool.true)
    (some "incomplete_closure:E8.argument_work") 0
  unless (← inferType proof).equal type do throwError "setup: statement proof type differs"

end LeanInformationAudit.Tests.DeclaredArguments
