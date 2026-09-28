import LeanInformationAudit.Tests.RegistrationGates.DeclaredStructural
import InformationSourceFixture

namespace LeanInformationAudit.Tests.DeclaredIndependentSources
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape
open DeclaredStructural (template)

abbrev arena : StructuralArena := ⟨Int⟩
def signature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Nat⟩
def law : StructuralPrimitiveLawArena arena where
  signature := signature
  Law r := ∀ x : Int, r.readout () x = Int.natAbs x

structural_theorem independentSource in law
  readout via (template arena signature (fun _ => Int.natAbs))
  realization (template arena signature (fun _ => Int.natAbs)) := by
    intro x
    rfl

abbrev fixtureArena : StructuralArena := ⟨Option Int⟩
def fixtureSignature : StructuralPrimitiveSignature := ⟨Unit, inferInstance, fun _ => Bool⟩
def fixtureLaw : StructuralPrimitiveLawArena fixtureArena where
  signature := fixtureSignature
  Law r := ∀ x : Option Int, r.readout () x = InformationSourceFixture.compositeReadout x

structural_theorem judgePackageSource in fixtureLaw
  readout via (template fixtureArena fixtureSignature
    (fun _ => InformationSourceFixture.compositeReadout))
  realization (template fixtureArena fixtureSignature
    (fun _ => InformationSourceFixture.compositeReadout)) := by
    intro x
    rfl

run_meta do
  let some record := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``independentSource)
    | throwError "setup: missing independent source binding"
  let .declaredValidated certificate := record.result
    | throwError "[FAIL] independent_standard_source_binding_validated"
  logInfo "[PASS] independent_standard_source_binding_validated"
  let some source := certificate.argumentInputs.find?
      (·.name == ``Int.natAbs)
    | throwError "[FAIL] independent_source_binding_retains_native_identities"
  unless source.typeIdentity.length == 64 &&
      source.bodyIdentity.length == 64 do
    throwError "[FAIL] independent_source_binding_retains_native_identities"
  logInfo "[PASS] independent_source_binding_retains_native_identities"
  let some fixture := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``judgePackageSource)
    | throwError "setup: missing judge package source binding"
  unless fixture.result matches .declaredUnresolved _ do
    throwError "[FAIL] judge_package_source_rejected"
  logInfo "[PASS] judge_package_source_rejected"

-- Exercise production reachability without publishing a checker API.
-- Each assessment owns one target/import graph and starts with an empty memo.
run_cmd do
  let resolve (userName : Name) : CommandElabM (TSyntax `ident) := do
    let declarations := (← getEnv).constants.toList.filter fun (name, _) =>
      privateToUserName? name == some userName
    unless declarations.length == 1 do throwError "expected one declaration: {userName}"
    return mkIdent declarations.head!.1
  let query ← resolve `LeanInformationAudit.TemplateAudit.independentSource
  let initial ← resolve `LeanInformationAudit.TemplateAudit.CompileState.mk
  let remaining ← resolve `LeanInformationAudit.TemplateAudit.CompileState.remaining
  elabCommand (← `(command| run_meta do
    let source := ``Int.natAbs
    let sibling := ``Int.negSucc
    let env ← getEnv
    unless env.getModuleIdxFor? source == env.getModuleIdxFor? sibling do
      throwError "setup: source declarations must share one owner"
    let identity ← RegistrationGates.argumentIdentityState ``True.intro 524288
    let (independent, state) ← ($query source).run
      ($initial 524288 (some identity) #[] #[] {} {} {})
    if independent then throwError "[FAIL] transitive_source_dependency_rejected"
    let used := 524288 - $remaining state
    unless used > 0 do throwError "setup: expected a real import traversal"
    -- Repeated owners and a transitive import fit one completed traversal's work.
    let twice := do
      let first ← ($query source)
      let second ← ($query sibling)
      let ancestor ← ($query ``True.intro)
      return (first, second, ancestor)
    let (answers, state) ← twice.run ($initial used (some identity) #[] #[] {} {} {})
    unless answers == (false, false, false) && $remaining state == 0 do
      throwError "[FAIL] dependent_source_memo_preserves_rejection"
    logInfo m!"[PASS] dependent_source_memo_preserves_rejection_without_retraversal work={used}"
    let exhausted ← try
      discard <| ($query source).run ($initial 0 (some identity) #[] #[] {} {} {})
      pure false
    catch error => pure ((← error.toMessageData.toString).contains "E8.work")
    unless exhausted do throwError "[FAIL] uncached_reachability_exhaustion_fails_closed"
    logInfo "[PASS] uncached_reachability_exhaustion_fails_closed"
    -- A fresh assessment must not reuse the previous target's negative answer.
    let other ← RegistrationGates.argumentIdentityState ``TemplateBinding.assess 524288
    let (independent, state) ← ($query source).run
      ($initial 524288 (some other) #[] #[] {} {} {})
    unless independent do throwError "[FAIL] source_memo_is_assessment_local"
    let used := 524288 - $remaining state
    -- The Int import diamond previously queued and charged 23 entries.
    -- Visit each owner once; duplicated edges must fit below that old debit.
    unless used < 23 do
      throwError "[FAIL] independent_source_import_diamond_is_not_retraversed"
    logInfo m!"[PASS] independent_source_import_diamond_is_not_retraversed work={used}"
    let (answers, state) ← twice.run ($initial used (some other) #[] #[] {} {} {})
    unless answers == (true, true, true) && $remaining state == 0 do
      throwError "[FAIL] independent_source_memo_preserves_acceptance"
    logInfo m!"[PASS] source_memo_is_assessment_local_and_preserves_both_answers work={used}"))

end LeanInformationAudit.Tests.DeclaredIndependentSources
