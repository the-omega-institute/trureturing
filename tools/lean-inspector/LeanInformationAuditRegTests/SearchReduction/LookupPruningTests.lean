import LeanInformationAuditRegTests.SearchReduction.LookupModel
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline
import LeanInformationAuditRegAnalysis.SearchReduction.Local

/-! Non-occurrence, premise matching, instance outputs, dependent types,
universe specialization and value-dependent Subtype projection boundaries. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let cases ← #[
    (← `(∀ _n : Nat, True), true),
    (← `(∀ n : Nat, n = n), false),
    (← `(∀ n : Nat, Mark n → Finish), false),
    (← `(∀ (n : Nat) [Certified n], Finish), false),
    (← `(∀ _n : Nat, {k : Nat // DataMark k}), false),
    (← `(∀ (α : Type) (_x : α), True), true),
    (← `(∀ (α : Type) (x : α), x = x), false),
    (← `(∀ _n : Nat, Nat), true),
    (← `(∀ (p : Prop) (_h : p), p), false),
    (← `(∀ (α : Type) [Inhabited α], True), false),
    (← `(∀ _p : Prop, True), true),
    (← `(∀ (_n : Nat) [Inhabited Nat], True), true),
    (← `(∀ (α : Type) (x : α) (_h : x = x), True), false)].mapM fun (stx, expected) => do
      let type ← Term.elabType stx
      Term.synthesizeSyntheticMVarsNoPostponing
      return (← instantiateMVars type, expected)
  for h : i in [:cases.size] do
    let (type, expected) := cases[i]
    let actual ← starCandidateImpossible type
    unless actual == expected do
      throwError "static star boundary {i}: expected {expected}, got {actual}: {type}"
  let polymorphic := mkForall `α .default (mkSort (.param `u))
    (mkForall `x .default (mkBVar 0) (mkConst ``True))
  if ← starCandidateImpossible polymorphic then
    throwError "sort-polymorphic data may become a proposition obligation"
  logInfo m!"STATIC_STAR_BOUNDARIES cases={cases.size + 1} passed=true"

open LeanInformationAudit.Tests.SearchReduction.GraphModel
#print axioms static_star_impossible_no_certificate

run_cmd liftTermElabM do
  let env := (← getEnv).setExporting false
  let table : LookupTable := {environment := env}
  let entries := DiskLookup.membershipEntries
    "LeanInformationAuditRegTests.SearchReduction.LookupBaseline"
    #[#[← getConstInfo ``instanceHiddenForm, ← getConstInfo ``unusedData,
      ← getConstInfo ``certifiedData]]
  for entry in entries do
    let original ← saveState
    let info ← getConstInfo entry.leanName
    let rejected ← starCandidateImpossible info.type
    let expectFailure := entry.leanName == ``unusedData
    unless rejected == expectFailure do
      throwError "wrong static boundary for {entry.leanName}"
    let target := if entry.leanName == ``certifiedData then
        mkApp (mkConst ``DataMark) (mkNatLit 11)
      else mkConst ``Finish
    let goal ← mkFreshExprMVar target
    let trace ← attemptLookupLeaf table entry goal.mvarId!
      (fun _ => pure false) (fun _ => pure false)
    unless trace.complete && trace.source?.isSome == !expectFailure do
      throwError "production candidate result disagrees for {entry.leanName}"
    unless expectFailure do checkLocalProof target (← instantiateMVars goal)
    original.restore
  logInfo "STATIC_STAR_RUNTIME instance_outparam=true subtype_computation=true unused_data=true"
