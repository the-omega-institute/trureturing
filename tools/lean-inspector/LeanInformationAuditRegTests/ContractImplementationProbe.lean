import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Controls.Implemented
import Reg.ContractPrototype.Implemented
import Reg.ContractPrototype.Controls.Partial
import Reg.ContractPrototype.Partial
import Reg.ContractPrototype.Controls.Extern
import Reg.ContractPrototype.Extern
import Reg.ContractPrototype.Controls.OpaqueImplemented
import Reg.ContractPrototype.OpaqueImplemented
import Reg.ContractPrototype.Controls.EqPartial
import Reg.ContractPrototype.EqPartial
import Reg.ContractPrototype.Controls.SymbolExtern
import Reg.ContractPrototype.SymbolExtern
import Reg.ContractPrototype.Controls.ValidatedImplemented
import Reg.ContractPrototype.ValidatedImplemented
import Reg.ContractPrototype.Controls.ValidatedPartial
import Reg.ContractPrototype.ValidatedPartial
import Reg.ContractPrototype.Controls.ValidatedExtern
import Reg.ContractPrototype.ValidatedExtern

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

private def withoutClaims (env : Environment) : Environment :=
  (TemplateBinding.ownedEvents env).foldl
    (fun e (_, event) => TemplateBinding.addOccurrence e event)
    (TemplateBinding.resetAssessmentRecords env)

set_option maxHeartbeats 0

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let mode := (← IO.getEnv "STRATALINT_CONTRACT_IMPLEMENTATION_MUTATION").getD "control"
    unless #["control", "old", "new"].contains mode do throwError "implementation_mode"
    let pairs : Array (Name × Name × Bool) := #[
      (`Reg.ContractPrototype.Controls.Implemented, `Reg.ContractPrototype.Implemented, false),
      (`Reg.ContractPrototype.Controls.Partial, `Reg.ContractPrototype.Partial, false),
      (`Reg.ContractPrototype.Controls.Extern, `Reg.ContractPrototype.Extern, false),
      (`Reg.ContractPrototype.Controls.OpaqueImplemented, `Reg.ContractPrototype.OpaqueImplemented, false),
      (`Reg.ContractPrototype.Controls.EqPartial, `Reg.ContractPrototype.EqPartial, false),
      (`Reg.ContractPrototype.Controls.SymbolExtern, `Reg.ContractPrototype.SymbolExtern, false),
      (`Reg.ContractPrototype.Controls.ValidatedImplemented, `Reg.ContractPrototype.ValidatedImplemented, true),
      (`Reg.ContractPrototype.Controls.ValidatedPartial, `Reg.ContractPrototype.ValidatedPartial, true),
      (`Reg.ContractPrototype.Controls.ValidatedExtern, `Reg.ContractPrototype.ValidatedExtern, true) ]
    let reports ← ContractPrototype.reports (pairs.flatMap fun (a, b, _) => #[a, b])
    for index in [:pairs.size] do
      let (oldRoot, newRoot, validated) := pairs[index]!
      let some (_, _, oldEnv) := reports[2 * index]? | throwError "old_report_missing"
      let some (_, _, newEnv) := reports[2 * index + 1]? | throwError "new_report_missing"
      let record (env : Environment) (owner : Name) :=
        ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
      let oldRecord := record oldEnv oldRoot
      let newRecord := record newEnv newRoot
      let stateOk (input : BindingRecord) := if validated then
        (input.result matches .declaredValidated _) else (input.result matches .declaredUnresolved _)
      unless stateOk oldRecord && stateOk newRecord do
        throwError "implementation_state:{newRoot}: {← TemplateBinding.recordJson oldRecord} / {← TemplateBinding.recordJson newRecord}"
      let label := newRoot.getString!
      let owners := if validated then
          #[(oldRoot, newRoot),
            (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut),
            ("Reg.ContractPrototype.Inputs".toName.str (label ++ "Old"),
              "Reg.ContractPrototype.Inputs".toName.str (label ++ "New")),
            ("ContractPrototypeFixtures".toName.str (label ++ "Old"),
              "ContractPrototypeFixtures".toName.str (label ++ "New"))]
        else #[(oldRoot, newRoot),
          (`Reg.Support.CounterexampleRecord, `Reg.ContractPrototype.Templates.Counterexample)]
      let authorization : Authorization := {
        owners := owners
        generatedBridges := if validated then
          #[(oldRecord.occurrence.realizationName, newRoot.str "bridge")] else #[] }
      let compare (state : String) (action : MetaM Json) : MetaM Unit := do
        if mode == "control" then
          discard <| action
          logInfo m!"[PASS] implementation_equal_{label}_{state}"
        else
          discard <| rejected ("implementation_" ++ label ++ "_" ++ state ++ "_" ++ mode)
            "dependency.mapped.body|dependency.mapped.implementation|dependency_enumeration|dependency_count" action
      if validated then
        compare "validated" <| verifyRecord oldEnv newEnv authorization oldRecord newRecord
      else
        compare "unresolved" <| ContractPrototype.UnresolvedEquivalence.verifyRecord
          oldEnv newEnv authorization oldRecord newRecord
        let missingOldEnv := withoutClaims oldEnv
        let missingNewEnv := withoutClaims newEnv
        let oldMissing ← inEnvironment missingOldEnv <| TemplateBinding.assess oldRecord.occurrence none
        let newMissing ← inEnvironment missingNewEnv <| TemplateBinding.assess newRecord.occurrence none
        unless (oldMissing.result matches .undeclared) && (newMissing.result matches .undeclared) do
          throwError "implementation_undeclared_state"
        compare "undeclared" <| verifyMissingRecord missingOldEnv missingNewEnv authorization oldMissing newMissing
    setEnv saved
