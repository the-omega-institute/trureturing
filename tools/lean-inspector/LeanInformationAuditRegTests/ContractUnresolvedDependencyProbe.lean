import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Controls.Unresolved
import Reg.ContractPrototype.UnresolvedChanged

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let oldRoot := `Reg.ContractPrototype.Controls.Unresolved
    let newRoot := `Reg.ContractPrototype.UnresolvedChanged
    let reports ← ContractPrototype.reports #[oldRoot, newRoot]
    let some (_, _, oldEnv) := reports[0]? | throwError "old_report_missing"
    let some (_, _, newEnv) := reports[1]? | throwError "new_report_missing"
    let record (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
    let oldRecord := record oldEnv oldRoot
    let newRecord := record newEnv newRoot
    unless (oldRecord.result matches .declaredUnresolved _) &&
        (newRecord.result matches .declaredUnresolved _) do throwError "unresolved_control_state"
    let reads (env : Environment) (owner : Name) : TermElabM Name := do
      let some name := env.header.moduleData[(env.getModuleIdx? owner).get!.toNat]!.constNames.find?
        (fun name => privateToUserName name == owner.str "reads") | throwError "reads_missing"
      return name
    let kernelValue (owner name : Name) (expected : Bool) : TermElabM Unit := do
      let expression ← Term.elabTerm (← `(($((mkIdent name)) : _).readout () (1 : Fin 2))) none
      let expression ← instantiateMVars expression
      let type ← mkEq expression (mkConst (if expected then ``Bool.true else ``Bool.false))
      let value ← mkEqRefl expression
      addDecl (.thmDecl { name := owner.str "kernelReadout", levelParams := [], type, value })
    kernelValue oldRoot (← reads oldEnv oldRoot) false
    kernelValue newRoot (← reads newEnv newRoot) true
    logInfo "unresolved_actual_readouts: state=1 old=false new=true kernel_checked=true"
    discard <| rejected "unresolved_actual_dependencies" "dependency_count|dependency_enumeration|dependency.mapped.body" <|
      ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv newEnv {
        owners := #[(oldRoot, newRoot),
          (`Reg.Support.CounterexampleRecord, `Reg.ContractPrototype.Templates.Counterexample)] }
        oldRecord newRecord
    setEnv saved
