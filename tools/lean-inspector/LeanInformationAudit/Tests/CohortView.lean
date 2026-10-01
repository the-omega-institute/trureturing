import LeanInformationAudit.SealCommand

/-! A report batch is the set of cache-missing modules one inspector process
loads and requests together, at most `NATIVE_BATCH_MODULES` at a time. None of
that is in a module's trace, so a target's contribution to the report must not
depend on it. `CohortAlone`, `CohortWithPeers` and `CohortPermuted` load the
target alone, with unrelated registering peers, and in another import order;
each requests it in several batches, including batches of 99 and 100 requested
modules (a 101st module forms a batch alone). All must report the identical
row and identical generated declarations for the target: the same digest in
all three modules and in every case within a module. -/

namespace LeanInformationAudit.Tests.CohortView
open Lean

def target : Name := `LeanInformationAudit.Tests.CohortTarget
def peer : Name := `LeanInformationAudit.Tests.CohortPeer
def other : Name := `LeanInformationAudit.Tests.CohortOther

/-- The target's row and generated declarations, rendered exactly. -/
def contribution (request : Array Name) : MetaM String := do
  let reports ← finiteInformationTemplateReportDriver request
  let some index := request.findIdx? (· == target) | throwError "setup: target not requested"
  let some (row, generated, env) := reports[index]? | throwError "setup: target row missing"
  let declarations ← generated.mapM fun name => do
    let some info := env.find? name | throwError "generated declaration missing: {name}"
    pure s!"{name} : {info.type} := {info.value? (allowOpaque := true)}"
  return "\n".intercalate (row.compress :: declarations.toList)

private def orThrow : Except String α → MetaM α
  | .ok value => pure value
  | .error message => throwError message

private def summary (row : String) : MetaM String := do
  let records ← orThrow <| (← orThrow <| Json.parse row).getObjValAs? (Array Json) "records"
  let parts ← records.mapM fun record => do
    let key ← orThrow <| record.getObjVal? "key"
    let theoremName ← orThrow <| key.getObjValAs? String "theorem"
    let state ← orThrow <| record.getObjValAs? String "state"
    let diagnostic := (record.getObjValAs? String "diagnostic").toOption.getD ""
    let rule := if (diagnostic.splitOn "dtr.unregistered_template").length > 1
      then ":unregistered_template" else ""
    return s!"{(theoremName.splitOn ".").getLast!}:{state}{rule}"
  return ",".intercalate parts.toList

/-- Batches of `size` requested modules with the target last; the other
members are loaded modules that register nothing, repository D5 modules first. -/
def batch (size : Nat) (members : Array Name) : MetaM (Array Name) := do
  let loaded := (← getEnv).header.moduleNames.filter fun name =>
    name != target && !members.contains name
  let inert := loaded.filter ((`D5).isPrefixOf ·) ++ loaded.filter (!(`D5).isPrefixOf ·)
  unless inert.size + members.size + 1 ≥ size do throwError "setup: too few loaded modules"
  return members ++ inert.extract 0 (size - members.size - 1) ++ #[target]

/-- Report the target in every requested batch; all must agree. -/
def observe (cases : Array (String × Array Name)) : MetaM Unit := do
  let env ← getEnv
  let mut expected : Option String := none
  for (label, request) in cases do
    let actual ← contribution request
    setEnv env
    if let some reference := expected then
      unless actual == reference do
        throwError "[FAIL] {label}: target contribution differs\n{actual}\nexpected:\n{reference}"
    else expected := some actual
  let some reference := expected | throwError "setup: no case"
  let row := (reference.splitOn "\n").head!
  logInfo m!"[PASS] report_target_cohort_independent cases={cases.size} \
    digest={hash reference} records={← summary row}"

end LeanInformationAudit.Tests.CohortView
