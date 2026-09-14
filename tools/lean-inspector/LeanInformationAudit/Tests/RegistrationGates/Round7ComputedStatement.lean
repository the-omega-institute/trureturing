import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries
open Lean LeanInformationAudit.RegistrationGates
namespace Round7ComputedStatement

def computedStatement : Prop :=
  Bool.rec (motive := fun _ => Prop) False ((137 : Nat) = 137) true

theorem computedTarget : computedStatement := rfl

def dictionaryRead (_ : Unit) (state : Bool) : Bool :=
  state && @decide ((137 : Nat) = 137) (.isTrue rfl)

run_cmd Elab.Command.liftCoreM do
  -- Shape control: inspect the definition before relying on the prediction.
  let some (.defnInfo info) := (← getEnv).find? ``computedStatement
    | throwError "[INVALID] ComputedStatementShape: missing definition"
  unless info.value.getAppFn.isConstOf ``Bool.rec do
    throwError "[INVALID] ComputedStatementShape: {repr info.value}"
  let env ← getEnv
  for (label, target, readout) in [
      ("PlainRegisteredScalarControl", ``AllowlistBoundaries.target,
        ``AllowlistBoundaries.forbiddenArgument),
      ("ComputedRegisteredProof", ``computedTarget,
        ``AllowlistBoundaries.forbiddenArgument),
      ("ComputedRegisteredNominalPayload", ``computedTarget,
        ``AllowlistBoundaries.hiddenPayload),
      ("ComputedRegisteredDecision", ``computedTarget, ``dictionaryRead)] do
    let result ← readoutClosure env target (mkConst readout)
    if result.1 && result.2.isSome then logInfo m!"[PASS] {label}: {result}"
    else logError m!"[FAIL] {label}: expected completed rejection; actual={result}"
end Round7ComputedStatement

namespace Round7ComputedStatement
private def full (label : String) (target readout : Name) : CoreM Unit := do
  let some (.defnInfo info) := (← getEnv).find? ``AllowlistBoundaries.template
    | throwError "[INVALID] missing template"
  let holder := `Round7ComputedStatement |>.str label
  addDecl <| .defnDecl {
    name := holder, levelParams := [], type := info.type
    value := info.value.replace fun e =>
      if e == mkConst ``AllowlistBoundaries.plain then some (mkConst readout) else none
    hints := .abbrev, safety := .safe }
  let actual ← provenanceErrorCurrent (← getEnv).header.mainModule `catalog target holder
  if actual.any (fun message => message.startsWith "IE-C050 ClosedTruthReadout " &&
      (message.contains "reason=unclassified_form" || message.contains "reason=forbidden_dependency")) then
    logInfo m!"[PASS] {label}Diagnostic: {actual}"
  else logError m!"[FAIL] {label}Diagnostic: expected IE-C050; actual={actual}"
  if target == ``computedTarget then
    if actual.any (fun message => message.contains "unclassified_statement_head" &&
        message.contains "\"first\":\"Bool.rec\"") then
      logInfo m!"[PASS] {label}HeadNamed: {actual}"
    else logError m!"[FAIL] {label}HeadNamed: expected unresolved Bool.rec head; actual={actual}"
run_cmd Elab.Command.liftCoreM do
  for (label, target, readout) in [
      ("PlainRegisteredScalarControl", ``AllowlistBoundaries.target,
        ``AllowlistBoundaries.forbiddenArgument),
      ("ComputedRegisteredProof", ``computedTarget,
        ``AllowlistBoundaries.forbiddenArgument),
      ("ComputedRegisteredNominalPayload", ``computedTarget,
        ``AllowlistBoundaries.hiddenPayload),
      ("ComputedRegisteredDecision", ``computedTarget, ``dictionaryRead)] do
    full label target readout
end Round7ComputedStatement
