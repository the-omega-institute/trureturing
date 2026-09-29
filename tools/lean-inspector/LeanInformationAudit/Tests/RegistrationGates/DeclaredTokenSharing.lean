import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Elab Command Meta LeanInformationAudit LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.Tests.DeclaredTokenSharing

private def firstReference (bytes : ByteArray) : Option (Nat × Nat × String × Nat) := Id.run do
  let mut offset := 0
  let mut tokens : Array String := #[]
  while offset < bytes.size do
    let start := offset
    let reference := bytes[offset]! == 64
    if reference then offset := offset + 1
    let mut n := 0
    while offset < bytes.size && bytes[offset]! != 58 do
      let digit := bytes[offset]!.toNat
      if digit < 48 || digit > 57 then return none
      n := 10 * n + digit - 48
      offset := offset + 1
    if offset == bytes.size then return none
    offset := offset + 1
    if reference then return (tokens[n]?).map fun value => (start, offset, value, tokens.size)
    if offset + n > bytes.size then return none
    let some value := String.fromUTF8? (bytes.extract offset (offset + n)) | return none
    tokens := tokens.push value
    offset := offset + n
  return none

private def runChecks : TermElabM Unit := do
  let .ok selected := selectedPlan (← getEnv)
      ``DTRIndex.A.selected |
    throwError "setup: checked cut template missing"
  let .ok bytes := planEncoding selected | throwError "setup: plan encoding failed"
  let reference := firstReference bytes
  let repeat := (planEncoding selected).toOption == some bytes
  let workRejected := !(planEncoding selected bytes.size).isOk
  let identityBound := selected.planIdentity == Sha256.hex bytes &&
    selected.serializedBytes == bytes.size
  for (label, passed) in #[
      ("shared_plan_tokens_deterministic", reference.isSome && repeat),
      ("shared_plan_identity_binds_encoding", identityBound),
      ("shared_plan_token_work_charged", workRejected)] do
    (if passed then logInfo else logError) m!"[{if passed then "PASS" else "FAIL"}] {label}"

run_elab runChecks

end LeanInformationAudit.Tests.DeclaredTokenSharing
