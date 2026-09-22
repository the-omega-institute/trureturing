import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

open Lean Elab Command Meta LeanInformationAudit LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.Tests.DeclaredTokenSharing

private def literal (value : String) : ByteArray :=
  (toString value.utf8ByteSize ++ ":" ++ value).toUTF8

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

-- Inserting a literal creates a new table entry under the mutation that allows
-- duplicates. Relocate later references to preserve the entire decoded value;
-- otherwise an unrelated parsing failure would hide that missing predicate.
private def relocateReferences (bytes : ByteArray) (start threshold : Nat) :
    Option ByteArray := Id.run do
  let mut output := ByteArray.empty
  let mut offset := start
  while offset < bytes.size do
    let first := offset
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
    if reference then
      output := output ++ ("@" ++ toString (if n ≥ threshold then n + 1 else n) ++ ":").toUTF8
    else
      if offset + n > bytes.size then return none
      offset := offset + n
      output := output ++ bytes.extract first offset
  return some output

private def runChecks : TermElabM Unit := do
  let .ok selected := selectedPlan (← getEnv)
      ``DTRIndex.A.selected |
    throwError "setup: checked cut template missing"
  let .ok bytes := planEncoding selected | throwError "setup: plan encoding failed"
  let reference := firstReference bytes
  let roundtrip := match PlanDecoder.decode bytes (32 * bytes.size) with
    | .ok (decoded, _) => (planEncoding decoded).toOption == some bytes
    | .error _ => false
  let duplicateRejected ← match reference with
    | none => pure false
    | some (start, stop, value, threshold) => match relocateReferences bytes stop threshold with
      | none => pure false
      | some suffix => do
        let mutated := bytes.extract 0 start ++ literal value ++ suffix
        match PlanDecoder.decode mutated (32 * mutated.size) with
        | .error _ => pure true
        | .ok (decoded, _) =>
          unless (planEncoding decoded).toOption == some bytes do
            throwError "setup: relocated duplicate changed the decoded plan"
          logInfo "duplicate_literal_preserves_decoded_plan=true"
          pure false
  let forward := "@0:".toUTF8 ++ bytes
  let workRejected := !(planEncoding selected bytes.size).isOk
  for (label, passed) in #[
      ("shared_plan_tokens_roundtrip", reference.isSome && roundtrip),
      ("shared_plan_forward_reference_rejected",
        !(PlanDecoder.decode forward (32 * forward.size)).isOk),
      ("shared_plan_duplicate_literal_rejected", duplicateRejected),
      ("shared_plan_token_work_charged", workRejected)] do
    (if passed then logInfo else logError) m!"[{if passed then "PASS" else "FAIL"}] {label}"

run_elab runChecks

end LeanInformationAudit.Tests.DeclaredTokenSharing
