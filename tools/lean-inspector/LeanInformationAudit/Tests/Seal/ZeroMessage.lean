import LeanInformationAudit.SealCommand
open Lean Lean.Elab.Command LeanInformationAudit
namespace LeanInformationAudit.Tests

def checkZeroMessages (kind : String) (count : Nat) (before : MessageLog) : CommandElabM Unit := do
  let mut records := #[]
  for message in (← get).messages.toList.drop before.toList.length do
    let text ← message.data.toString
    if text.startsWith "IE-C007 ZeroUniqueCapture: " then
      records := records.push (← ofExcept <| Json.parse (text.drop 27).toString)
  unless records.size == count do throwError "ZeroMessage: IE-C007 multiplicity"
  for record in records do
    let context ← ofExcept <| record.getObjVal? "context"
    unless (context.getObjValAs? String "kind").toOption == some kind do
      throwError "ZeroMessage: context kind"
    if kind == "finite" then
      let full ← ofExcept <| context.getObjValAs? Nat "full_escape_count"
      let without ← ofExcept <| context.getObjValAs? Nat "without_escape_count"
      let enumeration ← ofExcept <| context.getObjValAs? String "state_enumeration"
      unless full == without && (← getEnv).contains enumeration.toName do
        throwError "ZeroMessage: finite evidence"
    else
      unless (← ofExcept <| context.getObj?).size == 3 do
        throwError "ZeroMessage: structural count fields"
    let certificate ← ofExcept <| record.getObjValAs? String "triviality_certificate"
    unless (← getEnv).contains certificate.toName do throwError "ZeroMessage: certificate"
end LeanInformationAudit.Tests
