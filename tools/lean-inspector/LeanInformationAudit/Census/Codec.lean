import LeanInformationAudit.AnalysisDisposition

namespace LeanInformationAudit.DispositionCensus

open Lean

/-- Fixed-width lowercase rendering; a value outside the wire domain is rejected. -/
def renderStatementId (value : Nat) : Except String String := do
  unless value < 2 ^ 256 do throw "statement_id_nat exceeds 256 bits"
  let digits := Nat.toDigits 16 value
  return "sha256:" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def formatError (name : Name) (wire : String) : String :=
  identityError name "statement_id_format" "sha256: followed by 64 lowercase hex digits" wire

/-- Decode only the canonical wire spelling. No trimming or case normalization. -/
def decodeStatementId (name : Name) (wire : String) : Except String Nat := do
  unless wire.startsWith "sha256:" && wire.utf8ByteSize ≤ 71 do
    throw <| formatError name wire
  let mut value := 0
  for digit in (wire.drop 7).toString.toList do
    let nibble ← if '0' ≤ digit && digit ≤ '9' then pure (digit.toNat - '0'.toNat)
      else if 'a' ≤ digit && digit ≤ 'f' then pure (digit.toNat - 'a'.toNat + 10)
      else if 'A' ≤ digit && digit ≤ 'F' then pure (digit.toNat - 'A'.toNat + 10)
      else throw (formatError name wire)
    value := value * 16 + nibble
  -- This equality is the canonical spelling authority, including case and width.
  unless (← renderStatementId value) == wire do throw <| formatError name wire
  return value

/-- Elaborator boundary between a supplied Nat literal and its original wire id. -/
def bindStatementIdNat (name : Name) (wire : String) (value : Nat) : Except String Unit := do
  let decoded ← decodeStatementId name wire
  unless decoded == value do
    throw <| identityError name "statement_id_nat" (toString decoded) (toString value)

end LeanInformationAudit.DispositionCensus
