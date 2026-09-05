import LeanInformationAudit.Tests.Census.Coverage

open Lean LeanInformationAudit DispositionCensus

namespace LeanInformationAudit.Tests.Census

private def decoded (inventory : DispositionInventory) : Bool :=
  parseInventory (toJson inventory) == .ok inventory

/-- info: true -/
#guard_msgs in
#eval decoded { fourRows with entries := fourRows.sortedEntries }

private def wrongClass : Json := Json.mkObj [
  ("theorem_name", toJson "Fixture.unreachable"),
  ("statement_id", toJson "id-unreachable"),
  ("class", toJson "finite_occurrence"),
  ("payload", fourRows.entries[3]!.2.payloadJson)]

/-- info: Except.error "IE-C037 DispositionClassMismatch theorem=Fixture.unreachable class=finite_occurrence invalid=payload_fields" -/
#guard_msgs in
#eval (parseRow wrongClass).map (fun _ => ())

private def unknownReason : Json := Json.mkObj [
  ("theorem_name", toJson "Fixture.unreachable"),
  ("statement_id", toJson "id-unreachable"),
  ("class", toJson "unreachable"),
  ("payload", Json.mkObj [("reason", toJson "not_an_enum_member"),
    ("evidence", toJson "Evidence")])]

/-- info: Except.error "IE-C037 DispositionClassMismatch theorem=Fixture.unreachable class=unreachable invalid=reason" -/
#guard_msgs in
#eval (parseRow unknownReason).map (fun _ => ())

def report : FrozenReport := ⟨"fixture-head", "fixture-report-sha256", frozenRows⟩

/-- info: true -/
#guard_msgs in
#eval (artifact report fourRows).map Json.compress == (artifact report
  { fourRows with entries := fourRows.entries.reverse }).map Json.compress

def reportBytes : String := (Json.mkObj [
  ("schema", toJson "lean-information-frozen-elaborated-report-v1"),
  ("head_sha", toJson "fixture-head"),
  ("modules", Json.arr #[Json.mkObj [("declarations", Json.arr <|
    (frozenRows.map fun key => Json.mkObj [
      ("kind", toJson "theorem"), ("name", toJson key.theoremName.toString),
      ("statement_id", toJson key.statementId)]).push
    (Json.mkObj [("kind", toJson "def"), ("name", toJson "Fixture.definition")]))]])]).compress

def reportDigest := "sha256:" ++ Sha256.hex reportBytes.toUTF8

/-- info: Except.ok 4 -/
#guard_msgs in
#eval (parseReport "fixture-head" reportDigest reportBytes).map (·.theorems.size)

/-- info: true -/
#guard_msgs in
#eval match parseReport "fixture-head" "sha256:stale" reportBytes with
  | .error message => message.startsWith "IE-C036 DispositionIdentityMismatch"
  | .ok _ => false

/-- info: Except.error "IE-C036 DispositionIdentityMismatch theorem=[anonymous] component=head expected=stale-head actual=fixture-head" -/
#guard_msgs in
#eval (parseReport "stale-head" reportDigest reportBytes).map (fun _ => ())

end LeanInformationAudit.Tests.Census
