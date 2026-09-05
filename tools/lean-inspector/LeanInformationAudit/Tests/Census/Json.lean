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
  ("schema", toJson "stratalint.truth-export"),
  ("schema_version", toJson (1 : Nat)),
  ("dialect", toJson "stratalint.truth-export.v1"),
  ("producer", toJson "TruthExportCommand"),
  ("source_commit", toJson "fixture-head"),
  ("nodes", Json.arr #[Json.mkObj [("declarations", Json.arr <|
    (frozenRows.map fun key => Json.mkObj [
      ("kind", toJson "theorem"), ("declaration_name_key", toJson (encodeNameKey key.theoremName)),
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

/-- info: Except.ok "A.3" -/
#guard_msgs in
#eval (parseNameKey "nn(ns(n0,1:A),3)").map Name.toString

/-- info: true -/
#guard_msgs in
#eval parseNameKey "ns(n0,3:a.b)" == .ok (Name.mkSimple "a.b")

/-- info: true -/
#guard_msgs in
#eval parseNameKey "ns(n0,2:é)" == .ok (Name.mkSimple "é")

/-- info: true -/
#guard_msgs in
#eval match parseNameKey "ns(n0,1:é)" with
  | .error _ => true
  | .ok _ => false

/-- info: true -/
#guard_msgs in
#eval match parseNameKey "nn(ns(n0,1:A),3)garbage" with
  | .error _ => true
  | .ok _ => false

end LeanInformationAudit.Tests.Census
