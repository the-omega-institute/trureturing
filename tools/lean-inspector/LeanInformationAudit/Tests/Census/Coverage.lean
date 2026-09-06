import LeanInformationAudit.DispositionCensus

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Census

def finiteKey : StatementKey := ⟨`Fixture.finite, "id-finite"⟩
def structuralKey : StatementKey := ⟨`Fixture.structural, "id-structural"⟩
def boundedKey : StatementKey := ⟨`Fixture.bounded, "id-bounded"⟩
def unreachableKey : StatementKey := ⟨`Fixture.unreachable, "id-unreachable"⟩

def fourRows : DispositionInventory := {
  headSha := "fixture-head"
  entries := #[
    ⟨finiteKey, .finiteOccurrence ⟨`Finite.arena, `Finite.unit, `Finite.realization,
      `Finite.nondegenerate, `Finite.enumeration⟩⟩,
    ⟨structuralKey, .structuralOccurrence ⟨`Structural.arena, `Structural.unit,
      `Structural.realization, `Structural.strictness, `Structural.witness⟩⟩,
    ⟨boundedKey, .boundedFiniteTruncation ⟨`Truncation.family, 12,
      `Truncation.comparison, .reportOnly⟩⟩,
    ⟨unreachableKey, .unreachable ⟨.noCanonicalObjectCarrier, `Unreachable.evidence⟩⟩]
}

def frozenRows : Array StatementKey :=
  #[finiteKey, structuralKey, boundedKey, unreachableKey]

def frozenKeys : Finset StatementKey := frozenRows.toList.toFinset

def encodeNameKey : Name → String
  | .anonymous => "n0"
  | .str parent text => s!"ns({encodeNameKey parent},{text.utf8ByteSize}:{text})"
  | .num parent index => s!"nn({encodeNameKey parent},{index})"

theorem exactCoverage : fourRows.ExactlyCovers "fixture-head" frozenKeys := by decide

-- CT-001: independent of the separate IE-C034 diagnostic path.
theorem missingKeyDoesNotExactlyCover :
    ¬({ fourRows with entries := fourRows.entries.extract 0 3 }).ExactlyCovers
      "fixture-head" frozenKeys := by decide

/-- info: false -/
#guard_msgs in
#eval decide <| ({ fourRows with entries := fourRows.entries.extract 0 3 }).ExactlyCovers
  "fixture-head" frozenKeys

/-- info: 'LeanInformationAudit.Tests.Census.exactCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exactCoverage

private def check (inventory : DispositionInventory) : Except String Unit :=
  DispositionCensus.checkCoverage "fixture-head" frozenRows inventory

/-- info: Except.ok () -/
#guard_msgs in
#eval check fourRows

/-- info: Except.error "IE-C034 MissingAnalysisDisposition theorem=Fixture.unreachable statement_id=id-unreachable head=fixture-head" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.extract 0 3 }

/-- info: Except.error "IE-C035 DuplicateAnalysisDisposition theorem=Fixture.finite statement_id=id-finite records=[0,4]" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.push fourRows.entries[0]! }

/-- info: Except.error "IE-C035 DuplicateAnalysisDisposition theorem=Fixture.finite statement_id=id-finite records=[0,4]" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.push (
  ⟨⟨`Fixture.alias, "id-finite"⟩, .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩) }

/-- info: Except.error "IE-C036 DispositionIdentityMismatch theorem=Fixture.finite component=statement_id expected=id-finite actual=stale" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.set! 0 (
  ⟨⟨`Fixture.finite, "stale"⟩, .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩) }

/-- info: Except.error "IE-C036 DispositionIdentityMismatch theorem=Fixture.bounded component=head expected=fixture-head actual=stale-head" -/
#guard_msgs in
#eval check { fourRows with headSha := "stale-head" }

def counts := DispositionCensus.count fourRows

def everyReason : DispositionInventory := ⟨"reasons", #[
  ⟨⟨`NoCarrier, "1"⟩, .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩,
  ⟨⟨`NoBundle, "2"⟩, .unreachable ⟨.noFinitePrimitiveBundle, `Evidence⟩⟩,
  ⟨⟨`NoRealization, "3"⟩, .unreachable ⟨.noFaithfulPrimitiveRealization, `Evidence⟩⟩]⟩

-- CT-002: literal expected totals, independently of the counting function.
/-- info: (3, 1, 1, 1, 3) -/
#guard_msgs in
#eval let c := DispositionCensus.count everyReason
  (c.unreachable, c.noCanonicalObjectCarrier, c.noFinitePrimitiveBundle,
    c.noFaithfulPrimitiveRealization,
    c.noCanonicalObjectCarrier + c.noFinitePrimitiveBundle + c.noFaithfulPrimitiveRealization)

/-- info: (1, 1, 1, 1, 1, 0, 0) -/
#guard_msgs in
#eval (counts.finiteOccurrence, counts.structuralOccurrence,
  counts.boundedFiniteTruncation, counts.unreachable,
  counts.noCanonicalObjectCarrier, counts.noFinitePrimitiveBundle,
  counts.noFaithfulPrimitiveRealization)

/-- info: Except.error "IE-C044 DispositionCensusMismatch head=fixture-head component=finite_occurrence expected=1 actual=2" -/
#guard_msgs in
#eval DispositionCensus.checkCounts fourRows { counts with finiteOccurrence := 2 }

/-- info: Except.error "IE-C044 DispositionCensusMismatch head=fixture-head component=no_canonical_object_carrier expected=1 actual=0" -/
#guard_msgs in
#eval DispositionCensus.checkCounts fourRows { counts with noCanonicalObjectCarrier := 0 }

end LeanInformationAudit.Tests.Census
