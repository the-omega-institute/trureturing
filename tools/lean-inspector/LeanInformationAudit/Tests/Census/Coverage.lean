import LeanInformationAudit.DispositionCensus

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Census

def finiteKey : StatementKey := ⟨`Fixture.finite, "sha256:000000000000000000000000000000000000000000000000000000000000001e"⟩
def structuralKey : StatementKey := ⟨`Fixture.structural, "sha256:0000000000000000000000000000000000000000000000000000000000000020"⟩
def boundedKey : StatementKey := ⟨`Fixture.bounded, "sha256:000000000000000000000000000000000000000000000000000000000000001c"⟩
def unreachableKey : StatementKey := ⟨`Fixture.unreachable, "sha256:0000000000000000000000000000000000000000000000000000000000000021"⟩

def fourRows : DispositionInventory := {
  headSha := "fixture-head"
  entries := #[
    ⟨finiteKey, .certified <| .finiteOccurrence ⟨`Finite.arena, `Finite.unit, `Finite.realization,
      `Finite.nondegenerate, `Finite.enumeration⟩⟩,
    ⟨structuralKey, .certified <| .structuralOccurrence ⟨`Structural.arena, `Structural.unit,
      `Structural.realization, `Structural.strictness, `Structural.witness⟩⟩,
    ⟨boundedKey, .certified <| .boundedFiniteTruncation ⟨`Truncation.family, 12,
      `Truncation.comparison, .reportOnly⟩⟩,
    ⟨unreachableKey, .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Unreachable.evidence⟩⟩]
}

def frozenRows : Array StatementKey :=
  #[finiteKey, structuralKey, boundedKey, unreachableKey]

def frozenKeys : List Nat := [28, 30, 32, 33]

def keyManifest : CensusKeyManifest := ⟨"fixture-head", "digest", `Fixture, frozenKeys⟩

def encodeNameKey : Name → String
  | .anonymous => "n0"
  | .str parent text => s!"ns({encodeNameKey parent},{text.utf8ByteSize}:{text})"
  | .num parent index => s!"nn({encodeNameKey parent},{index})"

theorem exactCoverage : CensusKeyManifest.IdCoverage keyManifest.keys 4 frozenKeys.toFinset :=
  CensusKeyManifest.idCoverage_of_certificate _ _ _ ⟨by decide, rfl, rfl⟩

-- CT-001: independent of the separate IE-C034 diagnostic path.
theorem missingKeyDoesNotExactlyCover :
    ¬CensusKeyManifest.IdCoverage (frozenKeys.take 3) 4 frozenKeys.toFinset := by
  intro h
  have member : 33 ∈ frozenKeys.toFinset := by simp [frozenKeys]
  rw [← h.2.2] at member
  simpa [frozenKeys] using member

/-- info: false -/
#guard_msgs in
#eval (CensusManifest.checkManifestBinding
  ⟨"fixture-head", "digest", frozenRows⟩ `Fixture (frozenRows.extract 0 3)
  keyManifest frozenKeys).isOk

/-- info: 'LeanInformationAudit.Tests.Census.exactCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exactCoverage

private def check (inventory : DispositionInventory) : Except String Unit :=
  DispositionCensus.checkCoverage "fixture-head" frozenRows inventory

/-- info: Except.ok () -/
#guard_msgs in
#eval check fourRows

/-- info: Except.error "IE-C034 MissingAnalysisDisposition theorem=Fixture.unreachable statement_id=sha256:0000000000000000000000000000000000000000000000000000000000000021 head=fixture-head" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.extract 0 3 }

/-- info: Except.error "IE-C035 DuplicateAnalysisDisposition theorem=Fixture.finite statement_id=sha256:000000000000000000000000000000000000000000000000000000000000001e records=[0,4]" -/
#guard_msgs in
#eval check { fourRows with entries := (fourRows.entries.push fourRows.entries[0]!) }

/-- info: Except.error "IE-C035 DuplicateAnalysisDisposition theorem=Fixture.finite statement_id=sha256:000000000000000000000000000000000000000000000000000000000000001e records=[0,4]" -/
#guard_msgs in
#eval check { fourRows with entries :=
  (fourRows.entries.push (⟨⟨`Fixture.alias,
    "sha256:000000000000000000000000000000000000000000000000000000000000001e"⟩,
    .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩)) }

/-- info: Except.error "IE-C036 DispositionIdentityMismatch theorem=Fixture.finite component=statement_id expected=sha256:000000000000000000000000000000000000000000000000000000000000001e actual=sha256:00000000000000000000000000000000000000000000000000000000000000ff" -/
#guard_msgs in
#eval check { fourRows with entries := fourRows.entries.set! 0 (
  ⟨⟨`Fixture.finite, "sha256:00000000000000000000000000000000000000000000000000000000000000ff"⟩,
    .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩) }

/-- info: Except.error "IE-C036 DispositionIdentityMismatch theorem=Fixture.bounded component=head expected=fixture-head actual=stale-head" -/
#guard_msgs in
#eval check { fourRows with headSha := "stale-head" }

def counts := DispositionCensus.count fourRows

def everyReason : DispositionInventory := ⟨"reasons", #[
  ⟨⟨`NoCarrier, "sha256:0000000000000000000000000000000000000000000000000000000000000001"⟩, .certified <| .unreachable ⟨.noCanonicalObjectCarrier, `Evidence⟩⟩,
  ⟨⟨`NoBundle, "sha256:0000000000000000000000000000000000000000000000000000000000000002"⟩, .certified <| .unreachable ⟨.noFinitePrimitiveBundle, `Evidence⟩⟩,
  ⟨⟨`NoRealization, "sha256:0000000000000000000000000000000000000000000000000000000000000003"⟩, .certified <| .unreachable ⟨.noFaithfulPrimitiveRealization, `Evidence⟩⟩]⟩

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
