import LeanInformationAudit.Tests.Occurrence.ImportedArenaProvenance
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.SealCommand

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer

-- The construction information must survive a second olean boundary. This path
-- cannot read source: the unchanged seal noninterference audit enforces that.
run_cmd do
  for (name, expected) in #[
      (`ProvenanceProbe.copyArena, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.live, `ProvenanceProbe.copyArena),
      (`ProvenanceProbe.aliasArena, `ProvenanceProbe.arena),
      (`ProvenanceProbe.dead, `ProvenanceProbe.arena)] do
    let actual ← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name
    unless actual == expected do
      throwError "imported compiler provenance: {name}: expected {expected}, actual {actual}"

/-- error: IE-C003 ArenaSourceUnavailable declaration=ProvenanceProbe.sourceMutation reason=provenance -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence `ProvenanceProbe.sourceMutation

namespace ImportedArenaEvidence

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

theorem bridge : LegacyPrimitiveRealization lawArena True fixtureRealization where
  equivalence := Iff.rfl

register_information_theorem importedTheorem
  in lawArena object_arena ProvenanceProbe.live catalog copy
  primitives fixtureRealization.toPrimitiveBundle realization bridge

expect_information_occurrence importedTheorem in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"
expect_information_occurrence importedTheorem in ProvenanceProbe.copyArena
  from "LeanInformationAudit.Tests.Occurrence.ImportedArenaEvidence"

#seal_information_theory

end ImportedArenaEvidence
