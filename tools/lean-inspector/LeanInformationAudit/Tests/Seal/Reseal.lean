import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import LeanInformationAudit.Tests.SealSuccess
open Lean LeanInformationAudit Lean.Elab.Command
open LeanInformationAudit.Tests.SealSuccess
namespace LeanInformationAudit.Tests.Seal.Reseal
local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
information_theorem peer in arena primitives fstRealization : arena.Law fstRealization := by trivial
expect_information_occurrence fstTheorem in arena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence sndTheorem in arena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence notTheorem in notArena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence idTheorem in t001Arena from "LeanInformationAudit.Tests.SealSuccess"
expect_information_occurrence peer in arena from "LeanInformationAudit.Tests.Seal.Reseal"
#guard_msgs (error) in
#seal_information_theory
run_cmd do
  let env ← getEnv
  let old := SealRecords.forRoot env `LeanInformationAudit.Tests.SealSuccess
  let current := SealRecords.forRoot env env.header.mainModule
  let before := old.flatMap (·.theorems) |>.find? (·.theoremName == ``fstTheorem)
  let after := current.flatMap (·.theorems) |>.find? (·.theoremName == ``fstTheorem)
  unless (before.map (·.uniqueCaptureCount)).getD 0 > 0 &&
      after.map (·.uniqueCaptureCount) == some 0 &&
      (current.flatMap (·.theorems)).size == 5 do throwError "nonmonotone reseal loses old member"
  unless (current.flatMap (·.theorems)).any (fun t => t.uniqueCaptureCount > 0) do
    throwError "mixed catalog loses positive members"
end LeanInformationAudit.Tests.Seal.Reseal
