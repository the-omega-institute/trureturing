import LeanInformationAudit.SealCommand

open LeanInformationAudit
open Lean
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.CompleteRedundantIndices

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def constantRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

information_theorem firstTheorem
  in arena
  primitives constantRealization
  : arena.Law constantRealization := by trivial

information_theorem secondTheorem
  in arena
  primitives constantRealization
  : arena.Law constantRealization := by trivial

information_theorem thirdTheorem
  in arena
  primitives constantRealization
  : arena.Law constantRealization := by trivial

expect_information_occurrence firstTheorem
  in arena
  from "LeanInformationAudit.Tests.Occurrence.CompleteRedundantIndices"

expect_information_occurrence secondTheorem
  in arena
  from "LeanInformationAudit.Tests.Occurrence.CompleteRedundantIndices"

expect_information_occurrence thirdTheorem
  in arena
  from "LeanInformationAudit.Tests.Occurrence.CompleteRedundantIndices"

private def fixtureCatalog : Catalog arena.toArena :=
  Catalog.ofVector ![
    firstTheorem.__information_unit,
    secondTheorem.__information_unit,
    thirdTheorem.__information_unit]

example : fixtureCatalog.uniqueCaptureCount (0 : Fin 3) = 0 := by decide
example : fixtureCatalog.uniqueCaptureCount (1 : Fin 3) = 0 := by decide
example : fixtureCatalog.uniqueCaptureCount (2 : Fin 3) = 0 := by decide

private def artifactPath : System.FilePath :=
  "/tmp/lean-information-audit-complete-redundant-indices.json"

run_cmd do
  if <- artifactPath.pathExists then
    Lean.Elab.Command.liftIO <| IO.FS.removeFile artifactPath

#guard_msgs (error) in
#seal_information_theory

run_cmd do
  let records := SealRecords.forRoot (← getEnv) (← getEnv).header.mainModule
  unless records.size == 1 && records[0]!.theorems.map (·.uniqueCaptureCount) == #[0, 0, 0] do
    throwError "complete zero classification missing"
  let env ← getEnv
  unless records[0]!.theorems.all (fun row => env.contains row.certificateName) do
    throwError "missing triviality certificate"

/- The real seal above pins collection and certification; this pins the exact
completeness diagnostic independently. -/
/-- error: IE-C033 IncompleteRedundantIndexSet key=fixtureRoot/fixtureCatalog expected=[0,1,2] certified=[0] phase=first-zero -/
#guard_msgs (error) in
run_cmd do
  match validateRedundantIndices `fixtureRoot `fixtureCatalog #[0, 0, 0] #[0]
      "first-zero" with
  | .ok () => pure ()
  | .error message => throwError message

end LeanInformationAudit.Tests.CompleteRedundantIndices
