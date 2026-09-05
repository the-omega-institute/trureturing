import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean LeanInformationAudit Lean.Elab.Command
open LeanInformationAudit.Tests.ImportClosureProducer

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"

run_cmd do
  liftIO <| IO.FS.writeFile "/tmp/ie0905-j-v3.json" "invalid prior JSON"
  liftIO <| IO.FS.writeFile "/tmp/ie0905-j-v3.txt" "invalid prior ASCII"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
#seal_information_theory output "/tmp/ie0905-j-v2-additive.json"
  analysis_output "/tmp/ie0905-j-v3.json" ascii_output "/tmp/ie0905-j-v3.txt"

/-- info: complete v3 seal and output noninterference passed -/
#guard_msgs in
run_cmd do
  let contents ← liftIO <| IO.FS.readFile "/tmp/ie0905-j-v3.json"
  let artifact ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError message
  let root := (← getEnv).header.mainModule
  match validateV3KeySet root `system "root" #["schema", "root_id", "seal_scope",
      "registration_modules", "system_catalog_irredundant",
      "kernel_address_coincidence_classes", "catalogs"] artifact with
  | .ok () => pure ()
  | .error message => throwError message
  unless (artifact.getObjValAs? String "schema").toOption ==
      some "lean-intrinsic-information-escape-v3" do throwError "v3 schema"
  let some records := (artifact.getObjValAs? (Array Json) "catalogs").toOption
    | throwError "catalog inventory"
  unless records.size == 1 do throwError "maximal catalog inventory"
  let ascii ← liftIO <| IO.FS.readFile "/tmp/ie0905-j-v3.txt"
  unless ascii.startsWith "CATALOG " do throwError "ASCII inventory"
  let v2 ← liftIO <| IO.FS.readFile "/tmp/ie0905-j-v2-additive.json"
  unless v2 == serializeV2Artifact (SealRecords.forRoot (← getEnv) root) do
    throwError "v2 serializer changed"
  logInfo "complete v3 seal and output noninterference passed"

run_cmd do
  let env ← getEnv
  let root := env.header.mainModule.toString
  for (name, _) in env.constants.toList do
    if name.toString.contains root then
      elabCommand (← `(command| #print axioms $(mkIdent name)))
