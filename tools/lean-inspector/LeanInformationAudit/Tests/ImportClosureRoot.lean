import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.ImportClosureProducer

open Lean

namespace LeanInformationAudit.Tests.ImportClosureRoot

#seal_information_theory output "/tmp/lean-information-audit-import-closure.json"

/-- info: import-closure artifact provenance passed -/
#guard_msgs (info) in
run_cmd do
  let contents <- Lean.Elab.Command.liftIO <|
    IO.FS.readFile "/tmp/lean-information-audit-import-closure.json"
  let json <- match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError message
  let schema <- Json.getObjVal? json "schema" >>= Json.getStr?
  let scope <- Json.getObjVal? json "seal_scope" >>= Json.getStr?
  let modules <- Json.getObjVal? json "registration_modules" >>= Json.getArr?
  unless schema == "lean-intrinsic-information-escape-v3" &&
      scope == "import-closure" &&
      modules.any (fun value => value.getStr? ==
        .ok "LeanInformationAudit.Tests.ImportClosureProducer") do
    throwError "missing import-closure schema or registration provenance"
  logInfo "import-closure artifact provenance passed"

end LeanInformationAudit.Tests.ImportClosureRoot
