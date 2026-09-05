import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.ImportClosureProducer

open Lean
open LeanInformationAudit.Tests.ImportClosureProducer

namespace LeanInformationAudit.Tests.ImportClosureRoot

set_option linter.style.longLine false

#seal_information_theory output "/tmp/lean-information-audit-import-closure.json"

/-- info: import-closure artifact provenance passed -/
#guard_msgs (info) in
run_cmd do
  let contents <- Lean.Elab.Command.liftIO <|
    IO.FS.readFile "/tmp/lean-information-audit-import-closure.json"
  let json <- match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError message
  let schema <- match Json.getObjVal? json "schema" >>= Json.getStr? with
    | .ok value => pure value
    | .error message => throwError message
  let scope <- match Json.getObjVal? json "seal_scope" >>= Json.getStr? with
    | .ok value => pure value
    | .error message => throwError message
  let modules <- match Json.getObjVal? json "registration_modules" >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let systemVerdict <- match Json.getObjVal? json "system_catalog_irredundant" >>= Json.getBool? with
    | .ok value => pure value
    | .error message => throwError message
  unless schema == "lean-intrinsic-information-escape-v3" &&
      scope == "import-closure" &&
      !systemVerdict &&
      modules.any (fun value => value.getStr? ==
        .ok "LeanInformationAudit.Tests.ImportClosureProducer") do
    throwError "missing import-closure schema or registration provenance"
  logInfo "import-closure artifact provenance passed"

#print axioms
  objectArena.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_catalog
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__lowers_escape
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__escape_enriched
#print axioms
  objectArena.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__catalog_irredundant

end LeanInformationAudit.Tests.ImportClosureRoot
