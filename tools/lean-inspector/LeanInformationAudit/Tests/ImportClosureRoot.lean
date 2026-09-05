import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.ImportClosureProducer

open Lean
open LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer

namespace LeanInformationAudit.Tests.ImportClosureRoot

set_option linter.style.longLine false

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.ImportClosureProducer"

#seal_information_theory output "/tmp/lean-information-audit-import-closure.json"

/-- info: import-closure qualified identity passed -/
#guard_msgs (info) in
run_cmd do
  let env <- getEnv
  let root := env.header.mainModule
  let contents <- Lean.Elab.Command.liftIO <|
    IO.FS.readFile "/tmp/lean-information-audit-import-closure.json"
  let json <- match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError message
  let schema <- match Json.getObjVal? json "schema" >>= Json.getStr? with
    | .ok value => pure value
    | .error message => throwError message
  let occurrences := SealRecords.occurrencesForRoot env root
  let some occurrence := occurrences[0]?
    | throwError "missing staged occurrence state"
  let qualifier := root.toString ++ "/" ++
    (`LeanInformationAudit.Tests.ImportClosureProducer.objectArena).toString ++
    "/importedBool"
  let qualifierOf : Name -> Option String
    | .str (.str _ value) _ => some value
    | _ => none
  unless schema == "lean-intrinsic-information-escape-v2" &&
      occurrences.size == 1 && occurrence.rootId == root &&
      occurrence.catalogId == `importedBool &&
      qualifierOf occurrence.unitName == some qualifier &&
      qualifierOf occurrence.realizationName == some qualifier &&
      qualifierOf occurrence.certificateName == some qualifier do
    throwError "sealed occurrence identity is not root/catalog qualified"
  logInfo "import-closure qualified identity passed"

#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__primitive_realization
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit
#print axioms
  objectArena.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_catalog
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__lowers_escape
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__escape_enriched
#print axioms
  objectArena.«LeanInformationAudit.Tests.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__catalog_irredundant

end LeanInformationAudit.Tests.ImportClosureRoot
