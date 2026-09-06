import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean
open LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer

namespace LeanInformationAudit.Tests.ImportClosureRoot

set_option linter.style.longLine false

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ImportClosureProducer"

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
  let some record := (SealRecords.forRoot env root)[0]?
    | throwError "missing staged catalog"
  let emitted <- match do
      let arenas <- json.getObjValAs? (Array Json) "arenas"
      let catalogName <- arenas[0]!.getObjValAs? String "catalog"
      let theorems <- arenas[0]!.getObjValAs? (Array Json) "theorems"
      let unit <- theorems[0]!.getObjValAs? String "unit"
      let certificate <- theorems[0]!.getObjValAs? String "certificate"
      pure (catalogName, unit, certificate) with
    | .ok value => pure value
    | .error message => throwError message
  unless emitted == (record.catalog.catalogName.toString,
      occurrence.unitName.toString, occurrence.certificateName.toString) &&
      env.contains occurrence.certificateName do
    throwError "emitted catalog/unit/certificate does not name the staged declarations"
  unless qualifierOf record.catalog.catalogName == some qualifier do
    throwError "compiled catalog qualifier mismatch"
  let some catalogInfo := env.find? record.catalog.catalogName
    | throwError "missing compiled catalog"
  let some catalogValue := catalogInfo.value?
    | throwError "compiled catalog has no value"
  let memberNames := catalogValue.getUsedConstants.filter fun name =>
    name.getString! == theoremUnitSuffix
  unless memberNames == #[occurrence.unitName] do
    throwError "compiled catalog members do not match retained root-qualified units"
  let some certificateInfo := env.find? occurrence.certificateName
    | throwError "missing compiled certificate"
  unless (certificateInfo.type.getUsedConstants.filter fun name =>
      name.getString! == theoremUnitSuffix) == #[occurrence.unitName] do
    throwError "certificate type does not bind the root-qualified catalog members"
  logInfo "import-closure qualified identity passed"

#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__primitive_realization
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit
#print axioms
  objectArena.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_catalog
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__lowers_escape
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__escape_enriched
#print axioms
  objectArena.«LeanInformationAudit.Tests.Occurrence.ImportClosureRoot/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__catalog_irredundant

end LeanInformationAudit.Tests.ImportClosureRoot
