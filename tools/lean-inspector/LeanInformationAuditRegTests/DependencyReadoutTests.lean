import LeanInformationAudit.DependencyReadout
import LeanInformationAuditRegTests.DependencyFixtures.Users

namespace LeanInformationAuditRegTests.DependencyReadoutTests
open Lean LeanInformationAudit

private unsafe def checkMissingPrivatePart : IO Unit := do
  let owner := `LeanInformationAuditRegTests.DependencyFixtures.Base
  let original ← findOLean owner
  let saved ← searchPathRef.get
  IO.FS.withTempDir fun directory => do
    let copy := modToFilePath directory owner "olean"
    IO.FS.createDirAll copy.parent.get!
    IO.FS.writeBinFile copy (← IO.FS.readBinFile original)
    IO.FS.writeBinFile (copy.addExtension "server") (← IO.FS.readBinFile (original.addExtension "server"))
    searchPathRef.set (directory :: saved)
    try
      let raw ← DependencyReadout.readModules #[owner]
      let modules ← IO.ofExcept (raw.getObjValAs? (Array Json) "modules")
      let detail ← IO.ofExcept (modules[0]!.getObjValAs? String "detail")
      unless (← IO.ofExcept (modules[0]!.getObjValAs? String "status")) == "read_failed" &&
          (detail.splitOn "raw.missing_olean_part").length > 1 &&
          (detail.splitOn ":private").length > 1 do
        throw <| IO.userError "[FAIL] CompiledDependencyMissingPrivatePart"
    finally searchPathRef.set saved

unsafe def check : IO Unit := do
  let raw ← DependencyReadout.readModules #[
    `LeanInformationAuditRegTests.DependencyFixtures.Base,
    `LeanInformationAuditRegTests.DependencyFixtures.Users]
  let modules ← IO.ofExcept (raw.getObjValAs? (Array Json) "modules")
  let mut rows : Array Json := #[]
  for row in modules do
    unless (← IO.ofExcept (row.getObjValAs? String "status")) == "ok" do
      throw <| IO.userError s!"[FAIL] CompiledDependencyParts: {row.compress}"
    rows := rows ++ (← IO.ofExcept (row.getObjValAs? (Array Json) "declarations"))
  let find (name : String) : IO Json := do
    let some row := rows.find? (fun r => (r.getObjValAs? String "name").toOption == some name)
      | throw <| IO.userError s!"[FAIL] CompiledDependencyParts:missing:{name}"
    return row
  let contains (row : Json) (side name : String) : Bool :=
    ((row.getObjValAs? (Array String) side).toOption.getD #[]).contains name
  let direct ← find "DependencyFixture.Users.direct"
  unless contains direct "value" "DependencyFixture.seed" &&
      !contains direct "type" "DependencyFixture.seed" do
    throw <| IO.userError "[FAIL] CompiledDependencyValueNotType"
  let typeOnly ← find "DependencyFixture.Users.typeOnly"
  unless contains typeOnly "type" "DependencyFixture.Token" &&
      !contains typeOnly "value" "DependencyFixture.Token" &&
      !contains typeOnly "value" "DependencyFixture.seed" do
    throw <| IO.userError "[FAIL] CompiledDependencyTypeOnly"
  unless !contains (← find "DependencyFixture.Users.importOnly") "value" "DependencyFixture.seed" do
    throw <| IO.userError "[FAIL] CompiledDependencyImportOnly"
  let helper ← find "DependencyFixture.Users.throughHelper"
  let values ← IO.ofExcept (helper.getObjValAs? (Array String) "value")
  unless values.any (fun name => name.startsWith "_private.") &&
      rows.any (fun r => (r.getObjValAs? Bool "private").toOption == some true &&
        contains r "value" "DependencyFixture.seed") do
    throw <| IO.userError "[FAIL] CompiledDependencyPrivatePath"
  let generated ← find "DependencyFixture.Users.generated"
  let generatedValues ← IO.ofExcept (generated.getObjValAs? (Array String) "value")
  unless rows.any (fun row =>
      (row.getObjValAs? Bool "internal").toOption == some true &&
      ((row.getObjValAs? String "name").toOption.any generatedValues.contains)) do
    throw <| IO.userError "[FAIL] CompiledDependencyGeneratedPath"
  let absent ← IO.ofExcept ((← find "DependencyFixture.absentValue").getObjVal? "value")
  let empty ← IO.ofExcept ((← find "DependencyFixture.emptyValue").getObjVal? "value")
  unless absent == Json.null && empty == toJson (#[] : Array String) do
    throw <| IO.userError "[FAIL] CompiledDependencyNoneVersusEmpty"
  unless contains (← find "DependencyFixture.Shape") "type" "DependencyFixture.Shape.point" do
    throw <| IO.userError "[FAIL] CompiledDependencyInductiveConstructors"
  checkMissingPrivatePart
  IO.println "[PASS] CompiledDependencyParts: value/type/import, private path, none/empty, constructors"

end LeanInformationAuditRegTests.DependencyReadoutTests
