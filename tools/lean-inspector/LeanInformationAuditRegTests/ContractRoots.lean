import LeanInformationAuditRegTests.CompiledFixtureReader

namespace LeanInformationAuditRegTests.ContractRoots
open Lean LeanInformationAudit.Contract
private def checkTest (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"compiled.fixture:{label}"

unsafe def check (reader : IO.Ref LeanInformationAudit.RawArtifacts.Store) : IO Unit := do
  let discover := CompiledFixtureReader.discover reader
  for (fixture, diagnostic) in #[
    ("DuplicateCatalog", "contract.root_structure:root_catalog_count:"),
    ("DuplicateSeal", "contract.root_structure:seal_count:"),
    ("Empty", "contract.root_structure:root_catalog_count:"),
    ("HiddenCatalog", "contract.cannot_decode:"),
    ("HiddenExpected", "contract.cannot_decode:"),
    ("HiddenSeal", "contract.cannot_decode:"),
    ("IndependentExpected", "contract.root_structure:independent_expected_not_allowed:"),
    ("MissingCatalog", "contract.root_structure:root_catalog_count:"),
    ("MissingSeal", "contract.root_structure:seal_count:"),
    ("UnexpectedCatalog", "contract.root_structure:root_catalog_count:"),
    ("UnexpectedSeal", "contract.root_structure:seal_count:"),
    ("WrongCatalogOwner", "contract.root_structure:root_catalog_owner:"),
    ("WrongSealOwner", "contract.root_structure:seal_owner:")] do
    let owner := (`LeanInformationAuditRegTests.ContractRootFixtures).str fixture
    let kind := if fixture.startsWith "Unexpected" then RootStructure.Kind.ordinary
      else RootStructure.Kind.sealedCatalog
    let requirement : RootStructure.Requirement := ⟨owner, `ContractRoot, kind⟩
    let error ← try
      discard <| discover #[requirement] #[owner]
      pure "accepted"
    catch ex => pure ex.toString
    checkTest s!"root.negative.{fixture}:{error}" (error.contains diagnostic)
    IO.println s!"CONTRACT_DIAGNOSTIC root.{fixture} {error}"
  let owner := `LeanInformationAuditRegTests.ContractRootFixtures.Complete
  let requirement : RootStructure.Requirement := ⟨owner, `ContractRoot, .sealedCatalog⟩
  let snapshot ← discover #[requirement] #[owner]
  checkTest "root.positive.Complete" (snapshot.roots.size == 1 && snapshot.seals.size == 1)
  for (label, requirements, modules, diagnostic) in #[
      ("FilteredModule", #[requirement], #[], "contract.root_structure:required_module_missing:"),
      ("DuplicateRequirement", #[requirement, requirement], #[owner], "contract.root_structure:duplicate_requirement:"),
      ("DuplicateModule", #[requirement], #[owner, owner], "contract.discovery:duplicate_module:")] do
    let error ← try
      discard <| discover requirements modules
      pure "accepted"
    catch ex => pure ex.toString
    checkTest s!"root.negative.{label}" (error.contains diagnostic)
  for (path, expected) in #[
      ("Reg/Catalogs/Arbitrary/RootCatalog.lean", RootStructure.Kind.catalog),
      ("Reg/Catalogs/Arbitrary/SealedCatalog.lean", RootStructure.Kind.sealedCatalog),
      ("Reg/D5/S3/RootCatalog.lean", RootStructure.Kind.ordinary),
      ("Reg/D5/S3/SealedCatalog.lean", RootStructure.Kind.ordinary),
      ("Outside/RootCatalog.lean", RootStructure.Kind.ordinary),
      ("Reg/Catalogs/Ordinary.lean", RootStructure.Kind.ordinary),
      ("Reg/SealedCatalog/Ordinary.lean", RootStructure.Kind.ordinary)] do
    checkTest s!"root.path.{path}"
      (RootStructure.kindFromPath path == expected)
  let sourceError ← try
    discard <| RootStructure.requiredFor #[`Reg.AbsentSource] fun _ =>
      LeanInformationAudit.Repository.source "Reg/AbsentSource.lean"
    pure "accepted"
  catch ex => pure ex.toString
  checkTest "root.path.required_source_missing"
    (sourceError.startsWith "contract.root_structure:required_source_missing:")

end LeanInformationAuditRegTests.ContractRoots
