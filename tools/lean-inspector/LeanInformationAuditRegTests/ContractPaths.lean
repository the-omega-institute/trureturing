import LeanInformationAuditRegTests.CompiledFixtureReader


namespace LeanInformationAuditRegTests.ContractPaths
open Lean LeanInformationAudit.Contract
private def checkTest (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"compiled.fixture:{label}"

unsafe def check (reader : IO.Ref LeanInformationAudit.RawArtifacts.Store) : IO Unit := do
  let discover := CompiledFixtureReader.discover reader
  for (fixture, diagnostic) in #[
      ("Spelling.Rootcatalog", "contract.root_structure:root_catalog_count:"),
      ("Spelling.RootCatalogs", "contract.root_structure:root_catalog_count:"),
      ("MissingCatalog.SealedCatalog", "contract.root_structure:root_catalog_count:"),
      ("MissingSeal.SealedCatalog", "contract.root_structure:seal_count:"),
      ("IndependentExpected.SealedCatalog", "contract.root_structure:independent_expected_not_allowed:"),
      ("UnexpectedCatalog.Entry", "contract.root_structure:root_catalog_count:"),
      ("UnexpectedSeal.RootCatalog", "contract.root_structure:seal_count:"),
      ("DuplicateCatalog.RootCatalog", "contract.root_structure:root_catalog_count:"),
      ("DuplicateSeal.SealedCatalog", "contract.root_structure:seal_count:")] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs ++ fixture.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let error ← try
      discard <| discover requirements #[owner]
      pure "accepted"
    catch ex => pure ex.toString
    checkTest s!"root.path.negative.{fixture}:{error}" (error.contains diagnostic)
    IO.println s!"CONTRACT_DIAGNOSTIC root.path.{fixture} {error}"
  for (fixture, catalogs, seals) in #[
      ("Complete.SealedCatalog", 1, 1), ("Complete.RootCatalog", 1, 0),
      ("Ordinary.Entry", 0, 0)] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs ++ fixture.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let snapshot ← discover requirements #[owner]
    checkTest s!"root.path.positive.{fixture}"
      (snapshot.roots.size == catalogs && snapshot.seals.size == seals)
    let error ← try
      discard <| discover requirements #[]
      pure "accepted"
    catch ex => pure ex.toString
    checkTest s!"root.path.filtered.{fixture}"
      (error.startsWith "contract.root_structure:required_module_missing:")
unsafe def checkMirror (reader : IO.Ref LeanInformationAudit.RawArtifacts.Store) : IO Unit := do
  let discover := CompiledFixtureReader.discover reader
  for leaf in #["RootCatalog", "SealedCatalog"] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror ++ leaf.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let accepted ← try
      let snapshot ← discover requirements #[owner]
      pure (snapshot.registrations.size == 1 && snapshot.roots.isEmpty && snapshot.seals.isEmpty)
    catch _ => pure false
    checkTest s!"root.mirror.positive.{leaf}" accepted
end LeanInformationAuditRegTests.ContractPaths
