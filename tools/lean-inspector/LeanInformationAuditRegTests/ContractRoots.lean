import LeanInformationAuditRegTests.ContractGuards
import Reg.Catalogs.IffRegistrations
import LeanInformationAuditRegTests.ContractRootFixtures.Complete
import LeanInformationAuditRegTests.ContractRootFixtures.DuplicateCatalog
import LeanInformationAuditRegTests.ContractRootFixtures.DuplicateSeal
import LeanInformationAuditRegTests.ContractRootFixtures.Empty
import LeanInformationAuditRegTests.ContractRootFixtures.HiddenCatalog
import LeanInformationAuditRegTests.ContractRootFixtures.HiddenExpected
import LeanInformationAuditRegTests.ContractRootFixtures.HiddenSeal
import LeanInformationAuditRegTests.ContractRootFixtures.IndependentExpected
import LeanInformationAuditRegTests.ContractRootFixtures.MissingCatalog
import LeanInformationAuditRegTests.ContractRootFixtures.MissingSeal
import LeanInformationAuditRegTests.ContractRootFixtures.UnexpectedCatalog
import LeanInformationAuditRegTests.ContractRootFixtures.UnexpectedSeal
import LeanInformationAuditRegTests.ContractRootFixtures.WrongCatalogOwner
import LeanInformationAuditRegTests.ContractRootFixtures.WrongSealOwner

namespace LeanInformationAuditRegTests.ContractRoots
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
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
      discard <| Discovery.discoverWithStructure #[requirement] #[owner]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"root.negative.{fixture}" (error.startsWith diagnostic)
    logInfo m!"CONTRACT_DIAGNOSTIC root.{fixture} {error}"
  let owner := `LeanInformationAuditRegTests.ContractRootFixtures.Complete
  let requirement : RootStructure.Requirement := ⟨owner, `ContractRoot, .sealedCatalog⟩
  let snapshot ← Discovery.discoverWithStructure #[requirement] #[owner]
  assertTest "root.positive.Complete" (snapshot.roots.size == 1 && snapshot.seals.size == 1)
  for (label, requirements, modules, diagnostic) in #[
      ("FilteredModule", #[requirement], #[], "contract.root_structure:required_module_missing:"),
      ("DuplicateRequirement", #[requirement, requirement], #[owner], "contract.root_structure:duplicate_requirement:"),
      ("DuplicateModule", #[requirement], #[owner, owner], "contract.discovery:duplicate_module:")] do
    let error ← try
      discard <| Discovery.discoverWithStructure requirements modules
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"root.negative.{label}" (error.startsWith diagnostic)
  for (path, expected) in #[
      ("Reg/Catalogs/Arbitrary/RootCatalog.lean", RootStructure.Kind.catalog),
      ("Reg/Catalogs/Arbitrary/SealedCatalog.lean", RootStructure.Kind.sealedCatalog),
      ("Reg/D5/S3/RootCatalog.lean", RootStructure.Kind.ordinary),
      ("Reg/D5/S3/SealedCatalog.lean", RootStructure.Kind.ordinary),
      ("Outside/RootCatalog.lean", RootStructure.Kind.ordinary),
      ("Reg/Catalogs/Ordinary.lean", RootStructure.Kind.ordinary),
      ("Reg/SealedCatalog/Ordinary.lean", RootStructure.Kind.ordinary)] do
    assertTest s!"root.path.{path}"
      (RootStructure.kindFromPath path == expected)
  let requirements ← RootStructure.required (← getEnv)
  assertTest "root.path.pre_migration_ordinary"
    (requirements.any fun r => r.owner == `Reg.Catalogs.IffRegistrations && r.kind == .ordinary)
  let sourceError ← try
    discard <| RootStructure.requiredFor #[`Reg.AbsentSource] fun _ =>
      LeanInformationAudit.Repository.source "Reg/AbsentSource.lean"
    pure "accepted"
  catch ex => ex.toMessageData.toString
  assertTest "root.path.required_source_missing"
    (sourceError.startsWith "contract.root_structure:required_source_missing:")
  let error ← try
    discard <| Discovery.discover #[]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  assertTest "root.path.filtered_production_module"
    (error.startsWith "contract.root_structure:required_module_missing:")

end LeanInformationAuditRegTests.ContractRoots
