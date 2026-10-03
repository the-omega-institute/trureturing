import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractPathFixtures.MissingCatalog.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.MissingSeal.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.IndependentExpected.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Complete.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Complete.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Ordinary.Entry
import LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedCatalog.Entry
import LeanInformationAuditRegTests.ContractPathFixtures.UnexpectedSeal.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.DuplicateCatalog.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.DuplicateSeal.SealedCatalog

namespace LeanInformationAuditRegTests.ContractPaths
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  for (fixture, diagnostic) in #[
      ("MissingCatalog.SealedCatalog", "contract.root_structure:root_catalog_count:"),
      ("MissingSeal.SealedCatalog", "contract.root_structure:seal_count:"),
      ("IndependentExpected.SealedCatalog", "contract.root_structure:independent_expected_not_allowed:"),
      ("UnexpectedCatalog.Entry", "contract.root_structure:root_catalog_count:"),
      ("UnexpectedSeal.RootCatalog", "contract.root_structure:seal_count:"),
      ("DuplicateCatalog.RootCatalog", "contract.root_structure:root_catalog_count:"),
      ("DuplicateSeal.SealedCatalog", "contract.root_structure:seal_count:")] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures ++ fixture.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let error ← try
      discard <| Discovery.discoverWithStructure requirements #[owner]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"root.path.negative.{fixture}" (error.startsWith diagnostic)
    logInfo m!"CONTRACT_DIAGNOSTIC root.path.{fixture} {error}"
  for (fixture, catalogs, seals) in #[
      ("Complete.SealedCatalog", 1, 1), ("Complete.RootCatalog", 1, 0),
      ("Ordinary.Entry", 0, 0)] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures ++ fixture.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let snapshot ← Discovery.discoverWithStructure requirements #[owner]
    assertTest s!"root.path.positive.{fixture}"
      (snapshot.roots.size == catalogs && snapshot.seals.size == seals)
    let error ← try
      discard <| Discovery.discoverWithStructure requirements #[]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"root.path.filtered.{fixture}"
      (error.startsWith "contract.root_structure:required_module_missing:")
end LeanInformationAuditRegTests.ContractPaths
