import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.MissingCatalog.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.MissingSeal.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.IndependentExpected.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.SealedCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Complete.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Ordinary.Entry
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedCatalog.Entry
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.UnexpectedSeal.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateCatalog.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.DuplicateSeal.SealedCatalog

import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Spelling.Rootcatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs.Spelling.RootCatalogs
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
import LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.SealedCatalog

namespace LeanInformationAuditRegTests.ContractPaths
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
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
      discard <| Discovery.discoverWithStructure requirements #[owner]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"root.path.negative.{fixture}" (error.startsWith diagnostic)
    logInfo m!"CONTRACT_DIAGNOSTIC root.path.{fixture} {error}"
  for (fixture, catalogs, seals) in #[
      ("Complete.SealedCatalog", 1, 1), ("Complete.RootCatalog", 1, 0),
      ("Ordinary.Entry", 0, 0)] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.Catalogs ++ fixture.toName
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
run_meta do
  for leaf in #["RootCatalog", "SealedCatalog"] do
    let owner := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror ++ leaf.toName
    let requirements ← RootStructure.requiredFor #[owner] Discovery.moduleSource
    let accepted ← try
      let snapshot ← Discovery.discoverWithStructure requirements #[owner]
      pure (snapshot.registrations.size == 1 && snapshot.roots.isEmpty && snapshot.seals.isEmpty)
    catch _ => pure false
    assertTest s!"root.mirror.positive.{leaf}" accepted
end LeanInformationAuditRegTests.ContractPaths
