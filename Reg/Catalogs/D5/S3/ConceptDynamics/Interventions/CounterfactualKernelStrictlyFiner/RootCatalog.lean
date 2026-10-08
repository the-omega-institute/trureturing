import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import Reg.Support.SharedArenaPeers

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.RootCatalog
