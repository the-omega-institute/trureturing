import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import Reg.Support.SharedArenaPeers

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not), theoremName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:8b649e1191e8e2c40391ae6cd263fafc09d16bf7c6c684f60f8ff7430cc97052", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not), theoremName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:8b649e1191e8e2c40391ae6cd263fafc09d16bf7c6c684f60f8ff7430cc97052", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.RootCatalog
