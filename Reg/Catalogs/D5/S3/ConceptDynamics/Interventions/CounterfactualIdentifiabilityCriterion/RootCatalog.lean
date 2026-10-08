import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import Reg.Support.SharedArenaPeers

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable), theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, statementIdentity := some "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.RootCatalog
