import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot
import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.InformationRoot
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.InformationRoot
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot
import Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.InformationRoot
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.InformationRoot
import Reg.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.InformationRoot
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.InformationRoot
import Reg.Support.InformationRootContract
import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.InformationRootContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The production root seals eleven finite catalogs under the existing limit.
#seal_information_theory
