import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow
import Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
import Reg.Support.TemplateShadowContract
import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.TemplateShadowContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Seal the existing finite catalogs under the production seal limit.
#seal_information_theory


section
open LeanInformationAudit
end
