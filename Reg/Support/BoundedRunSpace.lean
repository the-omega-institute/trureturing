import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
open _root_.D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
register_information_template cutRealization constructors 1
  [D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom]
end
