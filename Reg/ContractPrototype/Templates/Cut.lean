/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope

namespace Reg.ContractPrototype.Templates.Cut
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

def enrollment : TemplateEnrollment (@cutRealization) where
  name := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization
  version := 1
  constructors := #[{
    name := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom
    type := D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom }]
  options := {}
end Reg.ContractPrototype.Templates.Cut
