/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations

namespace Reg.ContractPrototype.Templates.Iff
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates

def enrollment : TemplateEnrollment (@iffRealization) where
  name := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
  version := 1
  constructors := #[]
  options := {}
end Reg.ContractPrototype.Templates.Iff
