/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.ContractPrototype.Templates.DependentFamily
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe t s r o a

def enrollment : TemplateEnrollment (@realize.{t,s,r,o,a}) where
  name := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
  version := 1
  constructors := #[]
  options := {}
end Reg.ContractPrototype.Templates.DependentFamily
