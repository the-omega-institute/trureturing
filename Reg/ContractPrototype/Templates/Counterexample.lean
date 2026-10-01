/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord

namespace Reg.ContractPrototype.Templates.Counterexample
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord

def enrollment : TemplateEnrollment (@counterexampleRealization) where
  name := `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.counterexampleRealization
  version := 1
  constructors := #[]
  options := {}
end Reg.ContractPrototype.Templates.Counterexample
