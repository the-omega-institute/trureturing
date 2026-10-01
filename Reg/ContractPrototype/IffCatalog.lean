/- L0 原型 -/
import Reg.ContractPrototype.Readout
import Reg.ContractPrototype.DualReadout
import LeanInformationAuditInterface.Contract.Catalog

namespace Reg.ContractPrototype.IffCatalog
open LeanInformationAudit.Contract

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.IffCatalog
    expected := #[Reg.ContractPrototype.Readout.expectation, Reg.ContractPrototype.DualReadout.expectation]
    source := #[Reg.ContractPrototype.Readout.expectation, Reg.ContractPrototype.DualReadout.expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.IffCatalog }

def sealDeclaration : Seal where
  rootId := `Reg.ContractPrototype.IffCatalog
  options := {}
end Reg.ContractPrototype.IffCatalog
