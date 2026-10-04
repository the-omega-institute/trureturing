import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractTypeCarrierFixture
open LeanInformationAudit.Contract

def packed : Type × Unit := (Seal, ())
def carrierAlias : Type × Unit := packed
def hidden : packed.1 := { rootId := Lean.Name.anonymous, options := #[] }

end LeanInformationAuditRegTests.ContractTypeCarrierFixture
