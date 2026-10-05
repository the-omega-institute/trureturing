import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractTypeCarrierFixture
open LeanInformationAudit.Contract

def packed : Type 1 × Unit := (Seal.{0,0}, ())
def carrierAlias : Type 1 × Unit := packed
def hidden : packed.1 := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }

end LeanInformationAuditRegTests.ContractTypeCarrierFixture
