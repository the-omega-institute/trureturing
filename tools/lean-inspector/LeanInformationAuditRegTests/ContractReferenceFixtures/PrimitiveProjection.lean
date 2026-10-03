import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.PrimitiveProjection
def entry : Contract.Seal := { rootId := `root, options := #[] }
def value : Name := by_elab
  return Expr.proj ``Contract.Seal 0 (mkConst ``entry)
end ContractReferenceFixtures.PrimitiveProjection
