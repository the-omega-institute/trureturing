import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.PrimitiveProjection
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def value : Name := by_elab
  return Expr.proj ``Contract.Seal 0 (mkConst ``entry)
end ContractReferenceFixtures.PrimitiveProjection
