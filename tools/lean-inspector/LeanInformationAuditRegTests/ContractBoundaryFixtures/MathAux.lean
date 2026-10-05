import LeanInformationAuditInterface.Contract.Catalog

namespace Quality.MathAux
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := `Quality.root, catalogs := #[], options := #[] }
def measure : Nat := entry.options.size
theorem pure_measure : measure = measure := rfl
end Quality.MathAux
