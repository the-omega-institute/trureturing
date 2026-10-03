import LeanInformationAuditContract.Catalog

namespace Quality.MathAux
def entry : LeanInformationAudit.Contract.Seal := { rootId := `Quality.root, options := #[] }
def measure : Nat := entry.options.size
theorem pure_measure : measure = measure := rfl
end Quality.MathAux
