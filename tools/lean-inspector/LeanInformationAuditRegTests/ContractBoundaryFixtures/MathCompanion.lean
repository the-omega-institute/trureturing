import LeanInformationAuditContract.Catalog

namespace Quality.MathCompanion
def entry : LeanInformationAudit.Contract.Seal := { rootId := `Quality.root, options := #[] }
theorem pure_projection : entry.rootId = entry.rootId := rfl
end Quality.MathCompanion
