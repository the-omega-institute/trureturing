import LeanInformationAuditInterface.Contract.Catalog

namespace Quality.MathCompanion
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := `Quality.root, catalogs := #[], options := #[] }
theorem pure_projection : entry.rootId = entry.rootId := rfl
end Quality.MathCompanion
