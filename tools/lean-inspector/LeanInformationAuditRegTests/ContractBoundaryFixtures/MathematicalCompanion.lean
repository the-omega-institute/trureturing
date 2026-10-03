import LeanInformationAuditContract.Catalog
namespace ArchitectureFixtures.MathematicalCompanion
def entry : LeanInformationAudit.Contract.Seal := { rootId := `root, options := #[] }
theorem rootId_correct : entry.rootId = `root := rfl
end ArchitectureFixtures.MathematicalCompanion
