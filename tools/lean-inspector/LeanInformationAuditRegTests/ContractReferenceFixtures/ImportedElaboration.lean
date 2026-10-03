import LeanInformationAuditRegTests.ContractReferenceFixtures.ElaborationProvider
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ImportedElaboration
def entry : Contract.Seal := { rootId := `root, options := #[] }
def helper : Unit := emit_equation
end ContractReferenceFixtures.ImportedElaboration
