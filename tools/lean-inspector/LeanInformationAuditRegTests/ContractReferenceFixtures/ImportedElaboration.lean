import LeanInformationAuditRegTests.ContractReferenceFixtures.ElaborationProvider
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ImportedElaboration
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def helper : Unit := emit_equation
end ContractReferenceFixtures.ImportedElaboration
