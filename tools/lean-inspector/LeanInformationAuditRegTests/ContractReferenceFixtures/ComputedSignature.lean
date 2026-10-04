import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.ComputedSignature
def signature : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature := {
  Params := (fun T : Type => T) Contract.Seal
  State := fun _ => Unit, Role := Unit, finiteRole := inferInstance
  nonemptyRole := inferInstance, Output := fun _ _ => Unit
  Anchor := Unit, finiteAnchor := inferInstance }
def value : signature.Params := { rootId := `root, options := #[] }
end ContractReferenceFixtures.ComputedSignature
