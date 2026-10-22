import Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.LatticeSectorIntertwiner
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeSectorClassification
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeSectorIntertwiner.normalized_ground_detects_zero) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeSectorClassification.unit
  realizationName := `Reg.Support.LatticeSectorIntertwiner.NormalizedGround.family
  realizationSource := none
  generated := false
  arena := .source ⟨NormalizedGround.arena⟩
  objectArena := .source ⟨NormalizedGround.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source NormalizedGround.arena ⟨NormalizedGround.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature equality.readout equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeSectorClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeSectorClassification
