import Reg.Support.LatticeSectorIntertwiner
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.LatticeSectorIntertwiner
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeSectorIntertwiner.charge_homogeneity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner.unit
  realizationName := `Reg.Support.LatticeSectorIntertwiner.ChargeHomogeneity.family
  realizationSource := none
  generated := false
  arena := .source ⟨ChargeHomogeneity.arena⟩
  objectArena := .source ⟨ChargeHomogeneity.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ChargeHomogeneity.arena ⟨ChargeHomogeneity.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature equality.readout equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
