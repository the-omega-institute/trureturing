import Reg.Support.CyclicGroundOrbitFixedSpace

/-! Four-slot registration of the actual charge-cycle fixed-space theorem. -/

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.CyclicGroundOrbitFixedSpace
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace

def firstReturnAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace.first_return_ground_fixed_space)
    (Realization signature) LatticeData Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace.firstReturnUnit
  realizationName := `Reg.Support.CyclicGroundOrbitFixedSpace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature equality.readout equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
