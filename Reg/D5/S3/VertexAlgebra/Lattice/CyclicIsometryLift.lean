import Reg.Support.CyclicIsometryLift
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.CyclicIsometryLift
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
def canonicalAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.canonical_power)
    (Realization CanonicalPower.signature) LatticeData Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.canonicalUnit
  realizationName := `Reg.Support.CyclicIsometryLift.CanonicalPower.family
  realizationSource := none
  generated := false
  arena := .source ⟨CanonicalPower.arena⟩
  objectArena := .source ⟨CanonicalPower.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source CanonicalPower.arena ⟨CanonicalPower.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CanonicalPower.signature CanonicalPower.equality.readout
    CanonicalPower.equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def cyclicAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.cyclic_lift)
    (Realization CyclicLift.signature) LatticeData Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.cyclicUnit
  realizationName := `Reg.Support.CyclicIsometryLift.CyclicLift.family
  realizationSource := none
  generated := false
  arena := .source ⟨CyclicLift.arena⟩
  objectArena := .source ⟨CyclicLift.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source CyclicLift.arena ⟨CyclicLift.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CyclicLift.signature CyclicLift.equality.readout
    CyclicLift.equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
