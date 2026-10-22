import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.DirectSum

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.DirectSum

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
open LeanInformationAudit

noncomputable section

def inverseSignature : Signature where
  Params := Rank24Parameters
  State parameter := oddSector parameter.lattice parameter.native × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def inverseReadout : Realization inverseSignature :=
  realize inverseSignature (fun _ parameter state =>
    ((((integerDirectSumEquiv parameter.lattice parameter.native parameter.inverse
      parameter.leftInverse parameter.rightInverse parameter.rank24).symm state.1) state.2).val,
      integerProjector parameter.lattice parameter.native state.2 state.1.val))
    (fun empty => nomatch empty)

def inverseArena : Arena where
  signature := inverseSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem inverseBridge : (type_of% (@integer_inverse_coordinate)) ↔ inverseArena.Law inverseReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse parameter.leftInverse
      parameter.rightInverse parameter.rank24 state.1 state.2
  · intro law lattice native inverse leftInverse rightInverse rank24 state value
    exact law ⟨⟨lattice, native, inverse, leftInverse, rightInverse⟩, rank24⟩ ⟨state, value⟩

def inverseEscapeFrom := @integerAssembly
def inverseContinuation : Contract.Continuation Unit := .unknown
abbrev inverseRegistrationObligation := Registration inverseArena (type_of% (@integer_inverse_coordinate))
abbrev inverseContractObligation := Contract.Registration (@integer_inverse_coordinate)
  (type_of% inverseReadout) (type_of% inverseEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.DirectSum
