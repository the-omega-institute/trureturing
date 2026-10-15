import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Integral

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Integral

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
open LeanInformationAudit

noncomputable section

def integralSignature : Signature where
  Params := Rank24Parameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Submodule ℂ (ActualTensor parameter.lattice parameter.native) ×
    Submodule ℂ (ActualTensor parameter.lattice parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def integralReadout : Realization integralSignature :=
  realize integralSignature (fun _ parameter _ =>
    (⨆ value : ℤ, eigenspace parameter.lattice parameter.native parameter.inverse (value : ℂ),
      oddSector parameter.lattice parameter.native)) (fun empty => nomatch empty)

def integralArena : Arena where
  signature := integralSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem integralBridge : (type_of% (@integral_supremum)) ↔ integralArena.Law integralReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse parameter.leftInverse
      parameter.rightInverse parameter.rank24
  · intro law lattice native inverse leftInverse rightInverse rank24
    exact law ⟨⟨lattice, native, inverse, leftInverse, rightInverse⟩, rank24⟩ ()

def integralEscapeFrom := @oscillatorNegation
def integralContinuation : Contract.Continuation Unit := .unknown
abbrev integralRegistrationObligation := Registration integralArena (type_of% (@integral_supremum))
abbrev integralContractObligation := Contract.Registration (@integral_supremum)
  (type_of% integralReadout) (type_of% integralEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Integral
