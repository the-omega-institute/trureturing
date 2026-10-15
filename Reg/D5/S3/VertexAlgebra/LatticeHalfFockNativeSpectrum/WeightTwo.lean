import Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.WeightTwo

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.WeightTwo

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
open LeanInformationAudit
open scoped TensorProduct

noncomputable section

def basisSignature : Signature where
  Params := Rank24Parameters
  State parameter := Fin parameter.lattice.rank ×
    _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.Half
      (groundRank parameter.lattice parameter.native)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def basisReadout : Realization basisSignature :=
  realize basisSignature (fun _ parameter label =>
    ((weightTwoBasis parameter.lattice parameter.native parameter.inverse parameter.leftInverse
      parameter.rightInverse parameter.rank24 label).val,
      (MvPolynomial.X (label.1, 0) : Oscillator parameter.lattice) ⊗ₜ[ℂ]
        Pi.single label.2 (1 : ℂ))) (fun empty => nomatch empty)

def basisArena : Arena where
  signature := basisSignature
  Law readout := ∀ parameter label,
    (readout.readout () parameter label).1 = (readout.readout () parameter label).2

theorem basisBridge : (type_of% (@weightTwoBasis_vector)) ↔ basisArena.Law basisReadout := by
  constructor
  · intro source parameter label
    exact source parameter.lattice parameter.native parameter.inverse parameter.leftInverse
      parameter.rightInverse parameter.rank24 label
  · intro law lattice native inverse leftInverse rightInverse rank24 label
    exact law ⟨⟨lattice, native, inverse, leftInverse, rightInverse⟩, rank24⟩ label

def basisEscapeFrom := @weightTwoCreation
def basisContinuation : Contract.Continuation Unit := .unknown
abbrev basisRegistrationObligation := Registration basisArena (type_of% (@weightTwoBasis_vector))
abbrev basisContractObligation := Contract.Registration (@weightTwoBasis_vector)
  (type_of% basisReadout) (type_of% basisEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.WeightTwo
