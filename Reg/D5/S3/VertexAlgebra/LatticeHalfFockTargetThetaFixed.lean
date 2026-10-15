import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed
open _root_.D5.S3.VertexAlgebra.LatticeInvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

structure State (parameter : Parameters) where
  source : Carrier parameter.lattice
  fixed : theta parameter.lattice source = source
  exponent : ℤ
  vector : ActualTensor parameter.lattice parameter.native
  odd : vector ∈ oddTarget parameter.lattice parameter.native

def signature : Signature where
  Params := Parameters
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (Ytw parameter.lattice parameter.native state.source).coeff state.exponent state.vector ∈
      oddTarget parameter.lattice parameter.native) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state, observation.readout () parameter state

theorem bridge : (type_of% (@Ytw_fixed_oddTarget)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.native state.source state.fixed
      state.exponent state.vector state.odd
  · intro law lattice native source fixed exponent vector odd
    exact law ⟨lattice, native⟩ ⟨source, fixed, exponent, vector, odd⟩

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Ytw_fixed_oddTarget))
abbrev contractObligation := Contract.Registration (@Ytw_fixed_oddTarget)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaFixed
