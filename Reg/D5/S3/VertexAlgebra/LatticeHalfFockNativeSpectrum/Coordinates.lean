import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure SpectrumParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftInverse : inverse * gramComplex lattice = 1
  rightInverse : gramComplex lattice * inverse = 1

structure Rank24Parameters extends SpectrumParameters where
  rank24 : lattice.rank = 24

def coordinateSignature : Signature where
  Params := SpectrumParameters
  State parameter := ActualTensor parameter.lattice parameter.native × Occupation parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualGround parameter.lattice parameter.native ×
    ActualGround parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateReadout : Realization coordinateSignature :=
  realize coordinateSignature (fun _ parameter state =>
    (coefficients parameter.lattice parameter.native
      (nativeL0 parameter.lattice parameter.native parameter.inverse state.1) state.2,
      weightValue parameter.lattice (occupationWeight parameter.lattice state.2) •
        coefficients parameter.lattice parameter.native state.1 state.2)) (fun empty => nomatch empty)

def coordinateArena : Arena where
  signature := coordinateSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem coordinateBridge : (type_of% (@coefficient_diagonalization)) ↔
    coordinateArena.Law coordinateReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.inverse parameter.leftInverse
      parameter.rightInverse state.1 state.2
  · intro law lattice native inverse leftInverse rightInverse state exponent
    exact law ⟨lattice, native, inverse, leftInverse, rightInverse⟩ ⟨state, exponent⟩

def coordinateEscapeFrom := @nativeL0
def coordinateContinuation : Contract.Continuation Unit := .unknown
abbrev coordinateRegistrationObligation := Registration coordinateArena (type_of% (@coefficient_diagonalization))
abbrev coordinateContractObligation := Contract.Registration (@coefficient_diagonalization)
  (type_of% coordinateReadout) (type_of% coordinateEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Coordinates
