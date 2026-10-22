import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  word : List (Index lattice)

structure State (parameter : Parameters) where
  modes : ModeTuple parameter.lattice parameter.word
  exponent : ℤ
  vector : ActualTensor parameter.lattice parameter.native

def signature : Signature where
  Params := Parameters
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (sigmaTensor parameter.lattice parameter.native
      (flatCoefficient parameter.lattice parameter.native
        (chargedField parameter.lattice parameter.native parameter.charge)
          parameter.word state.modes state.exponent state.vector),
     ((-1 : ℂ) ^ parameter.word.length) •
       flatCoefficient parameter.lattice parameter.native
         (chargedField parameter.lattice parameter.native (-parameter.charge))
           parameter.word state.modes state.exponent
             (sigmaTensor parameter.lattice parameter.native state.vector)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@sigmaTensor_flatCoefficient)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.native parameter.charge parameter.word
      state.modes state.exponent state.vector
  · intro law lattice native charge word modes exponent vector
    exact law ⟨lattice, native, charge, word⟩ ⟨modes, exponent, vector⟩

def escapeFrom := @flatCoefficient
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@sigmaTensor_flatCoefficient))
abbrev contractObligation := Contract.Registration (@sigmaTensor_flatCoefficient)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaNormal
