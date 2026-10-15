import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta
open _root_.D5.S3.VertexAlgebra.LatticeInvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

structure State (parameter : Parameters) where
  source : Carrier parameter.lattice
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
      ((Ytw parameter.lattice parameter.native state.source).coeff state.exponent state.vector),
     (Ytw parameter.lattice parameter.native (theta parameter.lattice state.source)).coeff
       state.exponent (sigmaTensor parameter.lattice parameter.native state.vector)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@Ytw_target_theta)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.native state.source state.exponent state.vector
  · intro law lattice native source exponent vector
    exact law ⟨lattice, native⟩ ⟨source, exponent, vector⟩

def escapeFrom := @Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Ytw_target_theta))
abbrev contractObligation := Contract.Registration (@Ytw_target_theta)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetTheta
