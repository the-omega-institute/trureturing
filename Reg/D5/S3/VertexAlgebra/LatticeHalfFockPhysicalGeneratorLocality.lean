import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  determinant : IsUnit lattice.G.det
  index : Index lattice
  charge : Charge lattice
  parity : ℤ

def generatorSignature : Signature where
  Params := Parameters
  State parameter := ℤ × ℤ × ActualTensor parameter.lattice parameter.determinant
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.determinant
  Anchor := Empty
  finiteAnchor := inferInstance

def generatorReadout : Realization generatorSignature :=
  realize generatorSignature (fun _ parameter state =>
    delta^[parameter.index.2 + 1]
      (commutator (physicalJet parameter.lattice parameter.determinant parameter.index)
        (physicalSlice parameter.lattice parameter.determinant
          (chargedField parameter.lattice parameter.determinant parameter.charge)
          parameter.parity)) state.1 state.2.1 state.2.2)
    (fun empty => nomatch empty)

def generatorArena : Arena where
  signature := generatorSignature
  Law readout := ∀ parameter state, readout.readout () parameter state =
    (0 : ActualTensor parameter.lattice parameter.determinant)

theorem generatorBridge : (type_of% (@physicalJet_charge_locality)) ↔
    generatorArena.Law generatorReadout := by
  constructor
  · intro source parameter state
    have killed := source parameter.lattice parameter.determinant parameter.index
      parameter.charge parameter.parity
    exact congrArg (fun distribution : ℤ → ℤ →
      Module.End ℂ (ActualTensor parameter.lattice parameter.determinant) =>
      distribution state.1 state.2.1 state.2.2) killed
  · intro law lattice determinant index charge parity
    funext left right
    apply LinearMap.ext
    intro vector
    exact law ⟨lattice, determinant, index, charge, parity⟩ ⟨left, right, vector⟩

def generatorEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalJet
def generatorContinuation : Contract.Continuation Unit := .unknown
abbrev generatorRealizationObligation :=
  Registration generatorArena (type_of% (@physicalJet_charge_locality))
abbrev generatorContractObligation := Contract.Registration (@physicalJet_charge_locality)
  (type_of% generatorReadout) (type_of% generatorEscapeFrom) Unit
abbrev jetPairContractObligation := Contract.Registration (@physicalJet_pair_locality)
  (type_of% generatorReadout) (type_of% generatorEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
