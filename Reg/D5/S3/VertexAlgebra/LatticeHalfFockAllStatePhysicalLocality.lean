import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  determinant : IsUnit lattice.G.det
  first : Carrier lattice
  second : Carrier lattice

def localitySignature : Signature where
  Params := Parameters
  State parameter := ℕ × ℤ × ℤ × ActualTensor parameter.lattice parameter.determinant
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.determinant
  Anchor := Empty
  finiteAnchor := inferInstance

def localityReadout : Realization localitySignature :=
  realize localitySignature (fun _ parameter state =>
    (∑ offset ∈ Finset.range (state.1 + 1),
      (((-1 : ℂ) ^ offset) * (state.1.choose offset : ℂ)) •
        ((Ytw parameter.lattice parameter.determinant parameter.first).coeff
            (state.2.1 - 2 * ((state.1 - offset : ℕ) : ℤ))
          ((Ytw parameter.lattice parameter.determinant parameter.second).coeff
            (state.2.2.1 - 2 * (offset : ℤ)) state.2.2.2) -
          (Ytw parameter.lattice parameter.determinant parameter.second).coeff
            (state.2.2.1 - 2 * (offset : ℤ))
          ((Ytw parameter.lattice parameter.determinant parameter.first).coeff
            (state.2.1 - 2 * ((state.1 - offset : ℕ) : ℤ)) state.2.2.2)) :
        ActualTensor parameter.lattice parameter.determinant))
    (fun empty => nomatch empty)

def localityArena : Arena where
  signature := localitySignature
  Law readout := ∀ parameter, ∃ order : ℕ,
    ∀ firstExponent secondExponent vector,
      readout.readout () parameter (order, firstExponent, secondExponent, vector) =
        (0 : ActualTensor parameter.lattice parameter.determinant)

theorem localityBridge :
    (type_of% (@Ytw_physical_locality)) ↔ localityArena.Law localityReadout := by
  constructor
  · intro source parameter
    exact source parameter.lattice parameter.determinant parameter.first parameter.second
  · intro law lattice determinant first second
    exact law ⟨lattice, determinant, first, second⟩

def localityEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
def localityContinuation : Contract.Continuation Unit := .unknown
abbrev localityRealizationObligation :=
  Registration localityArena (type_of% (@Ytw_physical_locality))
abbrev localityContractObligation := Contract.Registration (@Ytw_physical_locality)
  (type_of% localityReadout) (type_of% localityEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
