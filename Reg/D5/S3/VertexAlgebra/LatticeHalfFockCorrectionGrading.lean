import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MvPolynomial

noncomputable section

structure Parameters where
  lattice : LatticeData
  charge : Charge lattice

def wordSignature : Signature where
  Params := Parameters
  State parameter := List (Index parameter.lattice)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def wordReadout : Realization wordSignature :=
  realize wordSignature (fun _ parameter word => correctionWord parameter.lattice parameter.charge word)
    (fun empty => nomatch empty)

def wordArena : Arena where
  signature := wordSignature
  Law readout := ∀ parameter word,
    IsWeightedHomogeneous (correctionWeight parameter.lattice)
      (readout.readout () parameter word) (wordWeight parameter.lattice word)

theorem wordBridge : (type_of% (@correctionWord_weighted)) ↔ wordArena.Law wordReadout := by
  constructor
  · intro source parameter word
    exact source parameter.lattice parameter.charge word
  · intro law lattice charge word
    exact law ⟨lattice, charge⟩ word

def coefficientSignature : Signature where
  Params := Parameters
  State parameter := {state : List (Index parameter.lattice) × ℕ × (Index parameter.lattice →₀ ℕ) //
    coeff state.2.2 ((optionEquivLeft ℂ (Index parameter.lattice)
      (correctionWord parameter.lattice parameter.charge state.1)).coeff state.2.1) ≠ 0}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientReadout : Realization coefficientSignature :=
  realize coefficientSignature (fun _ parameter source =>
    (source.val.2.1 + Finsupp.weight (sourceWeight parameter.lattice) source.val.2.2,
      wordWeight parameter.lattice source.val.1)) (fun empty => nomatch empty)

def coefficientArena : Arena where
  signature := coefficientSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem coefficientBridge : (type_of% (@correctionWord_coefficient_weight)) ↔
    coefficientArena.Law coefficientReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.charge state.val.1 state.val.2.1 state.val.2.2 state.property
  · intro law lattice charge word shift exponent nonzero
    exact law ⟨lattice, charge⟩ ⟨⟨word, shift, exponent⟩, nonzero⟩

def eulerSignature : Signature where
  Params := Parameters
  State parameter := Oscillator parameter.lattice × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice × Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def eulerReadout : Realization eulerSignature :=
  realize eulerSignature (fun _ parameter source =>
    (oscillatorEuler parameter.lattice (Corr parameter.lattice parameter.charge source.1 source.2) +
      (source.2 : ℂ) • Corr parameter.lattice parameter.charge source.1 source.2,
      Corr parameter.lattice parameter.charge (oscillatorEuler parameter.lattice source.1) source.2))
    (fun empty => nomatch empty)

def eulerArena : Arena where
  signature := eulerSignature
  Law readout := ∀ parameter source,
    (readout.readout () parameter source).1 = (readout.readout () parameter source).2

theorem eulerBridge : (type_of% (@Corr_Euler)) ↔ eulerArena.Law eulerReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.charge state.1 state.2
  · intro law lattice charge polynomial shift
    exact law ⟨lattice, charge⟩ ⟨polynomial, shift⟩

def correctionEscapeFrom := @Corr
def correctionContinuation : Contract.Continuation Unit := .unknown

abbrev wordRealizationObligation := Registration wordArena (type_of% (@correctionWord_weighted))
abbrev wordContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@correctionWord_weighted)
  (type_of% wordReadout) (type_of% correctionEscapeFrom) Unit
abbrev coefficientRealizationObligation := Registration coefficientArena
  (type_of% (@correctionWord_coefficient_weight))
abbrev coefficientContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@correctionWord_coefficient_weight)
  (type_of% coefficientReadout) (type_of% correctionEscapeFrom) Unit
abbrev eulerRealizationObligation := Registration eulerArena (type_of% (@Corr_Euler))
abbrev eulerContractObligation := Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Corr_Euler)
  (type_of% eulerReadout) (type_of% correctionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading
