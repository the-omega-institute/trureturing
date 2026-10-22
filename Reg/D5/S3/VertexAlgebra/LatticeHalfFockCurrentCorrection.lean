import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure CorrectionParameters where
  lattice : LatticeData
  charge : Charge lattice
  index : Index lattice

def correctionSignature : Signature where
  Params := CorrectionParameters
  State parameter := Oscillator parameter.lattice × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice × Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def correctionReadout : Realization correctionSignature :=
  realize correctionSignature (fun _ parameter state =>
    (MvPolynomial.pderiv parameter.index
        (Corr parameter.lattice parameter.charge state.1 state.2),
      Corr parameter.lattice parameter.charge (MvPolynomial.pderiv parameter.index state.1) state.2))
    (fun empty => nomatch empty)

def correctionArena : Arena where
  signature := correctionSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem correctionBridge : (type_of% (@Corr_partial)) ↔ correctionArena.Law correctionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.charge parameter.index state.1 state.2
  · intro law lattice charge index polynomial shift
    exact law ⟨lattice, charge, index⟩ ⟨polynomial, shift⟩

def correctionEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr
def correctionContinuation : Contract.Continuation Unit := .unknown
abbrev correctionRealizationObligation := Registration correctionArena (type_of% (@Corr_partial))
abbrev correctionContractObligation := Contract.Registration (@Corr_partial)
  (type_of% correctionReadout) (type_of% correctionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
