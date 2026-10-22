import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure ActionParameters where
  lattice : LatticeData
  charge : Charge lattice
  colour : Fin lattice.rank
  degree : ℕ

def actionSignature : Signature where
  Params := ActionParameters
  State parameter := Oscillator parameter.lattice × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice × Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def actionReadout : Realization actionSignature :=
  realize actionSignature (fun _ parameter state =>
    (Corr parameter.lattice parameter.charge
        (neutralPolynomialMode parameter.lattice parameter.colour parameter.charge parameter.degree
          state.1) state.2,
      neutralPolynomialMode parameter.lattice parameter.colour parameter.charge parameter.degree
        (Corr parameter.lattice parameter.charge state.1 state.2))) (fun empty => nomatch empty)

def actionArena : Arena where
  signature := actionSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem actionBridge : (type_of% (@Corr_neutralPolynomialMode)) ↔ actionArena.Law actionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.charge parameter.colour parameter.degree state.2 state.1
  · intro law lattice charge colour degree shift polynomial
    exact law ⟨lattice, charge, colour, degree⟩ ⟨polynomial, shift⟩

def actionEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr
def actionContinuation : Contract.Continuation Unit := .unknown
abbrev actionRealizationObligation := Registration actionArena (type_of% (@Corr_neutralPolynomialMode))
abbrev actionContractObligation := Contract.Registration (@Corr_neutralPolynomialMode)
  (type_of% actionReadout) (type_of% actionEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNormalCurrentAction
