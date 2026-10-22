import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
import D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators VertexOperator

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  colour : Fin lattice.rank
  degree : ℕ

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice × ℤ × ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    ActualTensor parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    ((Ytw parameter.lattice parameter.native
      (((unitCurrent parameter.lattice parameter.colour)[[-(parameter.degree : ℤ) - 1]])
        state.1)).coeff state.2.1 state.2.2,
      (∑ᶠ offset : ℕ, ((parameter.degree + offset).choose parameter.degree : ℂ) •
        (nativeFirst parameter.lattice parameter.native parameter.colour parameter.degree
          state.1 state.2.1 state.2.2 offset + (-1 : ℂ) ^ parameter.degree •
            nativeSecond parameter.lattice parameter.native parameter.colour parameter.degree
              state.1 state.2.1 state.2.2 offset)) -
      ∑ᶠ offset : ℕ, Ring.choose (1 / 2 : ℂ) (offset + 1) •
        nativeCorrection parameter.lattice parameter.native parameter.colour parameter.degree
          state.1 state.2.1 state.2.2 offset))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    (realization.readout () parameter state).1 = (realization.readout () parameter state).2

theorem bridge : (type_of% (@native_descendant)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.colour parameter.degree
      state.1 state.2.1 state.2.2
  · intro law lattice native colour degree state exponent vector
    exact law ⟨lattice, native, colour, degree⟩ ⟨state, exponent, vector⟩

def escapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@native_descendant))
abbrev contractObligation := Contract.Registration (@native_descendant)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants
