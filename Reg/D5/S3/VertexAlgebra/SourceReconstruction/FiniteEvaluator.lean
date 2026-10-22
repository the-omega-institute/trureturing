import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight
import Reg.D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants
import D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det

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
    (evaluate parameter.lattice parameter.native state.1 state.2.1 state.2.2,
      (Ytw parameter.lattice parameter.native state.1).coeff state.2.1 state.2.2))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    (realization.readout () parameter state).1 = (realization.readout () parameter state).2

theorem bridge : (type_of% (@evaluate_agrees)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native state.1 state.2.1 state.2.2
  · intro law lattice native state exponent vector
    exact law ⟨lattice, native⟩ ⟨state, exponent, vector⟩

def escapeFrom := @_root_.D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator.evaluateFuel
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@evaluate_agrees))
abbrev contractObligation := Contract.Registration (@evaluate_agrees)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.FiniteEvaluator
