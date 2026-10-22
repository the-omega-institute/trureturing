import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped VertexOperator

noncomputable section

structure Parameters where
  lattice : LatticeData
  colour : Fin lattice.rank
  degree : ℕ
  offset : ℕ

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (sourceWeightBound parameter.lattice
      (((unitCurrent parameter.lattice parameter.colour)
        [[-(parameter.degree : ℤ) + parameter.offset]]) state),
      sourceWeightBound parameter.lattice state + parameter.degree + 1))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    (realization.readout () parameter state).1 < (realization.readout () parameter state).2

theorem bridge : (type_of% (@correction_source_weight_lt)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.colour parameter.degree parameter.offset state
  · intro law lattice colour degree offset state
    exact law ⟨lattice, colour, degree, offset⟩ state

def escapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration.neutralPolynomialMode
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@correction_source_weight_lt))
abbrev contractObligation := Contract.Registration (@correction_source_weight_lt)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight
