import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MvPolynomial
open scoped BigOperators

noncomputable section

def signature : Signature where
  Params := LatticeData
  State lattice := Carrier lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ lattice := Carrier lattice × Carrier lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ lattice (state : Carrier lattice) =>
    (state, ∑ charge ∈ state.support,
      ∑ monomial ∈ ((basisMonomials (Index lattice) ℂ).repr (state charge)).support,
        ((basisMonomials (Index lattice) ℂ).repr (state charge) monomial) •
          oscillatorWord lattice charge (occurrences lattice monomial)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ lattice state,
    (realization.readout () lattice state).1 = (realization.readout () lattice state).2

theorem bridge : (type_of% (@finite_source_expansion)) ↔ arena.Law readout := by
  constructor
  · intro source lattice state
    exact source lattice state
  · intro law lattice state
    exact law lattice state

def escapeFrom := @_root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords.oscillatorWord
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@finite_source_expansion))
abbrev contractObligation := Contract.Registration (@finite_source_expansion)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
