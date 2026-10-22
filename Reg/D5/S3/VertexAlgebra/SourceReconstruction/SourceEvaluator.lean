import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
import D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := LatticeData
  State lattice := Carrier lattice × ℤ × Carrier lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ lattice := Carrier lattice × Carrier lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ lattice state =>
    (evaluate lattice state.1 state.2.1 state.2.2, mu lattice state.1 state.2.1 state.2.2))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ lattice state,
    (realization.readout () lattice state).1 = (realization.readout () lattice state).2

theorem bridge : (type_of% (@evaluate_agrees)) ↔ arena.Law readout := by
  constructor
  · intro source lattice state
    exact source lattice state.1 state.2.1 state.2.2
  · intro law lattice source mode target
    exact law lattice ⟨source, mode, target⟩

def escapeFrom := @_root_.D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator.sourceWord
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@evaluate_agrees))
abbrev contractObligation := Contract.Registration (@evaluate_agrees)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator
