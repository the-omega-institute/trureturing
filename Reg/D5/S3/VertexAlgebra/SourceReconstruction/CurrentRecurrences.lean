import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
import D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords
open _root_.D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators VertexOperator

noncomputable section

structure Parameters where
  lattice : LatticeData
  colour : Fin lattice.rank
  degree : ℕ
  mode : ℤ

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice × Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Carrier parameter.lattice × Carrier parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (mu parameter.lattice (((unitCurrent parameter.lattice parameter.colour)
      [[-(parameter.degree : ℤ) - 1]]) state.1) parameter.mode state.2,
      ∑ᶠ offset : ℕ, ((parameter.degree + offset).choose parameter.degree : ℂ) •
        (insertionFirst parameter.lattice parameter.colour parameter.degree parameter.mode
          state.1 state.2 offset + (-1 : ℂ) ^ parameter.degree •
            insertionSecond parameter.lattice parameter.colour parameter.degree parameter.mode
              state.1 state.2 offset)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter state,
    (realization.readout () parameter state).1 = (realization.readout () parameter state).2

theorem bridge : (type_of% (@source_insertion)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.colour parameter.degree parameter.mode state.1 state.2
  · intro law lattice colour degree mode source target
    exact law ⟨lattice, colour, degree, mode⟩ ⟨source, target⟩

def escapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeAllStateField.Y
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@source_insertion))
abbrev contractObligation := Contract.Registration (@source_insertion)
  (type_of% readout) (type_of% escapeFrom) Unit
def chargedSignature : Signature where
  Params := Parameters
  State parameter := Charge parameter.lattice × Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Carrier parameter.lattice × Carrier parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def chargedReadout : Realization chargedSignature :=
  realize chargedSignature (fun _ parameter state =>
    (mu parameter.lattice (Finsupp.single state.1 1) parameter.mode
      (((unitCurrent parameter.lattice parameter.colour)[[-(parameter.degree : ℤ) - 1]]) state.2),
      ((unitCurrent parameter.lattice parameter.colour)[[-(parameter.degree : ℤ) - 1]])
        (mu parameter.lattice (Finsupp.single state.1 1) parameter.mode state.2) -
        (bilinear parameter.lattice (unitCharge parameter.lattice parameter.colour) state.1 : ℂ) •
          mu parameter.lattice (Finsupp.single state.1 1) (parameter.mode - parameter.degree - 1) state.2))
    (fun empty => nomatch empty)

def chargedArena : Arena where
  signature := chargedSignature
  Law realization := ∀ parameter state,
    (realization.readout () parameter state).1 = (realization.readout () parameter state).2

theorem chargedBridge : (type_of% (@source_charged_commutation)) ↔ chargedArena.Law chargedReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.colour state.1 parameter.degree parameter.mode state.2
  · intro law lattice colour charge degree mode target
    exact law ⟨lattice, colour, degree, mode⟩ ⟨charge, target⟩

abbrev chargedRealizationObligation := Registration chargedArena
  (type_of% (@source_charged_commutation))
abbrev chargedContractObligation := Contract.Registration (@source_charged_commutation)
  (type_of% chargedReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
