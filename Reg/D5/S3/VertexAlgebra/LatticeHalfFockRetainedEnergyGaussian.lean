import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  first : Charge lattice
  second : Charge lattice

def signature : Signature where
  Params := Parameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def recurrenceReadout : Realization signature :=
  realize signature (fun _ parameter (energy : ℕ) =>
    (((energy : ℂ) + 1) • correctedCreationEnergy parameter.lattice parameter.first
      (parameter.first + parameter.second) (energy + 1 : ℕ),
      ∑ frequency ∈ Finset.range (energy + 1),
        retainedEnergyMultiplier parameter.lattice parameter.first parameter.second frequency *
          correctedCreationEnergy parameter.lattice parameter.first
            (parameter.first + parameter.second) ((energy - frequency : ℕ) : ℤ)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter energy,
    (observation.readout () parameter energy).1 = (observation.readout () parameter energy).2

theorem recurrenceBridge :
    (type_of% (@actual_full_retained_energy_recurrence)) ↔ arena.Law recurrenceReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.first parameter.second energy
  · intro law lattice first second energy
    exact law ⟨lattice, first, second⟩ energy

def escapeFrom := @correctedCreationEnergy
def continuation : Contract.Continuation Unit := .unknown

abbrev recurrenceRealizationObligation :=
  Registration arena (type_of% (@actual_full_retained_energy_recurrence))

abbrev recurrenceContractObligation := Contract.Registration
  (@actual_full_retained_energy_recurrence)
  (type_of% recurrenceReadout) (type_of% escapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian
