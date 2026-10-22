import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure EnergyParameters where
  lattice : LatticeData
  source : Charge lattice
  charge : Charge lattice

def contractionSignature : Signature where
  Params := EnergyParameters
  State parameter := ℕ × Index parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def contractionReadout : Realization contractionSignature :=
  realize contractionSignature (fun _ parameter state =>
    (pairDerivation parameter.lattice state.2
      (correctedCreationEnergy parameter.lattice parameter.source parameter.charge state.1),
      ∑ frequency ∈ Finset.range state.1,
        (((frequency + 1 : ℂ)⁻¹ *
          (bilinear parameter.lattice (unitCharge parameter.lattice state.2.1) parameter.source : ℂ)) •
          energyPairKernel parameter.lattice state.2 frequency) *
          correctedCreationEnergy parameter.lattice parameter.source parameter.charge
            ((state.1 : ℤ) - (frequency + 1 : ℕ))))
    (fun empty => nomatch empty)

def contractionArena : Arena where
  signature := contractionSignature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem contractionBridge :
    (type_of% (@actual_retained_creation_energy_contraction)) ↔
      contractionArena.Law contractionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.source parameter.charge state.1 state.2
  · intro law lattice source charge energy index
    exact law ⟨lattice, source, charge⟩ ⟨energy, index⟩

def recurrenceSignature : Signature where
  Params := EnergyParameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := CorrectionPolynomial parameter.lattice × CorrectionPolynomial parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def recurrenceReadout : Realization recurrenceSignature :=
  realize recurrenceSignature (fun _ parameter (energy : ℕ) =>
    (((energy : ℂ) + 1) • correctedCreationEnergy parameter.lattice parameter.source parameter.charge
      (energy + 1 : ℕ),
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin parameter.lattice.rank,
        (parameter.source coordinate : ℂ) • insertion parameter.lattice parameter.charge
          (coordinate, frequency) (correctedCreationEnergy parameter.lattice parameter.source parameter.charge
            ((energy - frequency : ℕ) : ℤ))))
    (fun empty => nomatch empty)

def recurrenceArena : Arena where
  signature := recurrenceSignature
  Law observation := ∀ parameter energy,
    (observation.readout () parameter energy).1 = (observation.readout () parameter energy).2

theorem recurrenceBridge :
    (type_of% (@actual_retained_creation_energy_recurrence)) ↔
      recurrenceArena.Law recurrenceReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.source parameter.charge energy
  · intro law lattice source charge energy
    exact law ⟨lattice, source, charge⟩ energy

def energyEscapeFrom := @correctedCreationEnergy
def energyContinuation : Contract.Continuation Unit := .unknown
abbrev contractionRealizationObligation :=
  Registration contractionArena (type_of% (@actual_retained_creation_energy_contraction))
abbrev contractionContractObligation := Contract.Registration
  (@actual_retained_creation_energy_contraction)
  (type_of% contractionReadout) (type_of% energyEscapeFrom) Unit
abbrev recurrenceRealizationObligation :=
  Registration recurrenceArena (type_of% (@actual_retained_creation_energy_recurrence))
abbrev recurrenceContractObligation := Contract.Registration
  (@actual_retained_creation_energy_recurrence)
  (type_of% recurrenceReadout) (type_of% energyEscapeFrom) Unit

structure NativeEnergyParameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  source : Charge lattice
  charge : Charge lattice

def nativeSignature : Signature where
  Params := NativeEnergyParameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter :=
    _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.NativeField parameter.lattice parameter.native ×
      _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.NativeField parameter.lattice parameter.native
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeReadout : Realization nativeSignature :=
  realize nativeSignature (fun _ parameter (energy : ℕ) =>
    (((energy : ℂ) + 1) • _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField.Ytw
      parameter.lattice parameter.native
      (Finsupp.single parameter.charge (creationCoeff parameter.lattice parameter.source (energy + 1 : ℕ))),
      ∑ frequency ∈ Finset.range (energy + 1), ∑ coordinate : Fin parameter.lattice.rank,
        (parameter.source coordinate : ℂ) •
          (_root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation
            parameter.lattice parameter.native parameter.charge
            ((MvPolynomial.X (some (coordinate, frequency)) +
                singletonPolynomial parameter.lattice parameter.charge (coordinate, frequency)) *
              correctedCreationEnergy parameter.lattice parameter.source parameter.charge
                ((energy - frequency : ℕ) : ℤ)) +
            ∑ pairedFrequency ∈ Finset.range (energy - frequency),
              _root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.nativeCorrectionEvaluation
                parameter.lattice parameter.native parameter.charge
                ((((pairedFrequency + 1 : ℂ)⁻¹ *
                    (bilinear parameter.lattice (unitCharge parameter.lattice coordinate) parameter.source : ℂ)) •
                    energyPairKernel parameter.lattice (coordinate, frequency) pairedFrequency) *
                  correctedCreationEnergy parameter.lattice parameter.source parameter.charge
                    (((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ))))))
    (fun empty => nomatch empty)

def nativeArena : Arena where
  signature := nativeSignature
  Law observation := ∀ parameter energy,
    (observation.readout () parameter energy).1 = (observation.readout () parameter energy).2

theorem nativeBridge :
    (type_of% (@actual_native_creation_energy_recurrence)) ↔
      nativeArena.Law nativeReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.native parameter.source parameter.charge energy
  · intro law lattice native source charge energy
    exact law ⟨lattice, native, source, charge⟩ energy

abbrev nativeRealizationObligation :=
  Registration nativeArena (type_of% (@actual_native_creation_energy_recurrence))
abbrev nativeContractObligation := Contract.Registration
  (@actual_native_creation_energy_recurrence)
  (type_of% nativeReadout) (type_of% energyEscapeFrom) Unit

structure ChargedParameters where
  lattice : LatticeData
  first : Charge lattice
  second : Charge lattice

def scalarSignature : Signature where
  Params := ChargedParameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ × ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarRecurrenceReadout : Realization scalarSignature :=
  realize scalarSignature (fun _ parameter (energy : ℕ) =>
    ((energy : ℂ) * actualEnergyScalar parameter.lattice parameter.first
        (parameter.first + parameter.second) energy,
      ∑ frequency ∈ Finset.range energy,
        (((frequency : ℂ) + 1) * chargedEnergyLogCoefficient parameter.lattice
          parameter.first parameter.second (frequency + 1)) *
            actualEnergyScalar parameter.lattice parameter.first (parameter.first + parameter.second)
              (energy - (frequency + 1)))) (fun empty => nomatch empty)

def scalarArena : Arena where
  signature := scalarSignature
  Law observation := ∀ parameter energy,
    (observation.readout () parameter energy).1 = (observation.readout () parameter energy).2

theorem scalarRecurrenceBridge :
    (type_of% (@actual_creation_energy_gaussian_recurrence)) ↔
      scalarArena.Law scalarRecurrenceReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.first parameter.second energy
  · intro law lattice first second energy
    exact law ⟨lattice, first, second⟩ energy

def scalarClosedReadout : Realization scalarSignature :=
  realize scalarSignature (fun _ parameter (energy : ℕ) =>
    (actualEnergyScalar parameter.lattice parameter.first (parameter.first + parameter.second) energy,
      PowerSeries.coeff energy (chargedEnergyGaussian parameter.lattice parameter.first parameter.second)))
    (fun empty => nomatch empty)

theorem scalarClosedBridge :
    (type_of% (@actual_creation_energy_gaussian_closed)) ↔ scalarArena.Law scalarClosedReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.first parameter.second energy
  · intro law lattice first second energy
    exact law ⟨lattice, first, second⟩ energy

def scalarEscapeFrom := @actualEnergyScalar
abbrev scalarRecurrenceRealizationObligation :=
  Registration scalarArena (type_of% (@actual_creation_energy_gaussian_recurrence))
abbrev scalarRecurrenceContractObligation := Contract.Registration
  (@actual_creation_energy_gaussian_recurrence)
  (type_of% scalarRecurrenceReadout) (type_of% scalarEscapeFrom) Unit
abbrev scalarClosedRealizationObligation :=
  Registration scalarArena (type_of% (@actual_creation_energy_gaussian_closed))
abbrev scalarClosedContractObligation := Contract.Registration
  (@actual_creation_energy_gaussian_closed)
  (type_of% scalarClosedReadout) (type_of% scalarEscapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
