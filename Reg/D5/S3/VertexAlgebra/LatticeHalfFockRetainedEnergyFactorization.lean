import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial LeanInformationAudit
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

def factorizationReadout : Realization signature :=
  realize signature (fun _ parameter (energy : ℕ) =>
    (correctedCreationEnergy parameter.lattice parameter.first (parameter.first + parameter.second) energy,
      PowerSeries.coeff energy
        (retainedGaussianProduct parameter.lattice parameter.first parameter.second)))
    (fun empty => nomatch empty)

def finiteReadout : Realization signature :=
  realize signature (fun _ parameter (energy : ℕ) =>
    (correctedCreationEnergy parameter.lattice parameter.first (parameter.first + parameter.second) energy,
      ∑ normalEnergy ∈ Finset.range (energy + 1),
        rename (some : Index parameter.lattice → Option (Index parameter.lattice))
          (creationCoeff parameter.lattice parameter.first normalEnergy) *
          (C (PowerSeries.coeff (energy - normalEnergy)
            (chargedEnergyGaussian parameter.lattice parameter.first parameter.second)) *
              X none ^ (energy - normalEnergy)))) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter energy,
    (observation.readout () parameter energy).1 = (observation.readout () parameter energy).2

theorem factorizationBridge :
    (type_of% (@actual_retained_energy_gaussian_factorization)) ↔ arena.Law factorizationReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.first parameter.second energy
  · intro law lattice first second energy
    exact law ⟨lattice, first, second⟩ energy

theorem finiteBridge :
    (type_of% (@actual_retained_energy_finite_gaussian)) ↔ arena.Law finiteReadout := by
  constructor
  · intro source parameter energy
    exact source parameter.lattice parameter.first parameter.second energy
  · intro law lattice first second energy
    exact law ⟨lattice, first, second⟩ energy

def escapeFrom := @correctedCreationEnergy
def continuation : Contract.Continuation Unit := .unknown

abbrev factorizationRealizationObligation :=
  Registration arena (type_of% (@actual_retained_energy_gaussian_factorization))
abbrev finiteRealizationObligation :=
  Registration arena (type_of% (@actual_retained_energy_finite_gaussian))
abbrev factorizationContractObligation := Contract.Registration
  (@actual_retained_energy_gaussian_factorization)
  (type_of% factorizationReadout) (type_of% escapeFrom) Unit
abbrev finiteContractObligation := Contract.Registration
  (@actual_retained_energy_finite_gaussian)
  (type_of% finiteReadout) (type_of% escapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization
