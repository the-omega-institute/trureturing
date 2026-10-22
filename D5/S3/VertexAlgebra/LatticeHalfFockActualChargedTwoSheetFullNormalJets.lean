/- GID: D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged retained-energy fields, full normal jets, and both literal two-sheet branches. -/

import D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization
import D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets

open LatticeGeneratingFieldLocality
open LatticeHalfFockCreationEnergyContraction
open LatticeHalfFockRetainedEnergyGaussian
open LatticeHalfFockRetainedEnergyFactorization
open LatticeHalfFockScalarLabelledGaussian
open LatticeHalfFockOriginalTwoSheetChartRecurrence
open LatticeHalfFockOrderedProducts
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

local macro "native_correction_source_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
    `D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian.native_correction_source))

def twoSheetParameter (u : ℂ) : ℂ := 4 * u / (1 - u) ^ 2

theorem two_sheet_composition (u : ℂ) (hu : 1 - u ≠ 0) :
    twoSheetParameter u * (1 - u) ^ 2 = 4 * u := by
  unfold twoSheetParameter
  field_simp [hu]

def retainedEnergyJet (object : NativeLattice) (source charge : Charge object.lattice)
    (energy : ℤ) (mode : ℤ) (target : ActualTensor object.lattice object.native) :
    ActualTensor object.lattice object.native :=
  (nativeCorrectionEvaluation object.lattice object.native charge
    (correctedCreationEnergy object.lattice source charge energy)).coeff mode target

def retainedGaussianJet (object : NativeLattice) (source charge : Charge object.lattice)
    (energy : ℕ) (mode : ℤ) (target : ActualTensor object.lattice object.native) :
    ActualTensor object.lattice object.native :=
  (nativeCorrectionEvaluation object.lattice object.native charge
    (PowerSeries.coeff energy
      (retainedGaussianProduct object.lattice source (charge - source)))).coeff mode target

def retainedGaussianJetSummand (object : NativeLattice) (first second : Charge object.lattice)
    (energy normalEnergy : ℕ) : NativeField object.lattice object.native :=
  nativeCorrectionEvaluation object.lattice object.native (first + second)
    (rename (some : Index object.lattice → Option (Index object.lattice))
        (creationCoeff object.lattice first normalEnergy) *
      (C (PowerSeries.coeff (energy - normalEnergy)
          (chargedEnergyGaussian object.lattice first second)) *
        X none ^ (energy - normalEnergy)))

theorem retained_energy_field_recurrence (object : NativeLattice)
    (first second : Charge object.lattice) (energy : ℕ) :
    (energy + 1 : ℂ) •
        Ytw object.lattice object.native
          (Finsupp.single (first + second) (creationCoeff object.lattice first
            (energy + 1 : ℕ))) =
      ∑ frequency ∈ Finset.range (energy + 1),
        nativeCorrectionEvaluation object.lattice object.native (first + second)
          (retainedEnergyMultiplier object.lattice first second frequency *
            correctedCreationEnergy object.lattice first (first + second)
              ((energy - frequency : ℕ) : ℤ)) := by
  have identity := congrArg
    (nativeCorrectionEvaluation object.lattice object.native (first + second))
    (actual_full_retained_energy_recurrence object.lattice first second energy)
  have source :
      nativeCorrectionEvaluation object.lattice object.native (first + second)
          (correctedCreationEnergy object.lattice first (first + second)
            (energy + 1 : ℕ)) =
        Ytw object.lattice object.native
          (Finsupp.single (first + second)
            (creationCoeff object.lattice first (energy + 1 : ℕ))) := by
    unfold correctedCreationEnergy
    exact native_correction_source_supplier _ _ _ _
  simp only [map_sum, map_smul, RingHom.id_apply] at identity
  rw [source] at identity
  exact identity

theorem retained_energy_normal_jet_recurrence (object : NativeLattice)
    (first second : Charge object.lattice) (energy : ℕ) (mode : ℤ)
    (target : ActualTensor object.lattice object.native) :
    (energy + 1 : ℂ) • retainedEnergyJet object first (first + second)
        (energy + 1 : ℤ) mode target =
      ∑ frequency ∈ Finset.range (energy + 1),
        (nativeCorrectionEvaluation object.lattice object.native (first + second)
          (retainedEnergyMultiplier object.lattice first second frequency *
            correctedCreationEnergy object.lattice first (first + second)
              ((energy - frequency : ℕ) : ℤ))).coeff mode target := by
  have identity := retained_energy_field_recurrence object first second energy
  have projected := congrArg (fun field : NativeField object.lattice object.native =>
      field.coeff mode target) identity
  have source :
      nativeCorrectionEvaluation object.lattice object.native (first + second)
          (correctedCreationEnergy object.lattice first (first + second)
            (energy + 1 : ℕ)) =
        Ytw object.lattice object.native
          (Finsupp.single (first + second)
            (creationCoeff object.lattice first (energy + 1 : ℕ))) := by
    unfold correctedCreationEnergy
    exact native_correction_source_supplier _ _ _ _
  rw [← source] at projected
  simpa only [retainedEnergyJet, HVertexOperator.coeff_apply_apply, map_sum,
    map_smul, Pi.smul_apply, Finsupp.smul_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply, Nat.cast_add, Nat.cast_one] using projected

theorem retained_energy_field_finite_gaussian (object : NativeLattice)
    (first second : Charge object.lattice) (energy : ℕ) :
    Ytw object.lattice object.native
        (Finsupp.single (first + second)
          (creationCoeff object.lattice first energy)) =
      ∑ normalEnergy ∈ Finset.range (energy + 1),
        nativeCorrectionEvaluation object.lattice object.native (first + second)
          (rename (some : Index object.lattice → Option (Index object.lattice))
              (creationCoeff object.lattice first normalEnergy) *
            (C (PowerSeries.coeff (energy - normalEnergy)
                (chargedEnergyGaussian object.lattice first second)) *
              X none ^ (energy - normalEnergy))) := by
  have identity := congrArg
    (nativeCorrectionEvaluation object.lattice object.native (first + second))
    (actual_retained_energy_finite_gaussian object.lattice first second energy)
  have source :
      nativeCorrectionEvaluation object.lattice object.native (first + second)
          (correctedCreationEnergy object.lattice first (first + second) energy) =
        Ytw object.lattice object.native
          (Finsupp.single (first + second)
            (creationCoeff object.lattice first energy)) := by
    unfold correctedCreationEnergy
    exact native_correction_source_supplier _ _ _ _
  simp only [map_sum, map_smul, RingHom.id_apply] at identity
  rw [source] at identity
  exact identity

theorem retained_energy_normal_jet_finite_gaussian (object : NativeLattice)
    (first second : Charge object.lattice) (energy : ℕ) (mode : ℤ)
    (target : ActualTensor object.lattice object.native) :
    retainedEnergyJet object first (first + second) (energy : ℤ) mode target =
      ∑ normalEnergy ∈ Finset.range (energy + 1),
        (retainedGaussianJetSummand object first second energy normalEnergy).coeff mode target := by
  have identity := retained_energy_field_finite_gaussian object first second energy
  have projected := congrArg (fun field : NativeField object.lattice object.native =>
      field.coeff mode target) identity
  have source :
      nativeCorrectionEvaluation object.lattice object.native (first + second)
          (correctedCreationEnergy object.lattice first (first + second) energy) =
        Ytw object.lattice object.native
          (Finsupp.single (first + second)
            (creationCoeff object.lattice first energy)) := by
    unfold correctedCreationEnergy
    exact native_correction_source_supplier _ _ _ _
  rw [← source] at projected
  simpa only [retainedEnergyJet, retainedGaussianJetSummand,
    correctedCreationEnergy, HVertexOperator.coeff_apply_apply, map_sum,
    Pi.smul_apply, Finsupp.smul_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply] using projected

theorem charged_product_two_sheet_normalization (object : NativeLattice)
    (left right : Charge object.lattice) (first second : ℤ) (order : ℕ)
    (total : ℤ) (state : ActualTensor object.lattice object.native) :
    localPlus object.lattice object.native left right order total
        (chargedCoefficient object.lattice object.native left first
          (chargedCoefficient object.lattice object.native right second state)) =
      localPlus object.lattice object.native left right order total
        ((chargeScalar object.lattice left * chargeScalar object.lattice right) •
          ∑ᶠ degree : ℕ,
            (PowerSeries.coeff degree (halfContraction object.lattice left right)) •
              tensorCommonKernel object.lattice object.native left right
                (first + chargeNorm object.lattice left + degree)
                (second + chargeNorm object.lattice right - degree) state) := by
  rw [charged_tensor_ordered_product]

theorem charged_product_two_sheet_normalization_below_start (object : NativeLattice)
    (left right : Charge object.lattice) (first second : ℤ) (order : ℕ)
    (total : ℤ) (state : ActualTensor object.lattice object.native)
    (belowPlus : order <
      ((bilinear object.lattice left right).natAbs +
        bilinear object.lattice left right : ℤ).toNat)
    (belowMinus : order <
      ((bilinear object.lattice left right).natAbs -
        bilinear object.lattice left right : ℤ).toNat) :
    localPlus object.lattice object.native left right order total
        (chargedCoefficient object.lattice object.native left first
          (chargedCoefficient object.lattice object.native right second state)) = 0 ∧
    localMinus object.lattice object.native left right order total
        (chargedCoefficient object.lattice object.native left first
          (chargedCoefficient object.lattice object.native right second state)) = 0 := by
  have normalized := charged_product_two_sheet_normalization object left right first second
    order total state
  constructor
  · rw [charged_tensor_ordered_product]
    exact (local_charts_below_start object left right order total _).1 belowPlus
  · rw [charged_tensor_ordered_product]
    exact (local_charts_below_start object left right order total _).2 belowMinus

theorem source_normal_jet_gaussian_closed
    (object : NativeLattice) (charge : Charge object.lattice)
    (weights : Index object.lattice →₀ ℂ) (degree : ℕ) (mode : ℤ)
    (target : ActualTensor object.lattice object.native) :
    (Ytw object.lattice object.native
      (Finsupp.single charge
        (sourceDirection object.lattice weights ^ degree))).coeff mode target =
      degree.factorial •
        (nativeCorrectionEvaluation object.lattice object.native charge
          (PowerSeries.coeff degree
            (retainedGaussian object.lattice charge weights))).coeff mode target := by
  have identity := actual_source_field_gaussian_closed object charge weights degree
  exact congrArg (fun field : NativeField object.lattice object.native =>
    field.coeff mode target) identity

#print axioms two_sheet_composition
#print axioms retained_energy_field_recurrence
#print axioms retained_energy_normal_jet_recurrence
#print axioms retained_energy_field_finite_gaussian
#print axioms retained_energy_normal_jet_finite_gaussian
#print axioms charged_product_two_sheet_normalization
#print axioms charged_product_two_sheet_normalization_below_start
#print axioms source_normal_jet_gaussian_closed

end

end D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets
