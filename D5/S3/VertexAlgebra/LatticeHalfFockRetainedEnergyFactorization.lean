/- GID: D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original retained creation coefficients factor into normal creation and the shifted scalar Gaussian. -/

import D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCreationEnergyContraction LatticeHalfFockRetainedEnergyGaussian
open MvPolynomial
open scoped BigOperators

noncomputable section

local macro "ordinary_derivative_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.exponential_derivative))

local macro "ordinary_log_derivative_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.logarithm_derivative_coeff))

local macro "scalar_initial_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.scalar_creation_initial))

local macro "corrected_initial_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.correctedSource_one))

def normalCreationSeries (D : LatticeData) (source : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.map (rename (some : Index D → Option (Index D))).toRingHom
    (creationExponential D source)

def scalarShiftSeries (D : LatticeData) (first second : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  PowerSeries.mk (fun energy =>
    C (actualEnergyScalar D first (first + second) energy) * X none ^ energy)

def retainedGaussianProduct (D : LatticeData) (first second : Charge D) :
    PowerSeries (CorrectionPolynomial D) :=
  normalCreationSeries D first * scalarShiftSeries D first second

private theorem derivative_map {Source Target : Type*} [CommRing Source] [CommRing Target]
    (homomorphism : Source →+* Target) (series : PowerSeries Source) :
    PowerSeries.derivative Target (PowerSeries.map homomorphism series) =
      PowerSeries.map homomorphism (PowerSeries.derivative Source series) := by
  apply PowerSeries.ext
  intro energy
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul, map_natCast,
    map_add, map_one]

private theorem normal_derivative (D : LatticeData) (source : Charge D) :
    PowerSeries.derivative (CorrectionPolynomial D) (normalCreationSeries D source) =
      PowerSeries.mk (normalEnergyMultiplier D source) * normalCreationSeries D source := by
  rw [normalCreationSeries, derivative_map, ordinary_derivative_supplier, map_mul, mul_comm]
  congr 1
  apply PowerSeries.ext
  intro energy
  simp only [PowerSeries.coeff_map, ordinary_log_derivative_supplier, PowerSeries.coeff_mk,
    normalEnergyMultiplier, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  change rename some ((source coordinate : ℂ) • (X (coordinate, energy) : Oscillator D)) = _
  rw [map_smul, rename_X]

private theorem scalar_derivative (D : LatticeData) (first second : Charge D) :
    PowerSeries.derivative (CorrectionPolynomial D) (scalarShiftSeries D first second) =
      PowerSeries.mk (fun frequency =>
        C ((frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1)) *
          X none ^ (frequency + 1)) * scalarShiftSeries D first second := by
  apply PowerSeries.ext
  intro energy
  simp only [scalarShiftSeries, PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have scalar := actual_creation_energy_gaussian_recurrence D first second (energy + 1)
  simp only [Nat.cast_add, Nat.cast_one] at scalar
  have embedded := congrArg (fun coefficient : ℂ =>
    (C coefficient : CorrectionPolynomial D) * X none ^ (energy + 1)) scalar
  rw [map_sum, Finset.sum_mul] at embedded
  calc
    C (actualEnergyScalar D first (first + second) (energy + 1)) * X none ^ (energy + 1) *
        (energy + 1 : CorrectionPolynomial D) =
      C ((energy + 1 : ℂ) * actualEnergyScalar D first (first + second) (energy + 1)) *
        X none ^ (energy + 1) := by simp only [map_mul, map_add, map_natCast, map_one]; ring
    _ = _ := embedded
    _ = _ := by
      apply Finset.sum_congr rfl
      intro frequency member
      have bound := Finset.mem_range.mp member
      rw [show energy + 1 - (frequency + 1) = energy - frequency by omega]
      simp only [map_mul]
      have powers :
          (X none : CorrectionPolynomial D) ^ (frequency + 1) * X none ^ (energy - frequency) =
            X none ^ (energy + 1) := by
        rw [← pow_add, show frequency + 1 + (energy - frequency) = energy + 1 by omega]
      rw [← powers]
      ring

private theorem product_recurrence (D : LatticeData) (first second : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • PowerSeries.coeff (energy + 1) (retainedGaussianProduct D first second) =
      ∑ frequency ∈ Finset.range (energy + 1),
        retainedEnergyMultiplier D first second frequency *
          PowerSeries.coeff (energy - frequency) (retainedGaussianProduct D first second) := by
  have derivative :
      PowerSeries.derivative (CorrectionPolynomial D) (retainedGaussianProduct D first second) =
        PowerSeries.mk (retainedEnergyMultiplier D first second) *
          retainedGaussianProduct D first second := by
    rw [retainedGaussianProduct, Derivation.leibniz, smul_eq_mul, normal_derivative,
      scalar_derivative]
    have multiplier : PowerSeries.mk (retainedEnergyMultiplier D first second) =
        PowerSeries.mk (normalEnergyMultiplier D first) +
          PowerSeries.mk (fun frequency =>
            C ((frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1)) *
              X none ^ (frequency + 1)) := by
      apply PowerSeries.ext
      intro frequency
      simp only [PowerSeries.coeff_mk, map_add, retainedEnergyMultiplier]
    rw [multiplier]
    ring
  have coefficient := congrArg (PowerSeries.coeff energy) derivative
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at coefficient
  simpa only [PowerSeries.coeff_mk, smul_eq_C_mul, map_add, map_natCast, map_one, mul_comm]
    using coefficient

private theorem retained_initial (D : LatticeData) (source charge : Charge D) :
    correctedCreationEnergy D source charge 0 = 1 := by
  rw [correctedCreationEnergy]
  have ordinary : creationCoeff D source 0 = 1 := by
    simpa [creationCoeff] using LatticeSugawaraConformal.exponential_constant D source
  rw [ordinary, corrected_initial_supplier]

private theorem product_initial (D : LatticeData) (first second : Charge D) :
    PowerSeries.coeff 0 (retainedGaussianProduct D first second) = 1 := by
  simp only [retainedGaussianProduct, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    normalCreationSeries, scalarShiftSeries]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    LatticeSugawaraConformal.exponential_constant, map_one]
  change 1 * (C (actualEnergyScalar D first (first + second) 0) * X none ^ 0) = 1
  rw [scalar_initial_supplier]
  simp

theorem actual_retained_energy_gaussian_factorization (D : LatticeData)
    (first second : Charge D) (energy : ℕ) :
    correctedCreationEnergy D first (first + second) energy =
      PowerSeries.coeff energy (retainedGaussianProduct D first second) := by
  induction energy using Nat.strong_induction_on with
  | h energy induction =>
    cases energy with
    | zero => rw [Nat.cast_zero, retained_initial, product_initial]
    | succ energy =>
      have nonzero : (energy + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero energy
      apply smul_right_injective (M := CorrectionPolynomial D) nonzero
      change (energy + 1 : ℂ) •
        correctedCreationEnergy D first (first + second) (energy + 1 : ℕ) =
          (energy + 1 : ℂ) • PowerSeries.coeff (energy + 1) (retainedGaussianProduct D first second)
      rw [actual_full_retained_energy_recurrence, product_recurrence]
      apply Finset.sum_congr rfl
      intro frequency member
      have bound := Finset.mem_range.mp member
      rw [induction (energy - frequency) (by omega)]

theorem actual_retained_energy_finite_gaussian (D : LatticeData)
    (first second : Charge D) (energy : ℕ) :
    correctedCreationEnergy D first (first + second) energy =
      ∑ normalEnergy ∈ Finset.range (energy + 1),
        rename (some : Index D → Option (Index D)) (creationCoeff D first normalEnergy) *
          (C (PowerSeries.coeff (energy - normalEnergy) (chargedEnergyGaussian D first second)) *
            X none ^ (energy - normalEnergy)) := by
  rw [actual_retained_energy_gaussian_factorization, retainedGaussianProduct,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro normalEnergy _
  simp only [normalCreationSeries, scalarShiftSeries, PowerSeries.coeff_map,
    PowerSeries.coeff_mk, actual_creation_energy_gaussian_closed]
  rw [creationCoeff, dif_neg (by omega), Int.toNat_natCast]
  rfl

#print axioms actual_retained_energy_gaussian_factorization
#print axioms actual_retained_energy_finite_gaussian

end

end D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization
