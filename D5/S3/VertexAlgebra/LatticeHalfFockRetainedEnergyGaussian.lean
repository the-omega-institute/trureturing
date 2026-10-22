/- GID: D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyGaussian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full retained creation-energy Gaussian with the original normal and shift variables. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectionTranslation LatticeHalfFockCreationEnergyContraction
open MvPolynomial
open scoped BigOperators

noncomputable section

local macro "expanded_energy_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.retained_expanded_energy_recurrence))

local macro "coordinate_pairing_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.coordinate_pairing))

local macro "ordered_pair_half_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.scalar_ordered_pair_half))

local macro "weighted_energy_log_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.weighted_energy_log))

def normalEnergyMultiplier (D : LatticeData) (source : Charge D) (frequency : ℕ) :
    CorrectionPolynomial D :=
  ∑ coordinate : Fin D.rank, (source coordinate : ℂ) • X (some (coordinate, frequency))

def retainedEnergyMultiplier (D : LatticeData) (first second : Charge D) (frequency : ℕ) :
    CorrectionPolynomial D :=
  normalEnergyMultiplier D first frequency +
    C ((frequency + 1 : ℂ) * chargedEnergyLogCoefficient D first second (frequency + 1)) *
      X none ^ (frequency + 1)

private theorem retained_raw_recurrence (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • correctedCreationEnergy D source charge (energy + 1 : ℕ) =
      (∑ frequency ∈ Finset.range (energy + 1),
        (normalEnergyMultiplier D source frequency +
          C ((bilinear D source charge : ℂ) * halfBinomial (frequency + 1)) *
            X none ^ (frequency + 1)) *
              correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ)) +
      ∑ frequency ∈ Finset.range (energy + 1),
        ∑ pairedFrequency ∈ Finset.range (energy - frequency),
          (C ((bilinear D source source : ℂ) * (pairedFrequency + 1 : ℂ)⁻¹ *
            pairScalar (frequency + 1) (pairedFrequency + 1)) *
              X none ^ (frequency + pairedFrequency + 2)) *
                correctedCreationEnergy D source charge
                  ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ) := by
  classical
  rw [expanded_energy_supplier]
  simp_rw [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro frequency _
    simp only [add_mul, smul_add, Finset.sum_add_distrib, normalEnergyMultiplier,
      Finset.sum_mul, smul_mul_assoc]
    congr 1
    simp only [singletonPolynomial, sourceWeight, smul_eq_C_mul]
    simp_rw [show ∀ coordinate : Fin D.rank,
      C (source coordinate : ℂ) *
        (C (halfBinomial (frequency + 1) * (bilinear D (unitCharge D coordinate) charge : ℂ)) *
          X none ^ (frequency + 1) *
            correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ)) =
      C ((source coordinate : ℂ) * (bilinear D (unitCharge D coordinate) charge : ℂ)) *
        (C (halfBinomial (frequency + 1)) * X none ^ (frequency + 1) *
          correctedCreationEnergy D source charge ((energy - frequency : ℕ) : ℤ)) by
            intro coordinate; simp only [map_mul]; ring]
    rw [← Finset.sum_mul, ← map_sum, coordinate_pairing_supplier]
    simp only [map_mul]
    ring
  · apply Finset.sum_congr rfl
    intro frequency _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro pairedFrequency member
    have bound := Finset.mem_range.mp member
    have difference : ((energy - frequency : ℕ) : ℤ) - (pairedFrequency + 1 : ℕ) =
        ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ) := by omega
    rw [difference]
    simp only [energyPairKernel, sourceWeight, smul_eq_C_mul]
    simp_rw [show ∀ coordinate : Fin D.rank,
      C (source coordinate : ℂ) *
        (C ((pairedFrequency + 1 : ℂ)⁻¹ * (bilinear D (unitCharge D coordinate) source : ℂ)) *
          (C (pairScalar (frequency + 1) (pairedFrequency + 1)) *
            X none ^ (frequency + 1 + (pairedFrequency + 1))) *
              correctedCreationEnergy D source charge
                ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ)) =
      C ((source coordinate : ℂ) * (bilinear D (unitCharge D coordinate) source : ℂ)) *
        (C ((pairedFrequency + 1 : ℂ)⁻¹ * pairScalar (frequency + 1) (pairedFrequency + 1)) *
          X none ^ (frequency + pairedFrequency + 2) *
            correctedCreationEnergy D source charge
              ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ)) by
                intro coordinate
                rw [show frequency + 1 + (pairedFrequency + 1) =
                  frequency + pairedFrequency + 2 by omega]
                simp only [map_mul]
                ring]
    rw [← Finset.sum_mul, ← map_sum, coordinate_pairing_supplier]
    simp only [map_mul]
    ring

private theorem polynomial_triangle_diagonals (D : LatticeData)
    (function : ℕ → ℕ → CorrectionPolynomial D) (energy : ℕ) :
    (∑ frequency ∈ Finset.range (energy + 1),
      ∑ pairedFrequency ∈ Finset.range (energy - frequency), function frequency pairedFrequency) =
        ∑ total ∈ Finset.range energy, ∑ frequency ∈ Finset.range (total + 1),
          function frequency (total - frequency) := by
  induction energy with
  | zero => simp
  | succ energy induction =>
    rw [Finset.sum_range_succ]
    rw [show energy + 1 - (energy + 1) = 0 by omega, Finset.sum_range_zero, add_zero]
    have expand :
        (∑ frequency ∈ Finset.range (energy + 1),
          ∑ pairedFrequency ∈ Finset.range (energy + 1 - frequency),
            function frequency pairedFrequency) =
          (∑ frequency ∈ Finset.range (energy + 1),
            ∑ pairedFrequency ∈ Finset.range (energy - frequency), function frequency pairedFrequency) +
          ∑ frequency ∈ Finset.range (energy + 1), function frequency (energy - frequency) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro frequency member
      have bound := Finset.mem_range.mp member
      rw [show energy + 1 - frequency = (energy - frequency) + 1 by omega,
        Finset.sum_range_succ]
    rw [expand, induction]
    exact (Finset.sum_range_succ (fun total =>
      ∑ frequency ∈ Finset.range (total + 1), function frequency (total - frequency)) energy).symm

private theorem retained_pair_energy_collapsed (D : LatticeData)
    (source charge : Charge D) (energy : ℕ) :
    (∑ frequency ∈ Finset.range (energy + 1),
      ∑ pairedFrequency ∈ Finset.range (energy - frequency),
        (C ((bilinear D source source : ℂ) * (pairedFrequency + 1 : ℂ)⁻¹ *
          pairScalar (frequency + 1) (pairedFrequency + 1)) *
            X none ^ (frequency + pairedFrequency + 2)) *
              correctedCreationEnergy D source charge
                ((energy - frequency - (pairedFrequency + 1) : ℕ) : ℤ)) =
      ∑ total ∈ Finset.range energy,
        (C ((bilinear D source source : ℂ) / 2 *
          ∑ frequency ∈ Finset.range (total + 1),
            halfBinomial (frequency + 1) * halfBinomial (total - frequency + 1)) *
              X none ^ (total + 2)) *
                correctedCreationEnergy D source charge ((energy - total - 1 : ℕ) : ℤ) := by
  rw [polynomial_triangle_diagonals]
  apply Finset.sum_congr rfl
  intro total member
  have totalBound := Finset.mem_range.mp member
  have normalized :
      (∑ frequency ∈ Finset.range (total + 1),
        (C ((bilinear D source source : ℂ) * (((total - frequency : ℕ) : ℂ) + 1)⁻¹ *
          pairScalar (frequency + 1) (total - frequency + 1)) *
            X none ^ (frequency + (total - frequency) + 2)) *
              correctedCreationEnergy D source charge
                ((energy - frequency - (total - frequency + 1) : ℕ) : ℤ)) =
        C ((bilinear D source source : ℂ) *
          ∑ frequency ∈ Finset.range (total + 1),
            (frequency + 1 : ℂ) / (total + 2 : ℂ) *
              halfBinomial (frequency + 1) * halfBinomial (total - frequency + 1)) *
            X none ^ (total + 2) *
              correctedCreationEnergy D source charge ((energy - total - 1 : ℕ) : ℤ) := by
    rw [Finset.mul_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro frequency frequencyMember
    have bound := Finset.mem_range.mp frequencyMember
    rw [show energy - frequency - (total - frequency + 1) = energy - total - 1 by omega,
      show frequency + (total - frequency) + 2 = total + 2 by omega]
    congr 2
    congr 1
    have denominator : (((total - frequency : ℕ) : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (by omega : total - frequency + 1 ≠ 0)
    have indexSum : (frequency : ℂ) + (total - frequency : ℕ) = (total : ℂ) := by
      exact_mod_cast (by omega : frequency + (total - frequency) = total)
    simp only [pairScalar, Nat.cast_add, Nat.cast_one]
    have wholeSum : (frequency + 1 : ℂ) + (((total - frequency : ℕ) : ℂ) + 1) =
        (total + 2 : ℂ) := by linear_combination indexSum
    rw [wholeSum]
    field_simp
  rw [normalized, ordered_pair_half_supplier]
  congr 2
  congr 1
  ring

theorem actual_full_retained_energy_recurrence (D : LatticeData)
    (first second : Charge D) (energy : ℕ) :
    (energy + 1 : ℂ) • correctedCreationEnergy D first (first + second) (energy + 1 : ℕ) =
      ∑ frequency ∈ Finset.range (energy + 1),
        retainedEnergyMultiplier D first second frequency *
          correctedCreationEnergy D first (first + second) ((energy - frequency : ℕ) : ℤ) := by
  classical
  rw [retained_raw_recurrence, retained_pair_energy_collapsed]
  have pairing : (bilinear D first (first + second) : ℂ) =
      (bilinear D first first : ℂ) + (bilinear D first second : ℂ) := by
    simp only [LatticeActualGeneratorLocality.bilinear_add_right, Int.cast_add]
  have pairs :
      (∑ total ∈ Finset.range energy,
        C ((bilinear D first first : ℂ) / 2 *
          ∑ frequency ∈ Finset.range (total + 1),
            halfBinomial (frequency + 1) * halfBinomial (total - frequency + 1)) *
              X none ^ (total + 2) *
                correctedCreationEnergy D first (first + second) ((energy - total - 1 : ℕ) : ℤ)) =
      ∑ frequency ∈ Finset.range (energy + 1),
        C ((bilinear D first first : ℂ) / 2 *
          ∑ pairedFrequency ∈ Finset.range frequency,
            halfBinomial (pairedFrequency + 1) * halfBinomial (frequency - pairedFrequency)) *
              X none ^ (frequency + 1) *
                correctedCreationEnergy D first (first + second) ((energy - frequency : ℕ) : ℤ) := by
    rw [Finset.sum_range_succ']
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, map_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro total _
    rw [show energy - (total + 1) = energy - total - 1 by omega]
    congr 2
    congr 1
    apply congrArg (fun coefficient : ℂ => (bilinear D first first : ℂ) / 2 * coefficient)
    apply Finset.sum_congr rfl
    intro frequency member
    have bound := Finset.mem_range.mp member
    rw [show total + 1 - frequency = total - frequency + 1 by omega]
  simp_rw [retainedEnergyMultiplier, weighted_energy_log_supplier, map_add, add_mul,
    Finset.sum_add_distrib, pairing]
  simp_rw [add_mul]
  rw [pairs]
  exact add_assoc _ _ _

#print axioms actual_full_retained_energy_recurrence

end

end D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian
