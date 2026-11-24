/- GID: D5/S3/Quantum/Decoherence/FourLevelBathCubic
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FourLevelBathCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/Decoherence/FourLevelBathCubic.fixed_bath_pinching_iff_cubic; instance=D5/S3/Quantum/Decoherence/FourLevelBathCubic.infeasible_fixed_bath_example
   digest: A guarded cubic decides exact qutrit pinching with a fixed faithful four-level Gibbs bath. -/

import D5.S3.Quantum.Decoherence.FourLevelBathPhysical
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic

/-! The cubic criterion and exact examples for a fixed four-level Gibbs bath. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FourLevelBathPhysical

open Matrix
open scoped BigOperators
open GibbsBathBandwidth (gibbsWeight gibbsWeight_pos sum_gibbsWeight matchingEnergies)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation (operation)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (projectiveReadout)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

/-- Strictly positive row weights allow each entry to be divided by its row's square root. -/
private theorem squared_moduli_iff_weighted_columns (p : Bath → ℝ) (hp : ∀ b, 0 < p b)
    (W : Matrix Bath System ℂ) :
    (∀ b i, ‖W b i‖ ^ 2 = p b) ↔
      ∃ z : Bath → System → ℂ, (∀ b i, Complex.normSq (z b i) = 1) ∧
        W = weightedColumns p z := by
  have hs (b : Bath) : Complex.normSq (Real.sqrt (p b) : ℂ) = p b := by
    rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (hp b).le]
  constructor
  · intro h
    let z (b : Bath) (i : System) := W b i / (Real.sqrt (p b) : ℂ)
    refine ⟨z, ?_, ?_⟩
    · intro b i
      change Complex.normSq (W b i / (Real.sqrt (p b) : ℂ)) = 1
      rw [Complex.normSq_div, hs, Complex.normSq_eq_norm_sq, h, div_self (hp b).ne']
    · apply Matrix.ext
      intro b i
      change W b i = (Real.sqrt (p b) : ℂ) * (W b i / (Real.sqrt (p b) : ℂ))
      rw [mul_comm]
      exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hp b)).ne')).symm
  · rintro ⟨z, hz, rfl⟩ b i
    rw [← Complex.normSq_eq_norm_sq, weightedColumns, Complex.normSq_mul, hs, hz, mul_one]

private theorem fixed_bath_pinching_iff_isometry (β : ℝ) (E : Bath → ℝ)
    (hE : Function.Injective E) :
    (∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ)) ↔
      ∃ W : Matrix Bath System ℂ, Wᴴ * W = 1 ∧
        ∀ b i, ‖W b i‖ ^ 2 = gibbsWeight β E b := by
  rw [fixed_bath_pinching_iff β E hE]
  constructor
  · rintro ⟨z, hz, hGram⟩
    exact ⟨weightedColumns (gibbsWeight β E) z, hGram,
      (squared_moduli_iff_weighted_columns _ (gibbsWeight_pos β E) _).2 ⟨z, hz, rfl⟩⟩
  · rintro ⟨W, hGram, hmod⟩
    obtain ⟨z, hz, rfl⟩ :=
      (squared_moduli_iff_weighted_columns _ (gibbsWeight_pos β E) W).1 hmod
    exact ⟨z, hz, hGram⟩

/-- The exact fixed-bath operation is equivalent to the row cap and an admissible cubic root. -/
theorem fixed_bath_pinching_iff_cubic (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E) :
    (∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ)) ↔
      let p := gibbsWeight β E
      (∀ b, p b ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        (∀ b, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.q p b ^ 2 * t ≥ D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.d p b ^ 2) ∧
        D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.phaseCubic p t = 0 :=
  (fixed_bath_pinching_iff_isometry β E hE).trans
    (D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic (gibbsWeight β E)
      (gibbsWeight_pos β E) (sum_gibbsWeight β E))

/-- The feasible rational law is realized by an exact fixed-bath operation at every positive β. -/
theorem feasible_fixed_bath_example (β : ℝ) (hβ : 0 < β) :
    ∃ E : Bath → ℝ, Function.Injective E ∧ gibbsWeight β E = D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights ∧
      ∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
        IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
        ∀ ρ : DensityState System,
          operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ) := by
  let p := D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights
  have hp (b : Bath) : 0 < p b := by
    fin_cases b <;> norm_num [p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights]
  have hsum : ∑ b, p b = 1 := by
    norm_num [Fin.sum_univ_four, p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights]
  have hinj : Function.Injective p := by
    intro b c h
    fin_cases b <;> fin_cases c <;> norm_num [p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasibleWeights] at h <;> rfl
  obtain ⟨hE, hg⟩ := matching_distinct_energies hβ p hp hsum hinj
  refine ⟨matchingEnergies β p, hE, hg, (fixed_bath_pinching_iff_isometry β _ hE).2 ?_⟩
  rw [hg]
  exact D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.feasible_weighted_phase_columns

/-- The infeasible rational law has distinct matching energies and satisfies the strict row cap. -/
theorem infeasible_fixed_bath_example (β : ℝ) (hβ : 0 < β) :
    ∃ E : Bath → ℝ, Function.Injective E ∧ gibbsWeight β E = D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasibleWeights ∧
      (∀ b, gibbsWeight β E b < 1 / 3) ∧
      ¬ (∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
        IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
        ∀ ρ : DensityState System,
          operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ)) := by
  let p := D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasibleWeights
  have hp (b : Bath) : 0 < p b := by
    fin_cases b <;> norm_num [p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasibleWeights]
  have hsum : ∑ b, p b = 1 := by
    norm_num [Fin.sum_univ_four, p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasibleWeights]
  have hinj : Function.Injective p := by
    intro b c h
    fin_cases b <;> fin_cases c <;> norm_num [p, D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasibleWeights] at h <;> rfl
  obtain ⟨hE, hg⟩ := matching_distinct_energies hβ p hp hsum hinj
  refine ⟨matchingEnergies β p, hE, hg, ?_, ?_⟩
  · rw [hg]
    exact D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns.1
  · rw [fixed_bath_pinching_iff_isometry β _ hE, hg]
    exact D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns.2

end D5.S3.Quantum.Decoherence.FourLevelBathPhysical
