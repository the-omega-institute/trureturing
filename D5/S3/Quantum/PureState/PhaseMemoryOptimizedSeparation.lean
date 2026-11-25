/- GID: D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The attained positive dominant qubit optimum separates asymmetric Fourier phases from Walsh phases. -/

import D5.S3.Quantum.PureState.PhaseMemoryQubitAttainment
import D5.S3.Quantum.PureState.QuantumMemoryBudget

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Subentropy.GuessingProbability (successProbability)
open JointRecordDecoding (phaseVector)
open PhaseMemorySaturatedFrame (fourier4 fourierTail fourier4_dominant_ne_upper)
open PhaseRecordDistillation (Feasible profileValue profileValue_le_of_certificate
  exists_success_le_profile)

open PhaseMemorySaturatedFrame (dominantProfile dominantSlope dominantProfile_data fourier4_norm)

namespace PhaseMemoryOptimized

noncomputable section

/-- The operational qubit optimum over one fixed encoder followed by a POVM. -/
def qubitOptimum (u : Fin 4 → Fin 4 → ℂ) (t : Fin 4 → ℝ) : ℝ :=
  sSup (successSet (Fin 2) (phaseVector u t))

/-- The dominant-coordinate value of the clipped scalar bound. -/
def dominantBound (t : Fin 4 → ℝ) : ℝ := (t 0 + fourierTail t) ^ 2 / 4

/-- This supremum is realized by a finite CPTP encoder and a POVM. -/
theorem qubitOptimum_isGreatest (u : Fin 4 → Fin 4 → ℂ) (t : Fin 4 → ℝ) :
    IsGreatest (successSet (Fin 2) (phaseVector u t)) (qubitOptimum u t) := by
  obtain ⟨s, hs⟩ := exists_isGreatest_successSet (b := Fin 2) (phaseVector u t)
  rw [qubitOptimum, hs.csSup_eq]
  exact hs

/-- The dominant clipped certificate bounds every strategy for any flat phases. -/
theorem score_le_dominantBound (u : Fin 4 → Fin 4 → ℂ) (hu : ∀ j i, ‖u j i‖ = 1)
    (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i) (hn : ∑ i, t i ^ 2 = 1)
    (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2)
    (Φ : QuantumChannel (Fin 4) (Fin 2)) (D : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hD : IsPOVM D) :
    score (phaseVector u t) Φ D ≤ dominantBound t := by
  obtain ⟨hp, hfact, hval⟩ := dominantProfile_data t ht hn hdom
  obtain ⟨ha, ha1, hmass, hr, hslope, hcap⟩ := hp
  obtain ⟨d, hd, hscore⟩ := exists_success_le_profile t (fun i => (ht i).le) u hu
    (JointRecordDecoding.phaseVector_norm u t hu hn) Φ D hD.1 hD.2
  let v (i : Fin 4) := dominantProfile t i ^ 2
  have hv : Feasible v 2 := ⟨fun i => sq_nonneg _, fun i => by
    simpa [v] using pow_le_pow_left₀ (ha i).le (ha1 i) 2, hmass.le⟩
  have hroot (i : Fin 4) : Real.sqrt (v i) = dominantProfile t i :=
    Real.sqrt_sq (ha i).le
  have hbest := profileValue_le_of_certificate t v d (dominantSlope t) (fourierTail t) 2
    hv (by simpa using hd) hmass hr.le hslope
    (fun i => by rw [hroot, mul_comm, hfact])
    (fun i hi => by
      by_contra hne
      have hone := hcap i hne
      simp [v, hone] at hi)
  have hvval : profileValue t v = t 0 + fourierTail t := by
    rw [← hval, profileValue]
    apply Finset.sum_congr rfl
    intro i _
    rw [hroot, ← hfact i]
    ring
  rw [hvval] at hbest
  have hconvert :
      score (phaseVector u t) Φ D ≤ (4 : ℝ)⁻¹ * profileValue t d ^ 2 := by
    simp only [successProbability, JointRecordDecoding.uniformPrior, ← Finset.mul_sum,
      Fintype.card_fin, Nat.cast_ofNat] at hscore
    rw [score, div_eq_mul_inv, mul_comm]
    exact hscore
  refine hconvert.trans ?_
  rw [dominantBound, div_eq_mul_inv, mul_comm _ (4 : ℝ)⁻¹]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => mul_nonneg (ht i).le (Real.sqrt_nonneg _))
      hbest 2) (by positivity)

/-- The actual optimized Fourier score is strictly below the clipped bound. -/
theorem fourier4_optimum_lt (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i)
    (hn : ∑ i, t i ^ 2 = 1) (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2) (hasym : t 1 ≠ t 3) :
    qubitOptimum fourier4 t < dominantBound t := by
  obtain ⟨Φ, D, hD, hscore⟩ := (qubitOptimum_isGreatest fourier4 t).1
  rw [hscore]
  apply lt_of_le_of_ne (score_le_dominantBound fourier4 fourier4_norm t ht hn hdom Φ D hD)
  intro he
  apply fourier4_dominant_ne_upper t ht hn hdom hasym Φ D hD.1 hD.2
  apply (div_left_inj' (show (4 : ℝ) ≠ 0 by norm_num)).mp
  simpa only [score, Fintype.card_fin, Nat.cast_ofNat, dominantBound] using he

/-- The actual optimized Walsh score equals the clipped bound. -/
theorem walsh4_optimum_eq (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i)
    (hn : ∑ i, t i ^ 2 = 1) (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2) :
    qubitOptimum walsh4 t = dominantBound t := by
  have hr : 0 < fourierTail t := Real.sqrt_pos.2
    (by nlinarith [pow_pos (ht 1) 2, sq_nonneg (t 2), sq_nonneg (t 3)])
  apply IsGreatest.csSup_eq
  exact ⟨walsh4_attains t hr, by
    rintro _ ⟨Φ, D, hD, rfl⟩
    exact score_le_dominantBound walsh4 walsh4_norm t ht hn hdom Φ D hD⟩

/-- In the positive dominant family the Fourier score attains the bound exactly
when the two conjugate-frequency amplitudes agree. -/
theorem fourier4_optimum_eq_iff (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i)
    (hn : ∑ i, t i ^ 2 = 1) (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2) :
    qubitOptimum fourier4 t = dominantBound t ↔ t 1 = t 3 := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_lt (fourier4_optimum_lt t ht hn hdom hne)) h
  · intro hs
    have hr : 0 < fourierTail t := Real.sqrt_pos.2
      (by nlinarith [pow_pos (ht 1) 2, sq_nonneg (t 2), sq_nonneg (t 3)])
    apply IsGreatest.csSup_eq
    exact ⟨symmetric_fourier4_attains t hr hs, by
      rintro _ ⟨Φ, D, hD, rfl⟩
      exact score_le_dominantBound fourier4 fourier4_norm t ht hn hdom Φ D hD⟩

/-- Identical amplitudes give strictly different qubit optima for the two phase matrices. -/
theorem phase_matrix_dependence (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i)
    (hn : ∑ i, t i ^ 2 = 1) (hdom : (1 / 2 : ℝ) ≤ t 0 ^ 2) (hasym : t 1 ≠ t 3) :
    qubitOptimum fourier4 t < qubitOptimum walsh4 t := by
  rw [walsh4_optimum_eq t ht hn hdom]
  exact fourier4_optimum_lt t ht hn hdom hasym

end

end PhaseMemoryOptimized
