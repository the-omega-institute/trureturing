import D5.S3.Quantum.Measurement.AuricUnitaryTransport
import D5.S3.Quantum.Measurement.AuricProtocolLimits

/-! # The exact distance for the source's full-input instrument at every angle -/

namespace D5.S3.Quantum.Measurement.AuricOriginalInstrument

open _root_.Matrix D5.S3.Quantum.Measurement.AuricSimulatorUpper
open D5.S3.Quantum.Measurement.AuricTiltedPermutationGram (activeLevel)
open D5.S3.Quantum.Measurement.AuricFiveLevelTilt
open D5.S3.Quantum.Measurement.AuricExactDistance
open D5.S3.Quantum.Measurement.AuricDiamondClosure
open D5.S3.Quantum.Measurement.AuricUnitaryTransport

noncomputable section

private def q : ℂ := (Real.sqrt 2 / 2 : ℝ)

private theorem q_sq : q * q = 1 / 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by nlinarith only [h]
  calc
    q * q = ((Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm
    _ = 1 / 2 := by rw [hr]; norm_num

private theorem star_q : (starRingEnd ℂ) q = q := Complex.conj_ofReal _

/-- The displayed zero-angle Kraus operators of AURIC §2 in the source basis. -/
def baseKraus (j : Flag) : Matrix Level Level ℂ :=
  if j = 0 then
    !![q, 0, 0, 0, 0; 0, 0, 1/2, 0, 0; 0, 0, 0, 0, 1; q, 0, 0, 0, 0; 0, 0, 1/2, 0, 0]
  else
    !![0, q, 0, 0, 0; 0, 0, 1/2, 0, 0; 0, 0, 0, 1, 0; 0, q, 0, 0, 0; 0, 0, 1/2, 0, 0]

private def changeBasis : Matrix Level Level ℂ :=
  !![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0]

private def outputBasis (j : Flag) : Matrix Level Level ℂ :=
  if j = 0 then
    !![q, q, 0, 0, 0; 0, 0, q, q, 0; 0, 0, 0, 0, 1; q, -q, 0, 0, 0; 0, 0, q, -q, 0]
  else
    !![q, q, 0, 0, 0; 0, 0, q, 0, q; 0, 0, 0, 1, 0; -q, q, 0, 0, 0; 0, 0, q, 0, -q]

private def reflection : Matrix Level Level ℂ :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]

private theorem reflection_star : reflectionᴴ = reflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reflection, Matrix.conjTranspose_apply]

private theorem reflection_sq : reflection * reflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private def rotation (θ : ℝ) : Matrix Level Level ℂ :=
  (Real.cos θ : ℂ) • 1 + (Complex.I * (Real.sin θ : ℂ)) • reflection

private def rotationUnitary (θ : ℝ) : RegisterUnitary :=
  ⟨rotation θ, Matrix.mem_unitaryGroup_iff'.2 (by
    change (rotation θ)ᴴ * rotation θ = 1
    have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    have hsc : star (Complex.I * (Real.sin θ : ℂ)) = -(Complex.I * (Real.sin θ : ℂ)) := by
      rw [star_mul, show star (Complex.I) = -Complex.I from Complex.conj_I,
        show star (Real.sin θ : ℂ) = (Real.sin θ : ℂ) from Complex.conj_ofReal _]
      ring
    have hc : star (Real.cos θ : ℂ) = (Real.cos θ : ℂ) := Complex.conj_ofReal _
    simp only [rotation, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hc, Matrix.conjTranspose_one, reflection_star, hsc, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      reflection_sq, smul_add, smul_smul]
    have hI := Complex.I_sq
    have hk : ((Real.cos θ : ℂ) * (Real.cos θ : ℂ) +
        (Complex.I * (Real.sin θ : ℂ)) * -(Complex.I * (Real.sin θ : ℂ))) = 1 := by
      linear_combination htrig - ((Real.sin θ : ℂ) ^ 2) * hI
    have hz : (Real.cos θ : ℂ) * -(Complex.I * (Real.sin θ : ℂ)) +
        (Complex.I * (Real.sin θ : ℂ)) * (Real.cos θ : ℂ) = 0 := by ring
    calc
      _ = (((Real.cos θ : ℂ) * (Real.cos θ : ℂ) +
          (Complex.I * (Real.sin θ : ℂ)) * -(Complex.I * (Real.sin θ : ℂ))) •
          (1 : Matrix Level Level ℂ)) +
          ((Real.cos θ : ℂ) * -(Complex.I * (Real.sin θ : ℂ)) +
          (Complex.I * (Real.sin θ : ℂ)) * (Real.cos θ : ℂ)) • reflection := by
        rw [add_smul, add_smul]
        abel
      _ = _ := by rw [hk, hz, one_smul, zero_smul, add_zero])⟩

private def reindexUnitary : RegisterUnitary :=
  ⟨changeBasis, Matrix.mem_unitaryGroup_iff'.2 (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [changeBasis, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ])⟩

set_option maxHeartbeats 1200000 in
-- Check the two five-column orthonormal bases in the source coordinates.
private def outputUnitary (j : Flag) : RegisterUnitary :=
  ⟨outputBasis j, Matrix.mem_unitaryGroup_iff'.2 (by
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k <;>
      norm_num [outputBasis, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, star_q, q_sq, neg_mul, mul_neg, ← two_mul] <;>
      (try rw [← mul_assoc, q_sq]) <;> ring)⟩

private def inputGate (θ : ℝ) : RegisterUnitary := reindexUnitary * rotationUnitary θ

private def feedbackGate (j : Flag) : RegisterUnitary := outputUnitary j * star reindexUnitary

set_option maxHeartbeats 1800000 in
-- Check both five-by-five Kraus products entrywise in the source coordinates.
private theorem factor_base (j : Flag) :
    (feedbackGate j).val * targetKraus j * reindexUnitary.val = baseKraus j := by
  have hactive (i : Level) : i ∈ Set.range (activeLevel (0 : Flag)) ↔ i = 0 ∨ i = 1 ∨ i = 4 := by
    simp [activeLevel, Set.mem_range, Fin.exists_fin_succ, or_assoc, or_comm, or_left_comm]
  have hactive' (i : Level) : i ∈ Set.range (activeLevel (1 : Flag)) ↔ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp [activeLevel, Set.mem_range, Fin.exists_fin_succ, or_assoc, or_comm, or_left_comm]
  change (outputBasis j * changeBasisᴴ) * targetKraus j * changeBasis = baseKraus j
  ext i k
  have hq : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = q := rfl
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    norm_num [targetKraus, hactive, hactive', baseKraus, outputBasis, changeBasis, hq,
      Matrix.diagonal_apply, q_sq]

private theorem base_mul_reflection (j : Flag) : baseKraus j * reflection = baseKraus (1 - j) := by
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [baseKraus, reflection, Matrix.mul_apply, Fin.sum_univ_succ]

/-- AURIC's fine flagged channel, on the original full five-level input. -/
def originalInstrument (θ : ℝ) : RecordedMap :=
  flagged fun j => (Real.cos θ : ℂ) • baseKraus j +
    (Complex.I * (Real.sin θ : ℂ)) • baseKraus (1 - j)

theorem originalInstrument_eq_transport (θ : ℝ) :
    originalInstrument θ = transport (inputGate θ) feedbackGate target := by
  rw [target, transport_flagged]
  unfold originalInstrument
  congr 1
  funext j
  change _ = (feedbackGate j).val * targetKraus j * (reindexUnitary.val * rotation θ)
  rw [← Matrix.mul_assoc ((feedbackGate j).val * targetKraus j), factor_base]
  simp [rotation, Matrix.mul_add, Matrix.mul_smul, base_mul_reflection]

/-- The original flagged instrument has the same exact unhalved distance at
all real angles. Its closed-class optimum is attained by a finite protocol mixture. -/
theorem original_exact_distance :
    ∃ r : WitnessInterval, matchingResidual r (tiltMass r) = 0 ∧
      ∀ θ : ℝ, ∃ T : RecordedMap, FiniteProtocolMixture T ∧
        DiamondBound (originalInstrument θ - T) (2 * matchingWeight r) ∧
        IsLeast {d : ℝ | ∃ F, ProtocolClosure F ∧ DiamondBound (originalInstrument θ - F) d}
          (2 * matchingWeight r) := by
  obtain ⟨r, hr, hfinite, hmatch, hleast⟩ := exact_distance_to_protocol_closure
  refine ⟨r, hr, fun θ => ?_⟩
  rw [originalInstrument_eq_transport]
  refine ⟨transport (inputGate θ) feedbackGate (matchingSimulator r),
    transport_finite _ _ hfinite, ?_, ?_⟩
  · rw [← map_sub]
    exact transport_bound _ _ hmatch
  · rw [transport_distance_set]
    exact hleast

end

end D5.S3.Quantum.Measurement.AuricOriginalInstrument
