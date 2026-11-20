/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordDiamondCoefficient
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordDiamondCoefficient
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveControlledRecord, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryEntropyExpansion]
   utility: none
   digest: Exact leading diamond coefficient of the primitive periodic record channel. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryEntropyExpansion
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveControlledRecord
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Batteries.Tactic.OpenPrivate

/-!
# Exact leading diamond coefficient of the primitive periodic record

The spectral calculation uses the reversal decomposition in the sibling
`binary-complementary-decoder/proof.txt` and its exact `mps_replay.py`.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PrimitiveRecordDiamondCoefficient

open _root_.Matrix Filter
open scoped BigOperators ComplexOrder _root_.Matrix MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_of_posSemidef)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (diamondDistance)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open PeriodicMPSPrimitiveCollision
open ComplementaryRecordRate
open PrimitiveRecordLeadingCoefficient
open PrimitiveComplementaryEntropyExpansion (norm_collisionPhaseRate)
open PrimitiveControlledRecord (jointChannel dephasedChannel jointChannel_distance)
open private visibleMatrix rowMajor z from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient

noncomputable section

private abbrev Pair := Fin 2 × Fin 2

private def evenPlus (s : ℝ) : ℝ := (1025 + 5 * s) / 1312
private def evenMinus (s : ℝ) : ℝ := (1025 - 155 * s) / 1312
private def oddScale (s : ℝ) : ℝ := (25 * s - 123) / 1312

/-- The first two columns are even under reversal, and the last two are odd.
The odd columns absorb a phase so their normalization uses rational coordinates. -/
private def reversalEigenvectors : Matrix Pair (Fin 4) ℂ :=
  let u : ℂ := ⟨3 / 10, 2 / 5⟩
  let v : ℂ := ⟨1 / 2, 0⟩
  let w : ℂ := ⟨1 / 2, 1 / 2⟩
  (!![u, u, w, 0; v, -v, 0, w; v, -v, 0, -w; u, u, -w, 0]).submatrix
    (finProdFinEquiv : Pair ≃ Fin 4) id

private def eigenvalues (s : ℝ) : Fin 4 → ℂ :=
  ![↑(evenPlus s), ↑(evenMinus s), ⟨3 * oddScale s, 4 * oddScale s⟩,
    ⟨3 * oddScale s, -(4 * oddScale s)⟩]

private def singularValues (s : ℝ) : Fin 4 → ℝ :=
  ![evenPlus s, evenMinus s, 5 * oddScale s, 5 * oddScale s]

set_option maxHeartbeats 1000000 in
private theorem reversalEigenvectors_isometry :
    reversalEigenvectorsᴴ * reversalEigenvectors = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [reversalEigenvectors, Matrix.mul_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.of_apply, finProdFinEquiv,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im]

set_option maxHeartbeats 1000000 in
private theorem Sstar_mul_reversalEigenvectors :
    Sstar * reversalEigenvectors = reversalEigenvectors * diagonal (eigenvalues (Real.sqrt 41)) := by
  apply Matrix.ext
  rintro ⟨i, k⟩ j
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    rw [Matrix.mul_diagonal] <;> apply Complex.ext <;>
    norm_num [Sstar, visibleMatrix, rowMajor, z, reversalEigenvectors, eigenvalues,
      evenPlus, evenMinus, oddScale, Matrix.mul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, finProdFinEquiv, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im] <;> ring

private theorem Sstar_spectral :
    Sstar = reversalEigenvectors * diagonal (eigenvalues (Real.sqrt 41)) * reversalEigenvectorsᴴ := by
  have hU : reversalEigenvectors * reversalEigenvectorsᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := reversalEigenvectors)
      (B := reversalEigenvectorsᴴ) (finProdFinEquiv : Pair ≃ Fin 4)).mpr
        reversalEigenvectors_isometry
  rw [← Sstar_mul_reversalEigenvectors, Matrix.mul_assoc, hU, Matrix.mul_one]

private theorem diagonal_gram (s : ℝ) :
    (diagonal (eigenvalues s))ᴴ * diagonal (eigenvalues s) =
      (diagonal fun i => (singularValues s i : ℂ))ᴴ * diagonal (fun i => (singularValues s i : ℂ)) := by
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [eigenvalues, singularValues, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

private theorem six_le_sqrt41 : (6 : ℝ) ≤ Real.sqrt 41 :=
  (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)

private theorem singularValues_nonneg (i : Fin 4) : 0 ≤ singularValues (Real.sqrt 41) i := by
  have hupper : Real.sqrt 41 < (13 : ℝ) / 2 :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  fin_cases i <;> simp [singularValues, evenPlus, evenMinus, oddScale, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    linarith [six_le_sqrt41]

/-- Exact trace norm of the checked leading cross reduction. -/
theorem traceNorm_Sstar : traceNorm Sstar = (205 + 25 * Real.sqrt 41) / 328 := by
  let s := Real.sqrt 41
  let P : Matrix (Fin 4) (Fin 4) ℂ := diagonal (fun i => (singularValues s i : ℂ))
  have hP : P.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr fun i =>
    Complex.nonneg_iff.mpr ⟨singularValues_nonneg i, rfl⟩
  have hGram : traceNorm (diagonal (eigenvalues s)) = traceNorm P := by
    simp only [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm, diagonal_gram, P]
  have hTrace : traceNorm P = P.trace.re := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef hP)
    simpa only [RCLike.ofReal_re, RCLike.re_eq_complex_re] using h
  calc
    traceNorm Sstar = traceNorm (diagonal (eigenvalues s)) := by
      rw [Sstar_spectral]
      exact traceNorm_isometry reversalEigenvectors reversalEigenvectors_isometry _
    _ = traceNorm P := hGram
    _ = P.trace.re := hTrace
    _ = (205 + 25 * Real.sqrt 41) / 328 := by
      norm_num [P, s, Matrix.trace_diagonal, Fin.sum_univ_succ, singularValues,
        evenPlus, evenMinus, oddScale, Complex.add_re, Complex.ofReal_re] <;> ring

theorem one_lt_traceNorm_Sstar : 1 < traceNorm Sstar := by
  rw [traceNorm_Sstar]
  linarith [six_le_sqrt41]

private theorem continuous_traceNorm_pair : Continuous (traceNorm : Matrix Pair Pair ℂ → ℝ) := by
  have habs : Continuous (CFC.abs : Matrix Pair Pair ℂ → Matrix Pair Pair ℂ) :=
    CFC.continuous_abs
  change Continuous (fun A : Matrix Pair Pair ℂ => (CFC.sqrt (Aᴴ * A)).trace.re)
  simpa only [Function.comp_def, CFC.abs, Matrix.star_eq_conjTranspose] using
    Complex.continuous_re.comp habs.matrix_trace

private theorem traceNorm_complex_smul (c : ℂ) (A : Matrix Pair Pair ℂ) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  have h := CFC.abs_smul c A
  change CFC.sqrt ((c • A)ᴴ * (c • A)) = ‖c‖ • CFC.sqrt (Aᴴ * A) at h
  change (CFC.sqrt ((c • A)ᴴ * (c • A))).trace.re =
    ‖c‖ * (CFC.sqrt (Aᴴ * A)).trace.re
  rw [h, Matrix.trace_smul]
  simp [Complex.smul_re]

private theorem cross_leading_matrix :
    Tendsto (fun m : ℕ => (collisionPhaseRate ^ (2 + m))⁻¹ • collisionNormalizedCross m)
      atTop (𝓝 Sstar) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  simpa only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    collision_cross_leading p q

private theorem cross_norm_leading :
    Tendsto (fun m : ℕ => traceNorm (collisionNormalizedCross m) / collisionAlpha ^ (2 + m))
      atTop (𝓝 (traceNorm Sstar)) := by
  refine (continuous_traceNorm_pair.continuousAt.tendsto.comp cross_leading_matrix).congr ?_
  intro m
  change traceNorm ((collisionPhaseRate ^ (2 + m))⁻¹ • collisionNormalizedCross m) = _
  rw [traceNorm_complex_smul, norm_inv, norm_pow, norm_collisionPhaseRate, div_eq_mul_inv, mul_comm]

/-- The actual joint channel has this unhalved diamond coefficient at total
length `2 + (m + 5)`, covering all rings of length at least seven. -/
theorem jointChannel_diamond_asymptotic :
    Tendsto (fun m : ℕ =>
      diamondDistance (jointChannel (m + 5) (by omega)) (dephasedChannel (m + 5) (by omega)) /
        collisionAlpha ^ (2 + (m + 5)))
      atTop (𝓝 ((205 + 25 * Real.sqrt 41) / 328)) := by
  simpa only [Function.comp_def, jointChannel_distance, traceNorm_Sstar] using
    cross_norm_leading.comp (tendsto_add_atTop_nat 5)

/-- The magnitude of the coherence multiplier after discarding the pair has
leading coefficient one under the same total-length normalization. -/
theorem discardedPair_overlap_asymptotic :
    Tendsto (fun m : ℕ => ‖collisionNormalizedOverlap (2 + m)‖ / collisionAlpha ^ (2 + m))
      atTop (𝓝 1) := by
  have htrace : Continuous (Matrix.trace : Matrix Pair Pair ℂ → ℂ) :=
    continuous_id.matrix_trace
  have h := (continuous_norm.comp htrace).continuousAt.tendsto.comp cross_leading_matrix
  have hlimit : Tendsto (fun m : ℕ =>
      ‖((collisionPhaseRate ^ (2 + m))⁻¹ • collisionNormalizedCross m).trace‖)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Sstar_trace, norm_one] using h
  refine hlimit.congr fun m => ?_
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_inv, norm_pow, norm_collisionPhaseRate,
    ← collisionFlattening_cross, collisionFlattening_overlap, div_eq_mul_inv, mul_comm]

/-- The excess over the discarded-pair coherence multiplier has a positive
leading coefficient for the actual periodic channels. -/
theorem jointChannel_excess_asymptotic :
    Tendsto (fun m : ℕ =>
      (diamondDistance (jointChannel (m + 5) (by omega)) (dephasedChannel (m + 5) (by omega)) -
        ‖collisionNormalizedOverlap (2 + (m + 5))‖) / collisionAlpha ^ (2 + (m + 5)))
      atTop (𝓝 ((205 + 25 * Real.sqrt 41) / 328 - 1)) := by
  simpa only [Function.comp_def, sub_div] using
    jointChannel_diamond_asymptotic.sub
      (discardedPair_overlap_asymptotic.comp (tendsto_add_atTop_nat 5))

end

end D5.S3.Quantum.TensorNetworks.PrimitiveRecordDiamondCoefficient
