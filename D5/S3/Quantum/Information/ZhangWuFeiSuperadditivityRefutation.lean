/- GID: D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.claim; result=D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.result; claim=D5/S3/Quantum/Information/ZhangWuFeiSuperadditivityRefutation.claim
   digest: A full-rank diagonal reference refutes relative-entropy superadditivity. -/

/-
result — proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18562; Refuted).
Direct frozen dependencies (same-module helpers expanded):
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    declaration statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy
    declaration statement_id: sha256:1fde73d469bc7e293eef439b271276205450d8758cb7358eaadae794794d8f0a
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy._proof_2
    declaration statement_id: sha256:b659ea76aac5668e0f3571e96a5458a857affe9cb128e8011882069921684364
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal
    declaration statement_id: sha256:3a60f49e4c654be846afb7f639e5ad2ed4d5eb5fbd277586af42d3a0b6fd1809
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.instNormedAlgebraComplexMatrix_d5
    declaration statement_id: sha256:2fdcc8ef4caa4a8edf8b4c8e0b99524e5e9a6270887ee2ce44c0ce67c03f3c94
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.instNormedRingMatrixComplex_d5
    declaration statement_id: sha256:ed10e8a6fa4ad211d664e509de41111634e8ab60eb279c237f63bcae71d5f51a
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState
    declaration statement_id: sha256:9b1299d5fa00a59321b435771bba283a533b7e1e7a071e7d927aae4eb94d4d42
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.densityMatrix
    declaration statement_id: sha256:e8ba081c519bb0c785f070157864cb2f6eecf4b55d1e6b6b8c50a07b3fb988a6
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    declaration statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.partialTraceLeft_diagonal
    declaration statement_id: sha256:e6d5d6efede41c1340a8739c9a5dec65a6a20b08a9033293a51c74678c9e9936
  D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.partialTraceRight_diagonal
    declaration statement_id: sha256:bba598f0eb8a825af3114f821ffcf1f6f74bb3f6eebb646ff80e76c6f165575d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalLeft
    declaration statement_id: sha256:7579934e8cf68c9a1e1f14470e58e70c66939704953b29e953ae8d75b92bef6a
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
    declaration statement_id: sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
    declaration statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    declaration statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.uniformTwo._simp_1
    declaration statement_id: sha256:376d627e9e8d8b7a86d18e267b577d3e6e73bdaaa5d03dcb4cc83a4c85375dc2
The original diagonalState definition is publicized unchanged in this delivery;
its current declaration identity is supplied by the scoped publication report.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
Unfinished escape audit for the published diagonalState: https://github.com/the-omega-institute/trureturing/issues/20328.
The claim uses the preregistered expressions; proofs reuse the original diagonalState constructor.
-/

import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation

/-! A maximally mixed input makes all three unitary orbits constant. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace D5.S3.Quantum.Information.ZhangWuFeiSuperadditivityRefutation

open scoped ComplexOrder MatrixOrder CStarAlgebra

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState quantumRelativeEntropy)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (marginalLeft marginalRight)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (unitaryConjugateState)

/-- Zhang–Wu–Fei, Section 4, inequality (4.2): for density matrices `ρ_AB`, `σ_AB` on
`H_A ⊗ H_B` with `σ_AB` full-ranked, there exist unitaries `U_A`, `U_B`, `U_AB` with
`S(U_AB ρ_AB U_AB† ‖ σ_AB) ≥ S(U_A ρ_A U_A† ‖ σ_A) + S(U_B ρ_B U_B† ‖ σ_B)`. -/
def claim : Prop :=
  ∀ (a b : ℕ) (ρ σ : DensityState (Fin a × Fin b)),
    (CStarMatrix.ofMatrix.symm σ.1).PosDef →
      ∃ (UAB : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
        (hAB : UAB ∈ Matrix.unitaryGroup (Fin a × Fin b) ℂ)
        (UA : Matrix (Fin a) (Fin a) ℂ) (hA : UA ∈ Matrix.unitaryGroup (Fin a) ℂ)
        (UB : Matrix (Fin b) (Fin b) ℂ) (hB : UB ∈ Matrix.unitaryGroup (Fin b) ℂ),
        quantumRelativeEntropy (unitaryConjugateState UA hA (marginalRight ρ)) (marginalRight σ) +
            quantumRelativeEntropy (unitaryConjugateState UB hB (marginalLeft ρ)) (marginalLeft σ) ≤
          quantumRelativeEntropy (unitaryConjugateState UAB hAB ρ) σ



noncomputable section

open scoped BigOperators
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow (densityMatrix)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private lemma diagonal_entropy {n : Type} [Fintype n] [DecidableEq n]
    (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    quantumRelativeEntropy (diagonalState p hp hps) (diagonalState q hq hqs) =
      ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  have hlog (r : n → ℝ) :
      CFC.log (CStarMatrix.ofMatrix (Matrix.diagonal fun i => (r i : ℂ))) =
        CStarMatrix.ofMatrix (Matrix.diagonal fun i => (Real.log (r i) : ℂ)) := by
    rw [← cfc_log_diagonal]
    have hM : (Matrix.diagonal fun i => (r i : ℂ)).IsHermitian := by
      exact Matrix.isHermitian_diagonal_iff.mpr (fun i => by
        change star (r i : ℂ) = (r i : ℂ)
        simp)
    exact (StarAlgHomClass.map_cfc (p := Matrix.IsHermitian) (q := IsSelfAdjoint)
      CStarMatrix.ofMatrixStarAlgEquiv Real.log _
      ((Matrix.diagonal fun i => (r i : ℂ)).finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hM (by
        change IsSelfAdjoint (CStarMatrix.ofMatrix (Matrix.diagonal fun i => (r i : ℂ)))
        exact hM)).symm
  unfold quantumRelativeEntropy diagonalState
  simp only [hlog]
  change (Matrix.trace ((Matrix.diagonal fun i => (p i : ℂ)) *
    ((Matrix.diagonal fun i => (Real.log (p i) : ℂ)) -
      (Matrix.diagonal fun i => (Real.log (q i) : ℂ))))).re = _
  rw [Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp

private lemma unitary_scalar_fixed {n : Type} [Fintype n] [DecidableEq n]
    (rho : DensityState n) (c : ℂ) (hc : densityMatrix rho = c • 1)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    unitaryConjugateState U hU rho = rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change U * densityMatrix rho * star U = densityMatrix rho
  rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mem_unitaryGroup_iff.mp hU]

private def p : Fin 2 × Fin 2 → ℝ := fun _ => 1/4
private def q : Fin 2 × Fin 2 → ℝ := fun i => if i = (0, 0) then 61/64 else 1/64
private def r : Fin 2 → ℝ := fun _ => 1/2
private def s : Fin 2 → ℝ := fun i => if i = 0 then 31/32 else 1/32

private lemma p_nonneg (i : Fin 2 × Fin 2) : 0 ≤ p i := by norm_num [p]
private lemma q_nonneg (i : Fin 2 × Fin 2) : 0 ≤ q i := by
  unfold q; split <;> norm_num
private lemma r_nonneg (i : Fin 2) : 0 ≤ r i := by norm_num [r]
private lemma s_nonneg (i : Fin 2) : 0 ≤ s i := by
  unfold s; split <;> norm_num
private lemma p_sum : ∑ i, p i = 1 := by
  norm_num [p, Fintype.sum_prod_type, Fin.sum_univ_two]
private lemma q_sum : ∑ i, q i = 1 := by
  norm_num [q, Fintype.sum_prod_type, Fin.sum_univ_two]
private lemma r_sum : ∑ i, r i = 1 := by norm_num [r, Fin.sum_univ_two]
private lemma s_sum : ∑ i, s i = 1 := by norm_num [s, Fin.sum_univ_two]

private def rho := diagonalState p p_nonneg p_sum
private def sigma := diagonalState q q_nonneg q_sum
private def rhoM := diagonalState r r_nonneg r_sum
private def sigmaM := diagonalState s s_nonneg s_sum

private lemma sigma_posDef : (CStarMatrix.ofMatrix.symm sigma.1).PosDef := by
  change (Matrix.diagonal fun i => (q i : ℂ)).PosDef
  rw [Matrix.posDef_diagonal_iff]
  intro i
  simp only [q]
  split <;> norm_num [Complex.pos_iff]

private lemma rho_right : marginalRight rho = rhoM := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceRight (Matrix.diagonal fun i => (p i : ℂ)) =
    Matrix.diagonal fun i => (r i : ℂ)
  rw [ChenKatoBrandaoCMIRefutation.partialTraceRight_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [p, r, Matrix.diagonal, Fin.sum_univ_two]
private lemma rho_left : marginalLeft rho = rhoM := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceLeft (Matrix.diagonal fun i => (p i : ℂ)) =
    Matrix.diagonal fun i => (r i : ℂ)
  rw [ChenKatoBrandaoCMIRefutation.partialTraceLeft_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [p, r, Matrix.diagonal, Fin.sum_univ_two]
private lemma sigma_right : marginalRight sigma = sigmaM := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceRight (Matrix.diagonal fun i => (q i : ℂ)) =
    Matrix.diagonal fun i => (s i : ℂ)
  rw [ChenKatoBrandaoCMIRefutation.partialTraceRight_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, s, Matrix.diagonal, Fin.sum_univ_two]
private lemma sigma_left : marginalLeft sigma = sigmaM := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceLeft (Matrix.diagonal fun i => (q i : ℂ)) =
    Matrix.diagonal fun i => (s i : ℂ)
  rw [ChenKatoBrandaoCMIRefutation.partialTraceLeft_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, s, Matrix.diagonal, Fin.sum_univ_two]

private lemma rho_scalar : densityMatrix rho = (1/4 : ℂ) • 1 := by
  simpa [densityMatrix, rho, diagonalState, p] using
    (Matrix.smul_one_eq_diagonal (m := Fin 2 × Fin 2) (1/4 : ℂ)).symm
private lemma rhoM_scalar : densityMatrix rhoM = (1/2 : ℂ) • 1 := by
  simpa [densityMatrix, rhoM, diagonalState, r] using
    (Matrix.smul_one_eq_diagonal (m := Fin 2) (1/2 : ℂ)).symm

private lemma joint_entropy : quantumRelativeEntropy rho sigma =
    Real.log (1/4) - Real.log (61/64)/4 - 3 * Real.log (1/64)/4 := by
  rw [show quantumRelativeEntropy rho sigma = _ from
    diagonal_entropy p q p_nonneg q_nonneg p_sum q_sum]
  norm_num [p, q, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring
private lemma marginal_entropy : quantumRelativeEntropy rhoM sigmaM =
    Real.log (1/2) - Real.log (31/32)/2 - Real.log (1/32)/2 := by
  rw [show quantumRelativeEntropy rhoM sigmaM = _ from
    diagonal_entropy r s r_nonneg s_nonneg r_sum s_sum]
  norm_num [r, s, Fin.sum_univ_two]
  ring

private lemma gap_neg : quantumRelativeEntropy rho sigma -
    2 * quantumRelativeEntropy rhoM sigmaM < 0 := by
  rw [joint_entropy, marginal_entropy]
  have hlog := Real.log_neg (by norm_num : (0 : ℝ) < 923521/3997696)
    (by norm_num : (923521/3997696 : ℝ) < 1)
  have hid : (923521/3997696 : ℝ) = 16 * (1/64) * (31/32)^4 / (61/64) := by norm_num
  rw [hid, Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hlog
  have h4 : Real.log (1/4 : ℝ) = -2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log (1/2 : ℝ) = -Real.log 2 := by
    simpa only [one_div] using Real.log_inv (2 : ℝ)
  have h64 : Real.log (1/64 : ℝ) = -6 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      show (64 : ℝ) = 2^6 by norm_num, Real.log_pow]
    norm_num
  have h32 : Real.log (1/32 : ℝ) = -5 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      show (32 : ℝ) = 2^5 by norm_num, Real.log_pow]
    norm_num
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
  rw [h4, h2, h64, h32]
  rw [h64, h16] at hlog
  linarith

/-- The full-ranked two-qubit reference with diagonal (61,1,1,1)/64 refutes (4.2). -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨UAB, hAB, UA, hA, UB, hB, hle⟩ := h 2 2 rho sigma sigma_posDef
  rw [rho_right, rho_left, sigma_right, sigma_left,
    unitary_scalar_fixed rhoM (1/2) rhoM_scalar UA hA,
    unitary_scalar_fixed rhoM (1/2) rhoM_scalar UB hB,
    unitary_scalar_fixed rho (1/4) rho_scalar UAB hAB] at hle
  exact (not_le_of_gt gap_neg) (sub_nonneg.mpr (by simpa [two_mul] using hle))

end
end D5.S3.Quantum.Information.ZhangWuFeiSuperadditivityRefutation
