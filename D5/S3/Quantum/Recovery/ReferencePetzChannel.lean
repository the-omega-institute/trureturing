/- GID: D5/S3/Quantum/Recovery/ReferencePetzChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/ReferencePetzChannel
   mirror-E: none(waiver:full-petz-work-in-progress)
   anchors: []
   utility: none
   digest: A support decoder is completed with the fixed reference density state. -/

import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Abel

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

namespace D5.S3.Quantum.Recovery.ReferencePetzChannel

variable {n d s : Type*} [Fintype n] [DecidableEq n]
  [Fintype d] [DecidableEq d] [Fintype s]

/-- Preparation with a matrix square-root factor, retaining the fixed reference state. -/
def densityResetKraus (S : Matrix d d ℂ) (B : Matrix n n ℂ) :
    d × n → Matrix d n ℂ := fun ij => S * rowReset ij.1 B ij.2

private theorem density_reset_action (S : Matrix d d ℂ) (B X : Matrix n n ℂ) :
    (∑ ij, densityResetKraus S B ij * X * (densityResetKraus S B ij)ᴴ) =
      Matrix.trace (B * X * Bᴴ) • (S * Sᴴ) := by
  classical
  simp only [densityResetKraus, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  have hrow (i : d) :
      (∑ j : n, S * rowReset i B j * X * ((rowReset i B j)ᴴ * Sᴴ)) =
        S * (Matrix.trace (B * X * Bᴴ) • Matrix.single i i 1) * Sᴴ := by
    rw [← row_reset_action i B X]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  simp_rw [hrow]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one,
    Matrix.mul_one]

private theorem density_reset_gram (S : Matrix d d ℂ) (B : Matrix n n ℂ) :
    (∑ ij, (densityResetKraus S B ij)ᴴ * densityResetKraus S B ij) =
      Matrix.trace (Sᴴ * S) • (Bᴴ * B) := by
  classical
  have hmatrix :
      (∑ i : d, ∑ j : n,
        (Matrix.single i j (1 : ℂ))ᴴ * (Sᴴ * S) * Matrix.single i j (1 : ℂ)) =
        Matrix.trace (Sᴴ * S) • (1 : Matrix n n ℂ) := by
    simp only [Matrix.conjTranspose_single, star_one]
    have hs (i : d) (j : n) :
        Matrix.single j i (1 : ℂ) * (Sᴴ * S) * Matrix.single i j (1 : ℂ) =
          (Sᴴ * S) i i • Matrix.single j j (1 : ℂ) := by
      simp [Matrix.smul_single]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    change (∑ j : n, Matrix.trace (Sᴴ * S) • Matrix.single j j (1 : ℂ)) = _
    rw [← Finset.smul_sum, Matrix.sum_single_one]
  calc
    _ = Bᴴ * (∑ i : d, ∑ j : n,
        (Matrix.single i j (1 : ℂ))ᴴ * (Sᴴ * S) * Matrix.single i j (1 : ℂ)) * B := by
      simp only [densityResetKraus, rowReset, Fintype.sum_prod_type,
        Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = Matrix.trace (Sᴴ * S) • (Bᴴ * B) := by
      rw [hmatrix, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Completion uses the specified density matrix, rather than a selected pure state.
This helper is intended for the full Petz equality proof and is not an independent content claim. -/
theorem complete_quantum_channel_with_reference
    (K : s → Matrix d n ℂ) (P : Matrix n n ℂ) (S : Matrix d d ℂ)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hK : (∑ a, (K a)ᴴ * K a) = P) (hS : Matrix.trace (S * Sᴴ) = 1) :
    ∃ recovery : QuantumChannel n d, ∀ X : Matrix n n ℂ,
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        (∑ a, K a * X * (K a)ᴴ) + Matrix.trace ((1 - P) * X) • (S * Sᴴ) := by
  classical
  let L : s ⊕ (d × n) → Matrix d n ℂ := Sum.elim K (densityResetKraus S (1 - P))
  have hS' : Matrix.trace (Sᴴ * S) = 1 :=
    (Matrix.trace_mul_comm Sᴴ S).trans hS
  have hcomplement : (1 - P)ᴴ * (1 - P) = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  have hnormal : (∑ a, (L a)ᴴ * L a) = 1 := by
    simp only [L, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hK, density_reset_gram, hS', one_smul, hcomplement]
    abel
  obtain ⟨recovery, hr⟩ := finite_kraus_quantum_channel L hnormal
  refine ⟨recovery, fun X => ?_⟩
  rw [hr]
  simp only [L, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [density_reset_action]
  have htrace : Matrix.trace ((1 - P) * X * (1 - P)ᴴ) =
      Matrix.trace ((1 - P) * X) := by
    rw [Matrix.trace_mul_comm ((1 - P) * X) (1 - P)ᴴ, ← Matrix.mul_assoc,
      hcomplement]
  rw [htrace]

#print axioms complete_quantum_channel_with_reference

-- The finite functional-calculus square root and matrix associativity require this budget.
set_option maxHeartbeats 1000000 in
/-- The completed Petz map is an actual quantum channel and recovers its fixed
reference state, including singular reference and output states. -/
theorem completed_reference_petz_channel
    (K : s → Matrix n d ℂ) (hK : (∑ a, (K a)ᴴ * K a) = 1)
    (σ : DensityState d) :
    let R := CStarMatrix.ofMatrix.symm σ.1
    let S := cfc Real.sqrt R
    let τ := ∑ a, K a * R * (K a)ᴴ
    let P := spectralSupport τ
    let W := spectralInverseSqrt τ
    ∃ recovery : QuantumChannel n d,
      (∀ X : Matrix n n ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ a, S * (K a)ᴴ * W * X * W * K a * S) +
            Matrix.trace ((1 - P) * X) • R) ∧
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix τ)) = R := by
  classical
  let R := CStarMatrix.ofMatrix.symm σ.1
  let S := cfc Real.sqrt R
  let τ := ∑ a, K a * R * (K a)ᴴ
  let P := spectralSupport τ
  let W := spectralInverseSqrt τ
  let E := fun a => K a * S
  change ∃ recovery : QuantumChannel n d,
      (∀ X : Matrix n n ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ a, S * (K a)ᴴ * W * X * W * K a * S) +
            Matrix.trace ((1 - P) * X) • R) ∧
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix τ)) = R
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
  have hRtrace : Matrix.trace R = 1 := σ.2.2
  have hSadj : Sᴴ = S := by
    change star (cfc Real.sqrt R) = cfc Real.sqrt R
    exact (cfc_predicate Real.sqrt R : IsSelfAdjoint (cfc Real.sqrt R)).star_eq
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ R) :=
    R.finite_real_spectrum.continuousOn f
  have hSS : S * S = R := by
    calc
      _ = cfc (fun x : ℝ => Real.sqrt x * Real.sqrt x) R :=
        (cfc_mul Real.sqrt Real.sqrt R (hcont _) (hcont _)).symm
      _ = cfc (fun x : ℝ => x) R := by
        apply cfc_congr
        intro x hx
        rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        nlinarith [Real.sq_sqrt (hR.eigenvalues_nonneg i)]
      _ = R := cfc_id' ℝ R hR.isHermitian.isSelfAdjoint
  have houtput : (∑ a, E a * (E a)ᴴ) = τ := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [E]
    rw [Matrix.conjTranspose_mul, hSadj]
    calc
      _ = K a * (S * S) * (K a)ᴴ := by simp only [Matrix.mul_assoc]
      _ = K a * R * (K a)ᴴ := by rw [hSS]
  have hdata : Wᴴ = W ∧ Pᴴ = P ∧ P * P = P ∧
      (∑ a, ((E a)ᴴ * W)ᴴ * ((E a)ᴴ * W)) = P := by
    simpa only [houtput] using spectral_decoder_normalization E
  obtain ⟨hWadj, hPadj, hPP, hdecoder⟩ := hdata
  have hPE (a : s) : P * E a = E a := by
    simpa only [houtput] using spectral_support_on_kraus E a
  have hPτ : P * τ = τ := by
    rw [← houtput, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Matrix.mul_assoc, hPE]
  have hWτW : W * τ * W = P := by
    calc
      _ = ∑ a, ((E a)ᴴ * W)ᴴ * ((E a)ᴴ * W) := by
        rw [← houtput]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hWadj, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = P := hdecoder
  have hEgram : (∑ a, (E a)ᴴ * E a) = R := by
    calc
      _ = S * (∑ a, (K a)ᴴ * K a) * S := by
        simp only [E, Matrix.conjTranspose_mul, hSadj, Matrix.mul_sum,
          Matrix.sum_mul, Matrix.mul_assoc]
      _ = R := by rw [hK, Matrix.mul_one, hSS]
  have hroottrace : Matrix.trace (S * Sᴴ) = 1 := by
    rw [hSadj, hSS]
    exact hRtrace
  obtain ⟨recovery, hr⟩ := complete_quantum_channel_with_reference
    (fun a => (E a)ᴴ * W) P S hPadj hPP hdecoder hroottrace
  refine ⟨recovery, ?_, ?_⟩
  · intro X
    simpa only [E, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hWadj, hSadj, hSS, Matrix.mul_assoc] using hr X
  · have hcore : (∑ a, ((E a)ᴴ * W) * τ * ((E a)ᴴ * W)ᴴ) = R := by
      calc
        _ = ∑ a, (E a)ᴴ * (W * τ * W) * E a := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            hWadj, Matrix.mul_assoc]
        _ = ∑ a, (E a)ᴴ * E a := by
          rw [hWτW]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Matrix.mul_assoc, hPE]
        _ = R := hEgram
    have hmissing : Matrix.trace ((1 - P) * τ) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPτ, sub_self, Matrix.trace_zero]
    rw [hr, hcore, hmissing, zero_smul, add_zero]

#print axioms completed_reference_petz_channel

end D5.S3.Quantum.Recovery.ReferencePetzChannel
