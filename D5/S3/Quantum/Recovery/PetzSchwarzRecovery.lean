/- GID: D5/S3/Quantum/Recovery/PetzSchwarzRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSchwarzRecovery
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Supported square-root columns force actual Petz recovery by Schwarz and trace rigidity. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery

noncomputable section
universe u v
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

namespace D5.S3.Quantum.Recovery.PetzSchwarzRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

private theorem sqrt_square {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  calc
    _ = cfc (fun x : ℝ => Real.sqrt x * Real.sqrt x) A :=
      (cfc_mul Real.sqrt Real.sqrt A (hc _) (hc _)).symm
    _ = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
    _ = A := cfc_id' ℝ A hA.isHermitian.isSelfAdjoint

private theorem support_spectral_facts {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    (spectralSupport Q)ᴴ = spectralSupport Q ∧
      spectralSupport Q * spectralSupport Q = spectralSupport Q ∧
      (spectralInverseSqrt Q)ᴴ = spectralInverseSqrt Q ∧
      spectralInverseSqrt Q * Q * spectralInverseSqrt Q = spectralSupport Q := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) :=
    Q.finite_real_spectrum.continuousOn f
  have hm (f g : ℝ → ℝ) :
      cfc f Q * cfc g Q = cfc (fun x => f x * g x) Q :=
    (cfc_mul f g Q (hc _) (hc _)).symm
  have hP : (spectralSupport Q)ᴴ = spectralSupport Q := by
    exact (cfc_predicate _ Q : IsSelfAdjoint (spectralSupport Q)).star_eq
  have hW : (spectralInverseSqrt Q)ᴴ = spectralInverseSqrt Q := by
    exact (cfc_predicate _ Q : IsSelfAdjoint (spectralInverseSqrt Q)).star_eq
  have hPP : spectralSupport Q * spectralSupport Q = spectralSupport Q := by
    unfold spectralSupport
    rw [hm]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  refine ⟨hP, hPP, hW, ?_⟩
  calc
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q * cfc (fun x : ℝ => x) Q *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q := by
      rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]
      rfl
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) Q := by
      rw [hm, hm]
    _ = spectralSupport Q := by
      apply cfc_congr
      intro x hx
      rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      by_cases h : hQ.isHermitian.eigenvalues i = 0
      · simp [spectralSupport, h]
      · have hs : Real.sqrt (hQ.isHermitian.eigenvalues i) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (hQ.eigenvalues_nonneg i) (Ne.symm h)))
        change (Real.sqrt (hQ.isHermitian.eigenvalues i))⁻¹ *
          hQ.isHermitian.eigenvalues i * (Real.sqrt (hQ.isHermitian.eigenvalues i))⁻¹ =
          if hQ.isHermitian.eigenvalues i = 0 then 0 else 1
        rw [if_neg h]
        field_simp [hs] <;> nlinarith [Real.sq_sqrt (hQ.eigenvalues_nonneg i)]

private theorem projection_column_lower_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A P B : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hB : Bᴴ = B) (hcol : A * P = B) : B * B ≤ A * Aᴴ := by
  have hp : (1 - P)ᴴ * (1 - P) = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hpos : (1 - P).PosSemidef := by
    rw [← hp]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hAP : A * P * Aᴴ = B * B := by
    calc
      _ = A * (P * P) * Aᴴ := by rw [hPP]
      _ = (A * P) * (A * P)ᴴ := by
        simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
      _ = B * B := by rw [hcol, hB]
  have h := hpos.mul_mul_conjTranspose_same A
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAP] using h

private theorem trace_rigidity {n : Type*} [Fintype n] [DecidableEq n]
    (R N : Matrix n n ℂ) (hle : R ≤ N) (htrace : N.trace = R.trace) : N = R := by
  have hpos := Matrix.le_iff.mp hle
  have hz : (N - R).trace = 0 := by rw [Matrix.trace_sub, htrace, sub_self]
  exact sub_eq_zero.mp (hpos.trace_eq_zero_iff.mp hz)

private theorem support_preserves_of_kernel {n : Type*} [Fintype n] [DecidableEq n]
    (Q T : Matrix n n ℂ) (hQ : Q.PosSemidef) (hT : T.PosSemidef)
    (hk : ∀ x : n → ℂ, Q *ᵥ x = 0 → T *ᵥ x = 0) :
    spectralSupport Q * T = T := by
  classical
  let U : Matrix n n ℂ := hQ.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i =>
    ((if hQ.isHermitian.eigenvalues i = 0 then 0 else 1 : ℝ) : ℂ))
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hQ.isHermitian.eigenvectorUnitary
  have hP : spectralSupport Q = U * D * Uᴴ := by
    rw [spectralSupport, hQ.isHermitian.cfc_eq]
    rfl
  have hTD : T * U * D = T * U := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : hQ.isHermitian.eigenvalues j = 0
    · have hq : Q *ᵥ (fun i => hQ.isHermitian.eigenvectorBasis j i) = 0 := by
        simpa only [hj, zero_smul] using hQ.isHermitian.mulVec_eigenvectorBasis j
      have ht := congrFun (hk _ hq) i
      change (T * U) i j * _ = (T * U) i j
      have hTU : (T * U) i j = 0 := by
        simpa only [U, Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
          Matrix.mulVec, dotProduct, Pi.zero_apply] using ht
      rw [hTU, zero_mul]
    · simp only [D, Matrix.diagonal_apply_eq, if_neg hj, Complex.ofReal_one, mul_one]
  have hTP : T * spectralSupport Q = T := by
    rw [hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTD, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  have hPadj := (support_spectral_facts Q hQ).1
  have h := congrArg Matrix.conjTranspose hTP
  simpa only [Matrix.conjTranspose_mul, hPadj, hT.isHermitian.eq] using h

/-- The actual output support projection preserves the channel output state.
This is also the identity that removes the CPTP completion's complement term. -/
theorem petz_output_support_projection
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) :
    spectralSupport M.data.Q * M.data.T = M.data.T := by
  apply support_preserves_of_kernel M.data.Q M.data.T M.data.hQ M.data.hT
  intro x hx
  exact M.outputSupport hx

-- The actual spectral matrices and the channel Schwarz congruence require this budget.
set_option maxHeartbeats 1000000 in
/-- The actual Petz core majorizes both the full adjoint amplitude and its
input-support columns, and has the actual input trace. These facts do not
assume equality of the square-root columns. -/
theorem petz_core_schwarz_and_trace
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) :
    let H := cfc Real.sqrt M.data.S
    let W := spectralInverseSqrt M.data.Q
    let Y := W * cfc Real.sqrt M.data.T
    let A := H * M.data.Ψ Y
    let C := A * spectralSupport M.data.R
    let N := H * M.data.Ψ (W * M.data.T * W) * H
    A * Aᴴ ≤ N ∧ C * Cᴴ ≤ N ∧ N.trace = M.data.R.trace := by
  let R := M.data.R
  let S := M.data.S
  let T := M.data.T
  let Q := M.data.Q
  let H := cfc Real.sqrt S
  let W := spectralInverseSqrt Q
  let Y := W * cfc Real.sqrt T
  let A := H * M.data.Ψ Y
  let N := H * M.data.Ψ (W * T * W) * H
  have hH : Hᴴ = H := (cfc_predicate _ S : IsSelfAdjoint H).star_eq
  obtain ⟨hPR, hPRPR, _, _⟩ := support_spectral_facts R M.data.hR
  obtain ⟨_, _, hW, hWQW⟩ := support_spectral_facts Q M.data.hQ
  have hYY : Y * Yᴴ = W * T * W := by
    have hTroot : (cfc Real.sqrt T)ᴴ = cfc Real.sqrt T :=
      (cfc_predicate _ T : IsSelfAdjoint (cfc Real.sqrt T)).star_eq
    dsimp only [Y]
    have hWadj : Wᴴ = W := hW
    rw [Matrix.conjTranspose_mul, hTroot, hWadj]
    calc
      _ = W * (cfc Real.sqrt T * cfc Real.sqrt T) * W := by
        simp only [Matrix.mul_assoc]
      _ = W * T * W := by rw [sqrt_square T M.data.hT]
  have hupp : A * Aᴴ ≤ N := by
    have h := (Matrix.le_iff.mp (M.schwarzLeft Y)).mul_mul_conjTranspose_same H
    apply Matrix.le_iff.mpr
    simpa only [A, N, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul,
      hH, Matrix.mul_assoc, hYY] using h
  have hprojection :
      (A * spectralSupport R) * (A * spectralSupport R)ᴴ ≤ A * Aᴴ := by
    have hp : (1 - spectralSupport R)ᴴ * (1 - spectralSupport R) =
        1 - spectralSupport R := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPR,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPRPR]
      abel
    have hpos : (1 - spectralSupport R).PosSemidef := by
      rw [← hp]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hAP : (A * spectralSupport R) * (A * spectralSupport R)ᴴ =
        A * spectralSupport R * Aᴴ := by
      rw [Matrix.conjTranspose_mul, hPR]
      calc
        _ = A * (spectralSupport R * spectralSupport R) * Aᴴ := by noncomm_ring
        _ = A * spectralSupport R * Aᴴ := by rw [hPRPR]
    have h := hpos.mul_mul_conjTranspose_same A
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAP] using h
  have hPT : spectralSupport Q * T = T := petz_output_support_projection M
  have htrace : N.trace = R.trace := by
    calc
      _ = (S * M.data.Ψ (W * T * W)).trace := by
        dsimp only [N]
        rw [Matrix.trace_mul_cycle, sqrt_square S M.data.hS]
      _ = (Q * (W * T * W)).trace := M.tracePair S (W * T * W)
      _ = ((W * Q * W) * T).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = T.trace := by rw [hWQW, hPT]
      _ = R.trace := by
        change Matrix.trace (CStarMatrix.ofMatrix.symm (Φ.mapState ρ).1) =
          Matrix.trace (CStarMatrix.ofMatrix.symm ρ.1)
        exact (Φ.mapState ρ).2.2.trans ρ.2.2.symm
  exact ⟨hupp, hprojection.trans hupp, htrace⟩

set_option maxHeartbeats 1000000 in
/-- The actual supported square-root columns force the actual Petz core to recover
the input state. The lower bound and trace rigidity use the common actual
Schwarz and trace supplier. -/
theorem petz_core_recovery_of_support_columns
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ)
    (hcolumns :
      (cfc Real.sqrt M.data.S * M.data.Ψ
        (spectralInverseSqrt M.data.Q * cfc Real.sqrt M.data.T)) *
        spectralSupport M.data.R = cfc Real.sqrt M.data.R) :
    cfc Real.sqrt M.data.S * M.data.Ψ
      (spectralInverseSqrt M.data.Q * M.data.T * spectralInverseSqrt M.data.Q) *
      cfc Real.sqrt M.data.S = M.data.R := by

  let R := M.data.R
  let S := M.data.S
  let T := M.data.T
  let Q := M.data.Q
  let H := cfc Real.sqrt S
  let W := spectralInverseSqrt Q
  let Y := W * cfc Real.sqrt T
  let A := H * M.data.Ψ Y
  let N := H * M.data.Ψ (W * T * W) * H
  have hroot : (cfc Real.sqrt R)ᴴ = cfc Real.sqrt R :=
    (cfc_predicate _ R : IsSelfAdjoint (cfc Real.sqrt R)).star_eq
  obtain ⟨hPR, hPRPR, _, _⟩ := support_spectral_facts R M.data.hR
  have hlow : R ≤ A * Aᴴ := by
    rw [← sqrt_square R M.data.hR]
    exact projection_column_lower_bound A (spectralSupport R) (cfc Real.sqrt R)
      hPR hPRPR hroot hcolumns
  obtain ⟨hupp, _, htrace⟩ := petz_core_schwarz_and_trace M
  exact trace_rigidity R N (hlow.trans hupp) htrace

#print axioms petz_output_support_projection
#print axioms petz_core_schwarz_and_trace
#print axioms petz_core_recovery_of_support_columns

end D5.S3.Quantum.Recovery.PetzSchwarzRecovery
