/- GID: D5/S3/Quantum/Information/BadhaniDasNoisyUnitary
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/BadhaniDasNoisyUnitary
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Noisy unitaries with qubit conditioning attain the Choi min-entropy bound. -/

/-
admission_basis: open-problem-resolution (#19060; Proved).
escape_witness: none. All proof_shape labels use the same-delivery inlining rule.
A' = A = Fin d, B' = B = Fin 2; Choi factors are ordered (R_A, A), (R_B, B).
The public channel entropy inlines the matrix-unit expression from #19060; proofs use the equal frozen inputFirstChoi/matrixAction owners.
FiniteKrausRepresentation has no frozen state record; its Kraus/Choi theorems are not used, and positivity and Kraus action are proved through Mathlib and FiniteKrausChannel.
The four-coordinate sign algebra below transports the frozen Subentropy.PinchingGap sign-twirl and sign_unitary owners along Fin 4 ≃ Fin 4 × Unit; the tuple sign is the literal convention in `sign`.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19176.
Direct frozen dependencies of result (same-delivery helpers inlined):
D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.complex_sqrt_two_sq; declaration statement_id: sha256:aa2d46ddad1e237909d93d17969740efc5ff85ce1ccb3dcbe8b20475fe1e7c71.
D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq; declaration statement_id: sha256:accd04d85421c0847456ddb52626f272e79ea98e568dcf9dfeddc5035a1f2013.
D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul; declaration statement_id: sha256:d184ab8cca52e9135914ea80c978d66f14d44259c135b16963fa87464917cf73.
D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel; declaration statement_id: sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0.
D5/S3/Quantum/Foundation/FiniteKrausChannel.flattenCStar; declaration statement_id: sha256:9b9e23ce473bc0a1b0766512b9fed6713cdd7939742568ad0ba31611e8a03a60.
D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState; declaration statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5.
D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel; declaration statement_id: sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05.
D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap; declaration statement_id: sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc.
D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.trace_preserving; declaration statement_id: sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15.
D5/S3/Quantum/Information/PartialTraceMutualInformation.density_posSemidef; declaration statement_id: sha256:b799be7b0c6e16bb8e03b4bcf99946d7abbc95ac0078be4a08391bec19c88bdc.
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft; declaration statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d.
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef; declaration statement_id: sha256:57037555d268cd6c22ff19563a5f64496a1d89f7e5d8b6b98943b78b84af873d.
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight; declaration statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77.
D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft; declaration statement_id: sha256:70e429b7996075b0f25052d5fb6f603c2ac2556abcf0d2510142499e0c5d267c.
D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi; declaration statement_id: sha256:7620ae518a39944b6825fd260cd713177187b28856493804968f5ddc77f33bd0.
D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction; declaration statement_id: sha256:83ac791e170c8f29d6ff3fedd7eb6d261e6a7ec791b03ef14422460da17cc9dc.
D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction._proof_1; declaration statement_id: sha256:de95647f5b774bd7a96171362bb7b499e0c7a57ae7cb79715b26222676f8720b.
D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction._proof_2; declaration statement_id: sha256:2b04e7ef3cd1e2120d6d95c969eccf49fc71c53501752c2f7d16ba7c55947cd9.
Theorem classifications (all bind-only, with consumers):
magicCoeff_adjoint_mul: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
magicW_gram: proof_shape: bind-only; consumers: magicW_cogram, maximally_entangled_eigenbasis.
magicW_cogram: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
magicRaw_real_congruence: proof_shape: bind-only; consumers: magicW_real_congruence.
magicW_real_congruence: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
real_cast_adjoint: proof_shape: bind-only; consumers: real_cast_unitary, real_spectral_basis.
real_cast_mul: proof_shape: bind-only; consumers: real_cast_unitary, real_spectral_basis.
real_cast_unitary: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
real_spectral_basis: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
sign_star: proof_shape: bind-only; consumers: sign_sq.
sign_sq: proof_shape: bind-only; consumers: signReal_sq.
signDiagonal_unitary: proof_shape: bind-only; consumers: sign_sq, signConjugate_unitary.
diagonal_twirl: proof_shape: bind-only; consumers: basis_twirl.
signConjugate_unitary: proof_shape: bind-only; consumers: sign_symmetry_of_eigenbasis.
basis_twirl: proof_shape: bind-only; consumers: symmetry_pinching_feasible.
symmetry_pinching_feasible: proof_shape: bind-only; consumers: replacement_of_sign_symmetry.
vectorRows_kronecker_action: proof_shape: bind-only; consumers: sign_tensor_invariant.
vectorRows_gram: proof_shape: bind-only; consumers: partner_gram_diagonal.
sign_tensor_invariant: proof_shape: bind-only; consumers: eigenbasis_sign_partner.
noisy_rankOne_invariant: proof_shape: bind-only; consumers: sign_symmetry_of_eigenbasis.
choiN_unitary: proof_shape: bind-only; consumers: choiN_noisy.
choiN_replacement: proof_shape: bind-only; consumers: choiN_noisy.
choiN_noisy: proof_shape: bind-only; consumers: choiN_noisy_trace, result.
choiN_eq_dimension_smul_choiState: proof_shape: bind-only; consumers: result.
unitary_row_inner: proof_shape: bind-only; consumers: reducedUnitary_left.
unitary_column_inner: proof_shape: bind-only; consumers: reducedUnitary_right.
reducedUnitary_left: proof_shape: bind-only; consumers: normalizedReduced_marginals, unitaryChoiVector_trace.
reducedUnitary_right: proof_shape: bind-only; consumers: normalizedReduced_marginals.
reducedUnitary_posSemidef: proof_shape: bind-only; consumers: result.
normalizedReduced_marginals: proof_shape: bind-only; consumers: result.
Dmax_eq_iInf_cost: proof_shape: bind-only; consumers: Dmax_le_of_cost_imp.
Dmax_smul_both: proof_shape: bind-only; consumers: entropy_identity_of_replacement.
feasible_trace_lower: proof_shape: bind-only; consumers: normalized_cost_lower.
Dmax_smul_left: proof_shape: bind-only; consumers: entropy_identity_of_replacement.
Dmax_le_of_cost_imp: proof_shape: bind-only; consumers: replacement_of_sign_symmetry.
choiQ_posSemidef: proof_shape: bind-only; consumers: choiQ_half_state.
choiQ_trace: proof_shape: bind-only; consumers: choiQ_half_state.
choiQ_half_state: proof_shape: bind-only; consumers: normalized_choi_infimum, entropy_identity_of_replacement, replacement_of_sign_symmetry.
mixed_unitary_choi: proof_shape: bind-only; consumers: pinch_is_normalized_choi.
magicW_vector_coeff: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
real_unitary_column_norm: proof_shape: bind-only; consumers: maximally_entangled_eigenbasis.
maximally_entangled_eigenbasis: proof_shape: bind-only; consumers: result.
maxent_vector_unitary: proof_shape: bind-only; consumers: pinch_is_normalized_choi.
pinch_is_normalized_choi: proof_shape: bind-only; consumers: replacement_of_sign_symmetry.
normalized_cost_lower: proof_shape: bind-only; consumers: entropy_identity_of_replacement, replacement_of_sign_symmetry.
ereal_iInf_add_real: proof_shape: bind-only; consumers: entropy_identity_of_replacement.
normalized_choi_infimum: proof_shape: bind-only; consumers: entropy_identity_of_replacement.
entropy_identity_of_replacement: proof_shape: bind-only; consumers: entropy_identity_of_sign_symmetry.
matrix_star_mul: proof_shape: bind-only; consumers: partner_gram_diagonal.
matrix_star_adjoint: proof_shape: bind-only; consumers: partner_gram_diagonal.
partner_gram_diagonal: proof_shape: bind-only; consumers: eigenbasis_sign_partner.
eigenbasis_sign_partner: proof_shape: bind-only; consumers: sign_symmetry_of_eigenbasis.
signReal_cast: proof_shape: bind-only; consumers: sign_star, signReal_sq, sign_symmetry_of_eigenbasis.
signReal_sq: proof_shape: bind-only; consumers: sign_symmetry_of_eigenbasis.
sign_symmetry_of_eigenbasis: proof_shape: bind-only; consumers: result.
unitaryChoiVector_trace: proof_shape: bind-only; consumers: choiN_noisy_trace.
choiN_noisy_trace: proof_shape: bind-only; consumers: choiState_noisy_trace.
choiState_noisy_trace: proof_shape: bind-only; consumers: result.
pinch_smul: proof_shape: bind-only; consumers: replacement_of_sign_symmetry.
replacement_of_sign_symmetry: proof_shape: bind-only; consumers: entropy_identity_of_sign_symmetry.
entropy_identity_of_sign_symmetry: proof_shape: bind-only; consumers: result.
result: proof_shape: bind-only; consumers: external open-problem settlement.
Definitions: Dmax, condMinEntropy, choiN, choiState, channelCondMinEntropy, noisyUnitary, claim, quaternionCoeff, magicCoeff, magicRaw, magicW, sign, signConjugate, pinch, unitaryChoiVector, reducedUnitary, signReal.
-/


import D5.S3.Quantum.Algebra.GramUnitaryExtension
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.Subentropy.PinchingGap

noncomputable section
namespace D5.S3.Quantum.Information.BadhaniDasNoisyUnitary
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (inputFirstChoi matrixAction)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder MatrixOrder Kronecker BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
section
variable {d : ℕ}
open scoped Classical in
def Dmax {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : EReal :=
  if ∃ t : ℝ, 0 ≤ t ∧ ρ ≤ t • σ then
    ((Real.logb 2 (sInf {t : ℝ | 0 ≤ t ∧ ρ ≤ t • σ}) : ℝ) : EReal)
  else ⊤
def condMinEntropy {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (ρ : Matrix (X × Y) (X × Y) ℂ) : EReal :=
  -⨅ σ : DensityState Y, Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val)
def choiN (N : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ → Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) : Matrix ((Fin d × Fin d) × (Fin 2 × Fin 2)) ((Fin d × Fin d) × (Fin 2 × Fin 2)) ℂ :=
  fun x y => N (Matrix.single (x.1.1, x.2.1) (y.1.1, y.2.1) (1 : ℂ)) (x.1.2, x.2.2) (y.1.2, y.2.2)
def choiState (N : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ → Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) : Matrix ((Fin d × Fin d) × (Fin 2 × Fin 2)) ((Fin d × Fin d) × (Fin 2 × Fin 2)) ℂ :=
  ((d * 2 : ℕ) : ℝ)⁻¹ • choiN N
def channelCondMinEntropy (N : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ → Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) : EReal :=
  -⨅ Q : QuantumChannel (Fin 2) (Fin 2), Dmax (choiN N) ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ (fun x y => CStarMatrix.ofMatrix.symm
    (Q.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single x.1 y.1 (1 : ℂ)))) x.2 y.2))
def noisyUnitary (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (p : ℝ) (Z : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ :=
  p • (Z.trace • (((d * 2 : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ))) +
    (1 - p) • ((U : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) * Z * star (U : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ))
def claim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (p : ℝ), 0 ≤ p → p ≤ 1 →
    channelCondMinEntropy (noisyUnitary U p) =
      condMinEntropy (choiState (noisyUnitary U p)) - ((Real.logb 2 d : ℝ) : EReal)
end
private def quaternionCoeff (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 : ℂ) + Complex.I * (v 3 : ℂ), (v 2 : ℂ) + Complex.I * (v 1 : ℂ);
     -(v 2 : ℂ) + Complex.I * (v 1 : ℂ), (v 0 : ℂ) - Complex.I * (v 3 : ℂ)]
private def magicCoeff (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2)⁻¹ • quaternionCoeff v
private lemma magicCoeff_adjoint_mul (v : Fin 4 → ℝ) (hv : ∑ i : Fin 4, (v i)^2 = 1) : (magicCoeff v).conjTranspose * magicCoeff v = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    simpa only [one_div] using TsirelsonInequality.sqrt_two_inv_mul_self
  have hq : (quaternionCoeff v).conjTranspose * quaternionCoeff v =
      ((∑ k : Fin 4, (v k)^2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [quaternionCoeff, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply, map_add, map_sub, map_mul, Complex.conj_I,
        Matrix.one_apply, pow_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have ht : (magicCoeff v).conjTranspose * magicCoeff v =
      (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold magicCoeff; rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      hq, hv]
    simpa only [Complex.ofReal_one, one_smul, smul_smul, hr]
  exact congrFun (congrFun ht i) j
private def magicRaw : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ := fun x =>
  !![1, 0, 0, Complex.I; 0, Complex.I, 1, 0;
     0, Complex.I, -1, 0; 1, 0, 0, -Complex.I]
       (if x.1 = 0 then (if x.2 = 0 then 0 else 1) else
         (if x.2 = 0 then 2 else 3))
private def magicW : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ := (Real.sqrt 2)⁻¹ • magicRaw
private lemma magicW_gram : magicW.conjTranspose * magicW = 1 := by
  have hraw : magicRaw.conjTranspose * magicRaw = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [magicRaw, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.star_def]
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    simpa only [one_div] using TsirelsonInequality.sqrt_two_inv_mul_self
  unfold magicW; rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, hraw]
  simp only [smul_smul, ← mul_assoc, hr]; norm_num
private lemma magicW_cogram : magicW * magicW.conjTranspose = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm).mp magicW_gram
private lemma magicRaw_real_congruence (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.IsHermitian) (hL : partialTraceLeft ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (hR : partialTraceRight ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) : ∀ i j : Fin 4, ((magicRaw.conjTranspose * ρ * magicRaw) i j).im = 0 := by
  have hH00im := congrArg Complex.im (hρ.apply (0,0) (0,0))
  have hH01re := congrArg Complex.re (hρ.apply (0,0) (0,1))
  have hH01im := congrArg Complex.im (hρ.apply (0,0) (0,1))
  have hH02re := congrArg Complex.re (hρ.apply (0,0) (1,0))
  have hH02im := congrArg Complex.im (hρ.apply (0,0) (1,0))
  have hH03re := congrArg Complex.re (hρ.apply (0,0) (1,1))
  have hH03im := congrArg Complex.im (hρ.apply (0,0) (1,1))
  have hH10re := congrArg Complex.re (hρ.apply (0,1) (0,0))
  have hH10im := congrArg Complex.im (hρ.apply (0,1) (0,0))
  have hH11im := congrArg Complex.im (hρ.apply (0,1) (0,1))
  have hH12re := congrArg Complex.re (hρ.apply (0,1) (1,0))
  have hH12im := congrArg Complex.im (hρ.apply (0,1) (1,0))
  have hH13re := congrArg Complex.re (hρ.apply (0,1) (1,1))
  have hH13im := congrArg Complex.im (hρ.apply (0,1) (1,1))
  have hH20re := congrArg Complex.re (hρ.apply (1,0) (0,0))
  have hH20im := congrArg Complex.im (hρ.apply (1,0) (0,0))
  have hH21re := congrArg Complex.re (hρ.apply (1,0) (0,1))
  have hH21im := congrArg Complex.im (hρ.apply (1,0) (0,1))
  have hH22im := congrArg Complex.im (hρ.apply (1,0) (1,0))
  have hH23re := congrArg Complex.re (hρ.apply (1,0) (1,1))
  have hH23im := congrArg Complex.im (hρ.apply (1,0) (1,1))
  have hH30re := congrArg Complex.re (hρ.apply (1,1) (0,0))
  have hH30im := congrArg Complex.im (hρ.apply (1,1) (0,0))
  have hH31re := congrArg Complex.re (hρ.apply (1,1) (0,1))
  have hH31im := congrArg Complex.im (hρ.apply (1,1) (0,1))
  have hH32re := congrArg Complex.re (hρ.apply (1,1) (1,0))
  have hH32im := congrArg Complex.im (hρ.apply (1,1) (1,0))
  have hH33im := congrArg Complex.im (hρ.apply (1,1) (1,1))
  have hL00 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 0 0) hL
  simp only [partialTraceLeft, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hL00
  have hL00re := congrArg Complex.re hL00
  have hL00im := congrArg Complex.im hL00
  have hL01 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 0 1) hL
  simp only [partialTraceLeft, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hL01
  have hL01re := congrArg Complex.re hL01
  have hL01im := congrArg Complex.im hL01
  have hL10 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 1 0) hL
  simp only [partialTraceLeft, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hL10
  have hL10re := congrArg Complex.re hL10
  have hL10im := congrArg Complex.im hL10
  have hL11 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 1 1) hL
  simp only [partialTraceLeft, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hL11
  have hL11re := congrArg Complex.re hL11
  have hL11im := congrArg Complex.im hL11
  have hR00 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 0 0) hR
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hR00
  have hR00re := congrArg Complex.re hR00
  have hR00im := congrArg Complex.im hR00
  have hR01 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 0 1) hR
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hR01
  have hR01re := congrArg Complex.re hR01
  have hR01im := congrArg Complex.im hR01
  have hR10 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 1 0) hR
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hR10
  have hR10re := congrArg Complex.re hR10
  have hR10im := congrArg Complex.im hR10
  have hR11 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) ℂ => Z 1 1) hR
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at hR11
  have hR11re := congrArg Complex.re hR11
  have hR11im := congrArg Complex.im hR11
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [magicRaw, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.star_def] at * <;> linarith
private lemma magicW_real_congruence (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.IsHermitian) (hL : partialTraceLeft ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (hR : partialTraceRight ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) : ∀ i j : Fin 4, ((magicW.conjTranspose * ρ * magicW) i j).im = 0 := by
  intro i j
  unfold magicW; simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    magicRaw_real_congruence ρ hρ hL hR, mul_zero]
private lemma real_cast_adjoint {n m : Type*} (A : Matrix n m ℝ) : (A.map Complex.ofReal).conjTranspose = A.conjTranspose.map Complex.ofReal := by
  exact (Matrix.conjTranspose_map Complex.ofReal (by intro x; simp)).symm
private lemma real_cast_mul {n m k : Type*} [Fintype m] (A : Matrix n m ℝ) (B : Matrix m k ℝ) : (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
  exact Matrix.map_mul (f := Complex.ofRealHom)
private lemma real_cast_unitary {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix.unitaryGroup n ℝ) : (O.val.map Complex.ofReal).conjTranspose * O.val.map Complex.ofReal = 1 ∧ O.val.map Complex.ofReal * (O.val.map Complex.ofReal).conjTranspose = 1 := by
  constructor
  · rw [real_cast_adjoint, ← real_cast_mul]
    have hO : O.val.conjTranspose * O.val = 1 := Matrix.mem_unitaryGroup_iff'.mp O.property
    rw [hO]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij, RCLike.ofReal_eq_complex_ofReal]
  · rw [real_cast_adjoint, ← real_cast_mul]
    have hO : O.val * O.val.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
    rw [hO]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij, RCLike.ofReal_eq_complex_ofReal]
private lemma real_spectral_basis {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (hreal : ∀ i j, (A i j).im = 0) : ∃ (O : Matrix.unitaryGroup n ℝ) (lam : n → ℝ), (O.val.map Complex.ofReal).conjTranspose * A * O.val.map Complex.ofReal = Matrix.diagonal (fun i => (lam i : ℂ)) := by
  let R : Matrix n n ℝ := A.map Complex.re
  have hR : R.IsHermitian := hA.map Complex.re (congrFun rfl)
  let O := hR.eigenvectorUnitary
  refine ⟨O, hR.eigenvalues, ?_⟩
  have hdiag : O.val.conjTranspose * R * O.val =
      Matrix.diagonal hR.eigenvalues := by
    simpa only [O, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hR.conjStarAlgAut_star_eigenvectorUnitary
  have hcast : R.map Complex.ofReal = A := by
    ext i j; apply Complex.ext
    · rfl
    · simp [hreal]
  have hh := congrArg (Matrix.map · Complex.ofReal) hdiag
  simpa only [real_cast_mul, ← real_cast_adjoint, hcast,
    Matrix.diagonal_map Complex.ofReal_zero] using hh
section
private def sign (s : ((Bool × Bool) × (Bool × Bool))) : Fin 4 → ℂ :=
  ![if s.1.1 then 1 else -1, if s.1.2 then 1 else -1,
    if s.2.1 then 1 else -1, if s.2.2 then 1 else -1]
variable {Y : Type*} [Fintype Y] [DecidableEq Y]
private def signConjugate (F : Matrix Y (Fin 4) ℂ) (s : ((Bool × Bool) × (Bool × Bool))) :=
  F * (Matrix.diagonal (sign s)) * F.conjTranspose
private def pinch (F : Matrix Y (Fin 4) ℂ) (M : Matrix Y Y ℂ) :=
  F * Matrix.diagonal (fun i => (F.conjTranspose * M * F) i i) * F.conjTranspose
private def signReal (s : ((Bool × Bool) × (Bool × Bool))) : Fin 4 → ℝ :=
  ![if s.1.1 then 1 else -1, if s.1.2 then 1 else -1,
    if s.2.1 then 1 else -1, if s.2.2 then 1 else -1]
private lemma signReal_cast (s : ((Bool × Bool) × (Bool × Bool))) (i : Fin 4) : (signReal s i : ℂ) = sign s i := by
  fin_cases i <;> simp [signReal,sign] <;> split_ifs <;> norm_num
private lemma sign_star (s : ((Bool × Bool) × (Bool × Bool))) (i : Fin 4) : star (sign s i) = sign s i := by
  rw [← signReal_cast s i]
  exact RCLike.conj_ofReal (signReal s i)
private def signEquiv : ((Bool × Bool) × (Bool × Bool)) ≃ (Fin 4 → Bool) where
  toFun s := ![!s.1.1, !s.1.2, !s.2.1, !s.2.2]
  invFun f := ((!f 0, !f 1), (!f 2, !f 3))
  left_inv s := by
    rcases s with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp
  right_inv f := by funext i; fin_cases i <;> simp
private lemma signDiagonal_unitary (s : ((Bool × Bool) × (Bool × Bool))) : ((Matrix.diagonal (sign s))).conjTranspose * (Matrix.diagonal (sign s)) = 1 := by
  have hbool (b : Bool) : (if b = false then (-1 : ℂ) else 1) = if b = true then 1 else -1 := by
    cases b <;> norm_num
  let e : (Fin 4 × Unit) ≃ Fin 4 := Equiv.prodUnique (α := Fin 4) (β := Unit)
  let f : Fin 4 → Bool := signEquiv s
  let V : Matrix (Fin 4 × Unit) (Fin 4 × Unit) ℂ :=
    D5.S3.Quantum.Subentropy.PinchingGap.signUnitary (B := Unit) f
  let U : Matrix (Fin 4) (Fin 4) ℂ := Matrix.reindex e e V
  have hV := D5.S3.Quantum.Subentropy.PinchingGap.sign_unitary (X := Fin 4) (B := Unit) f
  have hU : U.conjTranspose * U = 1 := by
    calc
      U.conjTranspose * U = Matrix.reindex e e V.conjTranspose * Matrix.reindex e e V := by
        rw [Matrix.conjTranspose_reindex]
      _ = Matrix.reindex e e (V.conjTranspose * V) := by
        exact Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ) e e e V.conjTranspose V
      _ = Matrix.reindex e e 1 := by rw [hV.1]
      _ = 1 := by exact Matrix.reindexLinearEquiv_one ℂ ℂ e
  have hdiag : U = Matrix.diagonal (sign s) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, e, f, signEquiv, sign, Matrix.reindex_apply, Matrix.diagonal_apply,
        D5.S3.Quantum.Subentropy.PinchingGap.blockSign,
        D5.S3.Quantum.Subentropy.PinchingGap.signUnitary,
        Equiv.prodUnique_apply, Equiv.prodUnique_symm_apply, hbool]
  rw [← hdiag]
  exact hU
private lemma sign_sq (s : ((Bool × Bool) × (Bool × Bool))) (i : Fin 4) : sign s i * sign s i = 1 := by
  simpa only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Pi.mul_apply, Pi.star_apply, sign_star, Matrix.one_apply_eq] using congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i i) (signDiagonal_unitary s)
private lemma diagonal_twirl (M : Matrix (Fin 4) (Fin 4) ℂ) : (1/16 : ℝ) • (∑ s : ((Bool × Bool) × (Bool × Bool)), (Matrix.diagonal (sign s)) * M * ((Matrix.diagonal (sign s))).conjTranspose) = Matrix.diagonal (fun i => M i i) := by
  have hbool (b : Bool) : (if b = false then (-1 : ℂ) else 1) = if b = true then 1 else -1 := by
    cases b <;> norm_num
  let e : (Fin 4 × Unit) ≃ Fin 4 := Equiv.prodUnique (α := Fin 4) (β := Unit)
  let A : Matrix (Fin 4 × Unit) (Fin 4 × Unit) ℂ := Matrix.reindex e.symm e.symm M
  have h := D5.S3.Quantum.Subentropy.PinchingGap.signTwirl_eq_blockPinch (X := Fin 4) (B := Unit) A
  ext i j
  have hij := congrArg (fun K => K (e.symm i) (e.symm j)) h
  simp only [D5.S3.Quantum.Subentropy.PinchingGap.signTwirl,
    D5.S3.Quantum.Subentropy.ClassicalQuantumGram.blockPinch,
    D5.S3.Quantum.Subentropy.PinchingGap.signUnitary,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at hij
  rw [← Equiv.sum_comp (signEquiv)] at hij
  have hsign (s : (Bool × Bool) × (Bool × Bool)) (k : Fin 4) : D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k = sign s k := by
    fin_cases k <;> simp [signEquiv, sign,
      D5.S3.Quantum.Subentropy.PinchingGap.blockSign, hbool]
  have hdiag_s (s : (Bool × Bool) × (Bool × Bool)) : Matrix.diagonal (fun k : Fin 4 × Unit => D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k.1) = (Matrix.diagonal (sign s)).submatrix e e := by
    simpa only [Matrix.submatrix_diagonal_equiv, Function.comp_def, e,
      Equiv.prodUnique_apply, hsign]
  have hprod (s : (Bool × Bool) × (Bool × Bool)) : Matrix.diagonal (fun k : Fin 4 × Unit => D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k.1) * A * (Matrix.diagonal (fun k : Fin 4 × Unit => D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k.1)).conjTranspose = ((Matrix.diagonal (sign s)) * M * (Matrix.diagonal (sign s)).conjTranspose).submatrix e e := by
    change Matrix.diagonal (fun k : Fin 4 × Unit => D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k.1) * M.submatrix e e * (Matrix.diagonal (fun k : Fin 4 × Unit => D5.S3.Quantum.Subentropy.PinchingGap.blockSign (signEquiv s) k.1)).conjTranspose = _
    rw [hdiag_s, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp_rw [hprod] at hij
  simp [A, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.reindex_apply, e] at hij
  have hentry : (if i = j then M i j else 0) = (if i = j then M i i else 0) := by by_cases h_ij : i = j <;> simp [h_ij]
  rw [hentry] at hij
  simpa [signEquiv, sign, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.conjTranspose_apply,
    Pi.star_apply, e, A, D5.S3.Quantum.Subentropy.PinchingGap.blockSign,
    D5.S3.Quantum.Subentropy.PinchingGap.signUnitary,
    RCLike.real_smul_eq_coe_mul, Matrix.submatrix_apply] using hij
private lemma signConjugate_unitary (F : Matrix Y (Fin 4) ℂ) (s : ((Bool × Bool) × (Bool × Bool))) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) : (signConjugate F s).conjTranspose * signConjugate F s = 1 := by
  simp only [signConjugate, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.conjTranspose, hF]; simp only [Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((Matrix.diagonal (sign s))).conjTranspose, signDiagonal_unitary]; simpa only [Matrix.one_mul] using hF'
private lemma basis_twirl (F : Matrix Y (Fin 4) ℂ) (M : Matrix Y Y ℂ) : (1/16 : ℝ) • (∑ s : ((Bool × Bool) × (Bool × Bool)), signConjugate F s * M * (signConjugate F s).conjTranspose) = pinch F M := by
  have hterm (s : ((Bool × Bool) × (Bool × Bool))) :
      signConjugate F s * M * (signConjugate F s).conjTranspose =
      F * ((Matrix.diagonal (sign s)) * (F.conjTranspose * M * F) * ((Matrix.diagonal (sign s))).conjTranspose) *
        F.conjTranspose := by
    simp only [signConjugate, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp_rw [hterm]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.smul_mul, ← Matrix.mul_smul]; rw [diagonal_twirl]
  rfl
private lemma symmetry_pinching_feasible {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix (X × Y) (X × Y) ℂ) (M : Matrix Y Y ℂ) (F : Matrix Y (Fin 4) ℂ) (P : ((Bool × Bool) × (Bool × Bool)) → Matrix.unitaryGroup X ℂ) (hsym : ∀ s : ((Bool × Bool) × (Bool × Bool)), ((P s).val ⊗ₖ signConjugate F s) * ρ * ((P s).val ⊗ₖ signConjugate F s).conjTranspose = ρ) (hρ : ρ ≤ (1 : Matrix X X ℂ) ⊗ₖ M) : ρ ≤ (1 : Matrix X X ℂ) ⊗ₖ pinch F M := by
  classical
  have hi (s : ((Bool × Bool) × (Bool × Bool))) : ρ ≤ (1 : Matrix X X ℂ) ⊗ₖ
      (signConjugate F s * M * (signConjugate F s).conjTranspose) := by
    have hc := (Matrix.le_iff.mp hρ).mul_mul_conjTranspose_same
      ((P s).val ⊗ₖ signConjugate F s)
    have hp : (P s).val * (P s).val.conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (P s).property
    rw [Matrix.mul_sub, Matrix.sub_mul, hsym] at hc
    have hr : ((P s).val ⊗ₖ signConjugate F s) * ((1 : Matrix X X ℂ) ⊗ₖ M) *
        ((P s).val ⊗ₖ signConjugate F s).conjTranspose =
        (1 : Matrix X X ℂ) ⊗ₖ
          (signConjugate F s * M * (signConjugate F s).conjTranspose) := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one, hp]
    rw [hr] at hc; exact Matrix.le_iff.mpr hc
  have hsum : (∑ s : ((Bool × Bool) × (Bool × Bool)), (1 : Matrix X X ℂ) ⊗ₖ
      (signConjugate F s * M * (signConjugate F s).conjTranspose)) =
      (1 : Matrix X X ℂ) ⊗ₖ
        (∑ s : ((Bool × Bool) × (Bool × Bool)), signConjugate F s * M * (signConjugate F s).conjTranspose) := by
    ext i j; simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hi s)
  have havg := smul_le_smul_of_nonneg_left hsumle (by norm_num : (0 : ℝ) ≤ 1/16)
  rw [hsum, ← Matrix.kronecker_smul, basis_twirl] at havg
  have hleft : (1/16 : ℝ) • (∑ _s : ((Bool × Bool) × (Bool × Bool)), ρ) = ρ := by
    rw [Finset.sum_const, Finset.card_univ]
    change (1/16 : ℝ) • ((16 : ℕ) • ρ) = ρ
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; norm_num
  rw [hleft] at havg; exact havg
end
section
variable {X Y I : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype I] [DecidableEq I]
private lemma vectorRows_kronecker_action (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (u : X × Y → ℂ) : Matrix.of (Function.curry ((P ⊗ₖ Q) *ᵥ u)) = P * (Matrix.of (Function.curry u)) * Q.transpose := by
  calc
    _ = (Q * (Matrix.of (Function.curry u)).transpose * P.transpose).transpose :=
      congrArg (fun v : X × Y → ℂ => Matrix.of (Function.curry v))
        (Matrix.kronecker_mulVec_vec Q (Matrix.of (Function.curry u)).transpose P)
    _ = _ := by simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
private lemma vectorRows_gram (u : X × Y → ℂ) : ((Matrix.of (Function.curry u))).conjTranspose * (Matrix.of (Function.curry u)) = (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft (Matrix.vecMulVec u (star u))).map star := by
  ext y z; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Function.curry,
    Matrix.map_apply, D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
    Matrix.vecMulVec_apply, Pi.star_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro x _; ring
private lemma sign_tensor_invariant (u : X × Y → ℂ) (F : Matrix Y I ℂ) (P : Matrix X X ℂ) (s : I → ℂ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hs : ∀ i, s i * s i = 1) (hP : P * ((Matrix.of (Function.curry u)) * F.map star) = ((Matrix.of (Function.curry u)) * F.map star) * Matrix.diagonal s) : (P ⊗ₖ (F * Matrix.diagonal s * F.conjTranspose)) *ᵥ u = u := by
  have hFF : F.transpose * F.map star = 1 := by
    have hh := congrArg Matrix.transpose hF
    simpa only [Matrix.transpose_mul, Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose, Matrix.transpose_one]
      using hh
  have hFF' : F.map star * F.transpose = 1 := by
    have hh := congrArg Matrix.transpose hF'
    simpa only [Matrix.transpose_mul, Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose, Matrix.transpose_one]
      using hh
  have hD : Matrix.diagonal s * Matrix.diagonal s = (1 : Matrix I I ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply, hs]
  apply Function.curry_injective
  change Matrix.of (Function.curry ((P ⊗ₖ (F * Matrix.diagonal s * F.conjTranspose)) *ᵥ u)) =
    Matrix.of (Function.curry u)
  rw [vectorRows_kronecker_action]
  have hrec : (Matrix.of (Function.curry u)) = ((Matrix.of (Function.curry u)) * F.map star) * F.transpose := by
    rw [Matrix.mul_assoc, hFF', Matrix.mul_one]
  calc
    _ = P * (Matrix.of (Function.curry u)) * (F.map star * Matrix.diagonal s * F.transpose) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose,
        Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = P * (((Matrix.of (Function.curry u)) * F.map star) * F.transpose) *
        (F.map star * Matrix.diagonal s * F.transpose) := by rw [← hrec]
    _ = (P * ((Matrix.of (Function.curry u)) * F.map star)) *
        (F.transpose * F.map star) * Matrix.diagonal s * F.transpose := by
      simp only [Matrix.mul_assoc]
    _ = ((Matrix.of (Function.curry u)) * F.map star) * (Matrix.diagonal s * Matrix.diagonal s) *
        F.transpose := by rw [hP,hFF]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (Matrix.of (Function.curry u)) := by rw [hD, Matrix.mul_one, ← hrec]
private lemma noisy_rankOne_invariant (u : X → ℂ) (K : Matrix.unitaryGroup X ℂ) (a b : ℝ) (hu : K.val *ᵥ u = u) : K.val * (a • (1 : Matrix X X ℂ) + b • Matrix.vecMulVec u (star u)) * K.val.conjTranspose = a • 1 + b • Matrix.vecMulVec u (star u) := by
  have hK : K.val * K.val.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp K.property
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hK]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star, hu]
end
section
variable {d : ℕ}
private def unitaryChoiVector (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : ((Fin d × Fin d) × (Fin 2 × Fin 2)) → ℂ :=
  Matrix.vec (U : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) ∘
    Equiv.prodProdProdComm (Fin d) (Fin d) (Fin 2) (Fin 2)
private lemma choiN_unitary (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : choiN (noisyUnitary U 0) = Matrix.vecMulVec (unitaryChoiVector U) (star (unitaryChoiVector U)) := by
  ext x y; simp [choiN, noisyUnitary, Matrix.mul_apply, Matrix.single, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, unitaryChoiVector, Matrix.vecMulVec_apply,
    ite_and, Finset.mul_sum, Finset.sum_mul]
private lemma choiN_replacement : choiN (fun Z : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ => Z.trace • (((d*2 : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ))) = (((d*2 : ℕ) : ℂ)⁻¹ • (1 : Matrix ((Fin d × Fin d) × (Fin 2 × Fin 2)) ((Fin d × Fin d) × (Fin 2 × Fin 2)) ℂ)) := by
  ext ⟨⟨r,a⟩,⟨s,b⟩⟩ ⟨⟨t,c⟩,⟨v,e⟩⟩; simp only [choiN, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  have ht : (Matrix.single (r,s) (t,v) (1 : ℂ)).trace =
      if (r,s) = (t,v) then 1 else 0 := by
    simp [Matrix.trace, Matrix.single, Matrix.diag_apply, ite_and, eq_comm]
  rw [ht]
  by_cases hrt : r = t <;> by_cases hst : s = v <;>
    by_cases hac : a = c <;> by_cases hbe : b = e <;>
      simp [Prod.mk.injEq, hrt, hst, hac, hbe]
private lemma choiN_noisy (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (p : ℝ) : choiN (noisyUnitary U p) = p • (((d*2 : ℕ) : ℂ)⁻¹ • (1 : Matrix ((Fin d × Fin d) × (Fin 2 × Fin 2)) ((Fin d × Fin d) × (Fin 2 × Fin 2)) ℂ)) + (1-p) • Matrix.vecMulVec (unitaryChoiVector U) (star (unitaryChoiVector U)) := by
  have he : choiN (noisyUnitary U p) =
      p • choiN (fun Z : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ =>
        Z.trace • (((d*2 : ℕ) : ℂ)⁻¹ • (1 : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ))) +
      (1-p) • choiN (noisyUnitary U 0) := by
    ext x y; simp only [choiN, noisyUnitary, Matrix.add_apply, Matrix.smul_apply,
      zero_smul, sub_zero, one_smul, Matrix.zero_apply, zero_add]
  rw [he, choiN_replacement, choiN_unitary]
private lemma choiN_eq_dimension_smul_choiState (N : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ → Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) (hd : 1 ≤ d) : choiN N = (((d*2 : ℕ) : ℝ)) • choiState N := by
  unfold choiState; rw [smul_smul, mul_inv_cancel₀]
  · exact (one_smul ℝ _).symm
  · exact_mod_cast (Nat.mul_ne_zero (by omega : d ≠ 0) (by decide : 2 ≠ 0))
end
section
variable {d : ℕ}
private def reducedUnitary (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  partialTraceLeft (Matrix.vecMulVec (unitaryChoiVector U) (star (unitaryChoiVector U)))
private lemma unitary_row_inner (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (x y : Fin d × Fin 2) : (∑ z : Fin d × Fin 2, U x z * star (U y z)) = if x = y then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ => M x y)
    (Matrix.mem_unitaryGroup_iff.mp U.property)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
private lemma unitary_column_inner (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (x y : Fin d × Fin 2) : (∑ z : Fin d × Fin 2, U z x * star (U z y)) = if x = y then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ => M y x)
    (Matrix.mem_unitaryGroup_iff'.mp U.property)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_comm, eq_comm] using h
private lemma reducedUnitary_left (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : partialTraceLeft (reducedUnitary U) = (d : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext b c
  change (∑ s : Fin 2, ∑ x : Fin d × Fin d,
    U (x.2,b) (x.1,s) * star (U (x.2,c) (x.1,s))) = _
  simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm]
  have he : (∑ r : Fin d, ∑ s : Fin 2, ∑ a : Fin d,
      U (a,b) (r,s) * star (U (a,c) (r,s))) =
      ∑ a : Fin d, ∑ z : Fin d × Fin 2, U (a,b) z * star (U (a,c) z) := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ r : Fin d, ∑ a : Fin d, ∑ s : Fin 2,
          U (a,b) (r,s) * star (U (a,c) (r,s)) := by
        apply Finset.sum_congr rfl
        intro r _; rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [he]
  simp_rw [unitary_row_inner]
  by_cases hbc : b = c
  · subst c
    simp
  · simp [hbc, Prod.mk.injEq, Matrix.one_apply_ne hbc]
private lemma reducedUnitary_right (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : partialTraceRight (reducedUnitary U) = (d : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext s t
  change (∑ b : Fin 2, ∑ x : Fin d × Fin d,
    U (x.2,b) (x.1,s) * star (U (x.2,b) (x.1,t))) = _
  simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm]
  have he (r : Fin d) : (∑ b : Fin 2, ∑ a : Fin d,
      U (a,b) (r,s) * star (U (a,b) (r,t))) =
      ∑ z : Fin d × Fin 2, U z (r,s) * star (U z (r,t)) := by
    exact (Fintype.sum_prod_type_right
      (fun z : Fin d × Fin 2 => U z (r,s) * star (U z (r,t)))).symm
  simp_rw [he, unitary_column_inner]
  by_cases hst : s = t
  · subst t
    simp
  · simp [hst, Prod.mk.injEq, Matrix.one_apply_ne hst]
private lemma reducedUnitary_posSemidef (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : (reducedUnitary U).PosSemidef :=
  partialTraceLeft_posSemidef (Matrix.posSemidef_vecMulVec_self_star _)
private lemma normalizedReduced_marginals (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (hd : 1 ≤ d) : partialTraceLeft ((((d*2 : ℕ) : ℂ)⁻¹) • reducedUnitary U) = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ partialTraceRight ((((d*2 : ℕ) : ℂ)⁻¹) • reducedUnitary U) = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hL : ∀ (a : ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      partialTraceLeft (a • M) = a • partialTraceLeft M := by
    intros a M
    exact D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul
      a (M.submatrix Prod.swap Prod.swap)
  have hR : ∀ (a : ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      partialTraceRight (a • M) = a • partialTraceRight M := by
    exact D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul
  constructor
  · rw [hL, reducedUnitary_left, smul_smul]
    congr 1
    push_cast; field_simp
  · rw [hR, reducedUnitary_right, smul_smul]
    congr 1
    push_cast; field_simp
end
private lemma Dmax_eq_iInf_cost {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) (a : ℝ) (ha : 0 < a) (hlower : ∀ t : ℝ, 0 ≤ t → ρ ≤ t • σ → a ≤ t) : Dmax ρ σ = ⨅ (t : ℝ) (_ : 0 ≤ t ∧ ρ ≤ t • σ), ((Real.logb 2 t : ℝ) : EReal) := by
  classical
  let S : Set ℝ := {t | 0 ≤ t ∧ ρ ≤ t • σ}
  let L : ℝ → EReal := fun t => ((Real.logb 2 t : ℝ) : EReal)
  have hi : sInf (L '' S) = ⨅ (t : ℝ) (_ : 0 ≤ t ∧ ρ ≤ t • σ), L t := by
    rw [sInf_image]
    rfl
  by_cases h : ∃ t : ℝ, 0 ≤ t ∧ ρ ≤ t • σ
  · have hS : S.Nonempty := h
    have hb : BddBelow S := ⟨a, fun t ht => hlower t ht.1 ht.2⟩
    have hq : 0 < sInf S := lt_of_lt_of_le ha
      (le_csInf hS (fun t ht => hlower t ht.1 ht.2))
    have hc : ContinuousWithinAt L S (sInf S) :=
      (continuous_coe_real_ereal.continuousAt.comp
        (Real.continuousAt_logb hq.ne')).continuousWithinAt
    have hm : MonotoneOn L S := by
      intro x hx y hy hxy; exact EReal.coe_le_coe_iff.mpr
        ((Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).monotoneOn
          (lt_of_lt_of_le ha (hlower x hx.1 hx.2))
          (lt_of_lt_of_le ha (hlower y hy.1 hy.2)) hxy)
    have hmap := MonotoneOn.map_csInf_of_continuousWithinAt hc hm hS hb
    rw [hi] at hmap; simpa only [Dmax, if_pos h, S, L] using hmap
  · have hS : S = ∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp h
    have hinf : (⨅ (t : ℝ) (_ : 0 ≤ t ∧ ρ ≤ t • σ), L t) = ⊤ := by
      rw [← hi, hS, Set.image_empty, sInf_empty]
    simpa only [Dmax, if_neg h, L, hinf]
private lemma Dmax_smul_both {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) (c : ℝ) (hc : 0 < c) : Dmax (c • ρ) (c • σ) = Dmax ρ σ := by
  classical
  have he (t : ℝ) : c • ρ ≤ t • (c • σ) ↔ ρ ≤ t • σ := by
    rw [smul_comm t c σ]; exact smul_le_smul_iff_of_pos_left hc
  simp only [Dmax, he]
private lemma feasible_trace_lower {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] (ρ : Matrix (X × Y) (X × Y) ℂ) (htrace : ρ.trace = 1) (M : Matrix Y Y ℂ) (hfeas : ρ ≤ (1 : Matrix X X ℂ) ⊗ₖ M) : (Fintype.card X : ℝ)⁻¹ ≤ M.trace.re := by
  have ht := (Matrix.tracePositiveLinearMap (X × Y) ℂ ℂ).monotone hfeas
  have ht' := RCLike.re_le_re ht
  change ρ.trace.re ≤ ((1 : Matrix X X ℂ) ⊗ₖ M).trace.re at ht'
  rw [htrace, Matrix.trace_kronecker] at ht'
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hbound : 1 ≤ (Fintype.card X : ℝ) * M.trace.re := by
    simpa using ht'
  rw [inv_eq_one_div]; exact (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hbound)
private lemma Dmax_smul_left {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (hlower : ∀ t : ℝ, 0 ≤ t → ρ ≤ t • σ → a ≤ t) : Dmax (c • ρ) σ = Dmax ρ σ + ((Real.logb 2 c : ℝ) : EReal) := by
  classical
  let S : Set ℝ := {t | 0 ≤ t ∧ ρ ≤ t • σ}
  let T : Set ℝ := {t | 0 ≤ t ∧ c • ρ ≤ t • σ}
  have hsets : T = (fun t : ℝ => c*t) '' S := by
    ext t
    constructor
    · intro ht
      refine ⟨t / c, ⟨div_nonneg ht.1 hc.le, ?_⟩, ?_⟩
      · apply (smul_le_smul_iff_of_pos_left hc).mp
        have hdiv : c * (t/c) = t := by field_simp
        simpa only [smul_smul, hdiv] using ht.2
      · field_simp
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mul_nonneg hc.le hx.1, ?_⟩
      simpa only [smul_smul] using smul_le_smul_of_nonneg_left hx.2 hc.le
  by_cases h : S.Nonempty
  · have hT : T.Nonempty := by rw [hsets]; exact h.image _
    have hb : BddBelow S := ⟨a, fun t ht => hlower t ht.1 ht.2⟩
    have hq : 0 < sInf S := lt_of_lt_of_le ha
      (le_csInf h (fun t ht => hlower t ht.1 ht.2))
    have hg := (isGLB_csInf h hb).mul_left hc.le
    have h_inf : sInf T = c * sInf S := by
      rw [hsets]; exact hg.csInf_eq (h.image _)
    have hs : (∃ t : ℝ, 0 ≤ t ∧ ρ ≤ t • σ) := h
    have ht : (∃ t : ℝ, 0 ≤ t ∧ c • ρ ≤ t • σ) := hT
    change (if _ then _ else _) = (if _ then _ else _) + _
    rw [if_pos ht, if_pos hs]
    change ((Real.logb 2 (sInf T) : ℝ) : EReal) = _
    rw [h_inf, Real.logb_mul hc.ne' hq.ne', EReal.coe_add]; exact add_comm _ _
  · have hT : ¬ T.Nonempty := by rw [hsets, Set.image_nonempty]; exact h
    have hs : ¬ ∃ t : ℝ, 0 ≤ t ∧ ρ ≤ t • σ := h
    have ht : ¬ ∃ t : ℝ, 0 ≤ t ∧ c • ρ ≤ t • σ := hT
    simp only [Dmax, if_neg hs, if_neg ht, EReal.top_add_coe]
private lemma Dmax_le_of_cost_imp {n : Type*} [Fintype n] [DecidableEq n] (ρ σ τ : Matrix n n ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hσ : ∀ t : ℝ, 0 ≤ t → ρ ≤ t • σ → a ≤ t) (hτ : ∀ t : ℝ, 0 ≤ t → ρ ≤ t • τ → b ≤ t) (hcost : ∀ t : ℝ, 0 ≤ t → ρ ≤ t • σ → ρ ≤ t • τ) : Dmax ρ τ ≤ Dmax ρ σ := by
  rw [Dmax_eq_iInf_cost ρ σ a ha hσ, Dmax_eq_iInf_cost ρ τ b hb hτ]
  refine le_iInf fun t => le_iInf fun ht => ?_
  exact iInf_le_of_le t (iInf_le_of_le ⟨ht.1, hcost t ht.1 ht.2⟩ le_rfl)
private lemma choiQ_posSemidef (Q : QuantumChannel (Fin 2) (Fin 2)) : (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)).PosSemidef := by
  let W : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (Matrix.single i j 1))
  have he : CStarMatrix.ofMatrix.symm (flattenCStar 2 W) =
      Matrix.vecMulVec (fun x : Fin 2 × Fin 2 => if x.1 = x.2 then (1 : ℂ) else 0)
        (star (fun x : Fin 2 × Fin 2 => if x.1 = x.2 then (1 : ℂ) else 0)) := by
    ext ⟨i,r⟩ ⟨j,s⟩; simp [W, flattenCStar, Matrix.single, Matrix.vecMulVec, eq_comm]
    split_ifs <;> simp_all
  have hflat : 0 ≤ flattenCStar 2 W := by
    have hp : 0 ≤ CStarMatrix.ofMatrix.symm (flattenCStar 2 W) := by
      rw [he]; exact (Matrix.posSemidef_vecMulVec_self_star _).nonneg
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp
  have hW : 0 ≤ W := by
    simpa using map_nonneg (flattenCStar (a := Fin 2) 2).symm hflat
  have hQ := Q.toCompletelyPositiveMap.map_cstarMatrix_nonneg W hW
  have hp := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
    (map_nonneg (flattenCStar (a := Fin 2) 2) hQ)
  exact (Matrix.nonneg_iff_posSemidef.mp hp).submatrix Prod.swap
private lemma choiQ_trace (Q : QuantumChannel (Fin 2) (Fin 2)) : ((inputFirstChoi (matrixAction Q.toCompletelyPositiveMap))).trace = 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, inputFirstChoi, matrixAction, PhyslibLeaf.MatrixMap.choi_matrix]
  change (∑ i : Fin 2, Matrix.trace
    (Q.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i i (1 : ℂ))))) = 2
  simp_rw [Q.trace_preserving]
  change (∑ i : Fin 2, ∑ j : Fin 2, (Matrix.single i i (1 : ℂ)) j j) = 2
  norm_num [Matrix.single, Fin.sum_univ_succ]
private lemma choiQ_half_state (Q : QuantumChannel (Fin 2) (Fin 2)) : ∃ σ : DensityState (Fin 2 × Fin 2), CStarMatrix.ofMatrix.symm σ.val = (1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)) := by
  refine ⟨⟨CStarMatrix.ofMatrix ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap))), ?_, ?_⟩, rfl⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((choiQ_posSemidef Q).smul (by norm_num : (0 : ℝ) ≤ 1/2)).nonneg
  · change Matrix.trace ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap))) = 1
    rw [Matrix.trace_smul, choiQ_trace]; norm_num
private lemma mixed_unitary_choi {κ : Type*} [Fintype κ] (V : κ → Matrix.unitaryGroup (Fin 2) ℂ) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : ∃ Q : QuantumChannel (Fin 2) (Fin 2), (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)) = ∑ i, w i • Matrix.vecMulVec (fun x : Fin 2 × Fin 2 => V i x.2 x.1) (fun x : Fin 2 × Fin 2 => star (V i x.2 x.1)) := by
  classical
  let K : κ → Matrix (Fin 2) (Fin 2) ℂ := fun i => Real.sqrt (w i) • (V i).val
  have hKi (i : κ) : (K i).conjTranspose * K i = w i • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp [K]
    have hv : (V i).val.conjTranspose * (V i).val = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (V i).property
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, hv]; simp only [smul_smul, ← pow_two, Real.sq_sqrt (hw i)]
  have hK : (∑ i, (K i).conjTranspose * K i) = 1 := by
    simp_rw [hKi]
    rw [← Finset.sum_smul, hs, one_smul]
  obtain ⟨Q, hQ⟩ := finite_kraus_quantum_channel K hK
  refine ⟨Q, ?_⟩
  have hEq : inputFirstChoi (matrixAction Q.toCompletelyPositiveMap) =
      ∑ i, Matrix.vecMulVec (fun x : Fin 2 × Fin 2 => K i x.2 x.1)
        (fun x : Fin 2 × Fin 2 => star (K i x.2 x.1)) := by
    ext x y
    change CStarMatrix.ofMatrix.symm
      (Q.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single x.1 y.1 1))) x.2 y.2 = _
    rw [hQ]; simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single, Matrix.vecMulVec,
      Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, ite_and]
  rw [hEq]
  have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  ext x y; simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.smul_apply, K, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
    star_mul, hstar, Prod.swap]
  apply Finset.sum_congr rfl
  intro i _
  have hroot : (Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ) = (w i : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hw i)
  calc
    _ = ((Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ)) *
      (V i x.2 x.1 * star (V i y.2 y.1)) := by ring
    _ = _ := by rw [hroot]
private lemma magicW_vector_coeff (v : Fin 4 → ℝ) : (fun a b : Fin 2 => (magicW *ᵥ (fun i => (v i : ℂ))) (a,b)) = magicCoeff v := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [magicW, magicRaw, magicCoeff, quaternionCoeff, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Complex.real_smul] <;> ring
private lemma real_unitary_column_norm (O : Matrix.unitaryGroup (Fin 4) ℝ) (i : Fin 4) : ∑ k : Fin 4, (O k i)^2 = 1 := by
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i i)
    (Matrix.mem_unitaryGroup_iff'.mp O.property)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, pow_two] using hh
private lemma maximally_entangled_eigenbasis (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.IsHermitian) (hL : partialTraceLeft ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (hR : partialTraceRight ρ = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) : ∃ (F : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ) (lam : Fin 4 → ℝ), F.conjTranspose * F = 1 ∧ F * F.conjTranspose = 1 ∧ F.conjTranspose * ρ * F = Matrix.diagonal (fun i => (lam i : ℂ)) ∧ ∀ i : Fin 4, (Matrix.of (fun a b : Fin 2 => F (a,b) i)).conjTranspose * (Matrix.of (fun a b : Fin 2 => F (a,b) i)) = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hA : (magicW.conjTranspose * ρ * magicW).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul magicW hρ
  obtain ⟨O,lam,hdiag⟩ := real_spectral_basis _ hA (magicW_real_congruence ρ hρ hL hR)
  let F : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ := magicW * O.val.map Complex.ofReal
  obtain ⟨hO,hO'⟩ := real_cast_unitary O
  have hF : F.conjTranspose * F = 1 := by
    dsimp [F]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]; rw [← Matrix.mul_assoc magicW.conjTranspose, magicW_gram, Matrix.one_mul, hO]
  have hF' : F * F.conjTranspose = 1 := by
    dsimp [F]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (O.val.map Complex.ofReal), hO', Matrix.one_mul, magicW_cogram]
  refine ⟨F,lam,hF,hF',?_,?_⟩
  · dsimp only [F]
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hdiag
  · intro i
    have hcoeff : (Matrix.of (fun a b : Fin 2 => F (a,b) i)) = magicCoeff (fun k => O k i) := by
      change (fun a b : Fin 2 => (magicW *ᵥ (fun k => (O k i : ℂ))) (a,b)) = _
      exact magicW_vector_coeff _
    rw [hcoeff]; exact magicCoeff_adjoint_mul _ (real_unitary_column_norm O i)
private lemma maxent_vector_unitary (f : Fin 2 × Fin 2 → ℂ) (hcoeff : (Matrix.of (fun a b : Fin 2 => f (a,b))).conjTranspose * (Matrix.of (fun a b : Fin 2 => f (a,b))) = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) : ∃ V : Matrix.unitaryGroup (Fin 2) ℂ, ∀ x : Fin 2 × Fin 2, V x.2 x.1 = Real.sqrt 2 • f x := by
  let G : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of (fun a b => f (a,b))
  let V : Matrix (Fin 2) (Fin 2) ℂ := Real.sqrt 2 • G.transpose
  have hT : G.transpose * (G.transpose).conjTranspose =
      (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hh := congrArg Matrix.transpose hcoeff
    simpa only [G, Matrix.transpose_mul, Matrix.conjTranspose_transpose,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_conjTranspose] using hh
  have hV : V * V.conjTranspose = 1 := by
    dsimp only [V]; rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      hT, smul_smul, smul_smul]
    have hr : Real.sqrt 2 * Real.sqrt 2 * (1/2) = 1 := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hr, one_smul]
  refine ⟨⟨V, Matrix.mem_unitaryGroup_iff.mpr hV⟩, ?_⟩
  intro x
  rfl
private lemma pinch_is_normalized_choi (F : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hcoeff : ∀ i : Fin 4, (Matrix.of (fun a b : Fin 2 => F (a,b) i)).conjTranspose * (Matrix.of (fun a b : Fin 2 => F (a,b) i)) = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hM : M.PosSemidef) (ht : M.trace = 1) : ∃ Q : QuantumChannel (Fin 2) (Fin 2), (1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)) = pinch F M := by
  classical
  choose V hV using fun i => maxent_vector_unitary (fun x => F x i) (hcoeff i)
  let a : Fin 4 → ℝ := fun i => (F.conjTranspose * M * F) i i |>.re
  have hpos := hM.conjTranspose_mul_mul_same F
  have ha (i : Fin 4) : 0 ≤ a i := (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1
  have hareal (i : Fin 4) : (a i : ℂ) = (F.conjTranspose * M * F) i i := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).2
  have hsum : ∑ i, a i = 1 := by
    have hh : (F.conjTranspose * M * F).trace = 1 := by
      rw [Matrix.trace_mul_cycle, hF', Matrix.one_mul, ht]
    change (∑ i, Complex.reAddGroupHom ((F.conjTranspose * M * F) i i)) = 1
    rw [← map_sum]; exact congrArg Complex.re hh
  obtain ⟨Q,hQ⟩ := mixed_unitary_choi V a ha hsum
  refine ⟨Q, ?_⟩
  rw [hQ]
  have hpinch (x y : Fin 2 × Fin 2) : pinch F M x y =
      ∑ i : Fin 4, F x i * ((F.conjTranspose * M * F) i i) * star (F y i) := by
    change (∑ i : Fin 4, (F * Matrix.diagonal (fun i => (F.conjTranspose * M * F) i i)) x i *
      star (F y i)) = _
    simp only [Matrix.mul_diagonal]
  ext x y; rw [hpinch]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp_rw [hV]
  simp only [Complex.real_smul, star_mul, Complex.star_def, Complex.conj_ofReal,
    RCLike.ofReal_eq_complex_ofReal]
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl
  intro i _
  have hr : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    simpa only [pow_two] using
      D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq
  rw [← hareal]; norm_num
  calc
    _ = ((1/2 : ℂ) * (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) *
      (F x i * (a i : ℂ) * star (F y i)) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [mul_assoc (1/2 : ℂ), hr]; norm_num
private lemma normalized_cost_lower {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] (ρ : Matrix (X × Y) (X × Y) ℂ) (htrace : ρ.trace = 1) (σ : DensityState Y) (t : ℝ) (hfeas : ρ ≤ t • ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val)) : (Fintype.card X : ℝ)⁻¹ ≤ t := by
  have h := feasible_trace_lower ρ htrace (t • CStarMatrix.ofMatrix.symm σ.val)
    (by simpa only [Matrix.kronecker_smul] using hfeas)
  have ht : (CStarMatrix.ofMatrix.symm σ.val).trace = 1 := σ.property.2
  simpa only [Matrix.trace_smul, ht, Complex.real_smul, mul_one, Complex.ofReal_re] using h
private lemma ereal_iInf_add_real {κ : Type*} (f : κ → EReal) (c : ℝ) : (⨅ i, f i + (c : EReal)) = (⨅ i, f i) + (c : EReal) := by
  apply le_antisymm
  · apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).mp
    refine le_iInf fun i => ?_
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).mpr (iInf_le _ i)
  · exact le_iInf fun i => add_le_add (iInf_le f i) le_rfl
private lemma normalized_choi_infimum {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix (X × (Fin 2 × Fin 2)) (X × (Fin 2 × Fin 2)) ℂ) (hreplace : ∀ σ : DensityState (Fin 2 × Fin 2), ∃ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) ≤ Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val)) : (⨅ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap))))) = ⨅ σ : DensityState (Fin 2 × Fin 2), Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val) := by
  apply le_antisymm
  · refine le_iInf fun σ => ?_
    obtain ⟨Q,hQ⟩ := hreplace σ
    exact (iInf_le _ Q).trans hQ
  · refine le_iInf fun Q => ?_
    obtain ⟨σ,hσ⟩ := choiQ_half_state Q
    simpa only [hσ] using (iInf_le (fun σ : DensityState (Fin 2 × Fin 2) =>
      Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val)) σ)
private lemma entropy_identity_of_replacement {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (ρ : Matrix (X × (Fin 2 × Fin 2)) (X × (Fin 2 × Fin 2)) ℂ) (htrace : ρ.trace = 1) (c : ℝ) (hc : 0 < c) (hreplace : ∀ σ : DensityState (Fin 2 × Fin 2), ∃ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) ≤ Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val)) : -(⨅ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ((2*c) • ρ) ((1 : Matrix X X ℂ) ⊗ₖ (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) = condMinEntropy ρ - ((Real.logb 2 c : ℝ) : EReal) := by
  have hcost (Q : QuantumChannel (Fin 2) (Fin 2)) :
      Dmax ((2*c) • ρ) ((1 : Matrix X X ℂ) ⊗ₖ (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap))) =
        Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) +
          ((Real.logb 2 c : ℝ) : EReal) := by
    obtain ⟨σ,hσ⟩ := choiQ_half_state Q
    have he : (1 : Matrix X X ℂ) ⊗ₖ (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)) =
        (2 : ℝ) • ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val) := by
      rw [hσ, Matrix.kronecker_smul, smul_smul]; norm_num
    rw [he, ← smul_smul, Dmax_smul_both _ _ 2 (by norm_num)]; rw [← hσ]
    apply Dmax_smul_left _ _ c (Fintype.card X : ℝ)⁻¹ hc
      (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))
    intro t ht hfeas; exact normalized_cost_lower ρ htrace σ t hfeas
  simp_rw [hcost]
  rw [ereal_iInf_add_real, normalized_choi_infimum ρ hreplace]; rw [EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))]
  rfl
section
variable {X Y I : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype I] [DecidableEq I]
private lemma matrix_star_mul (A : Matrix X Y ℂ) (B : Matrix Y I ℂ) : (A*B).map star = A.map star * B.map star := by
  exact Matrix.map_mul (f := starRingEnd ℂ)
private lemma matrix_star_adjoint (A : Matrix X Y ℂ) : (A.map star).conjTranspose = A.conjTranspose.map star := by
  exact Eq.symm (Matrix.conjTranspose_map star (congrFun rfl))
private lemma partner_gram_diagonal (u : X × Y → ℂ) (F : Matrix Y I ℂ) (lam : I → ℝ) (hdiag : F.conjTranspose * partialTraceLeft (Matrix.vecMulVec u (star u)) * F = Matrix.diagonal (fun i => (lam i : ℂ))) : ((Matrix.of (Function.curry u)) * F.map star).conjTranspose * ((Matrix.of (Function.curry u)) * F.map star) = Matrix.diagonal (fun i => (lam i : ℂ)) := by
  rw [Matrix.conjTranspose_mul, matrix_star_adjoint]
  calc
    _ = F.conjTranspose.map star * (((Matrix.of (Function.curry u))).conjTranspose * (Matrix.of (Function.curry u))) *
        F.map star := by simp only [Matrix.mul_assoc]
    _ = (F.conjTranspose * partialTraceLeft (Matrix.vecMulVec u (star u)) * F).map star := by
      rw [vectorRows_gram, matrix_star_mul, matrix_star_mul]
    _ = _ := by
      rw [hdiag]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.diagonal_apply, hij,
        Complex.star_def, Complex.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
private lemma eigenbasis_sign_partner (u : X × Y → ℂ) (F : Matrix Y I ℂ) (lam s : I → ℝ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hs : ∀ i, (s i)^2 = 1) (hdiag : F.conjTranspose * partialTraceLeft (Matrix.vecMulVec u (star u)) * F = Matrix.diagonal (fun i => (lam i : ℂ))) : ∃ P : Matrix.unitaryGroup X ℂ, (P.val ⊗ₖ (F * Matrix.diagonal (fun i => (s i : ℂ)) * F.conjTranspose)) *ᵥ u = u := by
  let C := (Matrix.of (Function.curry u)) * F.map star
  let D := Matrix.diagonal (fun i => (s i : ℂ))
  have hC : C.conjTranspose * C = Matrix.diagonal (fun i => (lam i : ℂ)) :=
    partner_gram_diagonal u F lam hdiag
  have hgram : (C * D).conjTranspose * (C * D) = C.conjTranspose * C := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = D.conjTranspose * (C.conjTranspose * C) * D := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hC]
        simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Complex.star_def,
            Complex.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
          have hh : (s i : ℂ) * (s i : ℂ) = 1 := by
            exact_mod_cast (by simpa only [pow_two] using hs i)
          calc
            _ = (lam i : ℂ) * ((s i : ℂ) * (s i : ℂ)) := by ring
            _ = _ := by rw [hh]; simp
        · simp [Matrix.diagonal_apply_ne _ hij, hij]
  obtain ⟨P,hP⟩ :=
    D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
      (C * D) C hgram
  refine ⟨P, ?_⟩
  apply sign_tensor_invariant u F P.val (fun i => (s i : ℂ)) hF hF' _ hP.symm
  intro i
  exact_mod_cast (by simpa only [pow_two] using hs i)
end
private lemma signReal_sq (s : ((Bool × Bool) × (Bool × Bool))) (i : Fin 4) : (signReal s i)^2 = 1 := by
  rw [pow_two]
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_one, signReal_cast] using sign_sq s i
private lemma sign_symmetry_of_eigenbasis {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] (u : X × Y → ℂ) (F : Matrix Y (Fin 4) ℂ) (lam : Fin 4 → ℝ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hdiag : F.conjTranspose * partialTraceLeft (Matrix.vecMulVec u (star u)) * F = Matrix.diagonal (fun i => (lam i : ℂ))) (a b : ℝ) : ∃ P : ((Bool × Bool) × (Bool × Bool)) → Matrix.unitaryGroup X ℂ, ∀ s : ((Bool × Bool) × (Bool × Bool)), ((P s).val ⊗ₖ signConjugate F s) * (a • (1 : Matrix (X × Y) (X × Y) ℂ) + b • Matrix.vecMulVec u (star u)) * ((P s).val ⊗ₖ signConjugate F s).conjTranspose = a • 1 + b • Matrix.vecMulVec u (star u) := by
  classical
  have hp (s : ((Bool × Bool) × (Bool × Bool))) := eigenbasis_sign_partner u F lam (signReal s) hF hF'
    (signReal_sq s) hdiag
  choose P hP using hp
  refine ⟨P, ?_⟩
  intro s
  have hD : Matrix.diagonal (fun i => (signReal s i : ℂ)) = (Matrix.diagonal (sign s)) := by
    ext i j; simp [ Matrix.diagonal_apply, signReal_cast]
  have hvec : ((P s).val ⊗ₖ signConjugate F s) *ᵥ u = u := by
    simpa only [hD, signConjugate] using hP s
  let Q : Matrix.unitaryGroup Y ℂ :=
    ⟨signConjugate F s, Matrix.mem_unitaryGroup_iff'.mpr (signConjugate_unitary F s hF hF')⟩
  let K : Matrix.unitaryGroup (X × Y) ℂ :=
    ⟨(P s).val ⊗ₖ Q.val, Matrix.kronecker_mem_unitary (P s).property Q.property⟩
  exact noisy_rankOne_invariant u K a b hvec
section
variable {d : ℕ}
private lemma unitaryChoiVector_trace (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) : (Matrix.vecMulVec (unitaryChoiVector U) (star (unitaryChoiVector U))).trace = ((d*2 : ℕ) : ℂ) := by
  calc
    _ = (reducedUnitary U).trace := (trace_partialTraceLeft _).symm
    _ = (partialTraceLeft (reducedUnitary U)).trace := (trace_partialTraceLeft _).symm
    _ = _ := by rw [reducedUnitary_left, Matrix.trace_smul]; simp
private lemma choiN_noisy_trace (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (p : ℝ) (hd : 1 ≤ d) : (choiN (noisyUnitary U p)).trace = ((d*2 : ℕ) : ℂ) := by
  rw [choiN_noisy, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, unitaryChoiVector_trace]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp only [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    smul_eq_mul, Complex.real_smul, RCLike.ofReal_eq_complex_ofReal, Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp
  ring
private lemma choiState_noisy_trace (U : Matrix.unitaryGroup (Fin d × Fin 2) ℂ) (p : ℝ) (hd : 1 ≤ d) : (choiState (noisyUnitary U p)).trace = 1 := by
  rw [choiState, Matrix.trace_smul, choiN_noisy_trace U p hd]
  have hd' : ((d*2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by omega : d ≠ 0) (by decide : 2 ≠ 0))
  simp only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, Complex.ofReal_natCast]; exact inv_mul_cancel₀ hd'
end
private lemma pinch_smul {Y : Type*} [Fintype Y] [DecidableEq Y] (F : Matrix Y (Fin 4) ℂ) (M : Matrix Y Y ℂ) (t : ℝ) : pinch F (t • M) = t • pinch F M := by
  simp only [pinch, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
  have hd : Matrix.diagonal (fun i => t • (F.conjTranspose * M * F) i i) =
      t • Matrix.diagonal (fun i => (F.conjTranspose * M * F) i i) := Matrix.diagonal_smul t _
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]
private lemma replacement_of_sign_symmetry {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (ρ : Matrix (X × (Fin 2 × Fin 2)) (X × (Fin 2 × Fin 2)) ℂ) (htrace : ρ.trace = 1) (F : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hcoeff : ∀ i : Fin 4, (Matrix.of (fun a b : Fin 2 => F (a,b) i)).conjTranspose * (Matrix.of (fun a b : Fin 2 => F (a,b) i)) = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (P : ((Bool × Bool) × (Bool × Bool)) → Matrix.unitaryGroup X ℂ) (hsym : ∀ s : ((Bool × Bool) × (Bool × Bool)), ((P s).val ⊗ₖ signConjugate F s) * ρ * ((P s).val ⊗ₖ signConjugate F s).conjTranspose = ρ) : ∀ σ : DensityState (Fin 2 × Fin 2), ∃ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ ((1/2 : ℝ) • (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) ≤ Dmax ρ ((1 : Matrix X X ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.val) := by
  intro σ
  let M := CStarMatrix.ofMatrix.symm σ.val
  have hM : M.PosSemidef := density_posSemidef σ
  have hMt : M.trace = 1 := σ.property.2
  obtain ⟨Q,hQ⟩ := pinch_is_normalized_choi F hF hF' hcoeff M hM hMt
  refine ⟨Q, ?_⟩
  obtain ⟨τ,hτ⟩ := choiQ_half_state Q
  let a : ℝ := (Fintype.card X : ℝ)⁻¹
  have ha : 0 < a := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  apply Dmax_le_of_cost_imp ρ _ _ a a ha ha
  · intro t ht hfeas
    exact normalized_cost_lower ρ htrace σ t hfeas
  · intro t ht hfeas
    rw [← hτ] at hfeas; exact normalized_cost_lower ρ htrace τ t hfeas
  · intro t ht hfeas
    have hh := symmetry_pinching_feasible ρ (t • M) F P hsym
      (by simpa only [Matrix.kronecker_smul] using hfeas)
    rw [pinch_smul, ← hQ, Matrix.kronecker_smul] at hh; exact hh
private lemma entropy_identity_of_sign_symmetry {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (ρ : Matrix (X × (Fin 2 × Fin 2)) (X × (Fin 2 × Fin 2)) ℂ) (htrace : ρ.trace = 1) (c : ℝ) (hc : 0 < c) (F : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ) (hF : F.conjTranspose * F = 1) (hF' : F * F.conjTranspose = 1) (hcoeff : ∀ i : Fin 4, (Matrix.of (fun a b : Fin 2 => F (a,b) i)).conjTranspose * (Matrix.of (fun a b : Fin 2 => F (a,b) i)) = (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (P : ((Bool × Bool) × (Bool × Bool)) → Matrix.unitaryGroup X ℂ) (hsym : ∀ s : ((Bool × Bool) × (Bool × Bool)), ((P s).val ⊗ₖ signConjugate F s) * ρ * ((P s).val ⊗ₖ signConjugate F s).conjTranspose = ρ) : -(⨅ Q : QuantumChannel (Fin 2) (Fin 2), Dmax ((2*c) • ρ) ((1 : Matrix X X ℂ) ⊗ₖ (inputFirstChoi (matrixAction Q.toCompletelyPositiveMap)))) = condMinEntropy ρ - ((Real.logb 2 c : ℝ) : EReal) :=
  entropy_identity_of_replacement ρ htrace c hc
    (replacement_of_sign_symmetry ρ htrace F hF hF' hcoeff P hsym)
theorem result : claim := by
  intro d hd U p hp hp'
  letI : NeZero d := ⟨by omega⟩
  let c : ℝ := ((d*2 : ℕ) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let R := c⁻¹ • reducedUnitary U
  have hR : R.PosSemidef := (reducedUnitary_posSemidef U).smul (inv_nonneg.mpr hc.le)
  have heq : R = (((d*2 : ℕ) : ℂ)⁻¹) • reducedUnitary U := by
    exact inv_natCast_smul_eq ℝ ℂ (d * 2) (reducedUnitary U)
  obtain ⟨hL,hRight⟩ := normalizedReduced_marginals U hd
  rw [← heq] at hL hRight
  obtain ⟨F,lam,hF,hF',hdiag,hcoeff⟩ :=
    maximally_entangled_eigenbasis R hR.isHermitian hL hRight
  have hraw : reducedUnitary U = c • R := by
    dsimp only [R]; rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
  have hdiagRaw : F.conjTranspose * reducedUnitary U * F =
      Matrix.diagonal (fun i => ((c * lam i : ℝ) : ℂ)) := by
    rw [hraw,Matrix.mul_smul,Matrix.smul_mul,hdiag]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply,Complex.real_smul,Complex.ofReal_mul]
    · simp [Matrix.diagonal_apply_ne _ hij,Matrix.smul_apply]
  have hGamma : choiN (noisyUnitary U p) =
      (p*c⁻¹) • (1 : Matrix ((Fin d × Fin d) × (Fin 2 × Fin 2))
        ((Fin d × Fin d) × (Fin 2 × Fin 2)) ℂ) +
      (1-p) • Matrix.vecMulVec (unitaryChoiVector U) (star (unitaryChoiVector U)) := by
    rw [choiN_noisy]
    congr 1
    ext x y; simp [Complex.real_smul,c,mul_assoc]
  obtain ⟨P,hP⟩ := sign_symmetry_of_eigenbasis (unitaryChoiVector U) F
    (fun i => c*lam i) hF hF' hdiagRaw (p*c⁻¹) (1-p)
  have hsym (s : ((Bool × Bool) × (Bool × Bool))) :
      ((P s).val ⊗ₖ signConjugate F s) * choiState (noisyUnitary U p) *
        ((P s).val ⊗ₖ signConjugate F s).conjTranspose = choiState (noisyUnitary U p) := by
    simp only [choiState,Matrix.mul_smul,Matrix.smul_mul,hGamma,hP]
  have hId := entropy_identity_of_sign_symmetry (choiState (noisyUnitary U p))
    (choiState_noisy_trace U p hd) (d : ℝ) (by positivity) F hF hF' hcoeff P hsym
  have hdim : (((d*2 : ℕ) : ℝ)) = 2*(d : ℝ) := by push_cast; ring
  have hchoi (Q : QuantumChannel (Fin 2) (Fin 2)) :
      inputFirstChoi (matrixAction Q.toCompletelyPositiveMap) =
        (fun x y => CStarMatrix.ofMatrix.symm
          (Q.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single x.1 y.1 (1 : ℂ)))) x.2 y.2) := rfl
  simpa only [channelCondMinEntropy,choiN_eq_dimension_smul_choiState _ hd,hdim,hchoi] using hId
end D5.S3.Quantum.Information.BadhaniDasNoisyUnitary
