/- GID: D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/RenyiInformationCombiningOrderThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary quantum information combining is an equality at Renyi order three. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#15115; Proved)
Direct frozen dependencies: F1--F5 are declaration identities, not module pins.
F1: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.trace_hermitian_product_real
  declaration statement_id: sha256:d57aafbe2afd1228c9b5e26bf06684ec80accc922d16f29290f16819337adc81
F2: D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity
  declaration statement_id: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
F3: D5/S3/Quantum/Information/PartialTraceMutualInformation.kronecker_eq_conj_diagonal_eigenvalues
  declaration statement_id: sha256:8b1b61a640dd9dac61868bff2b7627714c90764e99b8c320fdb404ae694c4b19
F4: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
  declaration statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
F5: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
  declaration statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15282
All theorem proofs are bind-only; private auxiliaries have live consumers.
Definitions encode the source objects or consumed internal expressions.
Per-declaration classifications (frozen dependencies expand same-delivery helpers):
proof_shape: condRenyiDown: bind-only; escape_witness: none
  Direct frozen dependencies (condRenyiDown): F4
  consumers (condRenyiDown): claim, input_entropy_eq, input_entropy_exp, input_entropy_range, output_entropy_exp, result
proof_shape: cqState: bind-only; escape_witness: none
  Direct frozen dependencies (cqState): none
  consumers (cqState): claim, cq_marginal, sandwich_blocks, input_entropy_eq, input_entropy_exp, input_entropy_range, xor_state, output_entropy_exp, result
proof_shape: tau: bind-only; escape_witness: none
  Direct frozen dependencies (tau): none
  consumers (tau): claim, xor_state, output_entropy_exp, result
proof_shape: traceOutX2: bind-only; escape_witness: none
  Direct frozen dependencies (traceOutX2): none
  consumers (traceOutX2): claim, xor_state, output_entropy_exp, result
proof_shape: hRenyi: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi): none
  consumers (hRenyi): hRenyiInv, claim, hRenyi_three, hRenyi_three_exp, hRenyi_three_continuous, hRenyi_three_strictMonoOn, hRenyi_three_zero, hRenyi_three_half, hRenyi_three_image, hRenyiInv_three_spec, hRenyi_three_combining, scalar_readout, result
proof_shape: hRenyiInv: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyiInv): none
  consumers (hRenyiInv): claim, hRenyiInv_three_spec, scalar_readout, result
proof_shape: bconv: bind-only; escape_witness: none
  Direct frozen dependencies (bconv): none
  consumers (bconv): claim, bconv_bias, hRenyi_three_combining, scalar_readout, result
proof_shape: claim: bind-only; escape_witness: none
  Direct frozen dependencies (claim): F4, F2
  consumers (claim): result
proof_shape: blk: bind-only; escape_witness: none
  Direct frozen dependencies (blk): none
  consumers (blk): blk_psd, blk_mul, blk_trace, blk_three, sandwich_blocks, input_entropy_eq
proof_shape: unit_psd: bind-only; escape_witness: none
  Direct frozen dependencies (unit_psd): none
  consumers (unit_psd): blk_psd
proof_shape: blk_psd: bind-only; escape_witness: none
  Direct frozen dependencies (blk_psd): none
  consumers (blk_psd): input_entropy_eq
proof_shape: blk_mul: bind-only; escape_witness: none
  Direct frozen dependencies (blk_mul): none
  consumers (blk_mul): blk_three
proof_shape: blk_trace: bind-only; escape_witness: none
  Direct frozen dependencies (blk_trace): none
  consumers (blk_trace): input_entropy_eq
proof_shape: blk_three: bind-only; escape_witness: none
  Direct frozen dependencies (blk_three): none
  consumers (blk_three): input_entropy_eq
proof_shape: cq_marginal: bind-only; escape_witness: none
  Direct frozen dependencies (cq_marginal): F4
  consumers (cq_marginal): input_entropy_eq
proof_shape: sandwich_blocks: bind-only; escape_witness: none
  Direct frozen dependencies (sandwich_blocks): none
  consumers (sandwich_blocks): input_entropy_eq
proof_shape: trace_cubic_moment: bind-only; escape_witness: none
  Direct frozen dependencies (trace_cubic_moment): none
  consumers (trace_cubic_moment): input_trace_moment
proof_shape: cubic_cross_nonneg: bind-only; escape_witness: none
  Direct frozen dependencies (cubic_cross_nonneg): F5
  consumers (cubic_cross_nonneg): input_trace_range
proof_shape: cubic_t_nonneg: bind-only; escape_witness: none
  Direct frozen dependencies (cubic_t_nonneg): F5
  consumers (cubic_t_nonneg): moment_nonneg
proof_shape: cfc_real_diagonal: bind-only; escape_witness: none
  Direct frozen dependencies (cfc_real_diagonal): none
  consumers (cfc_real_diagonal): cfc_unitary_diagonal
proof_shape: cfc_unitary_diagonal: bind-only; escape_witness: none
  Direct frozen dependencies (cfc_unitary_diagonal): none
  consumers (cfc_unitary_diagonal): kronecker_rpow
proof_shape: kronecker_rpow: bind-only; escape_witness: none
  Direct frozen dependencies (kronecker_rpow): F3
  consumers (kronecker_rpow): xor_sandwiches
proof_shape: k3: bind-only; escape_witness: none
  Direct frozen dependencies (k3): none
  consumers (k3): hRenyi_three, k3_pos, hRenyi_three_exp, hRenyi_three_continuous, hRenyi_three_strictMonoOn, hRenyi_three_zero, hRenyi_three_half, hRenyi_three_combining
proof_shape: hRenyi_three: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three): none
  consumers (hRenyi_three): hRenyi_three_exp, hRenyi_three_continuous, hRenyi_three_strictMonoOn, hRenyi_three_zero, hRenyi_three_half
proof_shape: k3_pos: bind-only; escape_witness: none
  Direct frozen dependencies (k3_pos): none
  consumers (k3_pos): hRenyi_three_exp, hRenyi_three_continuous, hRenyi_three_strictMonoOn
proof_shape: hRenyi_three_exp: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_exp): none
  consumers (hRenyi_three_exp): hRenyi_three_combining
proof_shape: hRenyi_three_continuous: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_continuous): none
  consumers (hRenyi_three_continuous): hRenyi_three_image
proof_shape: hRenyi_three_strictMonoOn: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_strictMonoOn): none
  consumers (hRenyi_three_strictMonoOn): hRenyi_three_image
proof_shape: hRenyi_three_zero: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_zero): none
  consumers (hRenyi_three_zero): hRenyi_three_image
proof_shape: hRenyi_three_half: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_half): none
  consumers (hRenyi_three_half): hRenyi_three_image
proof_shape: hRenyi_three_image: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_image): none
  consumers (hRenyi_three_image): hRenyiInv_three_spec
proof_shape: hRenyiInv_three_spec: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyiInv_three_spec): none
  consumers (hRenyiInv_three_spec): scalar_readout
proof_shape: bconv_bias: bind-only; escape_witness: none
  Direct frozen dependencies (bconv_bias): none
  consumers (bconv_bias): hRenyi_three_combining
proof_shape: hRenyi_three_combining: bind-only; escape_witness: none
  Direct frozen dependencies (hRenyi_three_combining): none
  consumers (hRenyi_three_combining): scalar_readout
proof_shape: exp_two_log_two: bind-only; escape_witness: none
  Direct frozen dependencies (exp_two_log_two): none
  consumers (exp_two_log_two): exp_neg_two_log_two, scalar_readout
proof_shape: exp_neg_two_log_two: bind-only; escape_witness: none
  Direct frozen dependencies (exp_neg_two_log_two): none
  consumers (exp_neg_two_log_two): reflected_exp_product, input_entropy_range
proof_shape: reflected_exp_product: bind-only; escape_witness: none
  Direct frozen dependencies (reflected_exp_product): none
  consumers (reflected_exp_product): scalar_readout
proof_shape: scalar_readout: bind-only; escape_witness: none
  Direct frozen dependencies (scalar_readout): none
  consumers (scalar_readout): result
proof_shape: sandwich: bind-only; escape_witness: none
  Direct frozen dependencies (sandwich): none
  consumers (sandwich): moment, sandwich_psd, sandwich_sum, sandwich_sum_cube_trace, input_trace_moment, moment_nonneg, input_trace_range, input_entropy_eq, input_entropy_range, xor_sandwiches, xor_moment
proof_shape: moment: bind-only; escape_witness: none
  Direct frozen dependencies (moment): none
  consumers (moment): input_trace_moment, moment_nonneg, input_trace_range, input_entropy_eq, input_entropy_exp, input_entropy_range, xor_moment, output_entropy_exp, result
proof_shape: marginal_psd: bind-only; escape_witness: none
  Direct frozen dependencies (marginal_psd): none
  consumers (marginal_psd): sandwich_sum, sandwich_sum_cube_trace, xor_sandwiches
proof_shape: marginal_trace: bind-only; escape_witness: none
  Direct frozen dependencies (marginal_trace): F2
  consumers (marginal_trace): sandwich_sum_cube_trace
proof_shape: sandwich_psd: bind-only; escape_witness: none
  Direct frozen dependencies (sandwich_psd): none
  consumers (sandwich_psd): moment_nonneg, input_trace_range, input_entropy_eq, xor_moment
proof_shape: inverse_third_sandwich: bind-only; escape_witness: none
  Direct frozen dependencies (inverse_third_sandwich): none
  consumers (inverse_third_sandwich): sandwich_sum
proof_shape: sandwich_sum: bind-only; escape_witness: none
  Direct frozen dependencies (sandwich_sum): none
  consumers (sandwich_sum): sandwich_sum_cube_trace
proof_shape: cube_root_cube: bind-only; escape_witness: none
  Direct frozen dependencies (cube_root_cube): none
  consumers (cube_root_cube): sandwich_sum_cube_trace
proof_shape: sandwich_sum_cube_trace: bind-only; escape_witness: none
  Direct frozen dependencies (sandwich_sum_cube_trace): F2
  consumers (sandwich_sum_cube_trace): input_trace_moment, input_trace_range
proof_shape: input_trace_moment: bind-only; escape_witness: none
  Direct frozen dependencies (input_trace_moment): F2
  consumers (input_trace_moment): input_trace_range, input_entropy_eq, input_entropy_range
proof_shape: moment_nonneg: bind-only; escape_witness: none
  Direct frozen dependencies (moment_nonneg): F5, F2
  consumers (moment_nonneg): input_trace_range, input_entropy_exp
proof_shape: input_trace_range: bind-only; escape_witness: none
  Direct frozen dependencies (input_trace_range): F2, F5
  consumers (input_trace_range): input_entropy_range
proof_shape: input_entropy_eq: bind-only; escape_witness: none
  Direct frozen dependencies (input_entropy_eq): F2, F4
  consumers (input_entropy_eq): input_entropy_exp
proof_shape: input_entropy_exp: bind-only; escape_witness: none
  Direct frozen dependencies (input_entropy_exp): F5, F2, F4
  consumers (input_entropy_exp): input_entropy_range, output_entropy_exp, result
proof_shape: input_entropy_range: bind-only; escape_witness: none
  Direct frozen dependencies (input_entropy_range): F2, F5, F4
  consumers (input_entropy_range): result
proof_shape: out0: bind-only; escape_witness: none
  Direct frozen dependencies (out0): none
  consumers (out0): xor_state, out_density, xor_marginal, xor_sandwiches, xor_moment, output_entropy_exp
proof_shape: out1: bind-only; escape_witness: none
  Direct frozen dependencies (out1): none
  consumers (out1): xor_state, out_density, xor_marginal, xor_sandwiches, xor_moment, output_entropy_exp
proof_shape: xor_state: bind-only; escape_witness: none
  Direct frozen dependencies (xor_state): none
  consumers (xor_state): output_entropy_exp
proof_shape: out_density: bind-only; escape_witness: none
  Direct frozen dependencies (out_density): F2
  consumers (out_density): output_entropy_exp
proof_shape: xor_marginal: bind-only; escape_witness: none
  Direct frozen dependencies (xor_marginal): none
  consumers (xor_marginal): xor_sandwiches
proof_shape: xor_sandwiches: bind-only; escape_witness: none
  Direct frozen dependencies (xor_sandwiches): F3, F2
  consumers (xor_sandwiches): xor_moment
proof_shape: xor_moment: bind-only; escape_witness: none
  Direct frozen dependencies (xor_moment): F1, F3, F2
  consumers (xor_moment): output_entropy_exp
proof_shape: output_entropy_exp: bind-only; escape_witness: none
  Direct frozen dependencies (output_entropy_exp): F1, F3, F2, F5, F4
  consumers (output_entropy_exp): result
  Direct frozen dependencies (result): F2, F5, F4, F1, F3
  consumers (result): settling result
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound

open Matrix
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open scoped Kronecker MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder

namespace D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree

section

variable {n a b n1 n2 : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype n1] [DecidableEq n1] [Fintype n2] [DecidableEq n2]

noncomputable def condRenyiDown (alpha : ℝ) (rho : Matrix (a × b) (a × b) ℂ) : ℝ :=
  let M := (1 : Matrix a a ℂ) ⊗ₖ ((partialTraceLeft rho) ^ ((1 - alpha) / (2 * alpha)))
  (1 / (1 - alpha)) * Real.log (RCLike.re (trace ((M * rho * M) ^ alpha)))

noncomputable def cqState (s0 s1 : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  (1/2 : ℂ) • (single 0 0 1 ⊗ₖ s0) + (1/2 : ℂ) • (single 1 1 1 ⊗ₖ s1)

noncomputable def tau (s1 : Fin 2 → Matrix n1 n1 ℂ)
    (s2 : Fin 2 → Matrix n2 n2 ℂ) :
    Matrix ((Fin 2 × Fin 2) × (n1 × n2)) ((Fin 2 × Fin 2) × (n1 × n2)) ℂ :=
  ∑ z, ∑ x2, (1/4 : ℂ) •
    (single (z + x2, x2) (z + x2, x2) 1 ⊗ₖ (s1 z ⊗ₖ s2 x2))

noncomputable def traceOutX2 (t : Matrix ((Fin 2 × Fin 2) × b) ((Fin 2 × Fin 2) × b) ℂ) :
    Matrix (Fin 2 × b) (Fin 2 × b) ℂ :=
  fun (z, j) (z', j') => ∑ x2, t ((z, x2), j) ((z', x2), j')

noncomputable def hRenyi (alpha p : ℝ) : ℝ :=
  (1 / (1 - alpha)) * Real.log (p ^ alpha + (1 - p) ^ alpha)

noncomputable def hRenyiInv (alpha : ℝ) : ℝ → ℝ :=
  Function.invFunOn (hRenyi alpha) (Set.Icc 0 (1/2))

noncomputable def bconv (p q : ℝ) : ℝ := p * (1 - q) + (1 - p) * q

noncomputable def claim : Prop :=
  ∀ (n1 n2 : ℕ) (s1 : Fin 2 → Matrix (Fin n1) (Fin n1) ℂ)
    (s2 : Fin 2 → Matrix (Fin n2) (Fin n2) ℂ),
    (∀ x, IsDensity (s1 x)) → (∀ x, IsDensity (s2 x)) →
    let H1 := condRenyiDown 3 (cqState (s1 0) (s1 1))
    let H2 := condRenyiDown 3 (cqState (s2 0) (s2 1))
    let Hout := condRenyiDown 3 (traceOutX2 (tau s1 s2))
    (H1 + H2 ≤ Real.log 2 →
      Hout = hRenyi 3 (bconv (hRenyiInv 3 H1) (hRenyiInv 3 H2))) ∧
    (Real.log 2 ≤ H1 + H2 →
      Hout = H1 + H2 - Real.log 2 +
        hRenyi 3 (bconv (hRenyiInv 3 (Real.log 2 - H1))
          (hRenyiInv 3 (Real.log 2 - H2))))

end

section
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

private def blk (A B : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  single 0 0 1 ⊗ₖ A + single 1 1 1 ⊗ₖ B

private lemma unit_psd (i : Fin 2) : (single i i (1 : ℂ)).PosSemidef := by
  have h : (diagonal (fun j : Fin 2 => if j = i then (1 : ℂ) else 0)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => by split <;> norm_num)
  convert h using 1
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [Matrix.single, Matrix.diagonal]

private lemma blk_psd {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (blk A B).PosSemidef := (unit_psd 0 |>.kronecker hA).add (unit_psd 1 |>.kronecker hB)

private lemma blk_mul (A B C D : Matrix n n ℂ) : blk A B * blk C D = blk (A*C) (B*D) := by
  unfold blk
  simp only [add_mul, mul_add, ← mul_kronecker_mul]
  simp

private lemma blk_trace (A B : Matrix n n ℂ) : trace (blk A B) = trace A + trace B := by
  unfold blk
  simp [trace_kronecker]

private lemma blk_three (A B : Matrix n n ℂ) : (blk A B)^3 = blk (A^3) (B^3) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, blk_mul]

private lemma cq_marginal (s0 s1 : Matrix n n ℂ) :
    partialTraceLeft (cqState s0 s1) = (1/2 : ℂ) • (s0 + s1) := by
  ext i j
  simp [partialTraceLeft, cqState, Fin.sum_univ_two, Matrix.single, kroneckerMap_apply, smul_add]
  ring

private lemma sandwich_blocks (s0 s1 T : Matrix n n ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T) * cqState s0 s1 *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T) =
    blk ((1/2 : ℂ) • (T*s0*T)) ((1/2 : ℂ) • (T*s1*T)) := by
  unfold cqState blk
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    ← mul_kronecker_mul, one_mul, mul_one, kronecker_smul]

private lemma trace_cubic_moment (A B : Matrix n n ℂ) :
    trace (A^3 + B^3) =
      (trace ((A+B)^3) + 3 * trace ((A+B)*(A-B)*(A-B))) / 4 := by
  have hABA : trace (A*B*A) = trace (A*A*B) := trace_mul_cycle A B A
  have hBAA : trace (B*A*A) = trace (A*A*B) := by rw [trace_mul_cycle]; rw [hABA]
  have hBAB : trace (B*A*B) = trace (A*B*B) := by rw [trace_mul_cycle]; rw [trace_mul_cycle]
  have hBBA : trace (B*B*A) = trace (A*B*B) := trace_mul_cycle B B A
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, sub_mul, mul_sub,
    trace_add, trace_sub, hABA, hBAA, hBAB, hBBA]
  ring

private lemma cubic_cross_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (trace (A^3+B^3)).re ≤ (trace ((A+B)^3)).re := by
  have h1 := RHLinalg.trace_mul_nonneg_of_posSemidef (hA.pow 2) hB
  have h2 := RHLinalg.trace_mul_nonneg_of_posSemidef hA (hB.pow 2)
  have hABA : trace (A*B*A) = trace (A*A*B) := trace_mul_cycle A B A
  have hBAA : trace (B*A*A) = trace (A*A*B) := by rw [trace_mul_cycle]; rw [hABA]
  have hBAB : trace (B*A*B) = trace (A*B*B) := by rw [trace_mul_cycle]; rw [trace_mul_cycle]
  have hBBA : trace (B*B*A) = trace (A*B*B) := trace_mul_cycle B B A
  simp only [pow_two, ← Matrix.mul_assoc, RCLike.re_eq_complex_re] at h1 h2
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, trace_add,
    hABA, hBAA, hBAB, hBBA, Complex.add_re] at ⊢
  linarith

private lemma cubic_t_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (trace ((A+B)*(A-B)*(A-B))).re := by
  have hD : (A-B).IsHermitian := hA.1.sub hB.1
  have hDD : ((A-B)*(A-B)).PosSemidef := by
    simpa [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self (A-B)
  simpa only [Matrix.mul_assoc, RCLike.re_eq_complex_re] using
    RHLinalg.trace_mul_nonneg_of_posSemidef (hA.add hB) hDD

end
end

section
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private lemma cfc_real_diagonal (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  let phi : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ :=
    { toAlgHom := Matrix.diagonalAlgHom ℂ
      map_star' := fun d => (Matrix.diagonal_conjTranspose d).symm }
  letI : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let z : n → ℂ := fun i => (d i : ℂ)
  have hd : IsSelfAdjoint z := by ext i; simp [z, Pi.star_apply]
  have hf : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    apply Set.Finite.continuousOn
    exact Set.finite_iUnion fun i => (Set.finite_singleton (d i)).subset
      (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hh := phi.map_cfc (R := ℝ) f z hf
    phi.toLinearMap.continuous_of_finiteDimensional hd
    (hd.map phi)
  change cfc f (phi z) = _
  rw [← hh, cfc_map_pi (S := ℂ) f z (by rwa [Pi.spectrum_eq] at hf) hd
    (fun i => by change star (d i : ℂ) = (d i : ℂ); simp)]
  change diagonal (fun i => cfc f (z i)) = diagonal (fun i => (f (d i) : ℂ))
  congr 1
  funext i
  simpa [z] using (cfc_algebraMap (R := ℝ) (A := ℂ) (d i) f)

private lemma cfc_unitary_diagonal (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * diagonal (fun i => (f (d i) : ℂ)) * star (U : Matrix n n ℂ) := by
  let phi := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U).toStarAlgHom
  have hd : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    exact isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])
  have hf := (diagonal (fun i => (d i : ℂ))).finite_real_spectrum.continuousOn (f := f)
  have h := phi.map_cfc (R := ℝ) f _ hf phi.toLinearMap.continuous_of_finiteDimensional hd
    (hd.map phi)
  change cfc f (phi (diagonal (fun i => (d i : ℂ)))) = _
  rw [← h, cfc_real_diagonal]
  rfl

private lemma kronecker_rpow {r1 : Matrix n n ℂ} {r2 : Matrix m m ℂ}
    (h1 : r1.PosSemidef) (h2 : r2.PosSemidef) (y : ℝ) :
    (r1 ⊗ₖ r2) ^ y = (r1 ^ y) ⊗ₖ (r2 ^ y) := by
  let U : Matrix.unitaryGroup (n × m) ℂ :=
    ⟨(h1.1.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ
      (h2.1.eigenvectorUnitary : Matrix m m ℂ),
      Matrix.kronecker_mem_unitary h1.1.eigenvectorUnitary.2 h2.1.eigenvectorUnitary.2⟩
  rw [CFC.rpow_eq_cfc_real (h1.kronecker h2).nonneg,
    CFC.rpow_eq_cfc_real h1.nonneg, CFC.rpow_eq_cfc_real h2.nonneg]
  have hspec := D5.S3.Quantum.Information.PartialTraceMutualInformation.kronecker_eq_conj_diagonal_eigenvalues h1.1 h2.1
  have hd : r1 ⊗ₖ r2 = (U : Matrix (n × m) (n × m) ℂ) *
      diagonal (fun p : n × m => ((h1.1.eigenvalues p.1 * h2.1.eigenvalues p.2 : ℝ) : ℂ)) *
      star (U : Matrix (n × m) (n × m) ℂ) := by
    simpa [U, Complex.ofReal_mul] using hspec
  rw [hd, cfc_unitary_diagonal, h1.1.cfc_eq, h2.1.cfc_eq]
  simp only [U, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal, Function.comp_apply]
  congr 2
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [Real.mul_rpow (h1.eigenvalues_nonneg p.1) (h2.eigenvalues_nonneg p.2)]
  · simp [diagonal_apply, hpq]

end
end

section
noncomputable section

private def k3 (p : ℝ) : ℝ := (1 + 3 * (1 - 2 * p) ^ 2) / 4

private lemma hRenyi_three (p : ℝ) : hRenyi 3 p = -(1/2 : ℝ) * Real.log (k3 p) := by
  unfold hRenyi k3
  rw [show (3 : ℝ) = (3 : ℕ) from rfl, Real.rpow_natCast, Real.rpow_natCast]
  congr 1
  · norm_num
  · congr 1
    ring

private lemma k3_pos (p : ℝ) : 0 < k3 p := by unfold k3; positivity

private lemma hRenyi_three_exp (p : ℝ) : Real.exp (-2 * hRenyi 3 p) = k3 p := by
  rw [hRenyi_three]
  ring_nf
  exact Real.exp_log (k3_pos p)

private lemma hRenyi_three_continuous : Continuous (hRenyi 3) := by
  have hk : Continuous k3 := by unfold k3; fun_prop
  change Continuous (fun p => hRenyi 3 p)
  simp_rw [hRenyi_three]
  exact continuous_const.mul (hk.log (fun p => ne_of_gt (k3_pos p)))

private lemma hRenyi_three_strictMonoOn : StrictMonoOn (hRenyi 3) (Set.Icc 0 (1/2)) := by
  intro p hp q hq hpq
  have hbq : 0 ≤ 1 - 2*q := by linarith [hq.2]
  have hbp : 1 - 2*q < 1 - 2*p := by linarith
  have hs : (1 - 2*q)^2 < (1 - 2*p)^2 := (sq_lt_sq₀ hbq (le_trans hbq hbp.le)).mpr hbp
  have hk : k3 q < k3 p := by unfold k3; nlinarith
  have hl := Real.log_lt_log (k3_pos q) hk
  rw [hRenyi_three, hRenyi_three]
  linarith

private lemma hRenyi_three_zero : hRenyi 3 0 = 0 := by
  rw [hRenyi_three]
  norm_num [k3]

private lemma hRenyi_three_half : hRenyi 3 (1/2) = Real.log 2 := by
  rw [hRenyi_three]
  norm_num [k3]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ)*2) := by norm_num
      _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
      _ = _ := by ring
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, h4]
  ring

private lemma hRenyi_three_image : hRenyi 3 '' Set.Icc 0 (1/2) = Set.Icc 0 (Real.log 2) := by
  rw [hRenyi_three_continuous.continuousOn.image_Icc_of_monotoneOn (by norm_num : (0 : ℝ) ≤ 1/2)
    hRenyi_three_strictMonoOn.monotoneOn, hRenyi_three_zero, hRenyi_three_half]

private lemma hRenyiInv_three_spec {H : ℝ} (hH : H ∈ Set.Icc 0 (Real.log 2)) :
    hRenyiInv 3 H ∈ Set.Icc 0 (1/2) ∧ hRenyi 3 (hRenyiInv 3 H) = H := by
  have him : H ∈ hRenyi 3 '' Set.Icc 0 (1/2) := by rw [hRenyi_three_image]; exact hH
  exact ⟨Function.invFunOn_mem him, Function.invFunOn_eq him⟩

private lemma bconv_bias (p q : ℝ) : 1 - 2*bconv p q = (1 - 2*p)*(1 - 2*q) := by
  unfold bconv
  ring

private lemma hRenyi_three_combining (p q : ℝ) :
    Real.exp (-2 * hRenyi 3 (bconv p q)) =
      (4 * Real.exp (-2 * hRenyi 3 p) * Real.exp (-2 * hRenyi 3 q) -
        Real.exp (-2 * hRenyi 3 p) - Real.exp (-2 * hRenyi 3 q) + 1) / 3 := by
  simp_rw [hRenyi_three_exp]
  unfold k3
  rw [bconv_bias]
  ring

private lemma exp_two_log_two : Real.exp (2*Real.log 2) = 4 := by
  rw [show (2 : ℝ)*Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private lemma exp_neg_two_log_two : Real.exp (-2*Real.log 2) = 1/4 := by
  rw [show (-2 : ℝ)*Real.log 2 = -(2*Real.log 2) by ring, Real.exp_neg, exp_two_log_two]
  norm_num

private lemma reflected_exp_product (H : ℝ) :
    Real.exp (-2*H)*Real.exp (-2*(Real.log 2-H)) = 1/4 := by
  rw [← Real.exp_add]
  convert exp_neg_two_log_two using 1 <;> congr 1 <;> ring

private lemma scalar_readout (H1 H2 Hout : ℝ)
    (h1 : H1 ∈ Set.Icc 0 (Real.log 2)) (h2 : H2 ∈ Set.Icc 0 (Real.log 2))
    (he : Real.exp (-2*Hout) =
      (4*Real.exp (-2*H1)*Real.exp (-2*H2)-Real.exp (-2*H1)-Real.exp (-2*H2)+1)/3) :
    Hout = hRenyi 3 (bconv (hRenyiInv 3 H1) (hRenyiInv 3 H2)) ∧
    Hout = H1+H2-Real.log 2 +
      hRenyi 3 (bconv (hRenyiInv 3 (Real.log 2-H1)) (hRenyiInv 3 (Real.log 2-H2))) := by
  constructor
  · have hh := hRenyi_three_combining (hRenyiInv 3 H1) (hRenyiInv 3 H2)
    rw [(hRenyiInv_three_spec h1).2, (hRenyiInv_three_spec h2).2] at hh
    have hi := Real.exp_injective (he.trans hh.symm)
    linarith
  · have hh1 : Real.log 2-H1 ∈ Set.Icc 0 (Real.log 2) := ⟨by linarith [h1.2], by linarith [h1.1]⟩
    have hh2 : Real.log 2-H2 ∈ Set.Icc 0 (Real.log 2) := ⟨by linarith [h2.2], by linarith [h2.1]⟩
    let R := hRenyi 3 (bconv (hRenyiInv 3 (Real.log 2-H1)) (hRenyiInv 3 (Real.log 2-H2)))
    have hR : Real.exp (-2*R) =
        (4*Real.exp (-2*(Real.log 2-H1))*Real.exp (-2*(Real.log 2-H2))-
        Real.exp (-2*(Real.log 2-H1))-Real.exp (-2*(Real.log 2-H2))+1)/3 := by
      exact (hRenyi_three_combining _ _).trans (by rw [(hRenyiInv_three_spec hh1).2,
        (hRenyiInv_three_spec hh2).2])
    have hs : Real.exp (-2*(H1+H2-Real.log 2+R)) =
        Real.exp (-2*H1)*Real.exp (-2*H2)*4*Real.exp (-2*R) := by
      rw [show -2*(H1+H2-Real.log 2+R) = ((-2*H1)+(-2*H2))+(2*Real.log 2)+(-2*R) by ring]
      rw [Real.exp_add, Real.exp_add, Real.exp_add, exp_two_log_two]
    rw [hR] at hs
    have hP1 := reflected_exp_product H1
    have hP2 := reflected_exp_product H2
    have h1' : Real.exp (-2*(Real.log 2-H1)) = 1/(4*Real.exp (-2*H1)) := by
      apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (Real.exp_pos _)))).mpr
      nlinarith
    have h2' : Real.exp (-2*(Real.log 2-H2)) = 1/(4*Real.exp (-2*H2)) := by
      apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (Real.exp_pos _)))).mpr
      nlinarith
    rw [h1', h2'] at hs
    have hm : Real.exp (-2*(H1+H2-Real.log 2+R)) = Real.exp (-2*Hout) := by
      rw [hs, he]
      field_simp
      <;> ring
    have hi := Real.exp_injective hm
    dsimp [R] at hi
    linarith

end
end

section
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

private def sandwich (r s : Matrix n n ℂ) := (1/2 : ℂ) • ((r ^ (-1/3 : ℝ))*s*(r ^ (-1/3 : ℝ)))
private def moment (s0 s1 : Matrix n n ℂ) : ℝ :=
  let r := midpoint ℂ s0 s1
  let A := sandwich r s0
  let B := sandwich r s1
  (trace ((A+B)*(A-B)*(A-B))).re

private lemma marginal_psd {s0 s1 : Matrix n n ℂ} (h0 : s0.PosSemidef) (h1 : s1.PosSemidef) :
    (midpoint ℂ s0 s1).PosSemidef := by
  simpa only [midpoint_eq_smul_add, invOf_eq_inv, inv_eq_one_div] using
    (h0.add h1).smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)

private lemma marginal_trace {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    trace (midpoint ℂ s0 s1) = 1 := by
  rw [midpoint_eq_smul_add, trace_smul, trace_add, h0.2, h1.2]
  norm_num

private lemma sandwich_psd {r s : Matrix n n ℂ} (hs : s.PosSemidef) :
    (sandwich r s).PosSemidef := by
  have hT : (r ^ (-1/3 : ℝ)).PosSemidef := (CFC.rpow_nonneg (a := r)).posSemidef
  have hh := hs.mul_mul_conjTranspose_same (r ^ (-1/3 : ℝ))
  rw [hT.1.eq] at hh
  exact hh.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)

private lemma inverse_third_sandwich {r : Matrix n n ℂ} (hr : r.PosSemidef) :
    (r ^ (-1/3 : ℝ))*r*(r ^ (-1/3 : ℝ)) = r ^ (1/3 : ℝ) := by
  have hf (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ r) := r.finite_real_spectrum.continuousOn f
  rw [CFC.rpow_eq_cfc_real hr.nonneg, CFC.rpow_eq_cfc_real hr.nonneg]
  calc
    cfc (fun x : ℝ => x ^ (-1/3 : ℝ)) r * r * cfc (fun x : ℝ => x ^ (-1/3 : ℝ)) r =
        cfc (fun x : ℝ => x ^ (-1/3 : ℝ)) r * cfc (fun x : ℝ => x) r *
          cfc (fun x : ℝ => x ^ (-1/3 : ℝ)) r := by
            have hi : cfc (fun x : ℝ => x) r = r := by
              change cfc (id : ℝ → ℝ) r = r
              exact cfc_id ℝ r (ha := hr.1)
            rw [hi]
    _ = cfc (fun x : ℝ => (x ^ (-1/3 : ℝ)*x)*x ^ (-1/3 : ℝ)) r := by
      rw [cfc_mul _ _ r (hf _) (hf _), cfc_mul _ _ r (hf _) (hf _)]
    _ = cfc (fun x : ℝ => x ^ (1/3 : ℝ)) r := by
      apply cfc_congr
      intro x hx
      obtain ⟨i, rfl⟩ := hr.1.spectrum_real_eq_range_eigenvalues ▸ hx
      have hx0 := hr.eigenvalues_nonneg i
      change (hr.1.eigenvalues i) ^ (-1/3 : ℝ) * hr.1.eigenvalues i *
        (hr.1.eigenvalues i) ^ (-1/3 : ℝ) = (hr.1.eigenvalues i) ^ (1/3 : ℝ)
      have hl : (hr.1.eigenvalues i) ^ (-1/3 : ℝ) * hr.1.eigenvalues i =
          (hr.1.eigenvalues i) ^ (2/3 : ℝ) := by
        calc
          _ = (hr.1.eigenvalues i) ^ (-1/3 : ℝ) * (hr.1.eigenvalues i) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (hr.1.eigenvalues i) ^ ((-1/3 : ℝ)+1) :=
            (Real.rpow_add' hx0 (by norm_num : (-1/3 : ℝ)+1 ≠ 0)).symm
          _ = _ := by norm_num
      rw [hl, ← Real.rpow_add' hx0 (by norm_num : (2/3 : ℝ)+(-1/3) ≠ 0)]
      norm_num

private lemma sandwich_sum {s0 s1 : Matrix n n ℂ} (h0 : s0.PosSemidef) (h1 : s1.PosSemidef) :
    sandwich (midpoint ℂ s0 s1) s0 + sandwich (midpoint ℂ s0 s1) s1 =
      (midpoint ℂ s0 s1) ^ (1/3 : ℝ) := by
  rw [← inverse_third_sandwich (marginal_psd h0 h1)]
  unfold sandwich
  simp only [midpoint_eq_smul_add, invOf_eq_inv, inv_eq_one_div]
  simp only [smul_add, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

private lemma cube_root_cube {r : Matrix n n ℂ} (hr : r.PosSemidef) :
    (r ^ (1/3 : ℝ)) ^ (3 : ℕ) = r := by
  rw [← CFC.rpow_natCast (r ^ (1/3 : ℝ)) 3]
  norm_num only [Nat.cast_ofNat]
  rw [CFC.rpow_rpow_of_exponent_nonneg r (1/3) 3 (by norm_num) (by norm_num) hr.nonneg]
  norm_num [CFC.rpow_one r hr.nonneg]

private lemma sandwich_sum_cube_trace {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    trace ((sandwich (midpoint ℂ s0 s1) s0 + sandwich (midpoint ℂ s0 s1) s1) ^ (3 : ℕ)) = 1 := by
  rw [sandwich_sum h0.1 h1.1, cube_root_cube (marginal_psd h0.1 h1.1), marginal_trace h0 h1]

private lemma input_trace_moment {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    (trace ((sandwich (midpoint ℂ s0 s1) s0)^3 + (sandwich (midpoint ℂ s0 s1) s1)^3)).re =
      (1 + 3 * moment s0 s1) / 4 := by
  rw [trace_cubic_moment, sandwich_sum_cube_trace h0 h1]
  simp [moment, Complex.div_re, Complex.mul_re]

private lemma moment_nonneg {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    0 ≤ moment s0 s1 := cubic_t_nonneg (sandwich_psd h0.1) (sandwich_psd h1.1)

private lemma input_trace_range {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    (1/4 : ℝ) ≤ (trace ((sandwich (midpoint ℂ s0 s1) s0)^3 + (sandwich (midpoint ℂ s0 s1) s1)^3)).re ∧
    (trace ((sandwich (midpoint ℂ s0 s1) s0)^3 + (sandwich (midpoint ℂ s0 s1) s1)^3)).re ≤ 1 := by
  constructor
  · rw [input_trace_moment h0 h1]
    linarith [moment_nonneg h0 h1]
  · have hh := cubic_cross_nonneg (sandwich_psd (r := midpoint ℂ s0 s1) h0.1)
      (sandwich_psd (r := midpoint ℂ s0 s1) h1.1)
    rwa [sandwich_sum_cube_trace h0 h1, Complex.one_re] at hh

private lemma input_entropy_eq {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    condRenyiDown 3 (cqState s0 s1) =
      -(1/2 : ℝ) * Real.log ((1+3*moment s0 s1)/4) := by
  unfold condRenyiDown
  dsimp only
  have hm : partialTraceLeft (cqState s0 s1) = midpoint ℂ s0 s1 := by
    simpa only [midpoint_eq_smul_add, invOf_eq_inv, inv_eq_one_div] using cq_marginal s0 s1
  rw [hm, show ((1-3)/(2*3) : ℝ) = (-1/3 : ℝ) by norm_num,
    show (1/(1-3) : ℝ) = -(1/2 : ℝ) by norm_num]
  rw [sandwich_blocks]
  have hb : (blk (sandwich (midpoint ℂ s0 s1) s0) (sandwich (midpoint ℂ s0 s1) s1)).PosSemidef :=
    blk_psd (sandwich_psd h0.1) (sandwich_psd h1.1)
  have hpow := CFC.rpow_natCast _ 3 hb.nonneg
  norm_num only [Nat.cast_ofNat] at hpow
  unfold sandwich at hpow
  rw [hpow, blk_three, blk_trace, ← trace_add, RCLike.re_eq_complex_re]
  have hi := input_trace_moment h0 h1
  unfold sandwich at hi
  rw [hi]

private lemma input_entropy_exp {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    Real.exp (-2 * condRenyiDown 3 (cqState s0 s1)) = (1+3*moment s0 s1)/4 := by
  rw [input_entropy_eq h0 h1]
  have hp : 0 < (1+3*moment s0 s1)/4 := by linarith [moment_nonneg h0 h1]
  convert Real.exp_log hp using 1 <;> congr 1 <;> ring

private lemma input_entropy_range {s0 s1 : Matrix n n ℂ} (h0 : IsDensity s0) (h1 : IsDensity s1) :
    condRenyiDown 3 (cqState s0 s1) ∈ Set.Icc 0 (Real.log 2) := by
  have hk := input_trace_range h0 h1
  rw [input_trace_moment h0 h1] at hk
  have he := input_entropy_exp h0 h1
  constructor
  · have hh : Real.exp (-2*condRenyiDown 3 (cqState s0 s1)) ≤ Real.exp 0 := by
      rw [he, Real.exp_zero]
      exact hk.2
    have hl := Real.exp_le_exp.mp hh
    linarith
  · have hh : Real.exp (-2*Real.log 2) ≤ Real.exp (-2*condRenyiDown 3 (cqState s0 s1)) := by
      rw [he, exp_neg_two_log_two]
      exact hk.1
    have hl := Real.exp_le_exp.mp hh
    linarith

end
end

section
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private def out0 (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ) :=
  (1/2 : ℂ) • (s1 0 ⊗ₖ s2 0 + s1 1 ⊗ₖ s2 1)
private def out1 (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ) :=
  (1/2 : ℂ) • (s1 0 ⊗ₖ s2 1 + s1 1 ⊗ₖ s2 0)

private lemma xor_state (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ) :
    traceOutX2 (tau s1 s2) = cqState (out0 s1 s2) (out1 s1 s2) := by
  ext ⟨z,i,j⟩ ⟨w,k,l⟩
  fin_cases z <;> fin_cases w <;>
    simp [traceOutX2, tau, cqState, out0, out1, Fin.sum_univ_two, Matrix.single,
      kroneckerMap_apply] <;> ring

private lemma out_density (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ)
    (h1 : ∀ x, IsDensity (s1 x)) (h2 : ∀ x, IsDensity (s2 x)) :
    IsDensity (out0 s1 s2) ∧ IsDensity (out1 s1 s2) := by
  constructor <;> constructor
  · exact ((h1 0).1.kronecker (h2 0).1 |>.add ((h1 1).1.kronecker (h2 1).1)).smul
      (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)
  · simp [out0, trace_smul, trace_add, trace_kronecker, (h1 0).2, (h1 1).2, (h2 0).2, (h2 1).2]
    norm_num
  · exact ((h1 0).1.kronecker (h2 1).1 |>.add ((h1 1).1.kronecker (h2 0).1)).smul
      (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/2)
  · simp [out1, trace_smul, trace_add, trace_kronecker, (h1 0).2, (h1 1).2, (h2 0).2, (h2 1).2]
    norm_num

private lemma xor_marginal (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ) :
    midpoint ℂ (out0 s1 s2) (out1 s1 s2) = midpoint ℂ (s1 0) (s1 1) ⊗ₖ midpoint ℂ (s2 0) (s2 1) := by
  simp only [midpoint_eq_smul_add, invOf_eq_inv, inv_eq_one_div]
  unfold out0 out1
  simp only [add_kronecker, kronecker_add, smul_kronecker, kronecker_smul, smul_add, smul_smul]
  module

private lemma xor_sandwiches (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ)
    (h1 : ∀ x, IsDensity (s1 x)) (h2 : ∀ x, IsDensity (s2 x)) :
    let r1 := midpoint ℂ (s1 0) (s1 1)
    let r2 := midpoint ℂ (s2 0) (s2 1)
    let ro := midpoint ℂ (out0 s1 s2) (out1 s1 s2)
    sandwich ro (out0 s1 s2) =
      sandwich r1 (s1 0) ⊗ₖ sandwich r2 (s2 0) + sandwich r1 (s1 1) ⊗ₖ sandwich r2 (s2 1) ∧
    sandwich ro (out1 s1 s2) =
      sandwich r1 (s1 0) ⊗ₖ sandwich r2 (s2 1) + sandwich r1 (s1 1) ⊗ₖ sandwich r2 (s2 0) := by
  dsimp only
  rw [xor_marginal]
  unfold sandwich
  rw [kronecker_rpow (marginal_psd (h1 0).1 (h1 1).1)
    (marginal_psd (h2 0).1 (h2 1).1)]
  constructor <;> simp only [out0, out1] <;>
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ← mul_kronecker_mul,
      smul_kronecker, kronecker_smul, smul_add, smul_smul]

private lemma xor_moment (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ)
    (h1 : ∀ x, IsDensity (s1 x)) (h2 : ∀ x, IsDensity (s2 x)) :
    moment (out0 s1 s2) (out1 s1 s2) = moment (s1 0) (s1 1) * moment (s2 0) (s2 1) := by
  have hh := xor_sandwiches s1 s2 h1 h2
  dsimp only at hh
  unfold moment
  dsimp only
  rw [hh.1, hh.2]
  have hs : ∀ (A B : Matrix n n ℂ) (C D : Matrix m m ℂ),
      (A ⊗ₖ C + B ⊗ₖ D) + (A ⊗ₖ D + B ⊗ₖ C) = (A+B) ⊗ₖ (C+D) := by
    intro A B C D
    simp only [add_kronecker, kronecker_add]
    abel
  have hd : ∀ (A B : Matrix n n ℂ) (C D : Matrix m m ℂ),
      (A ⊗ₖ C + B ⊗ₖ D) - (A ⊗ₖ D + B ⊗ₖ C) = (A-B) ⊗ₖ (C-D) := by
    intro A B C D
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [kroneckerMap_apply]
    ring
  rw [hs, hd, ← mul_kronecker_mul, ← mul_kronecker_mul, trace_kronecker, Complex.mul_re]
  have hi1 : (trace
      ((sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 0) + sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 1)) *
      (sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 0) - sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 1)) *
      (sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 0) - sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 1)))).im = 0 := by
    -- Cyclic trace makes the product trace real, despite noncommutativity.
    have hs1 := (sandwich_psd (r := midpoint ℂ (s1 0) (s1 1)) (h1 0).1).1
    have hs2 := (sandwich_psd (r := midpoint ℂ (s1 0) (s1 1)) (h1 1).1).1
    have hD := hs1.sub hs2
    have hDD : ((sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 0) - sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 1))*
        (sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 0) - sandwich (midpoint ℂ (s1 0) (s1 1)) (s1 1))).IsHermitian := by
      simpa [pow_two] using hD.pow 2
    simpa only [Matrix.mul_assoc] using
      D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real _ _ (hs1.add hs2) hDD

  rw [hi1, zero_mul, sub_zero]

private lemma output_entropy_exp (s1 : Fin 2 → Matrix n n ℂ) (s2 : Fin 2 → Matrix m m ℂ)
    (h1 : ∀ x, IsDensity (s1 x)) (h2 : ∀ x, IsDensity (s2 x)) :
    Real.exp (-2 * condRenyiDown 3 (traceOutX2 (tau s1 s2))) =
      (1+3*moment (s1 0) (s1 1)*moment (s2 0) (s2 1))/4 := by
  rw [xor_state, input_entropy_exp (out_density s1 s2 h1 h2).1 (out_density s1 s2 h1 h2).2,
    xor_moment s1 s2 h1 h2]
  ring

end
end

section
noncomputable section

theorem result : claim := by
  intro n1 n2 s1 s2 h1 h2
  dsimp only
  have he : Real.exp (-2*condRenyiDown 3 (traceOutX2 (tau s1 s2))) =
      (4*Real.exp (-2*condRenyiDown 3 (cqState (s1 0) (s1 1)))*
        Real.exp (-2*condRenyiDown 3 (cqState (s2 0) (s2 1)))-
        Real.exp (-2*condRenyiDown 3 (cqState (s1 0) (s1 1)))-
        Real.exp (-2*condRenyiDown 3 (cqState (s2 0) (s2 1)))+1)/3 := by
    rw [output_entropy_exp s1 s2 h1 h2, input_entropy_exp (h1 0) (h1 1), input_entropy_exp (h2 0) (h2 1)]
    ring
  have hr := scalar_readout _ _ _ (input_entropy_range (h1 0) (h1 1))
    (input_entropy_range (h2 0) (h2 1)) he
  exact ⟨fun _ => hr.1, fun _ => hr.2⟩

end
end

#print axioms result
#print claim
end D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
