/- GID: D5/S3/QuantumBounds/NonlocalityDepthQuantumBound
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/NonlocalityDepthQuantumBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact quantum maximum of the Bernards--Gühne Bell family for every n >= 3. -/
/-
admission_basis: escape-witness
escape_witness: Upper.unweighted_bound
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16779
Direct frozen dependencies:
  D5/S1/Words/AdmissibleWords/FibonacciGrayPath (Lean declaration D5.S1.Words.AdmissibleWords.FibonacciGrayPath.hamming_cons)
    declaration statement_id: sha256:72d64a43ff42dc04adfa3c7dc61f3d864186bb2c22fcda2ed8e8d0a13cca9c25
  D5/S3/Quantum/FiniteDimensional (Lean declaration D5.S3.Quantum.FiniteDimensional.QubitMatrix)
    declaration statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
  D5/S3/Quantum/FiniteDimensional (Lean declaration D5.S3.Quantum.FiniteDimensional.qubitX)
    declaration statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/FiniteDimensional (Lean declaration D5.S3.Quantum.FiniteDimensional.qubitZ)
    declaration statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/FiniteDimensional (Lean declaration D5.S3.Quantum.FiniteDimensional.qubit_weyl_star)
    declaration statement_id: sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d
  D5/S3/Quantum/Information/PartialTraceMutualInformation (Lean declaration D5.S3.Quantum.Information.PartialTraceMutualInformation.isHermitian_kronecker)
    declaration statement_id: sha256:aaaef5099708fcb8dd0b7f84e781799b378231842fffd861c64b67bc0c621ff0
  D5/S3/Quantum/Recovery/PurifiedLocalPath (Lean declaration D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap)
    declaration statement_id: sha256:8db6e5665e7fbd3cabf2ecaff9b9ad87e606f0bf633f99375a5ad2e669dcd639
  D5/S3/QuantumBounds/HybridMerminDepthBound (Lean declaration D5.S3.QuantumBounds.HybridMerminDepthBound.phase)
    declaration statement_id: sha256:13cad8af38abe67ac7c89fcb50f465b59e63d4958c97084d2db1aadb43ddeb75
  D5/S3/Analytic/Hunter/NCHunterPositivity (Lean declaration GVHunter.sum_word_succ)
    declaration statement_id: sha256:dbf2eda8f06c7495505e44726b0bd1f721d38c12ba1720b3219e7626161ed906
  D5/S3/Weil/ZetaLinear/RankTrace (Lean declaration RHLinalg.trace_mul_nonneg_of_posSemidef)
    declaration statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
Under Convention revision 1 on #16626, claim uses IsBinaryObservable by name,
  bellOp keeps corrOp's product body literal because ProductPrefixRigidity.productMap owns it,
  and claim keeps IsDensity's body literal because SL-010 forbids importing its I owner into this G module.
The Pauli selector is the expression of StabilizerPairLocalUnitaryInequivalence.pauliMatrix
  at X or Y. Its I owner cannot be imported by this G module; no selector alias is added.
Upper.unweighted_bound establishes a new shifted all-party PSD estimate by induction;
  the signed two-party CHSH estimate is an application of Mathlib tsirelson_inequality.
Upper.unweighted_bound uses phase, isHermitian_kronecker and sum_word_succ above.
Attainment.weight_cons applies the shared FibonacciGrayPath.hamming_cons.
result uses the frozen declarations above; both have witness Upper.unweighted_bound.
The attaining phase equals -star UniformParameterAnchor.Anchor17Probe.aa;
  its I owner cannot be imported by this G module, so the scalar expression is inline.
The classification below inlines same-delivery helpers and stops at frozen owners.
proof_shape: one_add_posSemidef_of_contraction: bind-only; consumers: D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one, Upper.involution_binary
proof_shape: bellOp_eq_generalBellOp: bind-only; consumers: result, upper_binary
proof_shape: Tensor.tensor_star: bind-only; consumers: Tensor.tensor_hermitian
proof_shape: Tensor.tensor_hermitian: bind-only; consumers: Attainment.tensor_column_one
proof_shape: Block.tensor_involution: bind-only; consumers: Block.unsigned_bound
proof_shape: Block.tensor_self_adjoint: bind-only; consumers: Block.unsigned_bound
proof_shape: Block.separate_commute: bind-only; consumers: Block.unsigned_bound
proof_shape: Block.unsigned_bound: bind-only; consumers: Block.signed_bound
proof_shape: Block.real_smul_involution: bind-only; consumers: Block.signed_bound
proof_shape: Block.signed_bound: bind-only; consumers: Upper.unweighted_two
proof_shape: Dilation.defect_nonneg: bind-only; consumers: Dilation.dilation_involution
proof_shape: Dilation.dilation_hermitian: bind-only; consumers: Upper.weighted_upper_binary
proof_shape: Dilation.dilation_involution: bind-only; consumers: Upper.weighted_upper_binary
proof_shape: Upper.phase_shift: bind-only; consumers: Attainment.phaseI_period, Upper.unweighted_shift, Upper.unweighted_two
proof_shape: Upper.phase_sq: bind-only; consumers: Upper.unweighted_two
proof_shape: Upper.weight_insert: bind-only; consumers: Attainment.weighted_amplitude, Upper.unweighted_split, Upper.weighted_decomposition
proof_shape: Upper.tensor_insert: bind-only; consumers: Upper.corr_insert
proof_shape: Upper.involution_binary: bind-only; consumers: Upper.tensor_spectator, result
proof_shape: Upper.tensor_spectator: bind-only; consumers: Upper.unweighted_bound, Upper.weighted_upper
proof_shape: Upper.unweighted_eq_tensor_sum: bind-only; consumers: Upper.unweighted_split
proof_shape: Upper.corr_insert: bind-only; consumers: Upper.unweighted_split, Upper.weighted_decomposition
proof_shape: Upper.unweighted_split: bind-only; consumers: Upper.unweighted_bound
proof_shape: Upper.sum_settings_split: bind-only; consumers: Attainment.phaseI_sum, Upper.sum_settings_two
proof_shape: Upper.sum_settings_two: bind-only; consumers: Upper.unweighted_two
proof_shape: Upper.unweighted_two: bind-only; consumers: Upper.unweighted_bound
proof_shape: Upper.unweighted_shift: bind-only; consumers: Upper.unweighted_bound, Upper.weighted_upper
proof_shape: Upper.unweighted_bound: content; escape_witness: Upper.unweighted_bound; consumers: Upper.weighted_upper
proof_shape: Upper.setting_incidence: bind-only; consumers: Attainment.weighted_amplitude, Upper.weighted_decomposition
proof_shape: Upper.weighted_decomposition: bind-only; consumers: Upper.weighted_upper
proof_shape: Upper.weighted_upper: content; escape_witness: Upper.unweighted_bound; consumers: Upper.weighted_upper_binary
proof_shape: Upper.weighted_dilation_compression: bind-only; consumers: Upper.weighted_upper_binary
proof_shape: Upper.weighted_upper_binary: content; escape_witness: Upper.unweighted_bound; consumers: upper_binary
proof_shape: Attainment.phaseI_period: bind-only; consumers: Attainment.phaseI_pair
proof_shape: Attainment.phaseI_pair: bind-only; consumers: Attainment.phaseI_sum
proof_shape: Attainment.weight_cons: bind-only; consumers: Attainment.phaseI_sum
proof_shape: Attainment.phaseI_sum: bind-only; consumers: Attainment.weighted_amplitude
proof_shape: Attainment.weighted_amplitude: bind-only; consumers: Attainment.bell_column_one, Attainment.bell_column_zero
proof_shape: Attainment.pauli_hermitian: bind-only; consumers: Attainment.tensor_column_one, result
proof_shape: Attainment.pauli_involution: bind-only; consumers: result
proof_shape: Attainment.productI: bind-only; consumers: Attainment.tensor_column_zero
proof_shape: Attainment.tensor_column_zero: bind-only; consumers: Attainment.bell_column_zero, Attainment.tensor_column_one
proof_shape: Attainment.tensor_column_one: bind-only; consumers: Attainment.bell_column_one
proof_shape: Attainment.bell_column_zero: bind-only; consumers: Attainment.psi_eigenvector
proof_shape: Attainment.bell_column_one: bind-only; consumers: Attainment.psi_eigenvector
proof_shape: Attainment.eta_norm: bind-only; consumers: Attainment.eta_amplitude_star, Attainment.psi_normalized
proof_shape: Attainment.zero_ne_one: bind-only; consumers: Attainment.psi_normalized
proof_shape: Attainment.psi_normalized: bind-only; consumers: Attainment.rho_attains, Attainment.rho_trace
proof_shape: Attainment.rho_psd: bind-only; consumers: result
proof_shape: Attainment.rho_trace: bind-only; consumers: result
proof_shape: Attainment.eta_amplitude: bind-only; consumers: Attainment.eta_amplitude_star, Attainment.psi_eigenvector
proof_shape: Attainment.eta_amplitude_star: bind-only; consumers: Attainment.psi_eigenvector
proof_shape: Attainment.psi_eigenvector: bind-only; consumers: Attainment.rho_attains
proof_shape: Attainment.rho_attains: bind-only; consumers: result
proof_shape: upper_binary: content; escape_witness: Upper.unweighted_bound; consumers: result
proof_shape: expectation_upper: bind-only; consumers: result
proof_shape: result: content; escape_witness: Upper.unweighted_bound; consumers: none (final assertion)
-/
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.QuantumBounds.HybridMerminDepthBound
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S1.Words.AdmissibleWords.FibonacciGrayPath
import D5.S3.Analytic.Hunter.NCHunterPositivity


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Recovery
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.QuantumBounds.HybridMerminDepthBound (phase)

namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound

open Matrix in
theorem one_add_posSemidef_of_contraction {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : Matrix ι ι ℂ) (hH : C.IsHermitian)
    (hC : (1 - Cᴴ * C).PosSemidef) : (1 + C).PosSemidef := by
  have hp := (posSemidef_conjTranspose_mul_self (1 + C)).add hC
  have he : (1 + C)ᴴ * (1 + C) + (1 - Cᴴ * C) = (2 : ℝ) • (1 + C) := by
    rw [conjTranspose_add, conjTranspose_one, hH.eq, two_smul ℝ]
    noncomm_ring
  have h := hp.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simpa only [he, smul_smul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    one_smul] using h

def IsBinaryObservable {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  M.IsHermitian ∧ (1 - M).PosSemidef ∧ (1 + M).PosSemidef

def bellOp (n : ℕ) {d : Fin n → ℕ}
    (A : ∀ j : Fin n, Bool → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    Matrix (∀ j, Fin (d j)) (∀ j, Fin (d j)) ℂ :=
  ∑ x : Fin n → Bool,
    (((hammingDist x (fun _ => false) : ℤ) * phase (hammingDist x (fun _ => false)) : ℤ) : ℂ)
      • (fun a b => ∏ j, A j (x j) (a j) (b j))

private def generalBellOp (n : ℕ) {σ : Fin n → Type*} [∀ j, Fintype (σ j)]
    (A : ∀ j : Fin n, Bool → Matrix (σ j) (σ j) ℂ) :
    Matrix (∀ j, σ j) (∀ j, σ j) ℂ :=
  ∑ x : Fin n → Bool,
    (((hammingDist x (fun _ => false) : ℤ) * phase (hammingDist x (fun _ => false)) : ℤ) : ℂ)
      • ProductPrefixRigidity.productMap σ (fun j => A j (x j))


private lemma bellOp_eq_generalBellOp {n : ℕ} {d : Fin n → ℕ}
    (A : ∀ j, Bool → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    bellOp n A = generalBellOp n A := rfl


def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → IsGreatest
    {v : ℝ | ∃ (d : Fin n → ℕ)
      (A : ∀ j : Fin n, Bool → Matrix (Fin (d j)) (Fin (d j)) ℂ)
      (ρ : Matrix (∀ j, Fin (d j)) (∀ j, Fin (d j)) ℂ),
      (∀ j s, IsBinaryObservable (A j s)) ∧ (ρ.PosSemidef ∧ Matrix.trace ρ = 1) ∧
      v = (Matrix.trace (ρ * bellOp n A)).re}
    (Real.sqrt 2 * n * 2 ^ (n - 2))


end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor

variable {n : ℕ} {σ : Fin n → Type*} [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]

lemma tensor_star (M : ∀ j, Matrix (σ j) (σ j) ℂ) :
    ProductPrefixRigidity.productMap σ (fun j => (M j)ᴴ) = (ProductPrefixRigidity.productMap σ M)ᴴ := by
  ext a b
  simp [ProductPrefixRigidity.productMap, Matrix.conjTranspose_apply, map_prod]

private lemma tensor_hermitian (M : ∀ j, Matrix (σ j) (σ j) ℂ)
    (hM : ∀ j, (M j).IsHermitian) : (ProductPrefixRigidity.productMap σ M).IsHermitian := by
  change (ProductPrefixRigidity.productMap σ M)ᴴ = ProductPrefixRigidity.productMap σ M
  rw [← tensor_star]
  congr 1
  funext j
  exact (hM j).eq


end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor


noncomputable section
open scoped ComplexOrder MatrixOrder Kronecker
namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Block

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

private lemma tensor_involution (P : Matrix m m ℂ) (Q : Matrix k k ℂ)
    (hP : P ^ 2 = 1) (hQ : Q ^ 2 = 1) : (P ⊗ₖ Q) ^ 2 = 1 := by
  rw [pow_two, ← Matrix.mul_kronecker_mul, ← pow_two, ← pow_two, hP, hQ,
    Matrix.one_kronecker_one]

omit [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k] in
private lemma tensor_self_adjoint (P : Matrix m m ℂ) (Q : Matrix k k ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) : star (P ⊗ₖ Q) = P ⊗ₖ Q := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.isHermitian_kronecker hP hQ).eq

private lemma separate_commute (P : Matrix m m ℂ) (Q : Matrix k k ℂ) :
    (P ⊗ₖ (1 : Matrix k k ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Q) =
      ((1 : Matrix m m ℂ) ⊗ₖ Q) * (P ⊗ₖ (1 : Matrix k k ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

private lemma unsigned_bound (P0 P1 : Matrix m m ℂ) (Q0 Q1 : Matrix k k ℂ)
    (hP0 : P0.IsHermitian) (hP1 : P1.IsHermitian)
    (hQ0 : Q0.IsHermitian) (hQ1 : Q1.IsHermitian)
    (eP0 : P0 ^ 2 = 1) (eP1 : P1 ^ 2 = 1)
    (eQ0 : Q0 ^ 2 = 1) (eQ1 : Q1 ^ 2 = 1) :
    (((2 * Real.sqrt 2 : ℝ) • (1 : Matrix (m × k) (m × k) ℂ)) -
      (P0 ⊗ₖ Q0 + P0 ⊗ₖ Q1 + P1 ⊗ₖ Q0 - P1 ⊗ₖ Q1)).PosSemidef := by
  have T : IsCHSHTuple
      (P0 ⊗ₖ (1 : Matrix k k ℂ)) (P1 ⊗ₖ (1 : Matrix k k ℂ))
      ((1 : Matrix m m ℂ) ⊗ₖ Q0) ((1 : Matrix m m ℂ) ⊗ₖ Q1) :=
    { A₀_inv := tensor_involution P0 1 eP0 (by simp)
      A₁_inv := tensor_involution P1 1 eP1 (by simp)
      B₀_inv := tensor_involution 1 Q0 (by simp) eQ0
      B₁_inv := tensor_involution 1 Q1 (by simp) eQ1
      A₀_sa := tensor_self_adjoint P0 1 hP0 Matrix.isHermitian_one
      A₁_sa := tensor_self_adjoint P1 1 hP1 Matrix.isHermitian_one
      B₀_sa := tensor_self_adjoint 1 Q0 Matrix.isHermitian_one hQ0
      B₁_sa := tensor_self_adjoint 1 Q1 Matrix.isHermitian_one hQ1
      A₀B₀_commutes := separate_commute P0 Q0
      A₀B₁_commutes := separate_commute P0 Q1
      A₁B₀_commutes := separate_commute P1 Q0
      A₁B₁_commutes := separate_commute P1 Q1 }
  have ht := tsirelson_inequality _ _ _ _ T
  have hc : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact Matrix.le_iff.mp (by
    simpa only [hc, ← Matrix.mul_kronecker_mul, mul_one, one_mul] using ht)

private lemma real_smul_involution (a : ℝ) (P : Matrix m m ℂ)
    (ha : a ^ 2 = 1) (hP : P ^ 2 = 1) : (a • P) ^ 2 = 1 := by
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two, ← pow_two,
    ha, hP, one_smul]

private lemma signed_bound (P0 P1 : Matrix m m ℂ) (Q0 Q1 : Matrix k k ℂ)
    (hP0 : P0.IsHermitian) (hP1 : P1.IsHermitian)
    (hQ0 : Q0.IsHermitian) (hQ1 : Q1.IsHermitian)
    (eP0 : P0 ^ 2 = 1) (eP1 : P1 ^ 2 = 1)
    (eQ0 : Q0 ^ 2 = 1) (eQ1 : Q1 ^ 2 = 1)
    (a b : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (((2 * Real.sqrt 2 : ℝ) • (1 : Matrix (m × k) (m × k) ℂ)) -
      (a • (P0 ⊗ₖ Q0) + b • (P0 ⊗ₖ Q1) +
        b • (P1 ⊗ₖ Q0) - a • (P1 ⊗ₖ Q1))).PosSemidef := by
  have hab : (a * b) ^ 2 = 1 := by rw [mul_pow, ha, hb, one_mul]
  have ht := unsigned_bound (a • P0) (b • P1) Q0 ((a * b) • Q1)
    (hP0.smul (by simp [IsSelfAdjoint])) (hP1.smul (by simp [IsSelfAdjoint])) hQ0
    (hQ1.smul (by simp [IsSelfAdjoint]))
    (real_smul_involution a P0 ha eP0) (real_smul_involution b P1 hb eP1)
    eQ0 (real_smul_involution (a * b) Q1 hab eQ1)
  have hab1 : a * b * a = b := by
    calc a * b * a = a ^ 2 * b := by ring
         _ = b := by rw [ha, one_mul]
  have hab2 : a * b * b = a := by rw [mul_assoc, ← pow_two, hb, mul_one]
  simpa only [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, hab1, hab2] using ht


end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Block


noncomputable section
open scoped ComplexOrder MatrixOrder
open Matrix
namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation

variable {m : Type*} [Fintype m] [DecidableEq m]

private def dilation (A : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  Matrix.fromBlocks A (CFC.sqrt (1 - A ^ 2)) (CFC.sqrt (1 - A ^ 2)) (-A)

private lemma defect_nonneg (A : Matrix m m ℂ)
    (hminus : (1 - A).PosSemidef) (hplus : (1 + A).PosSemidef) :
    (1 - A ^ 2).PosSemidef := by
  have hc : Commute (1 - A) (1 + A) := by
    show (1 - A) * (1 + A) = (1 + A) * (1 - A)
    noncomm_ring
  have he : (1 - A) * (1 + A) = 1 - A ^ 2 := by noncomm_ring
  exact Matrix.nonneg_iff_posSemidef.mp (he ▸ hc.mul_nonneg hminus.nonneg hplus.nonneg)

private lemma dilation_hermitian (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    (dilation A).IsHermitian := by
  have hS : (CFC.sqrt (1 - A ^ 2)).IsHermitian :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian
  change (dilation A)ᴴ = dilation A
  simp [dilation, Matrix.fromBlocks_conjTranspose, hA.eq, hS.eq]

private lemma dilation_involution (A : Matrix m m ℂ)
    (hminus : (1 - A).PosSemidef) (hplus : (1 + A).PosSemidef) :
    (dilation A) ^ 2 = 1 := by
  have hdef := defect_nonneg A hminus hplus
  have hs : CFC.sqrt (1 - A ^ 2) * CFC.sqrt (1 - A ^ 2) = 1 - A ^ 2 :=
    CFC.sqrt_mul_sqrt_self _ hdef.nonneg
  have hc : Commute (1 - A ^ 2) A := by
    show (1 - A ^ 2) * A = A * (1 - A ^ 2)
    noncomm_ring
  have hcs : Commute (CFC.sqrt (1 - A ^ 2)) A := hc.cfcₙ_nnreal NNReal.sqrt
  have e1 : A * A + CFC.sqrt (1 - A ^ 2) * CFC.sqrt (1 - A ^ 2) = 1 := by
    rw [hs, ← pow_two]
    abel
  have e2 : A * CFC.sqrt (1 - A ^ 2) + CFC.sqrt (1 - A ^ 2) * (-A) = 0 := by
    rw [Matrix.mul_neg, ← hcs.eq]
    abel
  have e3 : CFC.sqrt (1 - A ^ 2) * A + (-A) * CFC.sqrt (1 - A ^ 2) = 0 := by
    rw [Matrix.neg_mul, hcs.eq]
    abel
  have e4 : CFC.sqrt (1 - A ^ 2) * CFC.sqrt (1 - A ^ 2) + (-A) * (-A) = 1 := by
    rw [neg_mul_neg, add_comm]
    exact e1
  rw [pow_two]
  unfold dilation
  rw [Matrix.fromBlocks_multiply, e1, e2, e3, e4, Matrix.fromBlocks_one]


end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.QuantumBounds.HybridMerminDepthBound (phase)
open D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor
namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper

private lemma phase_shift (h : ℕ) : phase (h + 2) = -phase h := by
  unfold phase
  have he : 1 + (h + 2 + 1) / 2 = 1 + (h + 1) / 2 + 1 := by omega
  rw [he, pow_succ]
  ring

private lemma phase_sq (h : ℕ) : (phase h : ℝ) ^ 2 = 1 := by
  simp only [phase, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private lemma weight_insert {n : ℕ} (j : Fin (n + 1)) (b : Bool) (x : Fin n → Bool) :
    hammingDist (Fin.insertNth (α := fun _ => Bool) j b x) (fun _ => false) =
      (if b then 1 else 0) + hammingDist x (fun _ => false) := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false]
  rw [Fin.sum_univ_succAbove _ j]
  simp

private lemma tensor_insert {n : ℕ} {σ : Fin (n + 1) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ)
    (x : Fin (n + 1) → Bool) (j : Fin (n + 1)) :
    ProductPrefixRigidity.productMap σ (fun j => A j (x j)) =
      (A j (x j) ⊗ₖ ProductPrefixRigidity.productMap (fun i => σ (j.succAbove i))
        (fun i => A (j.succAbove i) (x (j.succAbove i)))).submatrix
        (Fin.insertNthEquiv σ j).symm (Fin.insertNthEquiv σ j).symm := by
  ext a b
  change (∏ i, A i (x i) (a i) (b i)) = A j (x j) (a j) (b j) *
    ∏ i, A (j.succAbove i) (x (j.succAbove i)) (a (j.succAbove i)) (b (j.succAbove i))
  exact (Fin.mul_prod_removeNth j (fun i => A i (x i) (a i) (b i))).symm

lemma involution_binary {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (eA : A ^ 2 = 1) :
    (1 - A).PosSemidef ∧ (1 + A).PosSemidef := by
  have defect (B : Matrix m m ℂ) (hB : B.IsHermitian) (eB : B ^ 2 = 1) :
      (1 - Bᴴ * B).PosSemidef := by
    simpa only [hB.eq, ← pow_two, eB, sub_self] using
      (Matrix.PosSemidef.zero : (0 : Matrix m m ℂ).PosSemidef)
  have hm := D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.one_add_posSemidef_of_contraction (-A) hA.neg (defect (-A) hA.neg (by simpa using eA))
  exact ⟨by simpa only [sub_eq_add_neg] using hm, D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.one_add_posSemidef_of_contraction A hA (defect A hA eA)⟩

private lemma tensor_spectator {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (A : Matrix m m ℂ) (B : Matrix k k ℂ)
    (hA : A.IsHermitian) (eA : A ^ 2 = 1) (q : ℝ)
    (hp : (q • (1 : Matrix k k ℂ) - B).PosSemidef)
    (hm : (q • (1 : Matrix k k ℂ) + B).PosSemidef) :
    (q • (1 : Matrix (m × k) (m × k) ℂ) - A ⊗ₖ B).PosSemidef := by
  have hAb := involution_binary A hA eA
  have hs := ((hAb.2.kronecker hp).add (hAb.1.kronecker hm)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have he : (1 + A) ⊗ₖ (q • 1 - B) + (1 - A) ⊗ₖ (q • 1 + B) =
      (2 : ℝ) • (q • (1 : Matrix (m × k) (m × k) ℂ) - A ⊗ₖ B) := by
    have hone : (1 : Matrix (m × k) (m × k) ℂ) =
        (1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix k k ℂ) := Matrix.one_kronecker_one.symm
    rw [hone]
    ext a b
    simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Complex.real_smul, Complex.ofReal_ofNat]
    ring
  rw [he, smul_smul] at hs
  norm_num at hs
  exact hs

def unweighted {n : ℕ} {σ : Fin n → Type*} [∀ j, Fintype (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) (r : ℕ) :
    Matrix (∀ j, σ j) (∀ j, σ j) ℂ :=
  ∑ x : Fin n → Bool,
    ((phase (hammingDist x (fun _ => false) + r) : ℤ) : ℂ) •
      ((fun a b => ∏ j, A j (x j) (a j) (b j)) : Matrix (∀ j, σ j) (∀ j, σ j) ℂ)


private lemma unweighted_eq_tensor_sum {n : ℕ} {σ : Fin n → Type*}
    [∀ j, Fintype (σ j)] (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) (r : ℕ) :
    unweighted A r = ∑ x : Fin n → Bool,
      ((phase (hammingDist x (fun _ => false) + r) : ℤ) : ℂ) • ProductPrefixRigidity.productMap σ (fun j => A j (x j)) := rfl


private lemma corr_insert {n : ℕ} {σ : Fin (n + 1) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) (j : Fin (n + 1)) (b : Bool)
    (x : Fin n → Bool) :
    ProductPrefixRigidity.productMap σ (fun i => A i ((Fin.insertNth (α := fun _ => Bool) j b x) i)) =
      (A j b ⊗ₖ ProductPrefixRigidity.productMap (fun i => σ (j.succAbove i))
        (fun i => A (j.succAbove i) (x i))).submatrix
        (Fin.insertNthEquiv σ j).symm (Fin.insertNthEquiv σ j).symm := by
  rw [tensor_insert A _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private lemma unweighted_split {n : ℕ} {σ : Fin (n + 1) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) (j : Fin (n + 1)) (r : ℕ) :
    unweighted A r =
      (A j false ⊗ₖ unweighted (fun i => A (j.succAbove i)) r +
       A j true ⊗ₖ unweighted (fun i => A (j.succAbove i)) (r + 1)).submatrix
        (Fin.insertNthEquiv σ j).symm (Fin.insertNthEquiv σ j).symm := by
  refine (unweighted_eq_tensor_sum A r).trans ?_
  simp only [unweighted_eq_tensor_sum]
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ x : Fin n → Bool,
    (phase (hammingDist (Fin.insertNth (α := fun _ => Bool) j b x) (fun _ => false) + r) : ℂ) •
      ProductPrefixRigidity.productMap σ (fun i => A i ((Fin.insertNth (α := fun _ => Bool) j b x) i))) = _
  simp only [Fintype.sum_bool, weight_insert, Bool.false_eq_true,
    if_false, if_true, zero_add, corr_insert]
  ext a b
  simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.add_apply, Finset.mul_sum, mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_comm, mul_left_comm]

private lemma sum_settings_split {R : Type*} [AddCommMonoid R] {n : ℕ}
    (f : (Fin (n + 1) → Bool) → R) :
    (∑ x, f x) = ∑ u : Fin n → Bool, (f (Fin.cons false u) + f (Fin.cons true u)) := by
  rw [← (Equiv.piCongrRight (fun _ : Fin (n + 1) => finTwoEquiv)).sum_comp f]
  rw [GVHunter.sum_word_succ, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  rw [← (Equiv.piCongrRight (fun _ : Fin n => finTwoEquiv)).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  congr 1 <;> congr 1 <;> funext j <;> cases j using Fin.cases <;> rfl

private lemma sum_settings_two {R : Type*} [AddCommMonoid R] (f : (Fin 2 → Bool) → R) :
    (∑ x, f x) = f ![false, false] + f ![false, true] +
      f ![true, false] + f ![true, true] := by
  rw [sum_settings_split, sum_settings_split]
  have hc (b0 b1 : Bool) (u : Fin 0 → Bool) :
      Fin.cons b0 (Fin.cons b1 u) = ![b0, b1] := by
    exact List.ofFn_inj.mp rfl
  simp only [Fintype.sum_unique, hc, add_assoc]
  abel

private lemma unweighted_two {σ : Fin 2 → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ)
    (hA : ∀ j s, (A j s).IsHermitian) (eA : ∀ j s, (A j s) ^ 2 = 1)
    (r : ℕ) :
    ((2 * Real.sqrt 2 : ℝ) • (1 : Matrix (∀ j, σ j) (∀ j, σ j) ℂ) -
      unweighted A r).PosSemidef := by
  let e : (∀ j, σ j) → σ 0 × σ 1 := fun a => (a 0, a 1)
  have he : Function.Injective e := (piFinTwoEquiv σ).injective
  let C : Matrix (σ 0 × σ 1) (σ 0 × σ 1) ℂ :=
    (phase r : ℝ) • (A 0 false ⊗ₖ A 1 false) +
      (phase (r + 1) : ℝ) • (A 0 false ⊗ₖ A 1 true) +
      (phase (r + 1) : ℝ) • (A 0 true ⊗ₖ A 1 false) -
      (phase r : ℝ) • (A 0 true ⊗ₖ A 1 true)
  have hC := D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Block.signed_bound (A 0 false) (A 0 true) (A 1 false) (A 1 true)
    (hA 0 false) (hA 0 true) (hA 1 false) (hA 1 true)
    (eA 0 false) (eA 0 true) (eA 1 false) (eA 1 true)
    (phase r) (phase (r + 1)) (phase_sq r) (phase_sq (r + 1))
  have hOp : unweighted A r = C.submatrix e e := by
    simp only [unweighted_eq_tensor_sum]
    rw [sum_settings_two]
    have h00 : hammingDist (![false, false] : Fin 2 → Bool) (fun _ => false) = 0 := rfl
    have h01 : hammingDist (![false, true] : Fin 2 → Bool) (fun _ => false) = 1 := rfl
    have h10 : hammingDist (![true, false] : Fin 2 → Bool) (fun _ => false) = 1 := rfl
    have h11 : hammingDist (![true, true] : Fin 2 → Bool) (fun _ => false) = 2 := rfl
    simp only [h00, h01, h10, h11, zero_add]
    ext a b
    simp [ProductPrefixRigidity.productMap, Matrix.sum_apply, C, e, Matrix.kroneckerMap_apply, Complex.real_smul,
      smul_eq_mul, phase_shift, Nat.add_comm, add_assoc] <;> ring
  have hp := hC.submatrix e
  rw [hOp]
  simpa [C, Matrix.submatrix_sub, Matrix.submatrix_smul, Matrix.submatrix_one e he] using hp

private lemma unweighted_shift {n : ℕ} {σ : Fin n → Type*} [∀ j, Fintype (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) (r : ℕ) :
    unweighted A (r + 2) = -unweighted A r := by
  simp only [unweighted_eq_tensor_sum, ← Nat.add_assoc, phase_shift, Int.cast_neg,
    neg_smul, Finset.sum_neg_distrib]

lemma unweighted_bound (k : ℕ) :
    ∀ {σ : Fin (k + 2) → Type*} [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
      (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ),
      (∀ j s, (A j s).IsHermitian) → (∀ j s, (A j s) ^ 2 = 1) →
      ∀ r : ℕ, ((Real.sqrt 2 * 2 ^ (k + 1)) •
        (1 : Matrix (∀ j, σ j) (∀ j, σ j) ℂ) - unweighted A r).PosSemidef := by
  induction k with
  | zero =>
    intro σ _ _ A hA eA r
    simpa [mul_comm] using unweighted_two A hA eA r
  | succ k ih =>
    intro σ _ _ A hA eA r
    let At : ∀ i : Fin (k + 2), Bool → Matrix (σ ((0 : Fin (k + 3)).succAbove i)) (σ ((0 : Fin (k + 3)).succAbove i)) ℂ :=
      fun i => A ((0 : Fin (k + 3)).succAbove i)
    let q : ℝ := Real.sqrt 2 * 2 ^ (k + 1)
    have htail (s : ℕ) :
        (q • (1 : Matrix (∀ i : Fin (k + 2), σ ((0 : Fin (k + 3)).succAbove i)) (∀ i : Fin (k + 2), σ ((0 : Fin (k + 3)).succAbove i)) ℂ)
          - unweighted At s).PosSemidef := ih At (fun i => hA ((0 : Fin (k + 3)).succAbove i)) (fun i => eA ((0 : Fin (k + 3)).succAbove i)) s
    have htailminus (s : ℕ) :
        (q • (1 : Matrix (∀ i : Fin (k + 2), σ ((0 : Fin (k + 3)).succAbove i)) (∀ i : Fin (k + 2), σ ((0 : Fin (k + 3)).succAbove i)) ℂ)
          + unweighted At s).PosSemidef := by
      simpa only [unweighted_shift, sub_neg_eq_add] using htail (s + 2)
    have hs0 := tensor_spectator (A 0 false) (unweighted At r)
      (hA 0 false) (eA 0 false) q (htail r) (htailminus r)
    have hs1 := tensor_spectator (A 0 true) (unweighted At (r + 1))
      (hA 0 true) (eA 0 true) q (htail (r + 1)) (htailminus (r + 1))
    have hp := (hs0.add hs1).submatrix (Fin.insertNthEquiv σ 0).symm
    have hsplit := unweighted_split A 0 r
    rw [hsplit]
    have hq : Real.sqrt 2 * 2 ^ (k.succ + 1) = q + q := by
      simp only [Nat.succ_add, pow_succ, q]
      ring
    rw [hq]
    convert hp using 1
    simp only [Matrix.submatrix_add, Matrix.submatrix_sub, Matrix.submatrix_smul,
      add_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [Matrix.submatrix_one ((Fin.insertNthEquiv σ 0).symm)
      ((Fin.insertNthEquiv σ 0).symm.injective)]
    dsimp [At]
    abel

private lemma setting_incidence {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : (Fin (n + 1) → Bool) → R) :
    (∑ x, hammingDist x (fun _ => false) • f x) =
      ∑ j : Fin (n + 1), ∑ y : Fin n → Bool, f (Fin.insertNth j true y) := by
  classical
  have point (x : Fin (n + 1) → Bool) :
      hammingDist x (fun _ => false) • f x = ∑ j, if x j then f x else 0 := by
    simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
      Bool.not_eq_false, Finset.sum_smul, ite_smul, one_nsmul, zero_nsmul]
  simp_rw [point]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.insertNthEquiv, Fintype.univ_bool]

private lemma weighted_decomposition {n : ℕ} {σ : Fin (n + 1) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) :
    generalBellOp _ A = ∑ j : Fin (n + 1),
      (A j true ⊗ₖ unweighted (fun i => A (j.succAbove i)) 1).submatrix
        (Fin.insertNthEquiv σ j).symm (Fin.insertNthEquiv σ j).symm := by
  unfold generalBellOp
  simp only [Int.cast_mul, Int.cast_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
  rw [setting_incidence]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [weight_insert, corr_insert]
  ext a b
  simp [unweighted_eq_tensor_sum, Matrix.sum_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Finset.mul_sum, mul_assoc, mul_left_comm, Nat.add_comm]

private lemma weighted_upper (k : ℕ) {σ : Fin (k + 3) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ)
    (hA : ∀ j s, (A j s).IsHermitian) (eA : ∀ j s, (A j s) ^ 2 = 1) :
    ((Real.sqrt 2 * (k + 3) * 2 ^ (k + 1) : ℝ) •
      (1 : Matrix (∀ j, σ j) (∀ j, σ j) ℂ) - generalBellOp _ A).PosSemidef := by
  let q : ℝ := Real.sqrt 2 * 2 ^ (k + 1)
  have hterm (j : Fin (k + 3)) :
      (q • (1 : Matrix (∀ j, σ j) (∀ j, σ j) ℂ) -
        (A j true ⊗ₖ unweighted (fun i => A (j.succAbove i)) 1).submatrix
          (Fin.insertNthEquiv σ j).symm (Fin.insertNthEquiv σ j).symm).PosSemidef := by
    have hp := unweighted_bound k (fun i => A (j.succAbove i))
      (fun i => hA (j.succAbove i)) (fun i => eA (j.succAbove i)) 1
    have hm := unweighted_bound k (fun i => A (j.succAbove i))
      (fun i => hA (j.succAbove i)) (fun i => eA (j.succAbove i)) 3
    have hm' : (q • 1 + unweighted (fun i => A (j.succAbove i)) 1).PosSemidef := by
      simpa only [show 3 = 1 + 2 by rfl, unweighted_shift, sub_neg_eq_add] using hm
    have hs := (tensor_spectator (A j true) (unweighted (fun i => A (j.succAbove i)) 1)
      (hA j true) (eA j true) q hp hm').submatrix (Fin.insertNthEquiv σ j).symm
    simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul,
      Pi.sub_apply, Pi.smul_apply, Matrix.submatrix_one _ (Fin.insertNthEquiv σ j).symm.injective] using hs
  have hsum := Matrix.posSemidef_sum Finset.univ (fun j _ => hterm j)
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← weighted_decomposition] at hsum
  convert hsum using 1
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  dsimp [q]
  push_cast
  ring

private lemma weighted_dilation_compression {n : ℕ} {σ : Fin n → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ) :
    (generalBellOp _ (fun j s => D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation.dilation (A j s))).submatrix
      (fun a j => Sum.inl (a j)) (fun a j => Sum.inl (a j)) = generalBellOp _ A := by
  ext a b
  simp [generalBellOp, ProductPrefixRigidity.productMap, D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation.dilation, Matrix.sum_apply, Matrix.submatrix_apply]

private lemma weighted_upper_binary (k : ℕ) {σ : Fin (k + 3) → Type*}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (A : ∀ j, Bool → Matrix (σ j) (σ j) ℂ)
    (hA : ∀ j s, (A j s).IsHermitian)
    (hminus : ∀ j s, (1 - A j s).PosSemidef)
    (hplus : ∀ j s, (1 + A j s).PosSemidef) :
    ((Real.sqrt 2 * (k + 3) * 2 ^ (k + 1) : ℝ) •
      (1 : Matrix (∀ j, σ j) (∀ j, σ j) ℂ) - generalBellOp _ A).PosSemidef := by
  let e : (∀ j, σ j) → (∀ j, σ j ⊕ σ j) := fun a j => Sum.inl (a j)
  have he : Function.Injective e := Function.Injective.piMap (fun _ => Sum.inl_injective)
  have hp := (weighted_upper k (fun j s => D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation.dilation (A j s))
    (fun j s => D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation.dilation_hermitian (A j s) (hA j s))
    (fun j s => D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Dilation.dilation_involution (A j s) (hminus j s) (hplus j s))).submatrix e
  simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
    Matrix.submatrix_one e he, e, weighted_dilation_compression] using hp


end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.QuantumBounds.HybridMerminDepthBound (phase)
open D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper
namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment

private def phaseI (h : ℕ) : ℂ := (phase h : ℂ) * Complex.I ^ h

private lemma phaseI_period (h : ℕ) : phaseI (h + 2) = phaseI h := by
  simp only [phaseI, phase_shift, Int.cast_neg, pow_add, Complex.I_sq]
  ring

private lemma phaseI_pair (h : ℕ) : phaseI h + phaseI (h + 1) = -1 + Complex.I := by
  induction h with
  | zero => norm_num [phaseI, phase]
  | succ h ih =>
    change phaseI (h + 1) + phaseI (h + 2) = _
    rw [phaseI_period, add_comm]
    exact ih

private lemma weight_cons {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    hammingDist (Fin.cons b x) (fun _ => false) =
      (if b then 1 else 0) + hammingDist x (fun _ => false) := by
  have h := D5.S1.Words.AdmissibleWords.FibonacciGrayPath.hamming_cons b false x (fun _ => false)
  change hammingDist (Fin.cons b x)
    (Fin.cons ((fun _ : Fin (n + 1) => false) 0) (Fin.tail (fun _ => false))) = _ at h
  rw [Fin.cons_self_tail (fun _ : Fin (n + 1) => false)] at h
  cases b <;> simpa using h

private lemma phaseI_sum (m : ℕ) :
    (∑ x : Fin (m + 1) → Bool, phaseI (hammingDist x (fun _ => false) + 1)) =
      (2 : ℂ) ^ m * (-1 + Complex.I) := by
  rw [sum_settings_split]
  simp_rw [weight_cons]
  simp only [Bool.false_eq_true, if_false, if_true, zero_add]
  have he (h : ℕ) : 1 + h + 1 = (h + 1) + 1 := by omega
  simp_rw [he, phaseI_pair]
  simp [Fintype.card_fun, nsmul_eq_mul] <;> ring

private lemma weighted_amplitude (m : ℕ) :
    (∑ x : Fin (m + 2) → Bool,
      (((hammingDist x (fun _ => false) : ℤ) * phase (hammingDist x (fun _ => false)) : ℤ) : ℂ) *
        Complex.I ^ hammingDist x (fun _ => false)) =
      ((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I) := by
  simp only [Int.cast_mul, Int.cast_natCast, mul_assoc]
  change (∑ x : Fin (m + 2) → Bool,
    (hammingDist x (fun _ => false) : ℂ) * phaseI (hammingDist x (fun _ => false))) = _
  have he := setting_incidence (fun x : Fin (m + 2) → Bool => phaseI (hammingDist x (fun _ => false)))
  simp only [nsmul_eq_mul] at he
  rw [he]
  simp_rw [weight_insert]
  simp only [if_true]
  simp_rw [Nat.add_comm 1, phaseI_sum]
  simp [nsmul_eq_mul, mul_assoc]
  left
  ring

private lemma pauli_hermitian (s : Bool) : ((fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) s).IsHermitian := by
  have hw := qubit_weyl_star
  have hx : qubitXᴴ = qubitX := by simpa only [Matrix.star_eq_conjTranspose] using hw.2.1
  have hz : qubitZᴴ = qubitZ := by simpa only [Matrix.star_eq_conjTranspose] using hw.2.2.1
  cases s
  · change qubitX.IsHermitian
    exact hx
  · change (Complex.I • (qubitX * qubitZ))ᴴ = Complex.I • (qubitX * qubitZ)
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hx, hz, hw.1,
      Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]


private lemma pauli_involution (s : Bool) : ((fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) s) ^ 2 = 1 := by
  have hw := qubit_weyl_star
  cases s
  · change qubitX ^ 2 = 1
    exact hw.2.2.2.1
  · have hp : (qubitX * qubitZ) * (qubitX * qubitZ) = -1 := by
      calc
        _ = qubitX * (qubitZ * qubitX) * qubitZ := by simp only [Matrix.mul_assoc]
        _ = -(qubitX * qubitX) * (qubitZ * qubitZ) := by
          rw [hw.1]
          simp only [mul_neg, neg_mul, Matrix.mul_assoc]
        _ = -1 := by rw [← pow_two, ← pow_two, hw.2.2.2.1, hw.2.2.2.2, neg_mul, one_mul]
    change (Complex.I • (qubitX * qubitZ)) ^ 2 = 1
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hp, Complex.I_mul_I,
      neg_one_smul, neg_neg]


private lemma productI {n : ℕ} (x : Fin n → Bool) :
    (∏ j, if x j then Complex.I else 1) = Complex.I ^ hammingDist x (fun _ => false) := by
  have hw : hammingDist x (fun _ => false) = ∑ j, if x j then 1 else 0 := by
    simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false]
  rw [hw, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases hx : x j <;> simp

private lemma tensor_column_zero {n : ℕ} (x : Fin n → Bool) (a : Fin n → Fin 2) :
    ProductPrefixRigidity.productMap (fun _ => Fin 2) (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)) a (fun _ : Fin n => (0 : Fin 2)) =
      if a = (fun _ : Fin n => (1 : Fin 2)) then Complex.I ^ hammingDist x (fun _ => false) else 0 := by
  classical
  by_cases h : a = (fun _ : Fin n => (1 : Fin 2))
  · subst a
    simp only [ProductPrefixRigidity.productMap]
    simp [Matrix.ite_apply, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
    exact productI x
  · obtain ⟨j, hj⟩ : ∃ j, a j ≠ 1 := by
      by_contra h'
      push Not at h'
      exact h (funext h')
    have haj : a j = 0 := by omega
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Matrix.ite_apply, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, haj]

private lemma tensor_column_one {n : ℕ} (x : Fin n → Bool) (a : Fin n → Fin 2) :
    ProductPrefixRigidity.productMap (fun _ => Fin 2) (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)) a (fun _ : Fin n => (1 : Fin 2)) =
      if a = (fun _ : Fin n => (0 : Fin 2)) then star (Complex.I ^ hammingDist x (fun _ => false)) else 0 := by
  classical
  have ht := (tensor_hermitian (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)) (fun j => pauli_hermitian (x j))).eq
  change (ProductPrefixRigidity.productMap (fun _ => Fin 2) (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)))ᴴ = ProductPrefixRigidity.productMap (fun _ => Fin 2) (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)) at ht
  have he := congrArg (fun M => M (fun _ : Fin n => (1 : Fin 2)) a) ht
  simp only [Matrix.conjTranspose_apply] at he
  have hlocal : ProductPrefixRigidity.productMap (fun _ => Fin 2) (fun j => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX) (x j)) (fun _ : Fin n => (1 : Fin 2)) a =
      if a = (fun _ : Fin n => (0 : Fin 2)) then Complex.I ^ hammingDist x (fun _ => false) else 0 := by
    by_cases h : a = (fun _ : Fin n => (0 : Fin 2))
    · subst a
      simp [tensor_column_zero]
    · obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
        by_contra h'
        push Not at h'
        exact h (funext h')
      have haj : a j = 1 := by omega
      rw [if_neg h]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Matrix.ite_apply, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, haj]
  rw [hlocal] at he
  apply star_injective
  by_cases h : a = (fun _ : Fin n => (0 : Fin 2))
  · simpa only [if_pos h, star_star] using he
  · simpa only [if_neg h, star_zero] using he

private lemma bell_column_zero (m : ℕ) (a : Fin (m + 2) → Fin 2) :
    generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)) a ((fun _ : Fin (m + 2) => (0 : Fin 2))) =
      if a = (fun _ : Fin (m + 2) => (1 : Fin 2)) then ((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I) else 0 := by
  classical
  simp only [generalBellOp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensor_column_zero]
  by_cases h : a = (fun _ : Fin (m + 2) => (1 : Fin 2))
  · simpa only [if_pos h] using weighted_amplitude m
  · simp [h]

private lemma bell_column_one (m : ℕ) (a : Fin (m + 2) → Fin 2) :
    generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)) a ((fun _ : Fin (m + 2) => (1 : Fin 2))) =
      if a = (fun _ : Fin (m + 2) => (0 : Fin 2)) then star (((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I)) else 0 := by
  classical
  simp only [generalBellOp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensor_column_one]
  by_cases h : a = (fun _ : Fin (m + 2) => (0 : Fin 2))
  · simp only [if_pos h]
    have he := congrArg star (weighted_amplitude m)
    simpa only [star_sum, star_mul, star_intCast, mul_comm] using he
  · simp [h]

private def psi (n : ℕ) : (Fin n → Fin 2) → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Pi.single (fun _ : Fin n => (0 : Fin 2)) 1 + ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) • Pi.single (fun _ : Fin n => (1 : Fin 2)) 1)

private lemma eta_norm : ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * star ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) = 1 := by
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) TsirelsonInequality.sqrt_two_inv_mul_self
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat] using he
  simp only [div_eq_mul_inv, star_mul, star_add, star_neg, star_one,
    Complex.star_def, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  calc
    _ = ((-1 + Complex.I) * (-1 - Complex.I)) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = 1 := by rw [hinv]; norm_num; ring_nf; norm_num

private lemma zero_ne_one (n : ℕ) (hn : 0 < n) : (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ : Fin n => (1 : Fin 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Function.const_injective.ne (by decide : (0 : Fin 2) ≠ 1)

private lemma psi_normalized (n : ℕ) (hn : 0 < n) : psi n ⬝ᵥ star (psi n) = 1 := by
  classical
  have h01 := zero_ne_one n hn
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) TsirelsonInequality.sqrt_two_inv_mul_self
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat] using he
  simp only [psi, star_smul, star_add, Pi.star_single, star_one,
    star_inv₀, Complex.star_def, Complex.conj_ofReal,
    smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add,
    single_dotProduct, Pi.single_apply, if_pos rfl, if_neg h01, if_neg h01.symm,
    smul_eq_mul, Pi.smul_apply]
  simp only [ite_true, mul_one, mul_zero, zero_add, add_zero]
  change (Real.sqrt 2 : ℂ)⁻¹ *
    ((Real.sqrt 2 : ℂ)⁻¹ + star ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)⁻¹ * ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)))) = 1
  calc
    _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * (1 + ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * star ((-1 + Complex.I) / (Real.sqrt 2 : ℂ))) := by ring
    _ = 1 := by rw [hinv, eta_norm]; norm_num

private lemma rho_psd (n : ℕ) : ((Matrix.vecMulVec (psi n) (star (psi n)))).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (psi n)

private lemma rho_trace (n : ℕ) (hn : 0 < n) : Matrix.trace ((Matrix.vecMulVec (psi n) (star (psi n)))) = 1 := by
  rw [Matrix.trace_vecMulVec, psi_normalized n hn]

private lemma eta_amplitude (m : ℕ) :
    ((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I) =
      (Real.sqrt 2 * (m + 2) * 2 ^ m : ℝ) * ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) := by
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Nat.cast_add, Nat.cast_ofNat]
  push_cast
  field_simp

private lemma eta_amplitude_star (m : ℕ) :
    ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * star (((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I)) =
      (Real.sqrt 2 * (m + 2) * 2 ^ m : ℝ) := by
  rw [eta_amplitude]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  change ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * (star ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)) * (Real.sqrt 2 * (m + 2) * 2 ^ m : ℝ)) = _
  rw [← mul_assoc, eta_norm, one_mul]

private lemma psi_eigenvector (m : ℕ) :
    generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)) *ᵥ psi (m + 2) =
      (Real.sqrt 2 * (m + 2) * 2 ^ m : ℝ) • psi (m + 2) := by
  classical
  have h0 : generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)) *ᵥ Pi.single ((fun _ : Fin (m + 2) => (0 : Fin 2))) 1 =
      (((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I)) • Pi.single ((fun _ : Fin (m + 2) => (1 : Fin 2))) 1 := by
    rw [Matrix.mulVec_single_one]
    ext a
    simp [Matrix.col, bell_column_zero, Pi.single_apply]
  have h1 : generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)) *ᵥ Pi.single ((fun _ : Fin (m + 2) => (1 : Fin 2))) 1 =
      star (((m + 2 : ℕ) : ℂ) * 2 ^ m * (-1 + Complex.I)) • Pi.single ((fun _ : Fin (m + 2) => (0 : Fin 2))) 1 := by
    rw [Matrix.mulVec_single_one]
    ext a
    simp [Matrix.col, bell_column_one, Pi.single_apply]
  simp only [psi, Matrix.mulVec_smul, Matrix.mulVec_add, h0, h1]
  ext a
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc ((-1 + Complex.I) / (Real.sqrt 2 : ℂ)), eta_amplitude_star, eta_amplitude]
  ring

private lemma rho_attains (m : ℕ) :
    Matrix.trace ((Matrix.vecMulVec (psi (m + 2)) (star (psi (m + 2)))) * generalBellOp (m + 2) (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX))) =
      (Real.sqrt 2 * (m + 2) * 2 ^ m : ℝ) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, psi_eigenvector,
    Matrix.trace_vecMulVec, smul_dotProduct, psi_normalized (m + 2) (by omega)]
  simp

end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment


noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace D5.S3.QuantumBounds.NonlocalityDepthQuantumBound

private lemma upper_binary (k : ℕ) {d : Fin (k + 3) → ℕ}
    (A : ∀ j, Bool → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hA : ∀ j s, ((A j s).IsHermitian ∧ (1 - A j s).PosSemidef ∧ (1 + A j s).PosSemidef)) :
    ((Real.sqrt 2 * (k + 3) * 2 ^ (k + 1) : ℝ) •
      (1 : Matrix (∀ j, Fin (d j)) (∀ j, Fin (d j)) ℂ) - bellOp (k + 3) A).PosSemidef := by
  rw [bellOp_eq_generalBellOp]
  exact D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper.weighted_upper_binary k A (fun j s => (hA j s).1)
      (fun j s => (hA j s).2.1) (fun j s => (hA j s).2.2)

lemma expectation_upper {m : Type*} [Fintype m] [DecidableEq m]
    (rho B : Matrix m m ℂ) (q : ℝ) (hr : (rho.PosSemidef ∧ Matrix.trace rho = 1))
    (hp : (q • (1 : Matrix m m ℂ) - B).PosSemidef) :
    (Matrix.trace (rho * B)).re ≤ q := by
  have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hr.1 hp
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, hr.2, smul_eq_mul, Complex.real_smul, mul_one,
    Complex.sub_re, Complex.ofReal_re] at ht
  exact sub_nonneg.mp ht

theorem result : claim := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have he : k + 3 - 2 = k + 1 := by omega
  rw [he]
  refine ⟨?_, ?_⟩
  · refine ⟨(fun _ => 2), (fun _ => (fun s : Bool => if s then Complex.I • (qubitX * qubitZ) else qubitX)), (Matrix.vecMulVec (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.psi (k + 3)) (star (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.psi (k + 3)))), ?_, ?_, ?_⟩
    · intro j s
      exact ⟨D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.pauli_hermitian s,
        D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper.involution_binary _ (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.pauli_hermitian s)
          (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.pauli_involution s)⟩
    · exact ⟨D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.rho_psd _, D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.rho_trace _ (by omega)⟩
    · rw [bellOp_eq_generalBellOp]
      have ha := congrArg Complex.re (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Attainment.rho_attains (k + 1))
      convert ha.symm using 1
      · simp only [Complex.ofReal_re]
        push_cast
        ring
  · rintro v ⟨d, A, rho, hA, hr, rfl⟩
    apply expectation_upper rho _ _ hr
    simpa only [Nat.cast_add, Nat.cast_ofNat] using upper_binary k A hA

end D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
