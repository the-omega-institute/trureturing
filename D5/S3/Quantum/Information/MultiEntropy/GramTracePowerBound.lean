/- GID: D5/S3/Quantum/Information/MultiEntropy/GramTracePowerBound
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound integer trace moments of rectangular unitary compressions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
import D5.S3.Quantum.Schatten.Holder

/-! The trace-power bound for a rectangular compression of a unitary. -/

open scoped Matrix MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.GramTracePowerBound

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.NormCompression.UpperBranchReduction (eigenPow schattenPow_eq_columnGram)
open CQReplicaRegroupingSupplier (tensorOp)

open private traceNorm_eq_sum_sqrt_eigenvalues from D5.S3.Quantum.Foundation.FiniteTraceDistance
open private schattenNorm_nat_pow tensor_pow rtrace_tensor_constant from
  D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining

variable {d k l : Type*}

/-- Positive trace powers are invariant under a cyclic rotation of two rectangular factors. -/
theorem trace_rectangular_mul_pow [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]
    (A : Matrix k l ℂ) (B : Matrix l k ℂ) {n : ℕ} (hn : 0 < n) :
    ((A * B) ^ n).trace = ((B * A) ^ n).trace := by
  have hintertwine (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ' (A * B), Matrix.mul_assoc, ih, pow_succ' (B * A)]
      simp only [Matrix.mul_assoc]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  calc
    ((A * B) ^ (m + 1)).trace = (A * (B * (A * B) ^ m)).trace := by
      rw [pow_succ' (A * B), Matrix.mul_assoc]
    _ = (B * ((A * B) ^ m * A)).trace := by
      rw [Matrix.trace_mul_comm A, Matrix.mul_assoc]
    _ = ((B * A) ^ (m + 1)).trace := by
      rw [hintertwine, ← Matrix.mul_assoc, pow_succ' (B * A)]

section Square

variable [Fintype d] [DecidableEq d]

private theorem schattenNorm_eq_gram (A : Matrix d d ℂ) (p : ℝ) :
    schattenNorm A p = eigenPow (p / 2) (Aᴴ * A) ^ (1 / p) := by
  unfold schattenNorm
  rw [schattenNorm_trace_as_eigenvalue_sum]
  calc
    _ = eigenPow (p / 2) (Aᴴ * (Aᴴ)ᴴ) ^ (1 / p) := by
      rw [eigenPow, dif_pos (Matrix.isHermitian_mul_conjTranspose_self Aᴴ)]
    _ = _ := by rw [Matrix.conjTranspose_conjTranspose]

private theorem schattenNorm_one_eq_traceNorm (A : Matrix d d ℂ) :
    schattenNorm A 1 = traceNorm A := by
  rw [schattenNorm_eq_gram, div_one, Real.rpow_one, traceNorm_eq_sum_sqrt_eigenvalues]
  simp only [eigenPow, dif_pos (Matrix.isHermitian_conjTranspose_mul_self A), Real.sqrt_eq_rpow]

/-- The modulus of the trace is bounded by the Schatten 1-norm. -/
theorem norm_trace_le_schattenNorm_one (A : Matrix d d ℂ) :
    ‖A.trace‖ ≤ schattenNorm A 1 := by
  rw [schattenNorm_one_eq_traceNorm]
  obtain ⟨c, hc, hcA⟩ := Complex.exists_norm_eq_mul_self A.trace
  have hcU : c ∈ unitary ℂ := by
    simp [Unitary.mem_iff, Complex.star_def, Complex.conj_mul', Complex.mul_conj', hc]
  let W : Matrix.unitaryGroup d ℂ :=
    ⟨c • (1 : Matrix d d ℂ), Unitary.smul_mem_of_mem hcU (one_mem _)⟩
  apply (traceNorm_eq_max_re_tr_U A).2
  refine ⟨W, ?_⟩
  change (((c • (1 : Matrix d d ℂ)) * A).trace).re = ‖A.trace‖
  rw [Matrix.smul_mul, one_mul, Matrix.trace_smul, smul_eq_mul, ← hcA, Complex.ofReal_re]

/-- Hölder for a power, with the reciprocal exponent adding once per factor. -/
theorem schattenNorm_pow_le (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p)
    {m : ℕ} (hm : 0 < m) :
    schattenNorm (A ^ m) (p / (m : ℝ)) ≤ schattenNorm A p ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      simp
    have hm' : 0 < m := Nat.pos_of_ne_zero hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm'
    have hsR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have he : 1 / (p / ((m + 1 : ℕ) : ℝ)) = 1 / (p / (m : ℝ)) + 1 / p := by
      simp only [Nat.cast_succ, one_div_div, add_div]
    calc
      _ ≤ schattenNorm (A ^ m) (p / (m : ℝ)) * schattenNorm A p := by
        rw [pow_succ]
        exact schattenNorm_mul_le _ _ (div_pos hp hsR) (div_pos hp hmR) hp he
      _ ≤ _ := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (ih hm') (schattenNorm_nonneg A p)

/-- The trace-power bound for an arbitrary square complex matrix. -/
theorem norm_trace_pow_le_schattenNorm (A : Matrix d d ℂ) {n : ℕ} (hn : 0 < n) :
    ‖(A ^ n).trace‖ ≤ schattenNorm A (n : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine (norm_trace_le_schattenNorm_one (A ^ n)).trans ?_
  simpa only [div_self hnR.ne'] using schattenNorm_pow_le A hnR hn

private theorem schattenNorm_unitary_mul (U A : Matrix d d ℂ) (hU : Uᴴ * U = 1)
    (p : ℝ) : schattenNorm (U * A) p = schattenNorm A p := by
  have hGram : (U * A)ᴴ * (U * A) = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Aᴴ Uᴴ (U * A),
      ← Matrix.mul_assoc Uᴴ U A, hU, one_mul]
  simp only [schattenNorm_eq_gram, hGram]

private theorem schattenNorm_posSemidef_nat_pow {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {n : ℕ} (hn : 0 < n) : schattenNorm A (n : ℝ) ^ n = (A ^ n).trace.re := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : schattenNorm A (n : ℝ) =
      D5.S3.Quantum.NormCompression.UpperBranchReduction.schattenNorm (n : ℝ) A := by
    rw [schattenNorm_eq_gram]
    unfold D5.S3.Quantum.NormCompression.UpperBranchReduction.schattenNorm
    rw [schattenPow_eq_columnGram _ hnR, eigenPow,
      dif_pos (Matrix.isHermitian_conjTranspose_mul_self A)]
  rw [he]
  exact schattenNorm_nat_pow hA hn

end Square

variable [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l]

/-- The trace power of a unitary compression is bounded by the Gram trace power. -/
theorem norm_trace_compression_pow_le (V : Matrix k l ℂ) (U : Matrix k k ℂ)
    (hU : Uᴴ * U = 1) {n : ℕ} (hn : 0 < n) :
    ‖((Vᴴ * U * V) ^ n).trace‖ ≤ ((Vᴴ * V) ^ n).trace.re := by
  rw [Matrix.mul_assoc Vᴴ U V, trace_rectangular_mul_pow Vᴴ (U * V) hn,
    Matrix.mul_assoc U V Vᴴ, trace_rectangular_mul_pow Vᴴ V hn]
  calc
    _ ≤ schattenNorm (U * (V * Vᴴ)) (n : ℝ) ^ n :=
      norm_trace_pow_le_schattenNorm _ hn
    _ = schattenNorm (V * Vᴴ) (n : ℝ) ^ n := by rw [schattenNorm_unitary_mul U _ hU]
    _ = _ := schattenNorm_posSemidef_nat_pow (Matrix.posSemidef_self_mul_conjTranspose V) hn

/-- For a tensor-power Gram matrix the right side is the bipartite trace power
raised to the replica order, as in Eq. (1.13). -/
theorem norm_trace_compression_pow_le_tensor {n : ℕ} (hn : 0 < n)
    (V : Matrix k (Fin n → l) ℂ) (U : Matrix k k ℂ) (hU : Uᴴ * U = 1)
    (B : Matrix l l ℂ) (hB : B.PosSemidef)
    (hGram : Vᴴ * V = tensorOp (fun _ : Fin n => B)) :
    ‖((Vᴴ * U * V) ^ n).trace‖ ≤ ((B ^ n).trace.re) ^ n := by
  refine (norm_trace_compression_pow_le V U hU hn).trans_eq ?_
  rw [hGram, tensor_pow]
  exact rtrace_tensor_constant (hB.pow n).isHermitian n


end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.GramTracePowerBound
