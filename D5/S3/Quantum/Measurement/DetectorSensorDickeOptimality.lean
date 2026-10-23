/- GID: D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/DetectorSensorDickeOptimality
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Balanced Dicke probes optimize detector-sensor identification. -/
/-
proof_shape and consumer map (names in this module namespace; escape_witness: none):
fire: bind-only; consumers=G_diag,G_phase,G_total,G_total_moment,N_diag,N_psd,average_gram_overlap,dicke_attainment,dicke_gram,dicke_gram_invariant,fire_normSq,global_success_upper_bound,isoSuccess,isoSuccess_gram,result,sum_N | isoSuccess: bind-only; consumers=claim,dicke_attainment,global_success_upper_bound,isoSuccess_gram(type),result | rCount: bind-only; consumers=claim,counts_partition,ratio,ratio_formula,result
lCount: bind-only; consumers=claim,counts_partition,lCount_pair_independent,lCount_perm,lCount_self,lCount_sum,pair_count_product,ratio,ratio_formula,result | T: bind-only; consumers=claim,global_success_upper_bound,result,threshold_range,threshold_small_nonneg | claim: bind-only; consumers=result(type); owners=Nat.lt_of_add_left_lt,Nat.zero_lt_of_lt
N_psd: bind-only; consumers=global_success_upper_bound | sum_N: bind-only; consumers=global_success_upper_bound | N_diag: bind-only; consumers=isoSuccess_gram
isoSuccess_gram: bind-only; consumers=dicke_attainment,global_success_upper_bound | phase_normSq: bind-only; consumers=fire_normSq | fire_normSq: bind-only; consumers=G_diag
G_diag: bind-only; consumers=average_gram_overlap | G_phase: bind-only; consumers=G_total,dicke_gram_invariant | G_total: bind-only; consumers=G_total_moment; owners=Eq.symm,Finset.sum_comm
phase_euler: bind-only; consumers=phase_sum | phase_sum: bind-only; consumers=phase_sum_normSq | phase_sum_normSq: bind-only; consumers=G_total_moment
avgMatrix: bind-only; consumers=average_gram_overlap,avgMatrix_diag,avgMatrix_eq_of_invariant,avgMatrix_invariant,avgMatrix_total,dicke_gram,global_success_upper_bound,invariant_constant_offDiagonal,sum_avgN | avgN: bind-only; consumers=avgN_objective,avgN_psd(type),global_success_upper_bound,sum_avgN | avgN_psd: bind-only; consumers=global_success_upper_bound
sum_avgN: bind-only; consumers=global_success_upper_bound | avgN_objective: bind-only; consumers=global_success_upper_bound | avgMatrix_invariant: bind-only; consumers=invariant_constant_offDiagonal
perm_pair_exists: bind-only; consumers=invariant_constant_offDiagonal,lCount_pair_independent | invariant_constant_offDiagonal: bind-only; consumers=average_gram_overlap; owners=Nat.lt_of_succ_le,Nat.zero_lt_of_lt | weight_class_card: bind-only; consumers=counts_partition,dicke_moment,dicke_normalized,pair_count_product
counts_partition: bind-only; consumers=ratio_formula | weight_le: bind-only; consumers=G_total_moment,moment_bounds | balanced_product_upper: bind-only; consumers=moment_bounds,ratio_minimizer_balanced; owners=Nat.zero_lt_succ
weight_permWord: bind-only; consumers=dicke_gram_invariant,lCount_perm | lCount_perm: bind-only; consumers=lCount_pair_independent | lCount_pair_independent: bind-only; consumers=pair_count_product
different_bits_row: bind-only; consumers=different_bits_total | different_bits_total: bind-only; consumers=pair_count_product | lCount_self: bind-only; consumers=pair_count_product
lCount_sum: bind-only; consumers=pair_count_product | pair_count_product: bind-only; consumers=ratio_formula; owners=Eq.symm,Finset.sum_comm,Finset.sum_const_nat | psd_cauchy_schwarz: bind-only; consumers=rank_certificate
outer_quadratic: bind-only; consumers=rank_certificate | rank_certificate: bind-only; consumers=constant_diagonal_gram_bound; owners=Matrix.mulVec_single_one,Pi.star_single,single_one_dotProduct | gram_decomposition_to_povm: bind-only; consumers=constant_diagonal_gram_bound
trace_rank_mul: bind-only; consumers=constant_diagonal_gram_bound | constant_diagonal_gram_bound: bind-only; consumers=constant_overlap_certificate | d: bind-only; consumers=H_diag,constant_overlap_certificate,d_antitone,d_hasDerivAt,d_nonneg,dicke_attainment,global_success_upper_bound,result
H: bind-only; consumers=H_diag,H_mul_Hinv,H_psd(type),H_sq,Hinv_mul_H,constant_overlap_certificate,dicke_attainment | J_psd: bind-only; consumers=P_psd | P_psd: bind-only; consumers=H_psd,Hinv_hermitian,Q_psd
P_sq: bind-only; consumers=H_sq,Hinv_mul_H,PQ_zero,QP_zero,Q_psd,Q_sq | Q_psd: bind-only; consumers=H_psd,Hinv_hermitian | PQ_zero: bind-only; consumers=H_sq,Hinv_mul_H
QP_zero: bind-only; consumers=H_sq,Hinv_mul_H | Q_sq: bind-only; consumers=H_sq,Hinv_mul_H | H_psd: bind-only; consumers=constant_overlap_certificate,dicke_attainment
H_sq: bind-only; consumers=constant_overlap_certificate,dicke_attainment; owners=Nat.zero_lt_of_lt | H_diag: bind-only; consumers=constant_overlap_certificate,dicke_attainment | d_nonneg: bind-only; consumers=constant_overlap_certificate,global_success_upper_bound
constant_overlap_certificate: bind-only; consumers=global_success_upper_bound; owners=Nat.zero_lt_of_lt | moment: bind-only; consumers=G_total_moment,average_gram_overlap,dicke_gram,dicke_moment,moment_bounds,overlap,overlap_bounds | overlap: bind-only; consumers=average_gram_overlap,dicke_gram,global_success_upper_bound,overlap_bounds
cstar: bind-only; consumers=cstar_cos,cstar_lt_one,dicke_attainment,dicke_gram,global_success_upper_bound,overlap_bounds,result,threshold_range,threshold_small_nonneg | moment_bounds: bind-only; consumers=overlap_bounds; owners=Nat.cast_nonneg',Real.arith_mean_weighted_of_constant | G_total_moment: bind-only; consumers=average_gram_overlap
avgMatrix_total: bind-only; consumers=average_gram_overlap | avgMatrix_diag: bind-only; consumers=average_gram_overlap | constant_overlap_total: bind-only; consumers=average_gram_overlap
average_gram_overlap: bind-only; consumers=dicke_gram,global_success_upper_bound | overlap_bounds: bind-only; consumers=global_success_upper_bound; owners=zero_le_four | balanced_product_exact: bind-only; consumers=ceiling_floor_ratio,ratio_minimizer_balanced
balanced_floor_positive: bind-only; consumers=cstar_lt_one | ceiling_floor_ratio: bind-only; consumers=cstar_cos | cstar_cos: bind-only; consumers=threshold_small_nonneg
threshold_small_nonneg: bind-only; consumers=threshold_range | threshold_range: bind-only; consumers=global_success_upper_bound,result | cstar_lt_one: bind-only; consumers=global_success_upper_bound,result
dprime: bind-only; consumers=d_antitone,d_hasDerivAt | d_hasDerivAt: bind-only; consumers=d_antitone | d_antitone: bind-only; consumers=global_success_upper_bound
ratio: bind-only; consumers=ratio_formula,ratio_minimizer_balanced,result | ratio_formula: bind-only; consumers=ratio_minimizer_balanced | ratio_minimizer_balanced: bind-only; consumers=result
dicke_normalized: bind-only; consumers=dicke_gram | dicke_gram_invariant: bind-only; consumers=dicke_gram | global_success_upper_bound: bind-only; consumers=result; owners=Nat.le_of_add_left_le,Nat.one_div_cast_nonneg,Nat.one_le_of_lt,Nat.zero_lt_of_lt
avgMatrix_eq_of_invariant: bind-only; consumers=dicke_gram | dicke_moment: bind-only; consumers=dicke_gram | dicke_gram: bind-only; consumers=result; owners=Nat.le_of_add_left_le
Hinv: bind-only; consumers=H_mul_Hinv,Hinv_hermitian(type),Hinv_mul_H,dicke_attainment | Hinv_hermitian: bind-only; consumers=dicke_attainment | Hinv_mul_H: bind-only; consumers=H_mul_Hinv,dicke_attainment; owners=Nat.zero_lt_of_lt
H_mul_Hinv: bind-only; consumers=dicke_attainment | E_psd: bind-only; consumers=sqrt_povm_exists | sum_E: bind-only; consumers=sqrt_povm_exists
sqrt_povm_exists: bind-only; consumers=dicke_attainment | square_root_diag: bind-only; consumers=dicke_attainment; owners=Matrix.diagonal_single,Matrix.single_eq_single_vecMulVec_single,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.mulVec_single_one,Matrix.single_one_vecMul  | dicke_attainment: bind-only; consumers=result; owners=Nat.one_le_of_lt,Nat.zero_lt_of_lt
result: bind-only; consumers=external-settling-result; owners=Nat.le_of_add_left_le,Nat.lt_of_add_left_lt,Nat.zero_lt_of_lt
rank_certificate.hii: bind-only; consumers=rank_certificate; owners=Pi.star_single,Matrix.mulVec_single_one,single_one_dotProduct
admission_basis: open-problem-resolution (#16668; Proved)
Direct frozen dependencies (owner GID; full Lean name; declaration statement_id):
D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise; D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM; sha256:259693a020b62c1cb3d3f9ba876f60edcf1b53e2616110c155f1e0765419db6d
D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise; D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM.complete; sha256:7eae06ac4525739183bde6d931ce6e264193b63ac8b82f67b112dfab516b237b
D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise; D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM.effect; sha256:e4c4b0609596ec62b349548f34b016a48e5f0a03f6f97b922af09f0d8f61a8a0
D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise; D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM.mk; sha256:14b2c3287dc8a6739f94451438065ff12f7a5add3d0353a396893bb2d6c5c030
D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise; D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM.positive; sha256:520dba18ac0209daf713fe532abfbb4b1a3da00fce40512cdf9db4e810d5c21f
D5/S3/Quantum/Measurement/AntidistinguishabilityGram; D5.S3.Quantum.Measurement.AntidistinguishabilityGram.hermitian_projection_complement_psd; sha256:f3cb74fbe3632aad2eae16e435345e87d531afa9b1e0e3b5fce022abec66b3ad
D5/S3/Quantum/Measurement/AntidistinguishabilityGram; D5.S3.Quantum.Measurement.AntidistinguishabilityGram.matrix_penrose_exists; sha256:513144412204993724a7d6fa4dad279c6f19c6d6086bd62ce5fefe72d6ab8f3e
D5/S3/Quantum/Measurement/AntidistinguishabilityGram; D5.S3.Quantum.Measurement.AntidistinguishabilityGram.psd_summand_projection; sha256:39658a336acceab2655f45c7b440ee5b1ce94d5857afe693e59a9d9b2d8d5236
D5/S3/Quantum/Recovery/PurifiedLocalPath; D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram; sha256:0d9f33a80e1ac7a06b318c665f644b5f59c6a7e2165b62fda1db1cf395ea82e7
D5/S3/Quantum/Reduction/IsometricCompression; D5.S3.Quantum.Reduction.IsometricCompression.compress; sha256:ece129ea3121d41eb72b96831bf50f675e9fccf3bae2b5d39dc556c28adb9beb
D5/S3/Weil/ZetaLinear/RankTrace; RHLinalg.trace_mul_nonneg_of_posSemidef; sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
The claim inlines the weight formula and retains its quantifiers; LocalPOVM supplies the measurement type.
The explicit factor 1/n supplies the uniform mean in isoSuccess; Finset.expect is used for permutation averages.
Matrix.transpose forms the fired-state matrix; ProductPrefixRigidity.gram and
IsometricCompression.compress supply its Gram matrix and pulled-back effects.
The Fin 2 weight owner DynamicCoolingParallelTieUniqueness and the phase owner
DelayedRemoteControlDimensionWitness are I-level; this G-level module uses their expressions inline.
Private helpers organize the Gram average, trace certificate and attaining measurement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16824.
-/
import D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Reduction.IsometricCompression
import D5.S3.Weil.ZetaLinear.RankTrace
noncomputable section
open Matrix
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram
def fire {n : ℕ} (θ : ℝ) (i : Fin n) (ψ : (Fin n → Bool) → ℂ) :
    (Fin n → Bool) → ℂ :=
  fun x => Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I) * ψ x
def isoSuccess {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)
    (M : LocalPOVM (Fin n → Bool) (Fin n)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (star (fire θ i ψ) ⬝ᵥ (M.effect i *ᵥ fire θ i ψ)).re
def rCount (n : ℕ) (i j : Fin n) (k : ℕ) :=
  (Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k ∧ x i = x j)).card
def lCount (n : ℕ) (i j : Fin n) (k : ℕ) :=
  (Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k ∧ x i ≠ x j)).card
def T (n : ℕ) : ℝ :=
  let q := (n + 1) / 2
  Real.arccos (-(((q : ℝ) - 1) / q)) / 2
def claim : Prop := ∀ n : ℕ, ∀ hn : 3 ≤ n, ∀ θ : ℝ, ((0 < θ ∧ θ ≤ T n) ∨ (Real.pi - T n ≤ θ ∧ θ < Real.pi)) →
  ∀ l : ℕ, l ≤ n →
    IsMinOn (fun k : ℕ => ((rCount n ⟨0, by exact Nat.zero_lt_of_lt hn⟩ ⟨1, by exact Nat.lt_of_add_left_lt hn⟩ k : ℝ) + Real.cos (2 * θ) * lCount n ⟨0, by exact Nat.zero_lt_of_lt hn⟩ ⟨1, by exact Nat.lt_of_add_left_lt hn⟩ k) / ((rCount n ⟨0, by exact Nat.zero_lt_of_lt hn⟩ ⟨1, by exact Nat.lt_of_add_left_lt hn⟩ k : ℝ) + lCount n ⟨0, by exact Nat.zero_lt_of_lt hn⟩ ⟨1, by exact Nat.lt_of_add_left_lt hn⟩ k)) (Set.Iic n) l →
  ∀ φ : (Fin n → Bool) → ℂ, (∀ x, Complex.normSq (φ x) = if (Finset.univ.filter (fun j => x j = true)).card = l then 1 / (n.choose l : ℝ) else 0) →
  ∀ ψ : (Fin n → Bool) → ℂ, ∑ x, Complex.normSq (ψ x) = 1 →
  ∀ M : LocalPOVM (Fin n → Bool) (Fin n), ∃ M' : LocalPOVM (Fin n → Bool) (Fin n), isoSuccess θ ψ M ≤ isoSuccess θ φ M'
private theorem N_psd {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (M : LocalPOVM (Fin n → Bool) (Fin n)) (i : Fin n) : ((D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i ψ)ᵀ) (M.effect i))).PosSemidef :=
  (M.positive i).conjTranspose_mul_mul_same (((fun i => fire θ i ψ)ᵀ))
private theorem sum_N {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (M : LocalPOVM (Fin n → Bool) (Fin n)) : ∑ i, (D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i ψ)ᵀ) (M.effect i)) = (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) := by
  simp only [D5.S3.Quantum.Reduction.IsometricCompression.compress, D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram, ← Matrix.sum_mul, ← Matrix.mul_sum, M.complete, Matrix.mul_one]
private theorem N_diag {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (M : LocalPOVM (Fin n → Bool) (Fin n)) (i : Fin n) :     (D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i ψ)ᵀ) (M.effect i)) i i = star (fire θ i ψ) ⬝ᵥ (M.effect i *ᵥ fire θ i ψ) := by
  rw [D5.S3.Quantum.Reduction.IsometricCompression.compress, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]
private theorem isoSuccess_gram {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (M : LocalPOVM (Fin n → Bool) (Fin n)) :     isoSuccess θ ψ M = (1 / (n : ℝ)) * ∑ i, ((D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i ψ)ᵀ) (M.effect i)) i i).re := by
  simp only [isoSuccess, N_diag, div_eq_mul_inv, one_mul]
private theorem phase_normSq (θ : ℝ) (b : Bool) : Complex.normSq ((Complex.exp ((if b then 1 else -1) * (θ : ℂ) * Complex.I))) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := Complex.norm_exp_ofReal_mul_I ((if b then 1 else -1) * θ)
  push_cast at h
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_neg] at h
  rw [h, one_pow]
private theorem fire_normSq {n : ℕ} (θ : ℝ) (i : Fin n) (ψ : (Fin n → Bool) → ℂ)     (x : Fin n → Bool) : Complex.normSq (fire θ i ψ x) = Complex.normSq (ψ x) := by
  change Complex.normSq ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)) * ψ x) = _
  rw [Complex.normSq_mul, phase_normSq, one_mul]
private theorem G_diag {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (hψ : ∑ x, Complex.normSq (ψ x) = 1) (i : Fin n) : (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) i i = 1 := by
  simp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose, Matrix.of_apply]
  have h : ∀ x, star (fire θ i ψ x) * fire θ i ψ x = (Complex.normSq (ψ x) : ℂ) := by
    intro x
    exact (Complex.normSq_eq_conj_mul_self (z := fire θ i ψ x)).symm.trans
      (congrArg Complex.ofReal (fire_normSq θ i ψ x))
  simp only [h, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
private theorem G_phase {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ) (i j : Fin n) :     (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) i j = ∑ x, (Complex.normSq (ψ x) : ℂ) *       star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) := by
  simp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro x _
  change star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)) * ψ x) * ((Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) * ψ x) = _
  rw [star_mul, Complex.normSq_eq_conj_mul_self]
  change (star (ψ x) * star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)))) * ((Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) * ψ x) =
    (star (ψ x) * ψ x) * star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I))
  ring
private theorem G_total {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ) :     (∑ i : Fin n, ∑ j : Fin n, (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) i j).re =       ∑ x, Complex.normSq (ψ x) * Complex.normSq (∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) := by
  have he : ∑ i : Fin n, ∑ j : Fin n, (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) i j =
      ∑ x, (Complex.normSq (ψ x) : ℂ) *
        (Complex.normSq (∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) : ℂ) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ x, (Complex.normSq (ψ x) : ℂ) *
          star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) := by simp only [G_phase]
      _ = ∑ i : Fin n, ∑ x, ∑ j : Fin n, (Complex.normSq (ψ x) : ℂ) *
          star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ x, ∑ i : Fin n, ∑ j : Fin n, (Complex.normSq (ψ x) : ℂ) *
          star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) := by exact Eq.symm Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Complex.normSq_eq_conj_mul_self (z := ∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)))]
        change ∑ i : Fin n, ∑ j : Fin n, (Complex.normSq (ψ x) : ℂ) *
          star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) * (Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)) =
          (Complex.normSq (ψ x) : ℂ) * (star (∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) *
            (∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))))
        simp only [star_sum, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he]
  simp [Complex.re_sum, Complex.mul_re]
private theorem phase_euler (θ : ℝ) (b : Bool) : (Complex.exp ((if b then 1 else -1) * (θ : ℂ) * Complex.I)) =     if b then (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I     else (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  · simpa only [↓reduceIte, one_mul] using
      Complex.exp_ofReal_mul_I θ
private theorem phase_sum {n : ℕ} (θ : ℝ) (x : Fin n → Bool) :     ∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)) =       (n : ℂ) * Real.cos θ + ((2 * (Finset.univ.filter (fun j => x j = true)).card : ℕ) - (n : ℂ)) * Real.sin θ * Complex.I := by
  simp only [phase_euler]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => x i = true)
  have hc : (Finset.univ.filter (fun i => ¬ x i = true)).card = n - (Finset.univ.filter (fun j => x j = true)).card := by
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change (Finset.univ.filter (fun j => x j = true)).card + _ = n at h
    omega
  have hw : (Finset.univ.filter (fun j => x j = true)).card ≤ n := card_finset_fin_le _
  rw [hc]
  change ((Finset.univ.filter (fun j => x j = true)).card : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) +
    ((n - (Finset.univ.filter (fun j => x j = true)).card : ℕ) : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) = _
  rw [Nat.cast_sub hw]
  push_cast
  ring
private theorem phase_sum_normSq {n : ℕ} (θ : ℝ) (x : Fin n → Bool) :     Complex.normSq (∑ i : Fin n, (Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I))) =       (n : ℝ)^2 - 4 * ((Finset.univ.filter (fun j => x j = true)).card : ℝ) * (n - (Finset.univ.filter (fun j => x j = true)).card) * Real.sin θ ^ 2 := by
  rw [phase_sum]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im]
  simp only [Complex.natCast_re, Complex.natCast_im]
  push_cast
  have hsc : (n : ℝ)^2 * (Real.sin θ^2 + Real.cos θ^2) = (n : ℝ)^2 := by
    rw [Real.sin_sq_add_cos_sq]
    ring
  nlinarith [hsc]
private def avgMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Finset.expect Finset.univ (fun σ : Equiv.Perm (Fin n) => B.submatrix σ σ)
private def avgN {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Finset.expect Finset.univ (fun σ : Equiv.Perm (Fin n) => (B (σ i)).submatrix σ σ)
private theorem avgN_psd {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℂ)     (hB : ∀ i, (B i).PosSemidef) (i : Fin n) : (avgN B i).PosSemidef := by
  exact (Finset.expect_nonneg (s := Finset.univ)
    (f := fun σ : Equiv.Perm (Fin n) => (B (σ i)).submatrix σ σ)
    (fun σ _ => ((hB (σ i)).submatrix σ).nonneg)).posSemidef
private theorem sum_avgN {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℂ) :     ∑ i, avgN B i = avgMatrix (∑ i, B i) := by
  ext j k
  simp only [avgN, avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact Equiv.sum_comp σ (fun i => B i (σ j) (σ k))
private theorem avgN_objective {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℂ) :     ∑ i, (avgN B i i i).re = ∑ i, (B i i i).re := by
  let w : ℝ := 1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  have he : ∀ σ : Equiv.Perm (Fin n), ∑ i, (B (σ i) (σ i) (σ i)).re =
      ∑ i, (B i i i).re := fun σ => Equiv.sum_comp σ (fun i => (B i i i).re)
  calc
    _ = w * ∑ i, ∑ σ : Equiv.Perm (Fin n), (B (σ i) (σ i) (σ i)).re := by
      simp only [avgN, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.re_sum, Finset.mul_sum, w]
    _ = w * ∑ σ : Equiv.Perm (Fin n), ∑ i, (B (σ i) (σ i) (σ i)).re := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, w]
      field_simp
private theorem avgMatrix_invariant {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)     (τ : Equiv.Perm (Fin n)) (i j : Fin n) :     avgMatrix B (τ i) (τ j) = avgMatrix B i j := by
  simp only [avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => B (σ i) (σ j))
private theorem perm_pair_exists {α : Type*} [DecidableEq α] (a b c d : α)     (hab : a ≠ b) (hcd : c ≠ d) :     ∃ σ : Equiv.Perm α, σ a = c ∧ σ b = d := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : Bool => if x then b else a)
    (fun x : Bool => if x then d else c)
    (Bool.injective_iff.mpr hab)
    (Bool.injective_iff.mpr hcd)
  exact ⟨σ, hσ false, hσ true⟩
private theorem invariant_constant_offDiagonal {n : ℕ} (hn : 2 ≤ n)     (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) :     ∃ c : ℝ, ∀ i j : Fin n, i ≠ j → avgMatrix B i j = (c : ℂ) := by
  let a : Fin n := ⟨0, by exact Nat.zero_lt_of_lt hn⟩
  let b : Fin n := ⟨1, by exact Nat.lt_of_succ_le hn⟩
  have hab : a ≠ b := not_eq_of_beq_eq_false rfl
  have he : ∀ i j : Fin n, i ≠ j → avgMatrix B i j = avgMatrix B a b := by
    intro i j hij
    obtain ⟨σ, ha, hb⟩ := perm_pair_exists a b i j hab hij
    simpa only [ha, hb] using avgMatrix_invariant B σ a b
  have hherm : (avgMatrix B).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
      star_smul, star_trivial, star_sum, hB.apply]
  have hswap := he b a hab.symm
  have hstar : star (avgMatrix B a b) = avgMatrix B a b := by
    rw [hherm.apply b a, hswap]
  have him : (avgMatrix B a b).im = 0 := Complex.conj_eq_iff_im.mp hstar
  refine ⟨(avgMatrix B a b).re, ?_⟩
  intro i j hij
  rw [he i j hij]
  exact Complex.ext rfl him
set_option backward.isDefEq.respectTransparency false in
private theorem weight_class_card (n k : ℕ) :     (Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k)).card = n.choose k := by
  classical
  have he : ∀ x : Fin n → Bool, (Finset.univ.filter (fun j => x j = true)).card = k ↔ ((((Equiv.arrowCongr (Equiv.refl (Fin n)) Equiv.propEquivBool.symm).trans (Equiv.ofBijective Set.ofPred Set.ofPred_bijective)).trans Fintype.finsetEquivSet.symm) x).card = k :=
    fun x => by
      have hx : ((((Equiv.arrowCongr (Equiv.refl (Fin n)) Equiv.propEquivBool.symm).trans (Equiv.ofBijective Set.ofPred Set.ofPred_bijective)).trans
          Fintype.finsetEquivSet.symm) x) = Finset.univ.filter (fun j => x j = true) := by
        ext j
        rw [Equiv.trans_apply, Fintype.finsetEquivSet_symm_apply]
        simp [Equiv.arrowCongr, Equiv.propEquivBool, Equiv.ofBijective]
      rw [hx]
  have hc := Finset.card_equiv (s := Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k))
    (t := Finset.univ.filter (fun s : Finset (Fin n) => s.card = k))
    ((((Equiv.arrowCongr (Equiv.refl (Fin n)) Equiv.propEquivBool.symm).trans (Equiv.ofBijective Set.ofPred Set.ofPred_bijective)).trans Fintype.finsetEquivSet.symm)) (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact he x)
  rw [hc]
  simp
private theorem counts_partition (n : ℕ) (i j : Fin n) (k : ℕ) :     rCount n i j k + lCount n i j k = n.choose k := by
  rw [← weight_class_card n k]
  simp only [rCount, lCount]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k))
    (p := fun x => x i = x j)
  simpa only [Finset.filter_filter] using h
private theorem weight_le {n : ℕ} (x : Fin n → Bool) : (Finset.univ.filter (fun j => x j = true)).card ≤ n := by
  exact card_finset_fin_le _
private theorem balanced_product_upper (n k : ℕ) (hk : k ≤ n) :     k * (n - k) ≤ n ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by exact Nat.zero_lt_succ 3 : 0 < 4)).mpr
  simpa only [Nat.add_sub_of_le hk, mul_assoc, mul_comm, mul_left_comm] using
    (four_mul_le_sq_add k (n - k))
private theorem weight_permWord {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :     (Finset.univ.filter (fun j => ((Equiv.arrowCongr σ.symm (Equiv.refl Bool)) x) j = true)).card = (Finset.univ.filter (fun j => x j = true)).card := by
  apply Finset.card_equiv σ
  intro j
  change (j ∈ Finset.univ.filter (fun j => x (σ j) = true)) ↔
    (σ j ∈ Finset.univ.filter (fun j => x j = true))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
private theorem lCount_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (k : ℕ) :     lCount n (σ i) (σ j) k = lCount n i j k := by
  unfold lCount
  apply Finset.card_equiv ((Equiv.arrowCongr σ.symm (Equiv.refl Bool)))
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, weight_permWord]
  rfl
private theorem lCount_pair_independent {n : ℕ} (i j a b : Fin n)     (hij : i ≠ j) (hab : a ≠ b) (k : ℕ) : lCount n i j k = lCount n a b k := by
  obtain ⟨σ, ha, hb⟩ := perm_pair_exists a b i j hab hij
  simpa only [ha, hb] using lCount_perm σ a b k
private theorem different_bits_row {n : ℕ} (x : Fin n → Bool) (i : Fin n) :     (∑ j : Fin n, if x i ≠ x j then 1 else 0 : ℕ) =       if x i then n - (Finset.univ.filter (fun j => x j = true)).card else (Finset.univ.filter (fun j => x j = true)).card := by
  rw [Finset.sum_boole]
  cases hi : x i
  · simp only [Bool.false_eq_true, if_false, Nat.cast_id]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_comm.trans Bool.ne_false_iff
  · simp only [if_true, Nat.cast_id]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun j => x j = true)
    have he : (Finset.univ.filter (fun j => true ≠ x j)).card =
        (Finset.univ.filter (fun j => ¬ x j = true)).card := by
      simp only [ne_comm]
    rw [he]
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
private theorem different_bits_total {n : ℕ} (x : Fin n → Bool) :     (∑ i : Fin n, ∑ j : Fin n, if x i ≠ x j then 1 else 0 : ℕ) =       2 * (Finset.univ.filter (fun j => x j = true)).card * (n - (Finset.univ.filter (fun j => x j = true)).card) := by
  simp only [different_bits_row]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun j => x j = true)
  have he : (Finset.univ.filter (fun j => ¬ x j = true)).card = n - (Finset.univ.filter (fun j => x j = true)).card := by
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change (Finset.univ.filter (fun j => x j = true)).card + _ = n at h
    omega
  simp only [he]
  change (Finset.univ.filter (fun j => x j = true)).card * (n - (Finset.univ.filter (fun j => x j = true)).card) + (n - (Finset.univ.filter (fun j => x j = true)).card) * (Finset.univ.filter (fun j => x j = true)).card = _
  ring
private theorem lCount_self (n : ℕ) (i : Fin n) (k : ℕ) : lCount n i i k = 0 := by
  simp [lCount]
private theorem lCount_sum (n : ℕ) (i j : Fin n) (k : ℕ) :     lCount n i j k = ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k),       if x i ≠ x j then 1 else 0 := by
  rw [Finset.sum_boole]
  simp [lCount, Finset.filter_filter]
private theorem pair_count_product (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :     lCount n a b k * (n * (n - 1)) = 2 * k * (n - k) * n.choose k := by
  let S := Finset.univ.filter (fun x : Fin n → Bool => (Finset.univ.filter (fun j => x j = true)).card = k)
  have hrow (i : Fin n) : ∑ j, lCount n i j k = (n - 1) * lCount n a b k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), lCount_self, add_zero]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, lCount n a b k := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lCount_pair_independent i j a b
          (fun h => (Finset.mem_erase.mp hj).1 h.symm) hab k
      _ = _ := by simp
  have htotal : ∑ i : Fin n, ∑ j : Fin n, lCount n i j k =
      ∑ x ∈ S, 2 * (Finset.univ.filter (fun j => x j = true)).card * (n - (Finset.univ.filter (fun j => x j = true)).card) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ x ∈ S, if x i ≠ x j then 1 else 0 := by
        simp only [lCount_sum, S]
      _ = ∑ i : Fin n, ∑ x ∈ S, ∑ j : Fin n, if x i ≠ x j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ x ∈ S, ∑ i : Fin n, ∑ j : Fin n, if x i ≠ x j then 1 else 0 := by exact Eq.symm Finset.sum_comm
      _ = _ := by simp only [different_bits_total]
  have hrhs : ∑ x ∈ S, 2 * (Finset.univ.filter (fun j => x j = true)).card * (n - (Finset.univ.filter (fun j => x j = true)).card) =
      S.card * (2 * k * (n - k)) := by
    calc
      _ = ∑ x ∈ S, 2 * k * (n - k) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hw := (Finset.mem_filter.mp hx).2
        rw [hw]
      _ = _ := by exact Finset.sum_const_nat fun x => congrFun rfl
  rw [hrhs] at htotal
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  have hcard : S.card = n.choose k := weight_class_card n k
  rw [hcard] at htotal
  nlinarith [htotal]
private theorem psd_cauchy_schwarz {h : Type*} [Fintype h] [DecidableEq h]     (H : Matrix h h ℂ) (hH : H.PosSemidef) (x y : h → ℂ) :     ‖star x ⬝ᵥ (H *ᵥ y)‖ ^ 2 ≤       (star x ⬝ᵥ (H *ᵥ x)).re * (star y ⬝ᵥ (H *ᵥ y)).re := by
  let := Matrix.toSeminormedAddCommGroup H hH
  let := Matrix.toInnerProductSpace H hH
  have hc := @inner_mul_inner_self_le ℂ (h → ℂ) _ _ _ x y
  rw [norm_inner_symm y x] at hc
  change ‖(H *ᵥ y) ⬝ᵥ star x‖ * ‖(H *ᵥ y) ⬝ᵥ star x‖ ≤
    ((H *ᵥ x) ⬝ᵥ star x).re * ((H *ᵥ y) ⬝ᵥ star y).re at hc
  simpa only [dotProduct_comm, pow_two] using hc
private theorem outer_quadratic {h : Type*} [Fintype h] (v z : h → ℂ) :     star z ⬝ᵥ (Matrix.vecMulVec v (star v) *ᵥ z) =       (star z ⬝ᵥ v) * (star v ⬝ᵥ z) := by
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, mul_comm]
private theorem rank_certificate {h : Type*} [Fintype h] [DecidableEq h]     (H : Matrix h h ℂ) (hH : H.PosSemidef) (i : h) :     ((H i i).re • H - Matrix.vecMulVec (H.col i) (star (H.col i))).PosSemidef := by
  have hd : 0 ≤ (H i i).re := Complex.nonneg_iff.mp hH.diag_nonneg |>.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hH.smul hd).isHermitian.sub (Matrix.posSemidef_vecMulVec_self_star (H.col i)).isHermitian)
  intro z
  have hc := psd_cauchy_schwarz H hH (Pi.single i 1) z
  have hsingle : star (Pi.single i (1 : ℂ) : h → ℂ) = (Pi.single i 1 : h → ℂ) := by
    simpa only [star_one] using Pi.star_single (R := fun _ : h => ℂ) i (1 : ℂ)
  have hcol : star (H.col i) = H i := by
    funext j
    exact hH.isHermitian.apply i j
  have hi : star (Pi.single i (1 : ℂ)) ⬝ᵥ (H *ᵥ z) = star (H.col i) ⬝ᵥ z := by
    rw [hsingle, dotProduct_comm, dotProduct_single_one, hcol]
    rfl
  have hii : star (Pi.single i (1 : ℂ)) ⬝ᵥ (H *ᵥ Pi.single i 1) = H i i := by
    rw [Pi.star_single, star_one, Matrix.mulVec_single_one, single_one_dotProduct]
    rfl
  rw [hi, hii] at hc
  have he : star z ⬝ᵥ (Matrix.vecMulVec (H.col i) (star (H.col i)) *ᵥ z) =
      (Complex.normSq (star (H.col i) ⬝ᵥ z) : ℂ) := by
    rw [outer_quadratic, Matrix.star_dotProduct]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, he]
  have hsmul : star z ⬝ᵥ ((H i i).re • (H *ᵥ z)) =
      ((H i i).re : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    simpa only [Complex.real_smul] using
      dotProduct_smul (H i i).re (star z) (H *ᵥ z)
  rw [hsmul]
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq] using sub_nonneg.mpr hc
  · have hz : (star z ⬝ᵥ (H *ᵥ z)).im = 0 :=
      (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg z)).2.symm
    simp [hz]
private theorem gram_decomposition_to_povm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)     (hH : H.IsHermitian) (N : Fin n → Matrix (Fin n) (Fin n) ℂ)     (hN : ∀ i, (N i).PosSemidef) (hs : ∑ i, N i = H * H) :     ∃ K : Fin n → Matrix (Fin n) (Fin n) ℂ,       (∀ i, (K i).PosSemidef) ∧ (1 - ∑ i, K i).PosSemidef ∧       ∀ i, H * K i * H = N i := by
  obtain ⟨B, hHBH, hBHB, hP, hQ⟩ := matrix_penrose_exists H
  let K : Fin n → Matrix (Fin n) (Fin n) ℂ := fun i => B * N i * Bᴴ
  have hQ2 : (B * H) * (B * H) = B * H := by
    rw [← Matrix.mul_assoc, hBHB]
  have hsumK : ∑ i, K i = B * H := by
    simp only [K, ← Matrix.sum_mul, ← Matrix.mul_sum, hs]
    calc
      _ = (B * H) * (B * H)ᴴ := by simp [Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
      _ = B * H := by rw [hQ.eq, hQ2]
  refine ⟨K, (fun i => (hN i).mul_mul_conjTranspose_same B), ?_, ?_⟩
  · rw [hsumK]
    exact hermitian_projection_complement_psd (B * H) hQ hQ2
  · intro i
    have hHP : H * (H * B) = H := by
      have hh := congrArg Matrix.conjTranspose hHBH
      simpa only [Matrix.conjTranspose_mul, hH.eq, hP.eq] using hh
    have hsumP : (∑ i, N i) * (H * B) = ∑ i, N i := by
      rw [hs, Matrix.mul_assoc, hHP]
    have hp := psd_summand_projection N hN (H * B) hP hsumP i
    calc
      H * K i * H = (H * B) * N i * (H * B)ᴴ := by
        simp [K, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
      _ = N i := by rw [hP.eq]; exact hp
private theorem trace_rank_mul {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)     (hH : H.IsHermitian) (i : Fin n) :     (Matrix.vecMulVec (H.col i) (star (H.col i)) * K).trace = (H * K * H) i i := by
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]
  have hcol : star (H.col i) = H i := by
    funext j
    exact hH.apply i j
  rw [hcol]
  change _ = (H * K).row i ⬝ᵥ H.col i
  rw [Matrix.dotProduct_mulVec]
  rfl
private theorem constant_diagonal_gram_bound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)     (hH : H.PosSemidef) (d : ℝ) (hd : 0 ≤ d) (hdiag : ∀ i, (H i i).re = d)     (N : Fin n → Matrix (Fin n) (Fin n) ℂ) (hN : ∀ i, (N i).PosSemidef)     (hs : ∑ i, N i = H * H) :     ∑ i, (N i i i).re ≤ (n : ℝ) * d^2 := by
  obtain ⟨K, hK, hR, hKN⟩ := gram_decomposition_to_povm H hH.isHermitian N hN hs
  have hi (i : Fin n) : (N i i i).re ≤ d * (H * K i).trace.re := by
    have hslack := rank_certificate H hH i
    rw [hdiag i] at hslack
    have hpos := RHLinalg.trace_mul_nonneg_of_posSemidef hslack (hK i)
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      trace_rank_mul H (K i) hH.isHermitian i, hKN i] at hpos
    simpa only [Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using sub_nonneg.mp hpos
  have ht : (H * ∑ i, K i).trace.re ≤ H.trace.re := by
    have hp := RHLinalg.trace_mul_nonneg_of_posSemidef hH hR
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub] at hp
    change 0 ≤ (H.trace - (H * ∑ i, K i).trace).re at hp
    rw [Complex.sub_re] at hp
    linarith
  calc
    _ ≤ ∑ i, d * (H * K i).trace.re := Finset.sum_le_sum (fun i _ => hi i)
    _ = d * (H * ∑ i, K i).trace.re := by
      simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    _ ≤ d * H.trace.re := mul_le_mul_of_nonneg_left ht hd
    _ = (n : ℝ) * d^2 := by
      simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, hdiag, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
private def d (n : ℕ) (c : ℝ) : ℝ :=
  (Real.sqrt (1 + ((n : ℝ) - 1) * c) + ((n : ℝ) - 1) * Real.sqrt (1 - c)) / n
private def H (n : ℕ) (c : ℝ) :=
  Real.sqrt (1 + ((n : ℝ) - 1) * c) • ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) + Real.sqrt (1-c) • (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))))
private theorem J_psd (n : ℕ) : ((Matrix.of (fun _ _ : Fin n => (1 : ℂ)))).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin n => (1 : ℂ)) using 1
  ext i j
  simp [Matrix.vecMulVec]
private theorem P_psd (n : ℕ) : (((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))).PosSemidef := (J_psd n).smul (by positivity)
private theorem P_sq (n : ℕ) (hn : 0 < n) : ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) * ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) = ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  ext i j
  simp [Matrix.mul_apply, Complex.real_smul]
  field_simp
private theorem Q_psd (n : ℕ) (hn : 0 < n) : ((1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))))).PosSemidef :=
  hermitian_projection_complement_psd (((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) (P_psd n).isHermitian (P_sq n hn)
private theorem PQ_zero (n : ℕ) (hn : 0 < n) : ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) * (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) = 0 := by
  exact (show IsIdempotentElem ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) from P_sq n hn).mul_one_sub_self
private theorem QP_zero (n : ℕ) (hn : 0 < n) : (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) * ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) = 0 := by
  exact (show IsIdempotentElem ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) from P_sq n hn).one_sub_mul_self
private theorem Q_sq (n : ℕ) (hn : 0 < n) : (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) * (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) = (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))))) := by
  exact (show IsIdempotentElem ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) from P_sq n hn).one_sub
private theorem H_psd (n : ℕ) (hn : 0 < n) (c : ℝ) : (H n c).PosSemidef :=
  ((P_psd n).smul (Real.sqrt_nonneg _)).add ((Q_psd n hn).smul (Real.sqrt_nonneg _))
private theorem H_sq (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : c ∈ Set.Icc 0 1) :     H n c * H n c = (1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + c • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))) := by
  have ha : 0 ≤ 1 + ((n : ℝ) - 1) * c := by
    have hnR : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
    exact add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hnR) hc.1)
  have hb : 0 ≤ 1-c := sub_nonneg.mpr hc.2
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by exact Nat.zero_lt_of_lt hn : 0 < n)
  have hp2 := P_sq n (by exact Nat.zero_lt_of_lt hn)
  have hq2 := Q_sq n (by exact Nat.zero_lt_of_lt hn)
  have hpq := PQ_zero n (by exact Nat.zero_lt_of_lt hn)
  have hqp := QP_zero n (by exact Nat.zero_lt_of_lt hn)
  unfold H
  generalize hp : ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) = p at *
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hp2, hq2, hpq, hqp, smul_zero, add_zero, zero_add,
    Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]
  rw [smul_sub]
  have hr : (1 + ((n : ℝ)-1)*c) • p + ((1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1-c) • p) =
      (1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + (1 + ((n : ℝ)-1)*c - (1-c)) • p := by module
  rw [hr, ← hp, smul_smul]
  have he : (1 + ((n : ℝ) - 1) * c - (1-c)) * (n : ℝ)⁻¹ = c := by
    field_simp
    ring
  rw [he]
private theorem H_diag (n : ℕ) (hn : 0 < n) (c : ℝ) (i : Fin n) :     H n c i i = (d n c : ℂ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [H, d, Matrix.one_apply, Complex.real_smul]
  push_cast
  field_simp
private theorem d_nonneg (n : ℕ) (hn : 1 ≤ n) (c : ℝ) : 0 ≤ d n c := by
  have hnR : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  unfold d
  positivity
private theorem constant_overlap_certificate (n : ℕ) (hn : 1 ≤ n) (c : ℝ)     (hc : c ∈ Set.Icc 0 1) (N : Fin n → Matrix (Fin n) (Fin n) ℂ)     (hN : ∀ i, (N i).PosSemidef)     (hs : ∑ i, N i = (1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + c • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) :     ∑ i, (N i i i).re ≤ (n : ℝ) * d n c ^ 2 := by
  apply constant_diagonal_gram_bound (H n c) (H_psd n (by exact Nat.zero_lt_of_lt hn) c) (d n c)
    (d_nonneg n hn c) (fun i => by rw [H_diag n (by exact Nat.zero_lt_of_lt hn) c i]; simp) N hN
  rw [H_sq n hn c hc]
  exact hs
private def moment {n : ℕ} (ψ : (Fin n → Bool) → ℂ) : ℝ :=
  ∑ x, Complex.normSq (ψ x) * (((Finset.univ.filter (fun j => x j = true)).card * (n-(Finset.univ.filter (fun j => x j = true)).card) : ℕ) : ℝ)
private def overlap {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ) : ℝ :=
  1 - 4 * Real.sin θ^2 * moment ψ / ((n : ℝ)*(n-1))
private def cstar (n : ℕ) (θ : ℝ) : ℝ :=
  1 - 4 * (n^2/4 : ℕ) * Real.sin θ^2 / ((n : ℝ)*(n-1))
private theorem moment_bounds {n : ℕ} (ψ : (Fin n → Bool) → ℂ)     (hψ : ∑ x, Complex.normSq (ψ x) = 1) :     0 ≤ moment ψ ∧ moment ψ ≤ (n^2/4 : ℕ) := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (Complex.normSq_nonneg _) (by exact Nat.cast_nonneg' ((Finset.univ.filter (fun j => x j = true)).card * (n - (Finset.univ.filter (fun j => x j = true)).card))))
  · calc
      _ ≤ ∑ x, Complex.normSq (ψ x) * ((n^2/4 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
        exact_mod_cast balanced_product_upper n ((Finset.univ.filter (fun j => x j = true)).card) (weight_le x)
      _ = _ := by exact Real.arith_mean_weighted_of_constant Finset.univ (fun i => Complex.normSq (ψ i)) (fun _ => ((n ^ 2 / 4 : ℕ) : ℝ)) ((n ^ 2 / 4 : ℕ) : ℝ) hψ (fun _ _ _ => rfl)
private theorem G_total_moment {n : ℕ} (θ : ℝ) (ψ : (Fin n → Bool) → ℂ)     (hψ : ∑ x, Complex.normSq (ψ x) = 1) :     (∑ i : Fin n, ∑ j : Fin n, (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)) i j).re =       (n : ℝ)^2 - 4 * Real.sin θ^2 * moment ψ := by
  rw [G_total]
  simp only [phase_sum_normSq]
  have he : ∀ x : Fin n → Bool, (((Finset.univ.filter (fun j => x j = true)).card*(n-(Finset.univ.filter (fun j => x j = true)).card) : ℕ) : ℝ) =
      ((Finset.univ.filter (fun j => x j = true)).card : ℝ)*((n : ℝ)-(Finset.univ.filter (fun j => x j = true)).card) := by
    intro x
    rw [Nat.cast_mul, Nat.cast_sub (weight_le x)]
  calc
    _ = (∑ x, Complex.normSq (ψ x)*(n : ℝ)^2) - 4*Real.sin θ^2*moment ψ := by
      simp only [moment, he, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [← Finset.sum_mul, hψ, one_mul]
private theorem avgMatrix_total {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :     ∑ i : Fin n, ∑ j : Fin n, avgMatrix B i j = ∑ i : Fin n, ∑ j : Fin n, B i j := by
  simp only [avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply,
    ← Finset.smul_sum]
  have hshuffle : (∑ i : Fin n, ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n), B (σ i) (σ j)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ j : Fin n, B (σ i) (σ j) := Finset.sum_comm_cycle
  have he (σ : Equiv.Perm (Fin n)) :
      ∑ i : Fin n, ∑ j : Fin n, B (σ i) (σ j) = ∑ i : Fin n, ∑ j : Fin n, B i j := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, B (σ i) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => B (σ i) j)
      _ = _ := Equiv.sum_comp σ (fun i => ∑ j, B i j)
  rw [hshuffle]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.real_smul]
  push_cast
  field_simp
private theorem avgMatrix_diag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)     (hd : ∀ i, B i i = 1) (i : Fin n) : avgMatrix B i i = 1 := by
  simpa only [avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply, hd] using
    (Fintype.expect_const (ι := Equiv.Perm (Fin n)) (1 : ℂ))
private theorem constant_overlap_total (n : ℕ) (c : ℝ) :     (∑ i : Fin n, ∑ j : Fin n,       ((1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + c • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) i j).re =       (n : ℝ) + (n : ℝ)*(n-1)*c := by
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Complex.real_smul,
    Finset.sum_add_distrib, ← Complex.ofReal_sum]
  push_cast
  ring
private theorem average_gram_overlap {n : ℕ} (hn : 2 ≤ n) (θ : ℝ)     (ψ : (Fin n → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1) :     avgMatrix ((D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ))) = (1-overlap θ ψ) • (1 : Matrix (Fin n) (Fin n) ℂ) +       overlap θ ψ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))) := by
  obtain ⟨c, hc⟩ := invariant_constant_offDiagonal hn ((D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ)))
    (Matrix.posSemidef_conjTranspose_mul_self (((fun i => fire θ i ψ)ᵀ))).isHermitian
  have he : avgMatrix ((D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ))) = (1-c) • (1 : Matrix (Fin n) (Fin n) ℂ) + c • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [avgMatrix_diag ((D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i ψ)ᵀ))) (G_diag θ ψ hψ)]
      simp [Complex.real_smul]
    · rw [hc i j hij]
      simp [Complex.real_smul, Matrix.one_apply, hij]
  have ht := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ =>
    (∑ i : Fin n, ∑ j : Fin n, B i j).re) he
  rw [avgMatrix_total, G_total_moment θ ψ hψ, constant_overlap_total] at ht
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hden : (n : ℝ)*(n-1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hco : c = overlap θ ψ := by
    unfold overlap
    field_simp [left_ne_zero_of_mul hden, right_ne_zero_of_mul hden]
    nlinarith [ht]
  rwa [hco] at he
private theorem overlap_bounds {n : ℕ} (hn : 2 ≤ n) (θ : ℝ)     (ψ : (Fin n → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1) :     cstar n θ ≤ overlap θ ψ ∧ overlap θ ψ ≤ 1 := by
  have hm := moment_bounds ψ hψ
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hden : 0 < (n : ℝ)*(n-1) := mul_pos (by linarith) (by linarith)
  have hs : 0 ≤ Real.sin θ^2 := sq_nonneg _
  constructor
  · unfold cstar overlap
    apply sub_le_sub_left
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith [mul_le_mul_of_nonneg_left hm.2 hs]
  · unfold overlap
    have hp : 0 ≤ 4*Real.sin θ^2*moment ψ / ((n : ℝ)*(n-1)) := div_nonneg (mul_nonneg (mul_nonneg (by exact zero_le_four) hs) hm.1) hden.le
    linarith
private theorem balanced_product_exact (n : ℕ) : (n / 2) * (n - n / 2) = n ^ 2 / 4 := by
  have hr : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
  rcases hr with hr | hr
  · have he : n ^ 2 = 4 * ((n / 2) * (n - n / 2)) := by
      rw [hr] at hn
      have hs : n - n / 2 = n / 2 := by omega
      rw [hs]
      nlinarith [hn]
    rw [he]
    omega
  · have he : n ^ 2 = 4 * ((n / 2) * (n - n / 2)) + 1 := by
      rw [hr] at hn
      have hs : n - n / 2 = n / 2 + 1 := by omega
      rw [hs]
      nlinarith [hn]
    rw [he]
    omega
private theorem balanced_floor_positive (n : ℕ) (hn : 2 ≤ n) : 0 < n ^ 2 / 4 := by
  have hx : 4 ≤ n ^ 2 := by nlinarith
  omega
private theorem ceiling_floor_ratio (n : ℕ) (hn : 2 ≤ n) :     4 * (n ^ 2 / 4 : ℕ) / ((n : ℝ) * (n - 1)) =       2 * (((n + 1) / 2 : ℕ) : ℝ) / (2 * (((n + 1) / 2 : ℕ) : ℝ) - 1) := by
  let p := n / 2
  have hpc : p * (n - p) = n ^ 2 / 4 := balanced_product_exact n
  have hp : 1 ≤ p := by dsimp [p]; omega
  have he : n = 2 * p ∨ n = 2 * p + 1 := by dsimp [p]; omega
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hpR : 1 ≤ (p : ℝ) := Nat.one_le_cast.mpr hp
  have hqR : 1 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
    have hq : 1 ≤ (n + 1) / 2 := by omega
    exact_mod_cast hq
  have hden : (n : ℝ) * (n - 1) ≠ 0 := by
    have hn0 : 0 < (n : ℝ) := by linarith
    have hn1 : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hqden : 2 * (((n + 1) / 2 : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  rw [← hpc]
  rcases he with he | he
  · have hq : (n + 1) / 2 = p := by omega
    have hs : n - p = p := by omega
    rw [hq, hs]
    have hncast : (n : ℝ) = 2 * (p : ℝ) := by exact_mod_cast he
    push_cast
    rw [hncast]
    field_simp [show (p : ℝ) ≠ 0 by positivity,
      show 2 * (p : ℝ) - 1 ≠ 0 by linarith,
      show 2 * (p : ℝ) + 1 ≠ 0 by positivity]
    ring
  · have hq : (n + 1) / 2 = p + 1 := by omega
    have hs : n - p = p + 1 := by omega
    rw [hq, hs]
    have hncast : (n : ℝ) = 2 * (p : ℝ) + 1 := by exact_mod_cast he
    push_cast
    rw [hncast]
    field_simp [show (p : ℝ) ≠ 0 by positivity,
      show 2 * (p : ℝ) - 1 ≠ 0 by linarith,
      show 2 * (p : ℝ) + 1 ≠ 0 by positivity]
    ring_nf
    field_simp [show (1 + (p : ℝ) * 2) ≠ 0 by positivity]
    ring
private theorem cstar_cos (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :     cstar n θ = ((((n+1)/2 : ℕ) : ℝ)-1 +       (((n+1)/2 : ℕ) : ℝ)*Real.cos (2*θ)) /       (2*(((n+1)/2 : ℕ) : ℝ)-1) := by
  have hq : 1 ≤ (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (n+1)/2)
  have hden : 2*(((n+1)/2 : ℕ) : ℝ)-1 ≠ 0 := by linarith
  unfold cstar
  rw [mul_div_right_comm, ceiling_floor_ratio n hn]
  rw [Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq θ
  field_simp
  nlinarith
private theorem threshold_small_nonneg (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)     (hθ : 0 ≤ θ) (ht : θ ≤ T n) : 0 ≤ cstar n θ := by
  let q : ℝ := (((n+1)/2 : ℕ) : ℝ)
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ (n+1)/2)
  have hq0 : 0 < q := by linarith
  have hu : -( (q-1)/q) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← neg_div]
    constructor
    · apply (le_div_iff₀ hq0).2
      linarith
    · apply (div_le_iff₀ hq0).2
      linarith
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ 2*θ)
    (Real.arccos_le_pi (-((q-1)/q)))
    (by change θ ≤ Real.arccos (-((q-1)/q))/2 at ht; linarith)
  rw [Real.cos_arccos hu.1 hu.2] at hc
  rw [cstar_cos n hn θ]
  change 0 ≤ (q-1 + q*Real.cos (2*θ))/(2*q-1)
  apply div_nonneg _ (by linarith)
  have hh := (div_le_iff₀ hq0).mp (show -(q-1)/q ≤ Real.cos (2*θ) by rw [neg_div]; exact hc)
  nlinarith
private theorem threshold_range (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)     (hθ : (0 < θ ∧ θ ≤ T n) ∨ (Real.pi-T n ≤ θ ∧ θ < Real.pi)) :     0 < θ ∧ θ < Real.pi ∧ 0 ≤ cstar n θ := by
  have hT : T n ≤ Real.pi/2 := by
    unfold T
    linarith [Real.arccos_le_pi (-(((((n+1)/2 : ℕ) : ℝ)-1)/(((n+1)/2 : ℕ) : ℝ)))]
  rcases hθ with h | h
  · exact ⟨h.1, by linarith [Real.pi_pos], threshold_small_nonneg n hn θ h.1.le h.2⟩
  · refine ⟨by linarith [Real.pi_pos], h.2, ?_⟩
    have hc := threshold_small_nonneg n hn (Real.pi-θ) (by linarith) (by linarith)
    simpa only [cstar, Real.sin_pi_sub] using hc
private theorem cstar_lt_one (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi) :     cstar n θ < 1 := by
  have hfloor : 0 < (n^2/4 : ℕ) := balanced_floor_positive n hn
  have hfloorR : 0 < ((n^2/4 : ℕ) : ℝ) := Nat.cast_pos'.mpr hfloor
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  unfold cstar
  have hp : 0 < 4 * ((n^2/4 : ℕ) : ℝ) * Real.sin θ^2 / ((n : ℝ)*(n-1)) := by positivity
  linarith
private def dprime (n : ℕ) (c : ℝ) : ℝ :=
  ((n - 1 : ℝ) / (2 * Real.sqrt (1 + (n - 1 : ℝ) * c)) -
    (n - 1 : ℝ) / (2 * Real.sqrt (1 - c))) / n
private theorem d_hasDerivAt (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :     HasDerivAt (d n) (dprime n x) x := by
  have hn' : 0 ≤ (n - 1 : ℝ) := by
    have hnr : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    linarith
  have hx0 : 0 ≤ x := hx.1.le
  have ha : 1 + (n - 1 : ℝ) * x ≠ 0 := by positivity
  have hb : 1 - x ≠ 0 := by linarith [hx.2]
  have h := (((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul (n - 1 : ℝ))).sqrt ha).add
    ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).sqrt hb).const_mul (n - 1 : ℝ))
  have hdiv := h.div_const (n : ℝ)
  have hp :
      ((0 + (n - 1 : ℝ) * 1) / (2 * Real.sqrt (1 + (n - 1 : ℝ) * x)) +
        (n - 1 : ℝ) * ((0 - 1) / (2 * Real.sqrt (1 - x)))) / n = dprime n x := by
    unfold dprime
    ring
  change HasDerivAt (d n)
    (((0 + (n - 1 : ℝ) * 1) / (2 * Real.sqrt (1 + (n - 1 : ℝ) * x)) +
      (n - 1 : ℝ) * ((0 - 1) / (2 * Real.sqrt (1 - x)))) / n) x at hdiv
  rw [hp] at hdiv
  exact hdiv
private theorem d_antitone (n : ℕ) (hn : 1 ≤ n) : AntitoneOn (d n) (Set.Icc 0 1) := by
  have hn' : 0 ≤ (n - 1 : ℝ) := by
    have hnr : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    linarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · unfold d
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (d_hasDerivAt n hn x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(d_hasDerivAt n hn x hx).deriv]
    have hb : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr (by linarith [hx.2])
    have hba : Real.sqrt (1 - x) ≤ Real.sqrt (1 + (n - 1 : ℝ) * x) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hx.1]
    apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg n)
    exact sub_nonpos.mpr (div_le_div_of_nonneg_left hn' (by positivity) (by linarith))
private def ratio (n : ℕ) (θ : ℝ) (a b : Fin n) (k : ℕ) : ℝ :=
  ((rCount n a b k : ℝ) + Real.cos (2*θ)*lCount n a b k) /
    ((rCount n a b k : ℝ) + lCount n a b k)
private theorem ratio_formula (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (a b : Fin n)     (hab : a ≠ b) (k : ℕ) (hk : k ≤ n) :     ratio n θ a b k = 1 - 4*Real.sin θ^2*((k*(n-k) : ℕ) : ℝ) /       ((n : ℝ)*(n-1)) := by
  have hC : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hden : (n : ℝ)*(n-1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hpart : (rCount n a b k : ℝ) + (lCount n a b k : ℝ) = (n.choose k : ℝ) := by
    exact_mod_cast counts_partition n a b k
  have hp : (lCount n a b k : ℝ) * ((n : ℝ)*(n-1)) =
      2*((k*(n-k) : ℕ) : ℝ)*(n.choose k : ℝ) := by
    have h := pair_count_product n a b hab k
    have hn1 : 1 ≤ n := Nat.one_le_of_lt hn
    exact_mod_cast (by nlinarith [h] : lCount n a b k * (n*(n-1)) = 2*(k*(n-k))*n.choose k)
  have hr : (rCount n a b k : ℝ) = (n.choose k : ℝ) - lCount n a b k := eq_sub_of_add_eq hpart
  unfold ratio
  have hcos : Real.cos (2*θ) = 1 - 2*Real.sin θ^2 := Real.cos_two_mul_eq_one_sub θ
  rw [hpart, hr, hcos]
  field_simp [show (n : ℝ) ≠ 0 by linarith, show (n : ℝ)-1 ≠ 0 by linarith, hC.ne']
  linear_combination -2*Real.sin θ^2*hp
private theorem ratio_minimizer_balanced (n : ℕ) (hn : 2 ≤ n) (θ : ℝ)     (hθ : 0 < θ ∧ θ < Real.pi) (a b : Fin n) (hab : a ≠ b)     (l : ℕ) (hl : l ≤ n) (hm : IsMinOn (ratio n θ a b) (Set.Iic n) l) :     l*(n-l) = n^2/4 := by
  have hh : n/2 ≤ n := Nat.div_le_self _ _
  have h : ratio n θ a b l ≤ ratio n θ a b (n/2) := hm hh
  rw [ratio_formula n hn θ a b hab l hl, ratio_formula n hn θ a b hab (n/2) hh,
    balanced_product_exact] at h
  have hup := balanced_product_upper n l hl
  have hnR : 2 ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hden : 0 < (n : ℝ)*(n-1) := mul_pos (by linarith) (by linarith)
  have hs : 0 < Real.sin θ^2 := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hc : 4*Real.sin θ^2*((n^2/4 : ℕ) : ℝ) ≤
      4*Real.sin θ^2*((l*(n-l) : ℕ) : ℝ) := by
    apply (div_le_div_iff_of_pos_right hden).mp
    linarith
  have hhR : ((n^2/4 : ℕ) : ℝ) ≤ ((l*(n-l) : ℕ) : ℝ) := by nlinarith
  exact Nat.le_antisymm hup (by exact_mod_cast hhR)
private theorem dicke_normalized {n : ℕ} (l : ℕ) (hl : l ≤ n)     (φ : (Fin n → Bool) → ℂ)     (hφ : ∀ x, Complex.normSq (φ x) = if (Finset.univ.filter (fun j => x j = true)).card = l then 1/(n.choose l : ℝ) else 0) :     ∑ x, Complex.normSq (φ x) = 1 := by
  have hC : (n.choose l : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hl)
  simp only [hφ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, weight_class_card]
  field_simp
private theorem dicke_gram_invariant {n : ℕ} (θ : ℝ) (l : ℕ)     (φ : (Fin n → Bool) → ℂ)     (hφ : ∀ x, Complex.normSq (φ x) = if (Finset.univ.filter (fun j => x j = true)).card = l then 1/(n.choose l : ℝ) else 0)     (σ : Equiv.Perm (Fin n)) (i j : Fin n) :     (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i φ)ᵀ)) (σ i) (σ j) = (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i φ)ᵀ)) i j := by
  simp only [G_phase]
  have he := Equiv.sum_comp ((Equiv.arrowCongr σ.symm (Equiv.refl Bool))) (fun x : Fin n → Bool =>
    (Complex.normSq (φ x) : ℂ)*star ((Complex.exp ((if x i then 1 else -1) * (θ : ℂ) * Complex.I)))*(Complex.exp ((if x j then 1 else -1) * (θ : ℂ) * Complex.I)))
  have hw (x : Fin n → Bool) : Complex.normSq (φ ((Equiv.arrowCongr σ.symm (Equiv.refl Bool)) x)) = Complex.normSq (φ x) := by
    rw [hφ, hφ, weight_permWord]
  simp only [hw] at he
  exact he
private theorem global_success_upper_bound (n : ℕ) (hn : 3 ≤ n) (θ : ℝ)     (hθ : (0 < θ ∧ θ ≤ T n) ∨ (Real.pi-T n ≤ θ ∧ θ < Real.pi))     (ψ : (Fin n → Bool) → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1)     (M : LocalPOVM (Fin n → Bool) (Fin n)) : isoSuccess θ ψ M ≤ d n (cstar n θ)^2 := by
  have ht := threshold_range n (by exact Nat.le_of_add_left_le hn) θ hθ
  have ho := overlap_bounds (by exact Nat.le_of_add_left_le hn) θ ψ hψ
  have hc : overlap θ ψ ∈ Set.Icc 0 1 := ⟨ht.2.2.trans ho.1, ho.2⟩
  have hcstar : cstar n θ ∈ Set.Icc 0 1 := ⟨ht.2.2, (cstar_lt_one n (by exact Nat.le_of_add_left_le hn) θ ⟨ht.1, ht.2.1⟩).le⟩
  have hb := constant_overlap_certificate n (by exact Nat.one_le_of_lt hn) (overlap θ ψ) hc
    (avgN (fun i => D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i ψ)ᵀ) (M.effect i))) (avgN_psd _ (N_psd θ ψ M))
    (by rw [sum_avgN, sum_N, average_gram_overlap (by exact Nat.le_of_add_left_le hn) θ ψ hψ])
  rw [avgN_objective] at hb
  have hd := d_antitone n (by exact Nat.one_le_of_lt hn) hcstar hc ho.1
  have hsq : d n (overlap θ ψ)^2 ≤ d n (cstar n θ)^2 :=
    sq_le_sq₀ (d_nonneg n (by exact Nat.one_le_of_lt hn) _) (d_nonneg n (by exact Nat.one_le_of_lt hn) _) |>.mpr hd
  rw [isoSuccess_gram]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by exact Nat.zero_lt_of_lt hn : 0 < n)
  calc
    _ ≤ (1/(n : ℝ))*((n : ℝ)*d n (overlap θ ψ)^2) :=
      mul_le_mul_of_nonneg_left hb (by exact Nat.one_div_cast_nonneg n)
    _ = d n (overlap θ ψ)^2 := by field_simp
    _ ≤ _ := hsq
private theorem avgMatrix_eq_of_invariant {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)     (hB : ∀ σ : Equiv.Perm (Fin n), ∀ i j, B (σ i) (σ j) = B i j) : avgMatrix B = B := by
  ext i j
  simpa only [avgMatrix, Finset.expect, Finset.card_univ, ← NNRat.cast_smul_eq_nnqsmul ℝ, NNRat.cast_inv, NNRat.cast_natCast, one_div, Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply, hB] using
    (Fintype.expect_const (ι := Equiv.Perm (Fin n)) (B i j))
private theorem dicke_moment {n : ℕ} (l : ℕ) (hl : l ≤ n) (φ : (Fin n → Bool) → ℂ)     (hφ : ∀ x, Complex.normSq (φ x) = if (Finset.univ.filter (fun j => x j = true)).card = l then 1/(n.choose l : ℝ) else 0) :     moment φ = ((l*(n-l) : ℕ) : ℝ) := by
  have hC : (n.choose l : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hl)
  unfold moment
  have he (x : Fin n → Bool) : Complex.normSq (φ x)*(((Finset.univ.filter (fun j => x j = true)).card*(n-(Finset.univ.filter (fun j => x j = true)).card) : ℕ) : ℝ) =
      if (Finset.univ.filter (fun j => x j = true)).card = l then (1/(n.choose l : ℝ))*((l*(n-l) : ℕ) : ℝ) else 0 := by
    rw [hφ]
    by_cases hx : (Finset.univ.filter (fun j => x j = true)).card = l <;> simp [hx]
  simp only [he, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, weight_class_card]
  field_simp
private theorem dicke_gram {n : ℕ} (hn : 3 ≤ n) (θ : ℝ) (l : ℕ) (hl : l ≤ n)     (hbalance : l*(n-l) = n^2/4) (φ : (Fin n → Bool) → ℂ)     (hφ : ∀ x, Complex.normSq (φ x) = if (Finset.univ.filter (fun j => x j = true)).card = l then 1/(n.choose l : ℝ) else 0) :     (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i φ)ᵀ)) = (1-cstar n θ) • (1 : Matrix (Fin n) (Fin n) ℂ) + cstar n θ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ))) := by
  have he := average_gram_overlap (by exact Nat.le_of_add_left_le hn) θ φ (dicke_normalized l hl φ hφ)
  rw [avgMatrix_eq_of_invariant _ (dicke_gram_invariant θ l φ hφ)] at he
  have ho : overlap θ φ = cstar n θ := by
    rw [overlap, dicke_moment l hl φ hφ, hbalance, cstar]
    ring
  rwa [ho] at he
private def Hinv (n : ℕ) (c : ℝ) :=
  (Real.sqrt (1 + ((n : ℝ)-1)*c))⁻¹ • ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) + (Real.sqrt (1-c))⁻¹ • (1 - ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))))
private theorem Hinv_hermitian (n : ℕ) (hn : 0 < n) (c : ℝ) : (Hinv n c).IsHermitian := by
  exact (((P_psd n).smul (by positivity)).add ((Q_psd n hn).smul (by positivity))).isHermitian
private theorem Hinv_mul_H (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c ∧ c < 1) :     Hinv n c * H n c = 1 := by
  have hnR : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have ha : 0 < 1+((n : ℝ)-1)*c := by
    have hp := mul_nonneg (sub_nonneg.mpr hnR) hc.1
    linarith
  have hb : 0 < 1-c := by linarith [hc.2]
  have hp2 := P_sq n (by exact Nat.zero_lt_of_lt hn)
  have hq2 := Q_sq n (by exact Nat.zero_lt_of_lt hn)
  have hpq := PQ_zero n (by exact Nat.zero_lt_of_lt hn)
  have hqp := QP_zero n (by exact Nat.zero_lt_of_lt hn)
  unfold Hinv H
  generalize hp : ((n : ℝ)⁻¹ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) = p at *
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hp2, hq2, hpq, hqp, smul_zero, add_zero, zero_add,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne', mul_inv_cancel₀ (Real.sqrt_pos.mpr hb).ne', one_smul]
  abel
private theorem H_mul_Hinv (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c ∧ c < 1) :     H n c * Hinv n c = 1 := by
  exact mul_eq_one_comm.mp (Hinv_mul_H n hn c hc)
private theorem E_psd {n : ℕ} (i : Fin n) : ((Matrix.diagonal (Pi.single i (1 : ℂ)))).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  exact Pi.single_nonneg.mpr zero_le_one
private theorem sum_E (n : ℕ) : ∑ i : Fin n, (Matrix.diagonal (Pi.single i (1 : ℂ))) = 1 := by
  simpa only [Matrix.diagonal_single] using (Matrix.sum_single_one (m := Fin n) (α := ℂ))
private theorem sqrt_povm_exists {h : Type*} [Fintype h] [DecidableEq h]     (n : ℕ) (hn : 0 < n) (A : Matrix h (Fin n) ℂ) (H R : Matrix (Fin n) (Fin n) ℂ)     (hH : H.IsHermitian) (hR : R.IsHermitian) (hRH : R*H=1) (hHR : H*R=1)     (hG : Aᴴ*A=H*H) :     ∃ M : LocalPOVM h (Fin n), ∀ i, Aᴴ*M.effect i*A=H*(Matrix.diagonal (Pi.single i (1 : ℂ)))*H := by
  let W := A*R
  have hWA : Wᴴ*A=H := by
    simp only [W, Matrix.conjTranspose_mul, hR.eq]
    rw [Matrix.mul_assoc, hG, ← Matrix.mul_assoc, hRH, Matrix.one_mul]
  have hAW : Aᴴ*W=H := by
    have hh := congrArg Matrix.conjTranspose hWA
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq] using hh
  have hWW : Wᴴ*W=1 := by
    change Wᴴ*(A*R)=1
    rw [← Matrix.mul_assoc, hWA, hHR]
  have hWH : W*H=A := by
    change A*R*H=A
    rw [Matrix.mul_assoc, hRH, Matrix.mul_one]
  let U := W*Wᴴ
  have hU : U.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self W
  have hU2 : U*U=U := by
    change (W*Wᴴ)*(W*Wᴴ)=W*Wᴴ
    calc
      _ = W*(Wᴴ*W)*Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWW, Matrix.mul_one]
  have hcomp : (1-U).PosSemidef :=
    (show IsStarProjection U from ⟨hU2, hU.isSelfAdjoint⟩).one_sub_nonneg.posSemidef
  let D : Fin n → Matrix h h ℂ := fun i => W*(Matrix.diagonal (Pi.single i (1 : ℂ)))*Wᴴ
  have hD (i : Fin n) : (D i).PosSemidef := (E_psd i).mul_mul_conjTranspose_same W
  have hsumD : ∑ i, D i=U := by
    simp only [D, ← Matrix.sum_mul, ← Matrix.mul_sum, sum_E, Matrix.mul_one, U]
  let z : Fin n := ⟨0, hn⟩
  let M : LocalPOVM h (Fin n) := {
    effect := fun i => D i + if i=z then 1-U else 0
    positive := fun i => (hD i).add (by split_ifs <;> first | exact hcomp | exact Matrix.PosSemidef.zero)
    complete := by simp only [Finset.sum_add_distrib, hsumD]; simp }
  refine ⟨M, ?_⟩
  have hkill : (1-U)*A=0 := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    change A-(W*Wᴴ)*A=0
    rw [Matrix.mul_assoc, hWA, hWH, sub_self]
  intro i
  change Aᴴ*(D i+if i=z then 1-U else 0)*A=H*(Matrix.diagonal (Pi.single i (1 : ℂ)))*H
  rw [Matrix.mul_add, Matrix.add_mul]
  have he : Aᴴ*D i*A=H*(Matrix.diagonal (Pi.single i (1 : ℂ)))*H := by
    change Aᴴ*(W*(Matrix.diagonal (Pi.single i (1 : ℂ)))*Wᴴ)*A=H*(Matrix.diagonal (Pi.single i (1 : ℂ)))*H
    calc
      _ = (Aᴴ*W)*(Matrix.diagonal (Pi.single i (1 : ℂ)))*(Wᴴ*A) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAW, hWA]
  rw [he]
  suffices hz : Aᴴ*(if i=z then 1-U else 0)*A=0 by rw [hz, add_zero]
  split_ifs
  · rw [Matrix.mul_assoc, hkill, Matrix.mul_zero]
  · simp
private theorem square_root_diag {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :     (H*(Matrix.diagonal (Pi.single i (1 : ℂ)))*H) i i = H i i * H i i := by
  rw [Matrix.diagonal_single, Matrix.single_eq_single_vecMulVec_single,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.mulVec_single_one, Matrix.single_one_vecMul]
  rfl
private theorem dicke_attainment {n : ℕ} (hn : 3 ≤ n) (θ : ℝ)     (hc : 0 ≤ cstar n θ ∧ cstar n θ < 1) (φ : (Fin n → Bool) → ℂ)     (hG : (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i φ)ᵀ)) = (1-cstar n θ) • (1 : Matrix (Fin n) (Fin n) ℂ) + cstar n θ • (Matrix.of (fun _ _ : Fin n => (1 : ℂ)))) :     ∃ M : LocalPOVM (Fin n → Bool) (Fin n), isoSuccess θ φ M = d n (cstar n θ)^2 := by
  obtain ⟨M, hM⟩ := sqrt_povm_exists n (by exact Nat.zero_lt_of_lt hn) (((fun i => fire θ i φ)ᵀ)) (H n (cstar n θ))
    (Hinv n (cstar n θ)) (H_psd n (by exact Nat.zero_lt_of_lt hn) _).isHermitian
    (Hinv_hermitian n (by exact Nat.zero_lt_of_lt hn) _) (Hinv_mul_H n (by exact Nat.one_le_of_lt hn) _ hc)
    (H_mul_Hinv n (by exact Nat.one_le_of_lt hn) _ hc)
    (by change (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((fun i => fire θ i φ)ᵀ)) = _; rw [hG, H_sq n (by exact Nat.one_le_of_lt hn) _ ⟨hc.1, hc.2.le⟩])
  refine ⟨M, ?_⟩
  have he (i : Fin n) : (D5.S3.Quantum.Reduction.IsometricCompression.compress ((fun i => fire θ i φ)ᵀ) (M.effect i)) i i = (d n (cstar n θ) : ℂ)^2 := by
    rw [D5.S3.Quantum.Reduction.IsometricCompression.compress, hM i, square_root_diag, H_diag n (by exact Nat.zero_lt_of_lt hn)]
    ring
  rw [isoSuccess_gram]
  simp only [he, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, zero_mul, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by exact Nat.zero_lt_of_lt hn : 0 < n)
  field_simp
theorem result : claim := by
  intro n hn θ hθ l hl hm φ hφ ψ hψ M
  let a : Fin n := ⟨0, by exact Nat.zero_lt_of_lt hn⟩
  let b : Fin n := ⟨1, by exact Nat.lt_of_add_left_lt hn⟩
  have hab : a ≠ b := not_eq_of_beq_eq_false rfl
  change IsMinOn (ratio n θ a b) (Set.Iic n) l at hm
  have ht := threshold_range n (by exact Nat.le_of_add_left_le hn) θ hθ
  have hbalance := ratio_minimizer_balanced n (by exact Nat.le_of_add_left_le hn) θ ⟨ht.1,ht.2.1⟩ a b hab l hl hm
  have hg := dicke_gram hn θ l hl hbalance φ hφ
  obtain ⟨M', hM'⟩ := dicke_attainment hn θ
    ⟨ht.2.2, cstar_lt_one n (by exact Nat.le_of_add_left_le hn) θ ⟨ht.1,ht.2.1⟩⟩ φ hg
  refine ⟨M', ?_⟩
  rw [hM']
  exact global_success_upper_bound n hn θ hθ ψ hψ M
end D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
