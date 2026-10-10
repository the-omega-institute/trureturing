/- GID: D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Faithful-state bouquet fixed points determine the identity map. -/

/-
proof_shape: fixed_powers: content; escape_witness=fixed_powers
  consumers: fixed_polynomials
proof_shape: fixed_polynomials: content; escape_witness=fixed_polynomials
  consumers: fixed_spectral_projectors, sigma_diagonal_projectors_fixed
proof_shape: aeval_diagonal: bind-only; escape_witness=none
  consumers: spectralProjector_polynomial, aeval_diagonal_lagrange
proof_shape: spectralProjector_polynomial: bind-only; escape_witness=none
  consumers: fixed_spectral_projectors
proof_shape: fixed_spectral_projectors: content; escape_witness=fixed_spectral_projectors
  consumers: likelihood_projectors_fixed
proof_shape: likelihood_projectors_fixed: content; escape_witness=likelihood_projectors_fixed
  consumers: state_matrix_fixed
proof_shape: fixed_corner: bind-only; escape_witness=none
  consumers: trace_preserving_of_projectors_fixed
proof_shape: unitary_conjugation_trace: bind-only; escape_witness=none
  consumers: spectralProjector_corner, spectralProjector_trace
proof_shape: single_corner: bind-only; escape_witness=none
  consumers: spectralProjector_corner
proof_shape: spectralProjector_corner: bind-only; escape_witness=none
  consumers: trace_preserving_of_projectors_fixed
proof_shape: spectralProjector_idempotent: bind-only; escape_witness=none
  consumers: trace_preserving_of_projectors_fixed
proof_shape: spectralProjector_trace: bind-only; escape_witness=none
  consumers: trace_preserving_of_projectors_fixed
proof_shape: spectralProjectors_sum: bind-only; escape_witness=none
  consumers: trace_preserving_of_projectors_fixed
proof_shape: trace_preserving_of_projectors_fixed: content; escape_witness=trace_preserving_of_projectors_fixed
  consumers: state_matrix_fixed
proof_shape: invariant_state_fixed_of_trace_preserving: content; escape_witness=invariant_state_fixed_of_trace_preserving
  consumers: state_matrix_fixed
proof_shape: state_matrix_fixed: content; escape_witness=state_matrix_fixed
  consumers: bouquet_fixed_point_rigidity
proof_shape: mu_mul: bind-only; escape_witness=none
  consumers: bouquet_jordan_generation, peirce_single_orientation
proof_shape: bouquet_jordan_generation: bind-only; escape_witness=none
  consumers: bouquet_fixed_point_rigidity
proof_shape: aeval_diagonal_lagrange: bind-only; escape_witness=none
  consumers: sigma_diagonal_projectors_fixed
proof_shape: sigma_diagonal_projectors_fixed: content; escape_witness=sigma_diagonal_projectors_fixed
  consumers: bouquet_fixed_point_rigidity
proof_shape: jordan_projector_edge: bind-only; escape_witness=none
  consumers: fixed_edge, peirce_two_plane
proof_shape: fixed_edge: content; escape_witness=fixed_edge
  consumers: fixed_real_likelihood_edge, fixed_imag_likelihood_edge
proof_shape: likelihoodWeight_pos: bind-only; escape_witness=none
  consumers: fixed_real_likelihood_edge, fixed_imag_likelihood_edge
proof_shape: likelihood_entry: bind-only; escape_witness=none
  consumers: fixed_real_likelihood_edge, fixed_imag_likelihood_edge
proof_shape: fixed_real_likelihood_edge: content; escape_witness=fixed_real_likelihood_edge
  consumers: bouquet_fixed_point_rigidity
proof_shape: fixed_imag_likelihood_edge: content; escape_witness=fixed_imag_likelihood_edge
  consumers: bouquet_fixed_point_rigidity
proof_shape: bouquet_fixed_point_rigidity: content; escape_witness=bouquet_fixed_point_rigidity
  consumers: ptp_unitalized_inverse
escape_witness: bouquet_fixed_point_rigidity
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
  declaration statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain
import D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum

noncomputable section
open D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum
open D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
namespace D5.S3.QuantumChannels.RenyiSufficiency.BouquetFixedPoint

section
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder ComplexStarModule Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem fixed_powers
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace) (hA : E A = A) :
    ∀ k : ℕ, E (A ^ k) = A ^ k := by
  intro k
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hj := fixed_jordan E hE h1 hS hstate hA ih
    have hjpow : jordan A (A^k) = (2 : ℂ) • (A^(k+1)) := by
      simp only [jordan, ← pow_succ, ← pow_succ', two_smul]
    rw [hjpow, map_smul] at hj
    exact (smul_right_inj (by norm_num : (2 : ℂ) ≠ 0)).mp hj

private theorem fixed_polynomials
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace) (hA : E A = A)
    (p : Polynomial ℂ) : E (aeval A p) = aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, fixed_powers E hE h1 hS hstate hA k]

private theorem aeval_diagonal (v : Fin n → ℂ) (p : Polynomial ℂ) :
    aeval (diagonal v) p = diagonal (fun i => p.eval (v i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    rw [diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, hij, Matrix.smul_apply]

private def spectralProjector {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
    Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (single i i 1)

private theorem spectralProjector_polynomial {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hsimple : Function.Injective hA.eigenvalues) (i : Fin n) :
    aeval A (Lagrange.basis Finset.univ (fun j => (hA.eigenvalues j : ℂ)) i) =
      spectralProjector hA i := by
  let J := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  let v : Fin n → ℂ := fun j => (hA.eigenvalues j : ℂ)
  have hv : Function.Injective v := by
    intro j k he; exact hsimple (Complex.ofReal_injective he)
  have hA' : A = J (diagonal v) := hA.spectral_theorem
  conv_lhs => arg 1; rw [hA']
  rw [aeval_algHom_apply, aeval_diagonal]
  change J (diagonal (fun j => (Lagrange.basis Finset.univ v i).eval (v j))) = J (single i i 1)
  apply congrArg J
  have hb : (fun j => (Lagrange.basis Finset.univ v i).eval (v j)) = Pi.single i (1 : ℂ) := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [Lagrange.eval_basis_self (fun j _ k _ he => hv he) (Finset.mem_univ i)]
      simp
    · rw [Lagrange.eval_basis_of_ne (Ne.symm hj) (Finset.mem_univ j)]
      simp [Pi.single_apply, hj, Ne.symm hj]
  rw [hb]
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply, Pi.single_apply, Matrix.single]
    · simp [Matrix.diagonal_apply, Pi.single_apply, Matrix.single, hij, Ne.symm hij]
  · by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply, Matrix.single, hjk, Ne.symm hjk]
    · simp [Matrix.diagonal_apply, Matrix.single, hij, hjk]

private theorem fixed_spectral_projectors
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace)
    (hA : A.IsHermitian) (hsimple : Function.Injective hA.eigenvalues)
    (hfix : E A = A) (i : Fin n) : E (spectralProjector hA i) = spectralProjector hA i := by
  rw [← spectralProjector_polynomial hA hsimple i]
  exact fixed_polynomials E hE h1 hS hstate hfix _

private theorem likelihood_projectors_fixed
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hfix : E (likelihood false) = likelihood false) (i : Fin 5) :
    E (spectralProjector (likelihood_hermitian false) i) =
      spectralProjector (likelihood_hermitian false) i :=
  fixed_spectral_projectors E hE h1 sigma_posDef hstate
    (likelihood_hermitian false) (likelihood_simple_spectrum false) hfix i
end

section
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem fixed_corner
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {p : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p)
    (hfix : E p = p) (hmd : JordanMD E p) (Y : Matrix (Fin n) (Fin n) ℂ) :
    E (p * Y * p) = p * E Y * p := by
  have hid (Z : Matrix (Fin n) (Fin n) ℂ) :
      jordan p (jordan p Z) - jordan p Z = (2 : ℂ) • (p * Z * p) := by
    dsimp [jordan]
    simp only [mul_add, add_mul]
    rw [← Matrix.mul_assoc p p, hp, Matrix.mul_assoc Z p p, hp]
    simp only [two_smul]
    noncomm_ring
  have h := congrArg E (hid Y)
  rw [map_sub, hmd, hmd, hfix, map_smul, hid] at h
  exact (smul_right_inj (by norm_num : (2 : ℂ) ≠ 0)).mp h.symm

private theorem unitary_conjugation_trace (U : Matrix.unitaryGroup (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U Y).trace = Y.trace := by
  exact Matrix.trace_map (Unitary.conjStarAlgAut ℂ _ U) Y

private theorem single_corner (i : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ) :
    single i i (1 : ℂ) * Y * single i i 1 = Y i i • single i i 1 := by
  simp only [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, smul_eq_mul]

private theorem spectralProjector_corner {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ) :
    spectralProjector hA i * Y * spectralProjector hA i =
      (spectralProjector hA i * Y).trace • spectralProjector hA i := by
  let J := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  let Z := J.symm Y
  have hY : Y = J Z := (J.apply_symm_apply Y).symm
  change J (single i i 1) * Y * J (single i i 1) =
    (J (single i i 1) * Y).trace • J (single i i 1)
  rw [hY, ← map_mul, ← map_mul, single_corner, map_smul,
    unitary_conjugation_trace, trace_single_mul]
  simp

private theorem spectralProjector_idempotent {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    spectralProjector hA i * spectralProjector hA i = spectralProjector hA i := by
  simp only [spectralProjector, ← map_mul, Matrix.single_mul_single_same, mul_one]

private theorem spectralProjector_trace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i : Fin n) :
    (spectralProjector hA i).trace = 1 := by
  rw [spectralProjector, unitary_conjugation_trace, trace_single_eq_same]

private theorem spectralProjectors_sum {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∑ i, spectralProjector hA i = 1 := by
  simp only [spectralProjector, ← map_sum]
  have hs : (∑ i : Fin n, single i i (1 : ℂ)) = 1 := by
    ext j k
    by_cases hjk : j = k
    · subst k; simp [Matrix.sum_apply, Matrix.single]
    · simp [Matrix.sum_apply, Matrix.single, hjk, Ne.symm hjk, Matrix.one_apply]
  rw [hs, map_one]

private theorem trace_preserving_of_projectors_fixed
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace) (hA : A.IsHermitian)
    (hfix : ∀ i, E (spectralProjector hA i) = spectralProjector hA i) :
    ∀ Y, (E Y).trace = Y.trace := by
  intro Y
  have hed (i : Fin n) : (spectralProjector hA i * E Y).trace =
      (spectralProjector hA i * Y).trace := by
    have h := fixed_corner E (spectralProjector_idempotent hA i) (hfix i)
      (fixed_jordan_domain E hE h1 hS hstate (hfix i)) Y
    rw [spectralProjector_corner, map_smul, hfix, spectralProjector_corner] at h
    have ht := congrArg Matrix.trace h
    simpa only [trace_smul, spectralProjector_trace, smul_eq_mul, mul_one] using ht.symm
  calc
    (E Y).trace = ((∑ i, spectralProjector hA i) * E Y).trace := by rw [spectralProjectors_sum, one_mul]
    _ = ∑ i, (spectralProjector hA i * E Y).trace := by rw [Finset.sum_mul, trace_sum]
    _ = ∑ i, (spectralProjector hA i * Y).trace := Finset.sum_congr rfl (fun i _ => hed i)
    _ = Y.trace := by rw [← trace_sum, ← Finset.sum_mul, spectralProjectors_sum, one_mul]

private theorem invariant_state_fixed_of_trace_preserving
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace)
    (htrace : ∀ Y, (E Y).trace = Y.trace) : E S = S := by
  let W := E S - S
  have hW : W.IsHermitian := (positive_map_hermitian E hE hS).sub hS
  have hp : (W * W).PosSemidef := by
    simpa only [hW.eq] using Matrix.posSemidef_conjTranspose_mul_self W
  have hk := (Matrix.le_iff.mp (kadison_hermitian E hE h1 hS)).trace_nonneg
  rw [trace_sub, htrace] at hk
  have ht : (W * W).trace = (E S * E S).trace - (S * S).trace := by
    dsimp [W]
    rw [sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
      trace_mul_comm (E S) S, hstate]
    ring
  have hz : (W * W).trace = 0 := by
    apply le_antisymm
    · rw [ht]; exact sub_nonpos.mpr (sub_nonneg.mp hk)
    · exact hp.trace_nonneg
  have hw0 : W = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hW.eq]; exact hz)
  exact sub_eq_zero.mp hw0

private theorem state_matrix_fixed
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hfix : E (likelihood false) = likelihood false) : E sigma = sigma := by
  exact invariant_state_fixed_of_trace_preserving E hE h1 sigma_posDef.isHermitian hstate
    (trace_preserving_of_projectors_fixed E hE h1 sigma_posDef hstate
      (likelihood_hermitian false) (likelihood_projectors_fixed E hE h1 hstate hfix))
end

section
open Matrix
theorem mu_mul (i j k l : Fin 5) : (single i j (1 : ℂ)) * (single k l (1 : ℂ)) = if j = k then (single i l (1 : ℂ)) else 0 := by
  by_cases h : j = k
  · subst k; simp
  · rw [if_neg h]; exact Matrix.single_mul_single_of_ne 1 i j k h 1

private def symEdge (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ := (single i j (1 : ℂ)) + (single j i (1 : ℂ))
private def imagEdge (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ := Complex.I • (single i j (1 : ℂ)) - Complex.I • (single j i (1 : ℂ))

private theorem bouquet_jordan_generation
    (F : Submodule ℂ (Matrix (Fin 5) (Fin 5) ℂ))
    (hJ : ∀ A ∈ F, ∀ B ∈ F, jordan A B ∈ F)
    (hdiag : ∀ i, (single i i (1 : ℂ)) ∈ F)
    (h01 : symEdge 0 1 ∈ F) (h12 : symEdge 1 2 ∈ F)
    (h03 : symEdge 0 3 ∈ F) (h34 : symEdge 3 4 ∈ F)
    (hi02 : imagEdge 0 2 ∈ F) : ∀ i j, (single i j (1 : ℂ)) ∈ F := by
  have hs02 : symEdge 0 2 ∈ F := by
    have h := hJ _ h01 _ h12
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h02 : (single (0 : Fin 5) (2 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := F.smul_mem (1/2 : ℂ) (F.sub_mem hs02 (F.smul_mem Complex.I hi02))
    convert h using 1
    simp only [symEdge, imagEdge, smul_sub, smul_add, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    simp only [Complex.I_mul_I, smul_smul, Complex.I_sq]
    module
  have h20 : (single (2 : Fin 5) (0 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := F.smul_mem (1/2 : ℂ) (F.add_mem hs02 (F.smul_mem Complex.I hi02))
    convert h using 1
    simp only [symEdge, imagEdge, smul_sub, smul_add, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    simp only [Complex.I_mul_I, smul_smul, Complex.I_sq]
    module
  have h01' : (single (0 : Fin 5) (1 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h02 _ h12
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h10 : (single (1 : Fin 5) (0 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h20 _ h12
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h13 : (single (1 : Fin 5) (3 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h10 _ h03
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h31 : (single (3 : Fin 5) (1 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h01' _ h03
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h03' : (single (0 : Fin 5) (3 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h01' _ h13
    convert h using 1 <;> simp only [jordan, mu_mul] <;> norm_num [Fin.ext_iff]
  have h30 : (single (3 : Fin 5) (0 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h31 _ h10
    convert h using 1 <;> simp only [jordan, mu_mul] <;> norm_num [Fin.ext_iff]
  have h04 : (single (0 : Fin 5) (4 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h03' _ h34
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h40 : (single (4 : Fin 5) (0 : Fin 5) (1 : ℂ)) ∈ F := by
    have h := hJ _ h30 _ h34
    convert h using 1 <;> simp only [symEdge, jordan, mul_add, add_mul, mu_mul] <;> norm_num [Fin.ext_iff]
  have h0i (i : Fin 5) : (single (0 : Fin 5) i (1 : ℂ)) ∈ F := by
    fin_cases i
    · exact hdiag 0
    · exact h01'
    · exact h02
    · exact h03'
    · exact h04
  have hi0 (i : Fin 5) : (single i (0 : Fin 5) (1 : ℂ)) ∈ F := by
    fin_cases i
    · exact hdiag 0
    · exact h10
    · exact h20
    · exact h30
    · exact h40
  intro i j
  by_cases hij : i = j
  · subst j; exact hdiag i
  by_cases hi : i = 0
  · subst i; exact h0i j
  by_cases hj : j = 0
  · subst j; exact hi0 i
  have h := hJ _ (hi0 i) _ (h0i j)
  convert h using 1
  simp [jordan, mu_mul, hij, Ne.symm hij]
end

section
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator


private theorem aeval_diagonal_lagrange {n : ℕ} (v : Fin n → ℂ) (hv : Function.Injective v)
    (i : Fin n) : aeval (diagonal v) (Lagrange.basis Finset.univ v i) = single i i 1 := by
  rw [aeval_diagonal]
  have hb : (fun j => (Lagrange.basis Finset.univ v i).eval (v j)) = Pi.single i (1 : ℂ) := by
    funext j
    by_cases hij : i = j
    · subst j
      simp only [Lagrange.eval_basis_self (fun j _ k _ h => hv h) (Finset.mem_univ i), Pi.single_eq_same]
    · rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
      simp [Pi.single_apply, hij]
  rw [hb, Matrix.diagonal_single]

private theorem sigma_diagonal_projectors_fixed
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hsigma : E sigma = sigma) (i : Fin 5) : E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)) := by
  let v : Fin 5 → ℂ := fun j => ((((j.val+1 : ℕ) : ℝ) / 15 : ℝ) : ℂ)
  have hv : Function.Injective v := by
    intro j k h
    have h' : (((j.val+1 : ℕ) : ℝ)/15) = (((k.val+1 : ℕ) : ℝ)/15) :=
      Complex.ofReal_injective h
    have hv' : j.val = k.val := by
      have : ((j.val : ℕ) : ℝ) = ((k.val : ℕ) : ℝ) := by push_cast at h'; linarith
      exact_mod_cast this
    exact Fin.ext hv'
  have hp := fixed_polynomials E hE h1 sigma_posDef hstate hsigma (Lagrange.basis Finset.univ v i)
  change E (aeval (diagonal v) _) = aeval (diagonal v) _ at hp
  simpa only [aeval_diagonal_lagrange v hv i] using hp

theorem jordan_projector_edge {n : ℕ} (i j : Fin n) (hij : i ≠ j) (Y : Matrix (Fin n) (Fin n) ℂ) :
    jordan (single i i 1) (jordan (single j j 1) Y) =
      Y i j • single i j 1 + Y j i • single j i 1 := by
  dsimp [jordan]
  simp only [mul_add, add_mul]
  rw [← Matrix.mul_assoc (single i i 1) (single j j 1) Y,
    Matrix.single_mul_single_of_ne 1 i i j hij 1, zero_mul,
    Matrix.single_mul_mul_single, Matrix.mul_assoc Y (single j j 1) (single i i 1),
    Matrix.single_mul_single_of_ne 1 j j i (Ne.symm hij) 1, mul_zero]
  rw [← Matrix.mul_assoc (single i i 1) Y (single j j 1), Matrix.single_mul_mul_single]
  simp only [zero_add, add_zero, one_mul, mul_one, Matrix.smul_single, smul_eq_mul]

private theorem fixed_edge
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hdiag : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ))) {Y : Matrix (Fin 5) (Fin 5) ℂ} (hY : E Y = Y)
    (i j : Fin 5) (hij : i ≠ j) :
    E (Y i j • (single i j (1 : ℂ)) + Y j i • (single j i (1 : ℂ))) = Y i j • (single i j (1 : ℂ)) + Y j i • (single j i (1 : ℂ)) := by
  have h := fixed_jordan E hE h1 sigma_posDef hstate (hdiag i)
    (fixed_jordan E hE h1 sigma_posDef hstate (hdiag j) hY)
  simpa only [jordan_projector_edge i j hij Y] using h

private def likelihoodWeight (i : Fin 5) : ℝ := (((i.val+1 : ℕ) : ℝ)/15) ^ (-1/2 : ℝ)
private theorem likelihoodWeight_pos (i : Fin 5) : 0 < likelihoodWeight i := by
  apply Real.rpow_pos_of_pos
  positivity

private theorem likelihood_entry (i j : Fin 5) :
    likelihood false i j = (likelihoodWeight i : ℂ) * rho false (1/1000) i j * (likelihoodWeight j : ℂ) := by
  have hs : matrixPower sigma (-1/2) = diagonal (fun i => (likelihoodWeight i : ℂ)) :=
    matrixPower_diagonal (fun i : Fin 5 => ((i.val+1 : ℕ) : ℝ)/15) (-1/2)
  simp only [likelihood, hs, Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem fixed_real_likelihood_edge
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hdiag : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (hX : E (likelihood false) = likelihood false)
    (i j : Fin 5) (hij : i ≠ j)
    (hrij : rho false (1/1000) i j = 1/5000)
    (hrji : rho false (1/1000) j i = 1/5000) : E (symEdge i j) = symEdge i j := by
  let c : ℂ := (likelihoodWeight i : ℂ) * (1/5000) * (likelihoodWeight j : ℂ)
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast ne_of_gt (likelihoodWeight_pos i)
      · norm_num
    · exact_mod_cast ne_of_gt (likelihoodWeight_pos j)
  have he : likelihood false i j • (single i j (1 : ℂ)) + likelihood false j i • (single j i (1 : ℂ)) =
      c • symEdge i j := by
    rw [likelihood_entry, likelihood_entry, hrij, hrji]
    have hr : (likelihoodWeight j : ℂ) * (1/5000) * (likelihoodWeight i : ℂ) = c := by dsimp [c]; ring
    rw [hr]
    simp only [symEdge, smul_add]
    rfl
  have hf := fixed_edge E hE h1 hstate hdiag hX i j hij
  rw [he, map_smul] at hf
  exact (smul_right_inj hc).mp hf

private theorem fixed_imag_likelihood_edge
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hdiag : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (hX : E (likelihood false) = likelihood false)
    (i j : Fin 5) (hij : i ≠ j)
    (hrij : rho false (1/1000) i j = -Complex.I/5000)
    (hrji : rho false (1/1000) j i = Complex.I/5000) : E (imagEdge i j) = imagEdge i j := by
  let c : ℂ := -(likelihoodWeight i : ℂ) * (1/5000) * (likelihoodWeight j : ℂ)
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr (by exact_mod_cast ne_of_gt (likelihoodWeight_pos i))
      · norm_num
    · exact_mod_cast ne_of_gt (likelihoodWeight_pos j)
  have he : likelihood false i j • (single i j (1 : ℂ)) + likelihood false j i • (single j i (1 : ℂ)) =
      c • imagEdge i j := by
    rw [likelihood_entry, likelihood_entry, hrij, hrji]
    dsimp [imagEdge, c]
    simp only [smul_sub, smul_smul]
    have hfirst : (likelihoodWeight i : ℂ) * (-Complex.I / 5000) * (likelihoodWeight j : ℂ) =
        (-↑(likelihoodWeight i) * (1 / 5000) * ↑(likelihoodWeight j)) * Complex.I := by ring
    have hsecond : (likelihoodWeight j : ℂ) * (Complex.I / 5000) * (likelihoodWeight i : ℂ) =
        -((-↑(likelihoodWeight i) * (1 / 5000) * ↑(likelihoodWeight j)) * Complex.I) := by ring
    rw [hfirst, hsecond, neg_smul, sub_eq_add_neg]
  have hf := fixed_edge E hE h1 hstate hdiag hX i j hij
  rw [he, map_smul] at hf
  exact (smul_right_inj hc).mp hf

theorem bouquet_fixed_point_rigidity
    (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hstate : ∀ Y, (sigma * E Y).trace = (sigma * Y).trace)
    (hX : E (likelihood false) = likelihood false) : E = LinearMap.id := by
  have hS := state_matrix_fixed E hE h1 hstate hX
  have hd := sigma_diagonal_projectors_fixed E hE h1 hstate hS
  have hj : ∀ A ∈ E.fixedSubmodule, ∀ B ∈ E.fixedSubmodule, jordan A B ∈ E.fixedSubmodule := by
    intro A hA B hB
    rw [LinearMap.mem_fixedSubmodule_iff] at hA hB ⊢
    exact fixed_jordan E hE h1 sigma_posDef hstate hA hB
  have hd' : ∀ i, (single i i (1 : ℂ)) ∈ E.fixedSubmodule := fun i => (LinearMap.mem_fixedSubmodule_iff).mpr (hd i)
  have hreal := fixed_real_likelihood_edge E hE h1 hstate hd hX
  have himag := fixed_imag_likelihood_edge E hE h1 hstate hd hX
  have hs : ∀ i j, (single i j (1 : ℂ)) ∈ E.fixedSubmodule := bouquet_jordan_generation (E.fixedSubmodule) hj hd'
    ((LinearMap.mem_fixedSubmodule_iff).mpr (hreal 0 1 (by decide) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons])))
    ((LinearMap.mem_fixedSubmodule_iff).mpr (hreal 1 2 (by decide) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons])))
    ((LinearMap.mem_fixedSubmodule_iff).mpr (hreal 0 3 (by decide) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons])))
    ((LinearMap.mem_fixedSubmodule_iff).mpr (hreal 3 4 (by decide) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons])))
    ((LinearMap.mem_fixedSubmodule_iff).mpr (himag 0 2 (by decide) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]; ring) (by norm_num [rho, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]; ring)))
  apply Matrix.ext_linearMap
  intro i j
  apply LinearMap.ext
  intro z
  change E (single i j z) = single i j z
  have hmu := (LinearMap.mem_fixedSubmodule_iff).mp (hs i j)
  have hid : single i j z = z • (single i j (1 : ℂ)) := by simp
  simp only [hid, map_smul, hmu, LinearMap.id_apply]
end

end D5.S3.QuantumChannels.RenyiSufficiency.BouquetFixedPoint
