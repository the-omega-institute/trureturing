/- GID: D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.claim; result=D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result; claim=D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.claim
   digest: Schatten approximants need not approach the strict spectral approximant. -/

/-
proof_shape: result: content; escape_witness: real_minimizers_separated.
admission_basis: open-problem-resolution (#15746; Refuted)
Direct frozen dependencies: the declaration identities F1--F13 below.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
Singular values use the preregistered function body; proofs use
LinearMap.singularValues directly without a duplicate definition.
The owner identities below are declaration statement_ids from the scoped Lean report.
Non-propositional definitions encode the matrix family and scalar comparison.
F1: D5/S3/Resource/LogDet/PathSpectralClassical.trace_cfc_eq_sum; statement_id: sha256:2afdc1322560955083985858579c052c3f1e7fed0978a76f0182f08e177e3b35
F2: D5/S3/Quantum/NormCompression/UpperBranchReduction.diagonal_power_le_eigenvalue_power; statement_id: sha256:03d15849b4321e9d735117ced3bf4471deb0f994c29d0c9ba729f2ae7141f440
F3: D5/S3/Quantum/NormCompression/UpperBranchReduction.expectation_eq_eigenvalue_sum; statement_id: sha256:0d39d88eeabb46d813df17d701780348c43576e9f0d1bb99e2ef587c53ac9090
F4: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm; statement_id: sha256:02fdf214898933eff1a32234bd5f4868da16db800b68e3790e820d4c60e070bd
F5: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_nonneg; statement_id: sha256:43666f702cfab70ba4261d59baa4e6e86d51d15aaf130f183161147d0935cbbb
F6: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenNorm_rpow; statement_id: sha256:786d90e773903cc7f0d7f34789781586e19f768740a7ae5cd3b6ba9cff6b3bd7
F7: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow; statement_id: sha256:d89d93b393dcd229e6d2b67f603b5fb8c30c589e2b35d5b74ce0e6147ddf3eb7
F8: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow._proof_1; statement_id: sha256:a66dd7b795c3399720b01de384eef119b6d2618ef78348798e438a8a2cebf335
F9: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow._proof_2; statement_id: sha256:39fa90cdb13817cbc8cea638edc11d553f35c1dce5a08ade6f9aba1adcf1679d
F10: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow._proof_3; statement_id: sha256:eccc6cf19eea6d3a9809139f36eeda665142a5103590bc328b547aad5955a471
F11: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_eq_columnGram; statement_id: sha256:d642ee6ac6eba0dc6698eff622ca63b6f12758091e4ee26b7c3de3991546637a
F12: D5/S3/Quantum/NormCompression/UpperBranchReduction.schattenPow_nonneg; statement_id: sha256:9e230c8440a1171a6c06fd33baecf3f99fa91c9e71b6a1aa6817b51048e7fc0f
F13: RHLinalg.sum_eigenvalues_reindex; statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
proof_shape: IsCpApproximant: bind-only; escape_witness: none; consumer: chosenApproximant, chosenApproximant_spec, claim, cp_minimizers_separated, cp_power_min, exists_cp_approximant, cp_projects_to_real_min, result; Direct frozen dependencies: F4.
proof_shape: IsStrictSpectralApproximant: bind-only; escape_witness: none; consumer: claim; Direct frozen dependencies: none.
proof_shape: claim: bind-only; escape_witness: none; consumer: result; Direct frozen dependencies: F4.
proof_shape: H: bind-only; escape_witness: none; consumer: M, E_mem, parametrization, residual_eq_strict, cp_power_min, residual_formula, exists_cp_approximant; Direct frozen dependencies: none.
proof_shape: M: bind-only; escape_witness: none; consumer: chosenApproximant, chosenApproximant_spec, parametrization, cp_minimizers_separated, cp_power_min, exists_cp_approximant, cp_projects_to_real_min, strict_approximant, result; Direct frozen dependencies: none.
proof_shape: R: bind-only; escape_witness: none; consumer: strict_sv, exists_pair_minimizer, parametrization, real_residual_contracts, residual_eq_strict, spectral_face, residual_power_lower, residual_real_schattenPow, cp_minimizers_separated, competitor_power_bound, hermitianPart_residual, cp_power_min, residual_real_eq_block, residual_formula, exists_cp_approximant, sv_residual_zero_first_two, cp_projects_to_real_min, strict_approximant, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: residual_formula: bind-only; escape_witness: none; consumer: parametrization, residual_eq_strict, cp_power_min, exists_cp_approximant; Direct frozen dependencies: none.
proof_shape: parametrization: bind-only; escape_witness: none; consumer: cp_minimizers_separated, exists_cp_approximant, strict_approximant; Direct frozen dependencies: none.
proof_shape: E_mem: bind-only; escape_witness: none; consumer: strict_approximant; Direct frozen dependencies: none.
proof_shape: disk_intersection: bind-only; escape_witness: none; consumer: spectral_face; Direct frozen dependencies: none.
proof_shape: residual_eq_strict: bind-only; escape_witness: none; consumer: strict_approximant; Direct frozen dependencies: none.
proof_shape: norm_apply_le_sv0: bind-only; escape_witness: none; consumer: entry_le_sv0; Direct frozen dependencies: F3.
proof_shape: entry_le_sv0: bind-only; escape_witness: none; consumer: entry_pow_le, spectral_face; Direct frozen dependencies: F3.
proof_shape: diagonal_hermitian: bind-only; escape_witness: none; consumer: sv_diagonal, diagonal_sorted_eigenvalues; Direct frozen dependencies: none.
proof_shape: diagonal_roots: bind-only; escape_witness: none; consumer: diagonal_sorted_eigenvalues; Direct frozen dependencies: none.
proof_shape: diagonal_sorted_eigenvalues: bind-only; escape_witness: none; consumer: sv_diagonal; Direct frozen dependencies: none.
proof_shape: sv_diagonal: bind-only; escape_witness: none; consumer: strict_sv, sv_residual_zero_first_two; Direct frozen dependencies: none.
proof_shape: strict_sv: bind-only; escape_witness: none; consumer: strict_approximant; Direct frozen dependencies: none.
proof_shape: sv_residual_zero_first_two: bind-only; escape_witness: none; consumer: strict_approximant; Direct frozen dependencies: none.
proof_shape: spectral_face: bind-only; escape_witness: none; consumer: strict_approximant; Direct frozen dependencies: F3.
proof_shape: strict_approximant: bind-only; escape_witness: none; consumer: result; Direct frozen dependencies: F3.
proof_shape: schattenPow_trace: bind-only; escape_witness: none; consumer: continuous_schattenPow; Direct frozen dependencies: F1, F7, F11.
proof_shape: continuous_schattenPow: bind-only; escape_witness: none; consumer: exists_pair_minimizer; Direct frozen dependencies: F1, F7, F11.
proof_shape: sv0_pow_le: bind-only; escape_witness: none; consumer: entry_pow_le; Direct frozen dependencies: F7, F8, F9, F10, F12.
proof_shape: entry_pow_le: bind-only; escape_witness: none; consumer: exists_pair_minimizer; Direct frozen dependencies: F3, F7, F8, F9, F10, F12.
proof_shape: exists_pair_minimizer: bind-only; escape_witness: none; consumer: exists_cp_approximant; Direct frozen dependencies: F1, F3, F7, F8, F9, F10, F11, F12.
proof_shape: exists_cp_approximant: bind-only; escape_witness: none; consumer: chosenApproximant, chosenApproximant_spec; Direct frozen dependencies: F1, F3, F4, F7, F8, F9, F10, F11, F12.
proof_shape: block: bind-only; escape_witness: none; consumer: residual_real_schattenPow, residual_real_eq_block, block_schattenPow, gram_charpoly; Direct frozen dependencies: none.
proof_shape: top: bind-only; escape_witness: none; consumer: eigen_product, eigen_sum, top_comparison_gap, top_competitor_bounds, residual_real_schattenPow, competitor_power_bound, top_gap, top_ge, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: bottom: bind-only; escape_witness: none; consumer: eigen_product, eigen_sum, top_competitor_bounds, residual_real_schattenPow, competitor_power_bound, top_gap, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: eigen_sum: bind-only; escape_witness: none; consumer: top_competitor_bounds, residual_real_schattenPow, top_gap; Direct frozen dependencies: none.
proof_shape: eigen_product: bind-only; escape_witness: none; consumer: residual_real_schattenPow, top_gap; Direct frozen dependencies: none.
proof_shape: top_ge: bind-only; escape_witness: none; consumer: top_comparison_gap, top_competitor_bounds, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: top_gap: bind-only; escape_witness: none; consumer: top_comparison_gap, top_competitor_bounds; Direct frozen dependencies: none.
proof_shape: gram_charpoly: bind-only; escape_witness: none; consumer: block_schattenPow; Direct frozen dependencies: none.
proof_shape: schattenPow_roots: bind-only; escape_witness: none; consumer: hermitian_schattenPow, block_schattenPow; Direct frozen dependencies: F7, F11.
proof_shape: rpow_square_half: bind-only; escape_witness: none; consumer: hermitian_schattenPow, block_schattenPow; Direct frozen dependencies: none.
proof_shape: block_schattenPow: bind-only; escape_witness: none; consumer: residual_real_schattenPow; Direct frozen dependencies: F7, F11.
proof_shape: residual_real_eq_block: bind-only; escape_witness: none; consumer: residual_real_schattenPow; Direct frozen dependencies: none.
proof_shape: residual_real_schattenPow: bind-only; escape_witness: none; consumer: competitor_power_bound, real_minimizers_separated; Direct frozen dependencies: F7, F11.
proof_shape: hermitian_schattenPow: bind-only; escape_witness: none; consumer: hermitianPart_contracts; Direct frozen dependencies: F7, F11.
proof_shape: gram_basis_bound: bind-only; escape_witness: none; consumer: hermitianPart_contracts, diagonal_power_bound; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: diagonal_power_bound: bind-only; escape_witness: none; consumer: residual_power_lower; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: hermitianPart_hermitian: bind-only; escape_witness: none; consumer: hermitianPart_contracts; Direct frozen dependencies: none.
proof_shape: re_inner_hermitianPart: bind-only; escape_witness: none; consumer: hermitianPart_contracts; Direct frozen dependencies: none.
proof_shape: hermitianPart_contracts: bind-only; escape_witness: none; consumer: real_residual_contracts; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: hermitianPart_residual: bind-only; escape_witness: none; consumer: real_residual_contracts; Direct frozen dependencies: none.
proof_shape: real_residual_contracts: bind-only; escape_witness: none; consumer: cp_projects_to_real_min; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: sstar: bind-only; escape_witness: none; consumer: competitor_power_bound, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: envelope: bind-only; escape_witness: none; consumer: envelope_eventually, competitor_power_bound, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: abs_bernoulli: bind-only; escape_witness: none; consumer: residual_power_lower; Direct frozen dependencies: none.
proof_shape: top_competitor_bounds: bind-only; escape_witness: none; consumer: competitor_power_bound, real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: top_comparison_gap: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: rpow_difference_bound: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: exp_limit_bound: bind-only; escape_witness: none; consumer: envelope_eventually; Direct frozen dependencies: none.
proof_shape: residual_power_lower: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: competitor_power_bound: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: F7, F11.
proof_shape: envelope_eventually: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: exponential_small: bind-only; escape_witness: none; consumer: real_minimizers_separated; Direct frozen dependencies: none.
proof_shape: real_minimizers_separated: content; escape_witness: real_minimizers_separated; consumer: cp_minimizers_separated; Direct frozen dependencies: F2, F7, F11, F13.
proof_shape: cp_power_min: bind-only; escape_witness: none; consumer: cp_projects_to_real_min; Direct frozen dependencies: F4, F5, F6, F7.
proof_shape: cp_projects_to_real_min: bind-only; escape_witness: none; consumer: cp_minimizers_separated; Direct frozen dependencies: F2, F4, F5, F6, F7, F11, F13.
proof_shape: cp_minimizers_separated: content; escape_witness: real_minimizers_separated; consumer: result; Direct frozen dependencies: F2, F4, F5, F6, F7, F11, F13.
proof_shape: chosenApproximant: bind-only; escape_witness: none; consumer: chosenApproximant_spec, result; Direct frozen dependencies: F1, F3, F4, F7, F8, F9, F10, F11, F12.
proof_shape: chosenApproximant_spec: bind-only; escape_witness: none; consumer: result; Direct frozen dependencies: F1, F3, F4, F7, F8, F9, F10, F11, F12.
proof_shape: result: content; escape_witness: real_minimizers_separated; consumer: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13.
-/

import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
import D5.S3.Quantum.NormCompression.UpperBranchReduction
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
namespace D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation

open Polynomial
open D5.S3.Quantum.NormCompression.UpperBranchReduction

def IsCpApproximant {m n : ℕ} (p : ℝ)
    (M : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (A B : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  B ∈ M ∧ ∀ X ∈ M, schattenNorm p (A - B) ≤ schattenNorm p (A - X)

def IsStrictSpectralApproximant {m n : ℕ}
    (M : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (A B : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  B ∈ M ∧ ∀ X ∈ M, toLex ((fun k => (Matrix.toEuclideanLin (A - B)).singularValues k)) ≤ toLex ((fun k => (Matrix.toEuclideanLin (A - X)).singularValues k))

def claim : Prop := ∀ (m n : ℕ)
    (M : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (A Bst : Matrix (Fin m) (Fin n) ℂ)
    (B : ℝ → Matrix (Fin m) (Fin n) ℂ),
  IsStrictSpectralApproximant M A Bst →
  (∀ p, 1 < p → IsCpApproximant p M A (B p)) →
  Filter.Tendsto (fun p => A - B p) Filter.atTop (nhds (A - Bst))

open scoped Matrix BigOperators InnerProductSpace

private def H : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 1; 0, -2, 0; 1, 0, 0]

private def M : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) := Submodule.span ℂ {H, (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ)))}
private def R (s t : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![1 + s, 0, s; 0, 1 - 2 * s, 0; s, 0, t]

private theorem residual_formula (s t : ℂ) :
    (1 : Matrix (Fin 3) (Fin 3) ℂ) - ((-s) • H + (1 - t) • (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ)))) = R s t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.diagonal_apply, Pi.single_apply, R, Matrix.one_apply, Matrix.smul_apply] <;> ring

private theorem parametrization (B : Matrix (Fin 3) (Fin 3) ℂ) : B ∈ M ↔ ∃ s t : ℂ, 1 - B = R s t := by
  constructor
  · intro hB
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hB
    refine ⟨-a, 1 - b, ?_⟩
    rw [← hab]
    simpa using residual_formula (-a) (1 - b)
  · rintro ⟨s, t, hst⟩
    apply Submodule.mem_span_pair.mpr
    refine ⟨-s, 1 - t, ?_⟩
    have h := residual_formula s t
    rw [← hst] at h
    exact sub_right_injective h

private theorem E_mem : (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))) ∈ M := by
  apply Submodule.subset_span
  simp

private theorem disk_intersection {s : ℂ} (h1 : ‖1 + s‖ ≤ 1) (h2 : ‖1 - 2 * s‖ ≤ 1) : s = 0 := by
  have h1sq : ‖1 + s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (1 + s)]
  have h2sq : ‖1 - 2 * s‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (1 - 2 * s)]
  rw [← Complex.normSq_eq_norm_sq] at h1sq h2sq
  simp [Complex.normSq_apply] at h1sq h2sq
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · nlinarith [sq_nonneg s.re, sq_nonneg s.im]
  · nlinarith [sq_nonneg s.re, sq_nonneg s.im]

private theorem residual_eq_strict : R 0 0 = 1 - (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))) := by
  simpa using (residual_formula 0 0).symm

private theorem norm_apply_le_sv0 {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : V →ₗ[ℂ] W) (x : V) :
    ‖T x‖ ≤ T.singularValues 0 * ‖x‖ := by
  by_cases hd : Module.finrank ℂ V = 0
  · haveI : Subsingleton V := (Module.finrank_zero_iff.mp hd)
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  let n := Module.finrank ℂ V
  have hn : 0 < n := Nat.pos_of_ne_zero hd
  let G := T.adjoint ∘ₗ T
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  have he := expectation_eq_eigenvalue_sum T.isSymmetric_adjoint_comp_self rfl x
  have hnorm : (inner ℂ x (G x)).re = ‖T x‖ ^ 2 := by
    dsimp [G]
    rw [T.adjoint_inner_right]
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (T x)).symm
  rw [hnorm] at he
  have hbound : ‖T x‖ ^ 2 ≤ T.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
    rw [he]
    calc
      _ ≤ ∑ j : Fin n, ‖inner ℂ (b j) x‖ ^ 2 * T.singularValues 0 ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [T.sq_singularValues_of_lt rfl hn]
        apply T.isSymmetric_adjoint_comp_self.eigenvalues_antitone
        exact Nat.zero_le _
      _ = _ := by rw [← Finset.sum_mul, b.sum_sq_norm_inner_right]; ring
  have hp : 0 ≤ T.singularValues 0 * ‖x‖ := mul_nonneg (T.singularValues_nonneg 0) (norm_nonneg _)
  nlinarith [norm_nonneg (T x)]

private theorem entry_le_sv0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    ‖A i j‖ ≤ (Matrix.toEuclideanLin A).singularValues 0 := by
  let v : EuclideanSpace ℂ (Fin n) := (EuclideanSpace.basisFun (Fin n) ℂ) j
  have hb := norm_apply_le_sv0 (Matrix.toEuclideanLin A) v
  have hv : ‖v‖ = 1 := OrthonormalBasis.norm_eq_one _ _
  have ha : Matrix.toEuclideanLin A v = WithLp.toLp 2 (fun k => A k j) := by
    ext k
    simp [v, EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one]
  rw [hv, mul_one, ha] at hb
  exact (PiLp.norm_apply_le (WithLp.toLp 2 (fun k => A k j)) i).trans hb

private theorem diagonal_hermitian {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [IsSelfAdjoint]

private theorem diagonal_roots {n : ℕ} (d : Fin n → ℂ) :
    (Matrix.diagonal d).charpoly.roots = Finset.univ.val.map d := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private theorem diagonal_sorted_eigenvalues {n : ℕ} (d : Fin n → ℝ) (hd : Antitone d) :
    (diagonal_hermitian d).eigenvalues₀ = fun i => d (Fin.cast (Fintype.card_fin n) i) := by
  have he := (diagonal_hermitian d).sort_roots_charpoly_eq_eigenvalues₀
  rw [diagonal_roots] at he
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re, Fin.univ_val_map,
    Multiset.map_coe, List.map_ofFn, RCLike.ofReal_re, Multiset.coe_sort] at he
  change (List.ofFn d).mergeSort (fun x y => decide (x ≥ y)) = _ at he
  have hsorted : List.Pairwise (fun x y : ℝ => decide (x ≥ y) = true) (List.ofFn d) := by
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hd.sortedGE_ofFn
  rw [List.mergeSort_of_pairwise hsorted] at he
  apply List.ofFn_inj.mp
  simpa using he.symm

private theorem sv_diagonal {n : ℕ} (d : Fin n → ℂ) (hd : Antitone (fun i => ‖d i‖))
    (i : Fin n) : (fun k => (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues k) i = ‖d i‖ := by
  let T := Matrix.toEuclideanLin (Matrix.diagonal d)
  have hgram : T.adjoint ∘ₗ T =
      Matrix.toEuclideanLin (Matrix.diagonal (fun j => ((‖d j‖ ^ 2 : ℝ) : ℂ))) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change Matrix.toLpLin 2 2 (Matrix.diagonal d)ᴴ ∘ₗ
      Matrix.toLpLin 2 2 (Matrix.diagonal d) = _
    rw [← Matrix.toLpLin_mul_same]
    congr 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [RCLike.conj_mul]
  have hsq := T.sq_singularValues_fin finrank_euclideanSpace
    (Fin.cast (Fintype.card_fin n).symm i)
  have hmono : Antitone (fun j => ‖d j‖ ^ 2) := by
    intro a b hab
    have hh := hd hab
    nlinarith [norm_nonneg (d a), norm_nonneg (d b)]
  simp only [hgram] at hsq
  change _ = (diagonal_hermitian (fun j => ‖d j‖ ^ 2)).eigenvalues₀
    (Fin.cast (Fintype.card_fin n).symm i) at hsq
  rw [diagonal_sorted_eigenvalues _ hmono] at hsq
  simp only [Fin.cast_cast, Fin.cast_refl] at hsq
  have hnonneg := T.singularValues_nonneg i
  change 0 ≤ (fun k => (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues k) i at hnonneg
  change (fun k => (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues k) i ^ 2 = ‖d i‖ ^ 2 at hsq
  nlinarith [norm_nonneg (d i)]

private theorem strict_sv (k : ℕ) : (fun k => (Matrix.toEuclideanLin (R 0 0)).singularValues k) k = if k < 2 then 1 else 0 := by
  let d : Fin 3 → ℂ := ![1, 1, 0]
  have heq : R 0 0 = Matrix.diagonal d := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, Matrix.diagonal, d]
  rw [heq]
  by_cases hk : k < 3
  · have hmono : Antitone (fun i => ‖d i‖) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [d]
    have hh := sv_diagonal d hmono (⟨k, hk⟩ : Fin 3)
    change (fun k => (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues k) k = ‖d ⟨k, hk⟩‖ at hh
    rw [hh]
    interval_cases k <;> norm_num [d]
  · have hz := (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues_of_finrank_le
      (by simpa using Nat.le_of_not_gt hk)
    simp only [hz, if_neg (by omega : ¬ k < 2)]

private theorem sv_residual_zero_first_two {t : ℂ} (ht : ‖t‖ ≤ 1) {k : ℕ} (hk : k < 2) :
    (fun k => (Matrix.toEuclideanLin (R 0 t)).singularValues k) k = 1 := by
  let d : Fin 3 → ℂ := ![1, 1, t]
  have heq : R 0 t = Matrix.diagonal d := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, Matrix.diagonal, d]
  have hmono : Antitone (fun i => ‖d i‖) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hs := sv_diagonal d hmono (⟨k, by omega⟩ : Fin 3)
  change (fun k => (Matrix.toEuclideanLin (Matrix.diagonal d)).singularValues k) k = ‖d ⟨k, by omega⟩‖ at hs
  rw [heq, hs]
  interval_cases k <;> norm_num [d]

private theorem spectral_face {s t : ℂ} (hsv : (fun k => (Matrix.toEuclideanLin (R s t)).singularValues k) 0 ≤ 1) : s = 0 ∧ ‖t‖ ≤ 1 := by
  have hzero : s = 0 := disk_intersection
    (by simpa [R] using (entry_le_sv0 (R s t) 0 0).trans hsv)
    (by simpa [R] using (entry_le_sv0 (R s t) 1 1).trans hsv)
  refine ⟨hzero, ?_⟩
  simpa [R] using (entry_le_sv0 (R s t) 2 2).trans hsv

private theorem strict_approximant : IsStrictSpectralApproximant M 1 (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))) := by
  refine ⟨E_mem, ?_⟩
  intro X hX
  obtain ⟨s, t, hst⟩ := (parametrization X).mp hX
  rw [← residual_eq_strict, hst]
  by_cases hfirst : (fun k => (Matrix.toEuclideanLin (R s t)).singularValues k) 0 ≤ 1
  · obtain ⟨rfl, ht⟩ := spectral_face hfirst
    apply Pi.toLex_monotone
    intro k
    by_cases hk : k < 2
    · simp only [strict_sv, if_pos hk, sv_residual_zero_first_two ht hk, le_refl]
    · simp only [strict_sv, if_neg hk]
      exact (Matrix.toEuclideanLin (R 0 t)).singularValues_nonneg k
  · apply le_of_lt
    change Pi.Lex (· < ·) (· < ·) ((fun k => (Matrix.toEuclideanLin (R 0 0)).singularValues k)) ((fun k => (Matrix.toEuclideanLin (R s t)).singularValues k))
    refine ⟨0, ?_, ?_⟩
    · intro j hj
      omega
    · simpa only [strict_sv, if_pos (by norm_num : (0 : ℕ) < 2)] using lt_of_not_ge hfirst

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

private theorem schattenPow_trace {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Matrix (Fin n) (Fin n) ℂ) :
    schattenPow p A = (cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)).trace.re := by
  rw [schattenPow_eq_columnGram p hp A, D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum _ (Matrix.isHermitian_conjTranspose_mul_self A)]

private theorem continuous_schattenPow {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (schattenPow p : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  have hfun : Continuous (fun x : ℝ => x ^ (p / 2)) :=
    continuous_id.rpow_const (fun _ => Or.inr (by positivity))
  have hgram : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => Aᴴ * A) := by fun_prop
  have hcont : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)) := by
    exact hgram.cfc_of_mem_nhdsSet (fun x : ℝ => x ^ (p / 2))
      (s := Set.univ) (by simp) (fun A => (Matrix.isHermitian_conjTranspose_mul_self A).isSelfAdjoint)
      hfun.continuousOn
  have htrace : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)).trace.re) := by
    unfold Matrix.trace
    fun_prop
  convert htrace using 1
  funext A
  exact schattenPow_trace hp A

private theorem sv0_pow_le {m n : ℕ} {p : ℝ} (hp : 0 < p) (A : Matrix (Fin m) (Fin n) ℂ) :
    (Matrix.toEuclideanLin A).singularValues 0 ^ p ≤ schattenPow p A := by
  let T := Matrix.toEuclideanLin A
  by_cases hz : T.singularValues 0 = 0
  · simpa [hz, T, Real.zero_rpow hp.ne'] using schattenPow_nonneg p A
  · exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (T.singularValues_nonneg i) p)
      (Finsupp.mem_support_iff.mpr hz)

private theorem entry_pow_le {m n : ℕ} {p : ℝ} (hp : 0 < p) (A : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin m) (j : Fin n) : ‖A i j‖ ^ p ≤ schattenPow p A :=
  (Real.rpow_le_rpow (norm_nonneg _) (entry_le_sv0 A i j) hp.le).trans (sv0_pow_le hp A)

private theorem exists_pair_minimizer {p : ℝ} (hp : 1 < p) :
    ∃ z : ℂ × ℂ, ∀ w : ℂ × ℂ,
      schattenPow p (R z.1 z.2) ≤ schattenPow p (R w.1 w.2) := by
  let f : ℂ × ℂ → ℝ := fun z => schattenPow p (R z.1 z.2)
  have hf : Continuous f := by
    apply (continuous_schattenPow (by linarith : 0 < p)).comp
    unfold R
    fun_prop
  have hf0 : 0 ≤ f 0 := schattenPow_nonneg p (R 0 0)
  let C := f 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; linarith [hf0]
  have hbounded (z : ℂ × ℂ) (hz : f z ≤ f 0) : ‖z‖ ≤ C := by
    have hcoord (a : ℂ) (ha : ‖a‖ ^ p ≤ f z) : ‖a‖ ≤ C := by
      by_contra! h
      have h1 : 1 ≤ ‖a‖ := by dsimp [C] at h; linarith [hf0]
      have hpow := Real.self_le_rpow_of_one_le h1 hp.le
      dsimp [C] at h
      linarith
    have hs := entry_pow_le (by linarith : 0 < p) (R z.1 z.2) 0 2
    have ht := entry_pow_le (by linarith : 0 < p) (R z.1 z.2) 2 2
    have hs' : ‖z.1‖ ≤ C := hcoord z.1 (by simpa [R, f] using hs)
    have ht' : ‖z.2‖ ≤ C := hcoord z.2 (by simpa [R, f] using ht)
    simpa only [Prod.norm_def, max_le_iff] using And.intro hs' ht'
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall (0 : ℂ × ℂ) C).exists_isMinOn
    ⟨0, by simpa using hC⟩ hf.continuousOn
  refine ⟨z, fun w => ?_⟩
  by_cases hw : w ∈ Metric.closedBall (0 : ℂ × ℂ) C
  · exact hmin hw
  · have h0 : f z ≤ f 0 := hmin (by simpa using hC)
    have hhigh : f 0 < f w := by
      by_contra! h
      exact hw (by simpa [Metric.mem_closedBall, dist_zero_right] using hbounded w h)
    exact h0.trans hhigh.le

private theorem exists_cp_approximant {p : ℝ} (hp : 1 < p) : ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsCpApproximant p M 1 B := by
  obtain ⟨z, hz⟩ := exists_pair_minimizer hp
  let B : Matrix (Fin 3) (Fin 3) ℂ := (-z.1) • H + (1 - z.2) • (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ)))
  refine ⟨B, ?_, ?_⟩
  · exact Submodule.mem_span_pair.mpr ⟨-z.1, 1 - z.2, rfl⟩
  · intro X hX
    obtain ⟨s, t, hst⟩ := (parametrization X).mp hX
    have hmin := hz (s, t)
    unfold schattenNorm
    dsimp [B]
    rw [residual_formula, hst]
    exact Real.rpow_le_rpow (schattenPow_nonneg p _) hmin (by positivity)

open scoped BigOperators Matrix
open Polynomial D5.S3.Quantum.NormCompression.UpperBranchReduction
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar

private def block (d h s t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := !![d, 0, s; 0, h, 0; s, 0, t]
private theorem gram_charpoly (d h s t a b : ℝ) (hab : a + b = d + t) (hp : a * b = d * t - s ^ 2) :
    ((block d h s t)ᴴ * block d h s t).charpoly =
      (X - C ((a ^ 2 : ℝ) : ℂ)) * (X - C ((h ^ 2 : ℝ) : ℂ)) * (X - C ((b ^ 2 : ℝ) : ℂ)) := by
  have hsum : a ^ 2 + b ^ 2 = d ^ 2 + t ^ 2 + 2 * s ^ 2 := by
    have hs := congrArg (fun x : ℝ => x ^ 2) hab
    nlinarith
  have hprod : a ^ 2 * b ^ 2 = (d * t - s ^ 2) ^ 2 := by rw [← hp]; ring
  have hsumC := congrArg (fun x : ℝ => C (x : ℂ)) hsum
  have hprodC := congrArg (fun x : ℝ => C (x : ℂ)) hprod
  push_cast at hsumC hprodC
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hsumC hprodC
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three, block,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, Matrix.conjTranspose_apply]
  linear_combination X * ((X : ℂ[X]) - C (h : ℂ) ^ 2) * hsumC -
    ((X : ℂ[X]) - C (h : ℂ) ^ 2) * hprodC

private theorem schattenPow_roots {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Matrix (Fin n) (Fin n) ℂ) :
    schattenPow p A = (((Aᴴ * A).charpoly.roots.map (fun z : ℂ => z.re ^ (p / 2))).sum) := by
  rw [schattenPow_eq_columnGram p hp A,
    (Matrix.isHermitian_conjTranspose_mul_self A).roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_map, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, List.sum_ofFn]

theorem rpow_square_half (a p : ℝ) : (a ^ 2) ^ (p / 2) = |a| ^ p := by
  rw [Real.rpow_div_two_eq_sqrt _ (sq_nonneg a), Real.sqrt_sq_eq_abs]

private theorem block_schattenPow {p : ℝ} (hp : 0 < p) (d h s t a b : ℝ)
    (hab : a + b = d + t) (hpab : a * b = d * t - s ^ 2) :
    schattenPow p (block d h s t) = |a| ^ p + |h| ^ p + |b| ^ p := by
  have hchar := gram_charpoly d h s t a b hab hpab
  have hroots : ((block d h s t)ᴴ * block d h s t).charpoly.roots =
      ({((a ^ 2 : ℝ) : ℂ), ((h ^ 2 : ℝ) : ℂ), ((b ^ 2 : ℝ) : ℂ)} : Multiset ℂ) := by
    rw [hchar]
    rw [Polynomial.roots_mul (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _)) (Polynomial.X_sub_C_ne_zero _)),
      Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _))]
    simp only [Polynomial.roots_X_sub_C]
    rfl
  rw [schattenPow_roots hp, hroots]
  have hcast (x : ℝ) : ((x : ℂ) ^ (2 : ℕ)).re = x ^ (2 : ℕ) := by
    simp [pow_two, Complex.mul_re]
  simp [hcast, rpow_square_half, add_assoc]

private theorem residual_real_eq_block (s t : ℝ) : R (s : ℂ) (t : ℂ) = block (1 + s) (1 - 2 * s) s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R, block] <;> push_cast <;> ring

private theorem residual_real_schattenPow {p : ℝ} (hp : 0 < p) (s t : ℝ) :
    schattenPow p (R (s : ℂ) (t : ℂ)) =
      |topRoot (1 + s) s t| ^ p + |1 - 2 * s| ^ p + |bottomRoot (1 + s) s t| ^ p := by
  rw [residual_real_eq_block]
  exact block_schattenPow hp _ _ _ _ _ _ (topRoot_sum _ _ _) (topRoot_product _ _ _)

open scoped BigOperators Matrix InnerProductSpace ComplexOrder MatrixOrder
open Polynomial D5.S3.Quantum.NormCompression.UpperBranchReduction

private theorem hermitian_schattenPow {n : ℕ} {p : ℝ} (hp : 0 < p)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    schattenPow p A = ∑ i, |hA.eigenvalues i| ^ p := by
  have hchar : (Aᴴ * A).charpoly =
      ∏ i, (X - C (((hA.eigenvalues i) ^ (2 : ℕ) : ℝ) : ℂ)) := by
    rw [hA.eq, ← sq, ← cfc_pow_id (R := ℝ) A 2 hA.isSelfAdjoint]
    exact hA.charpoly_cfc_eq (fun x : ℝ => x ^ (2 : ℕ))
  have hroots : (Aᴴ * A).charpoly.roots = Finset.univ.val.map
      (fun i : Fin n => (((hA.eigenvalues i) ^ (2 : ℕ) : ℝ) : ℂ)) := by
    rw [hchar, Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero _))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have hcast (x : ℝ) : ((x : ℂ) ^ (2 : ℕ)).re = x ^ (2 : ℕ) := by
    simp [pow_two, Complex.mul_re]
  rw [schattenPow_roots hp, hroots]
  simp [Multiset.map_map, Function.comp_def, hcast, rpow_square_half, List.sum_ofFn]

private theorem gram_basis_bound {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (∑ i, ‖Matrix.toEuclideanLin A (b i)‖ ^ p) ≤ schattenPow p A := by
  let T := Matrix.toEuclideanLin A
  let e := finCongr (Fintype.card_fin n).symm
  have hdiag := diagonal_power_le_eigenvalue_power T.isPositive_adjoint_comp_self finrank_euclideanSpace (b.reindex e)
    (show 1 ≤ p / 2 by linarith)
  have hgram : T.adjoint ∘ₗ T = Matrix.toEuclideanLin (Aᴴ * A) := by
    dsimp [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change Matrix.toLpLin 2 2 Aᴴ ∘ₗ Matrix.toLpLin 2 2 A = _
    rw [← Matrix.toLpLin_mul_same]
  have hexp (i : Fin n) : (⟪b i, (T.adjoint ∘ₗ T) (b i)⟫_ℂ).re = ‖T (b i)‖ ^ 2 := by
    rw [LinearMap.comp_apply, T.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hself (x : EuclideanSpace ℂ (Fin n)) : (⟪x,x⟫_ℂ).re = ‖x‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simp only [OrthonormalBasis.reindex_apply, LinearMap.comp_apply, T.adjoint_inner_right,
    hself, ← Real.rpow_natCast_mul (norm_nonneg _)] at hdiag
  have hr := RHLinalg.sum_eigenvalues_reindex (Matrix.isHermitian_conjTranspose_mul_self A) (· ^ (p / 2))
  simp only [hgram] at hdiag
  change (∑ i : Fin (Fintype.card (Fin n)), ‖T (b (e.symm i))‖ ^ ((2 : ℝ)*(p/2))) ≤
    ∑ i, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ i ^ (p/2) at hdiag
  rw [← hr] at hdiag
  have hsum := Equiv.sum_comp e.symm (fun i : Fin n => ‖T (b i)‖ ^ p)
  have he : (2 : ℝ)*(p/2) = p := by ring
  simp only [he] at hdiag
  rw [hsum] at hdiag
  rw [schattenPow_eq_columnGram p (by linarith) A]
  exact hdiag

private theorem diagonal_power_bound {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ‖A i i‖ ^ p) ≤ schattenPow p A := by
  have h := gram_basis_bound hp A (EuclideanSpace.basisFun (Fin n) ℂ)
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) h
  apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
  have he : Matrix.toEuclideanLin A ((EuclideanSpace.basisFun (Fin n) ℂ) i) =
      WithLp.toLp 2 (fun k => A k i) := by
    ext k
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one]
  rw [he]
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun k => A k i)) i

private theorem hermitianPart_hermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (((selfAdjointPart ℝ A).val)).IsHermitian := by
  exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (selfAdjointPart ℝ A).property

private theorem re_inner_hermitianPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    (⟪x, Matrix.toEuclideanLin (((selfAdjointPart ℝ A).val)) x⟫_ℂ).re =
      (⟪x, Matrix.toEuclideanLin A x⟫_ℂ).re := by
  have he : (selfAdjointPart ℝ A).val = (1 / 2 : ℂ) • (A + Aᴴ) := by
    ext i j
    simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, smul_eq_mul]
    ring
  rw [he, map_smul, map_add, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.smul_apply, LinearMap.add_apply, inner_smul_right, inner_add_right,
    LinearMap.adjoint_inner_right]
  simp only [Complex.mul_re, Complex.add_re, Complex.conj_re,
    show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num,
    show (1 / 2 : ℂ).im = 0 by norm_num, mul_zero, sub_zero]
  have hre := inner_re_symm (𝕜 := ℂ) x (Matrix.toEuclideanLin A x)
  change (⟪x, Matrix.toEuclideanLin A x⟫_ℂ).re =
    (⟪Matrix.toEuclideanLin A x, x⟫_ℂ).re at hre
  rw [hre]
  ring

private theorem hermitianPart_contracts {n : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    schattenPow p (((selfAdjointPart ℝ A).val)) ≤ schattenPow p A := by
  let hP := hermitianPart_hermitian A
  let b := hP.eigenvectorBasis
  rw [hermitian_schattenPow (by linarith) hP]
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) (gram_basis_bound hp A b)
  have heig : Matrix.toEuclideanLin (((selfAdjointPart ℝ A).val)) (b i) =
      (hP.eigenvalues i : ℂ) • b i := by
    ext j
    change (((selfAdjointPart ℝ A).val) *ᵥ (b i).ofLp) j =
      (hP.eigenvalues i : ℂ) * (b i).ofLp j
    exact congrFun (hP.mulVec_eigenvectorBasis i) j
  have hinner := congrArg (fun y => (⟪b i, y⟫_ℂ).re) heig
  rw [re_inner_hermitianPart] at hinner
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K,
    OrthonormalBasis.norm_eq_one] at hinner
  simp only [RCLike.ofReal_one, one_pow, mul_one, RCLike.ofReal_re] at hinner
  change (⟪b i, Matrix.toEuclideanLin A (b i)⟫_ℂ).re = hP.eigenvalues i at hinner
  apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
  rw [← hinner]
  calc
    |(⟪b i, Matrix.toEuclideanLin A (b i)⟫_ℂ).re| ≤
        ‖⟪b i, Matrix.toEuclideanLin A (b i)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖b i‖ * ‖Matrix.toEuclideanLin A (b i)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [OrthonormalBasis.norm_eq_one, one_mul]

private theorem hermitianPart_residual (s t : ℂ) :
    ((selfAdjointPart ℝ (R s t)).val) = R (s.re : ℂ) (t.re : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose, RCLike.real_smul_eq_coe_smul, R, Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem real_residual_contracts {p : ℝ} (hp : 2 ≤ p) (s t : ℂ) :
    schattenPow p (R (s.re : ℂ) (t.re : ℂ)) ≤ schattenPow p (R s t) := by
  rw [← hermitianPart_residual]
  exact hermitianPart_contracts hp _

open scoped BigOperators Matrix
open Filter D5.S3.Quantum.NormCompression.UpperBranchReduction

private def sstar (p : ℝ) : ℝ := 1 / (8 * p)
private def envelope (p : ℝ) : ℝ :=
  (1 + (1/7)/p)^p + (1 + (-1/4)/p)^p + (51/100 : ℝ)^p

private theorem abs_bernoulli {p x : ℝ} (hp : 1 ≤ p) : 1 + p*x ≤ |1+x|^p := by
  by_cases hx : -1 ≤ x
  · simpa only [abs_of_nonneg (show 0 ≤ 1+x by linarith)] using
      one_add_mul_self_le_rpow_one_add hx hp
  · have hpx : p*x ≤ -1 := by nlinarith
    exact (by linarith : 1+p*x ≤ 0).trans (Real.rpow_nonneg (abs_nonneg _) _)

private theorem top_competitor_bounds {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/10) :
    1+s ≤ topRoot (1+s) s (-1/2) ∧
    topRoot (1+s) s (-1/2) ≤ 1+s+(2/3)*s^2 ∧
    |bottomRoot (1+s) s (-1/2)| ≤ 51/100 := by
  have hge := topRoot_bounds (1+s) s (-1/2)
  have he := topRoot_determinant (1+s) s (-1/2)
  have hsum := topRoot_sum (1+s) s (-1/2)
  have hdelta : 0 ≤ topRoot (1+s) s (-1/2) - (1+s) := by linarith
  have hbound : topRoot (1+s) s (-1/2) - (1+s) ≤ (2/3)*s^2 := by
    nlinarith
  have hb : bottomRoot (1+s) s (-1/2) ≤ 0 := by linarith
  rw [abs_of_nonpos hb]
  have hsq : s^2 ≤ 1/100 := by nlinarith
  exact ⟨hge.1, by linarith, by linarith⟩

private theorem top_comparison_gap {s t : ℝ} (hs : 0 ≤ s)
    (hL : topRoot (1+s) s t ≤ 11/10) (ht : -1/4 ≤ t) :
    s^2/21 ≤ topRoot (1+s) s t - topRoot (1+s) s (-1/2) := by
  have hge := topRoot_bounds (1+s) s t
  have hge' := topRoot_bounds (1+s) s (-1/2)
  have he := topRoot_determinant (1+s) s t
  have he' := topRoot_determinant (1+s) s (-1/2)
  have hdelta : 0 ≤ topRoot (1+s) s t - (1+s) := by linarith
  have hdelta' : 0 ≤ topRoot (1+s) s (-1/2) - (1+s) := by linarith
  have ha : topRoot (1+s) s t - t ≤ 27/20 := by linarith
  have hb : 3/2 ≤ topRoot (1+s) s (-1/2) + 1/2 := by linarith
  have hlower : (20/27)*s^2 ≤ topRoot (1+s) s t - (1+s) := by nlinarith
  have hupper : topRoot (1+s) s (-1/2) - (1+s) ≤ (2/3)*s^2 := by nlinarith
  nlinarith [sq_nonneg s]

private theorem rpow_difference_bound {p a b : ℝ} (hp : 1 ≤ p) (hb : 1 ≤ b) (hab : b ≤ a) :
    p*(a-b) ≤ a^p-b^p := by
  have hb0 : 0 < b := by linarith
  have hx : -1 ≤ (a-b)/b := (by norm_num : (-1 : ℝ) ≤ 0).trans (div_nonneg (sub_nonneg.mpr hab) hb0.le)
  have hh := one_add_mul_self_le_rpow_one_add hx hp
  have he : 1+(a-b)/b = a/b := by field_simp; ring
  rw [he, Real.div_rpow (by linarith : 0 ≤ a) hb0.le] at hh
  have hh' := (le_div_iff₀ (Real.rpow_pos_of_pos hb0 p)).mp hh
  have hbpow := Real.self_le_rpow_of_one_le hb hp
  have hmul : p*(a-b) ≤ p*(a-b)/b*b^p := by
    have hnonneg : 0 ≤ p*(a-b)/b := by positivity
    have h := mul_le_mul_of_nonneg_left hbpow hnonneg
    have he' : p*(a-b)/b*b = p*(a-b) := by field_simp
    rwa [he'] at h
  have heq : (1 + p * ((a-b)/b)) * b^p = b^p + p*(a-b)/b*b^p := by ring
  rw [heq] at hh'
  linarith

private theorem exp_limit_bound : Real.exp (1/7) + Real.exp (-1/4) < (63/32 : ℝ) := by
  have h1 := Real.exp_bound_div_one_sub_of_interval (x := 1/7) (by norm_num) (by norm_num)
  have h2 : Real.exp (-1/4) ≤ 4/5 := by
    have h := Real.add_one_le_exp (1/4)
    rw [show (-1/4 : ℝ) = -(1/4) by ring, Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  norm_num at h1
  linarith

open scoped BigOperators Matrix
open Filter D5.S3.Quantum.NormCompression.UpperBranchReduction

private theorem residual_power_lower {p : ℝ} (hp : 2 ≤ p) (s t : ℝ) :
    2-p*s ≤ schattenPow p (R (s : ℂ) (t : ℂ)) := by
  have hd := diagonal_power_bound hp (R (s : ℂ) (t : ℂ))
  rw [Fin.sum_univ_three] at hd
  change ‖1+(s : ℂ)‖^p + ‖1-2*(s : ℂ)‖^p + ‖(t : ℂ)‖^p ≤
    schattenPow p (R (s : ℂ) (t : ℂ)) at hd
  have hn1 : ‖1+(s : ℂ)‖ = |1+s| := by rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖1-2*(s : ℂ)‖ = |1-2*s| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn1, hn2, Complex.norm_real, Real.norm_eq_abs] at hd
  have h1 := abs_bernoulli (by linarith : 1 ≤ p) (x := s)
  have h2 := abs_bernoulli (by linarith : 1 ≤ p) (x := -2*s)
  have h2' : 1+p*(-2*s) ≤ |1-2*s|^p := by simpa only [sub_eq_add_neg, neg_mul] using h2
  have ht := Real.rpow_nonneg (abs_nonneg t) p
  linarith

private theorem competitor_power_bound {p : ℝ} (hp : 2 ≤ p) :
    schattenPow p (R ((sstar p) : ℂ) ((-1/2 : ℝ) : ℂ)) ≤ envelope p := by
  have hp0 : 0 < p := by linarith
  have hs : 0 ≤ sstar p := by unfold sstar; positivity
  have hs1 : sstar p ≤ 1/10 := by
    unfold sstar
    apply (div_le_iff₀ (by positivity : 0 < 8*p)).mpr
    linarith
  have hs2 : sstar p + (2/3)*(sstar p)^2 ≤ (1/7)/p := by
    unfold sstar
    field_simp
    nlinarith
  have hb := top_competitor_bounds hs hs1
  have htop : 0 ≤ topRoot (1+sstar p) (sstar p) (-1/2) := by linarith
  have hmid : 0 ≤ 1-2*sstar p := by linarith
  unfold envelope
  rw [residual_real_schattenPow hp0, abs_of_nonneg htop, abs_of_nonneg hmid]
  have hmidEq : 1-2*sstar p = 1+(-1/4)/p := by unfold sstar; field_simp; ring
  rw [hmidEq]
  have hlead := Real.rpow_le_rpow htop (show topRoot (1+sstar p) (sstar p) (-1/2) ≤ 1+(1/7)/p by linarith) hp0.le
  have htail := Real.rpow_le_rpow (abs_nonneg _) hb.2.2 hp0.le
  linarith

private theorem envelope_eventually : ∀ᶠ p : ℝ in atTop, envelope p < 63/32 := by
  have h1 := Real.tendsto_one_add_div_rpow_exp (1/7)
  have h2 := Real.tendsto_one_add_div_rpow_exp (-1/4)
  have h3 := tendsto_rpow_atTop_of_base_lt_one (51/100) (by norm_num) (by norm_num)
  have hlim : Tendsto envelope atTop (nhds (Real.exp (1/7)+Real.exp (-1/4))) := by
    change Tendsto (fun p : ℝ => (1+(1/7)/p)^p + (1+(-1/4)/p)^p + (51/100 : ℝ)^p) atTop _
    simpa only [add_zero] using (h1.add h2).add h3
  exact hlim.eventually (gt_mem_nhds exp_limit_bound)

private theorem exponential_small : Tendsto (fun p : ℝ => 21*p*(51/100 : ℝ)^p) atTop (nhds 0) := by
  have hlog : 0 < -Real.log (51/100 : ℝ) := neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hlog).const_mul 21
  convert h using 1
  · funext p
    rw [Real.rpow_one, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 51/100)]
    simp only [neg_neg]
    ring
  · ring

open scoped BigOperators Matrix
open Filter D5.S3.Quantum.NormCompression.UpperBranchReduction

set_option maxHeartbeats 800000 in
private theorem real_minimizers_separated :
    ∀ᶠ p : ℝ in atTop, ∀ s t : ℝ, (∀ u v : ℝ, schattenPow p (R (s : ℂ) (t : ℂ)) ≤ schattenPow p (R (u : ℂ) (v : ℂ))) → t < -1/4 := by
  have hbig : ∀ᶠ p : ℝ in atTop, 2 < (11/10 : ℝ)^p :=
    (tendsto_rpow_atTop_of_base_gt_one (11/10) (by norm_num)).eventually (eventually_gt_atTop 2)
  have hsmall : ∀ᶠ p : ℝ in atTop, 21*p*(51/100 : ℝ)^p < (1/64 : ℝ)^2 :=
    exponential_small.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop (2 : ℝ), envelope_eventually, hbig, hsmall] with p hp henv hbig hsmall
  intro s t hmin
  have hp0 : 0 < p := by linarith
  have hlow := residual_power_lower hp s t
  have hvalue : schattenPow p (R (s : ℂ) (t : ℂ)) < 63/32 :=
    (hmin (sstar p) (-1/2)).trans_lt ((competitor_power_bound hp).trans_lt henv)
  have hs : 0 < s := by
    by_contra! h
    have hps : p*s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0.le h
    linarith
  have hge := topRoot_bounds (1+s) s t
  have hL0 : 0 ≤ topRoot (1+s) s t := by linarith
  have hLpow : topRoot (1+s) s t ^ p ≤ schattenPow p (R (s : ℂ) (t : ℂ)) := by
    rw [residual_real_schattenPow hp0, abs_of_nonneg hL0]
    have hh := Real.rpow_nonneg (abs_nonneg (1-2*s)) p
    have hb := Real.rpow_nonneg (abs_nonneg (bottomRoot (1+s) s t)) p
    linarith
  have hL : topRoot (1+s) s t ≤ 11/10 := by
    by_contra! h
    have hb := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 11/10) h.le hp0.le
    linarith
  have hs1 : s ≤ 1/10 := by linarith
  by_contra! ht
  have hgap := top_comparison_gap hs.le hL ht
  have hc := top_competitor_bounds hs.le hs1
  have hLc0 : 0 ≤ topRoot (1+s) s (-1/2) := by linarith
  have horder : topRoot (1+s) s (-1/2) ≤ topRoot (1+s) s t := by nlinarith [sq_nonneg s]
  have hdiff := rpow_difference_bound (by linarith : 1 ≤ p)
    (by linarith : 1 ≤ topRoot (1+s) s (-1/2)) horder
  have hmgap := mul_le_mul_of_nonneg_left hgap hp0.le
  have hm := hmin s (-1/2)
  rw [residual_real_schattenPow hp0, residual_real_schattenPow hp0,
    abs_of_nonneg hL0, abs_of_nonneg hLc0] at hm
  have htail := Real.rpow_le_rpow (abs_nonneg _) hc.2.2 hp0.le
  have hb := Real.rpow_nonneg (abs_nonneg (bottomRoot (1+s) s t)) p
  have hineq : p*s^2/21 ≤ (51/100 : ℝ)^p := by nlinarith
  have hmineq := mul_le_mul_of_nonneg_left hineq (show 0 ≤ 21*p by positivity)
  have hps2 : (p*s)^2 ≤ 21*p*(51/100 : ℝ)^p := by nlinarith
  have hps : p*s < 1/64 := by nlinarith [mul_nonneg hp0.le hs.le]
  linarith

private theorem cp_power_min {p : ℝ} (hp : 0 < p) {B : Matrix (Fin 3) (Fin 3) ℂ}
    (hB : IsCpApproximant p M 1 B) (s t : ℂ) :
    schattenPow p (1-B) ≤ schattenPow p (R s t) := by
  have hmem : (-s) • H + (1-t) • (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))) ∈ M :=
    Submodule.mem_span_pair.mpr ⟨-s, 1-t, rfl⟩
  have hm := hB.2 _ hmem
  rw [residual_formula] at hm
  have h := Real.rpow_le_rpow (schattenNorm_nonneg p (1-B)) hm hp.le
  rwa [schattenNorm_rpow hp, schattenNorm_rpow hp] at h

private theorem cp_projects_to_real_min {p : ℝ} (hp : 2 ≤ p) {B : Matrix (Fin 3) (Fin 3) ℂ}
    (hB : IsCpApproximant p M 1 B) {s t : ℂ} (hst : 1-B = R s t) :
    (∀ u v : ℝ, schattenPow p (R (s.re : ℂ) (t.re : ℂ)) ≤ schattenPow p (R (u : ℂ) (v : ℂ))) := by
  intro u v
  have hc := real_residual_contracts hp s t
  have hm := cp_power_min (by linarith) hB (u : ℂ) (v : ℂ)
  rw [hst] at hm
  exact hc.trans hm

private theorem cp_minimizers_separated :
    ∀ᶠ p : ℝ in atTop, ∀ B : Matrix (Fin 3) (Fin 3) ℂ, IsCpApproximant p M 1 B → ((1-B) 2 2).re < -1/4 := by
  filter_upwards [eventually_ge_atTop (2 : ℝ), real_minimizers_separated] with p hp hsep
  intro B hB
  obtain ⟨s,t,hst⟩ := (parametrization B).mp hB.1
  have hm := cp_projects_to_real_min hp hB hst
  have h := hsep s.re t.re hm
  rw [hst]
  change t.re < -1/4
  exact h

open Filter D5.S3.Quantum.NormCompression.UpperBranchReduction

private def chosenApproximant (p : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  if hp : 1 < p then Classical.choose (exists_cp_approximant hp) else 0

private theorem chosenApproximant_spec (p : ℝ) (hp : 1 < p) :
    IsCpApproximant p M 1 (chosenApproximant p) := by
  simpa only [chosenApproximant, dif_pos hp] using Classical.choose_spec (exists_cp_approximant hp)

theorem result : ¬ claim := by
  intro hclaim
  have hlim := hclaim 3 3 M 1 (Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))) chosenApproximant strict_approximant chosenApproximant_spec
  have hc : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A 2 2).re) := by fun_prop
  have hcoord : Tendsto (fun p => ((1-chosenApproximant p) 2 2).re) atTop (nhds 0) := by
    simpa [Function.comp_def, Matrix.diagonal, Pi.single_apply, Matrix.one_apply] using (hc.tendsto (1-(Matrix.diagonal (Pi.single (2 : Fin 3) (1 : ℂ))))).comp hlim
  have hlow : ∀ᶠ p : ℝ in atTop, -1/8 < ((1-chosenApproximant p) 2 2).re :=
    hcoord.eventually_const_lt (by norm_num)
  have hbad : ∀ᶠ p : ℝ in atTop, False := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), cp_minimizers_separated, hlow] with p hp hsep hlow
    have h := hsep (chosenApproximant p) (chosenApproximant_spec p hp)
    linarith
  obtain ⟨p,hp⟩ := hbad.exists
  exact hp


end D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation
