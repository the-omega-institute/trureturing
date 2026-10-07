/- GID: D5/S3/Quantum/NormCompression/UpperBranchReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/NormCompression/UpperBranchReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper norm compression reduces to three rescaled original block columns. -/

/-
proof_shape: rescaling_upper_three: content; escape_witness: concentrate_three.
proof_shape: upper_three_columns: content; escape_witness: concentrate_three.
proof_shape: r1_upper: content; escape_witness: concentrate_three.
escape_witness: concentrate_three; recursive face elimination preserves three moments
and selects a boundary weight with a nondecreasing convex objective.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Weil/ZetaLinear/PosIndex;
RHLinalg.sum_eigenvalues_reindex;
statement_id: sha256:44735eecb5fa2fcff2a5c87a00623ee55b92a49196ae105de44a7f861b8dfd47.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: expectation_eq_eigenvalue_sum: bind-only; consumer: diagonal_power_le_eigenvalue_power.
proof_shape: diagonal_power_le_eigenvalue_power: bind-only; consumer: eigenPow_mix_le.
proof_shape: eigenPow_sq: bind-only; consumer: schattenPow_eq_eigenPow.
proof_shape: eigenPow_mix_le: bind-only; consumer: schattenNorm_triangle.
proof_shape: roots_smul: bind-only; consumer: sum_eigenvalues_smul.
proof_shape: sum_eigenvalues_smul: bind-only; consumer: schattenPow_sqrt_smul.
proof_shape: sum_eigenvalues_gram: bind-only; consumer: schattenPow_eq_rowGram.
proof_shape: schattenPow_eq_columnGram: bind-only; consumer: schattenPow_eq_rowGram, schattenPow_eq_eigenPow_columnGram, schattenPow_sqrt_smul.
proof_shape: schattenPow_eq_rowGram: bind-only; consumer: schattenPow_eq_eigenPow_rowGram.
proof_shape: schattenPow_eq_eigenPow_columnGram: bind-only; consumer: schattenPow_eq_eigenPow.
proof_shape: schattenPow_eq_eigenPow_rowGram: bind-only; consumer: rescaling_upper_three, upper_three_columns, r1_upper.
proof_shape: schattenPow_eq_eigenPow: bind-only; consumer: eigenPow_eq_norm_rpow, rescaling_upper_three.
proof_shape: schattenPow_nonneg: bind-only; consumer: schattenNorm_nonneg, schattenNorm_zero_iff, schattenNorm_sqrt_smul, schattenNorm_rpow, rescaling_upper_three.
proof_shape: schattenPow_zero_iff: bind-only; consumer: schattenNorm_zero_iff.
proof_shape: schattenPow_sqrt_smul: bind-only; consumer: schattenNorm_sqrt_smul.
proof_shape: schattenNorm_nonneg: bind-only; consumer: schattenNorm_triangle, schattenPow_mix_le, r1_upper.
proof_shape: schattenNorm_zero_iff: bind-only; consumer: gram_zero_of_norms_zero, schattenNorm_triangle, rescaling_upper_three, r1_upper.
proof_shape: schattenNorm_sqrt_smul: bind-only; consumer: compression_rescale, schattenNorm_smul.
proof_shape: fromRows_rescale: bind-only; consumer: gram_rescale.
proof_shape: gram_rescale: bind-only; consumer: rescaled_assemble_gram.
proof_shape: assemble_gram: bind-only; consumer: rescaled_assemble_gram, rescaling_upper_three.
proof_shape: rescaled_assemble_gram: bind-only; consumer: rescaling_upper_three, selected_assemble_gram.
proof_shape: compression_rescale: bind-only; consumer: compressionGram_rescale_apply.
proof_shape: compressionGram_rescale_apply: bind-only; consumer: compressionGram_rescale_eq_of_moments, selected_compressionGram.
proof_shape: compressionGram_rescale_eq_of_moments: bind-only; consumer: rescaling_upper_three.
proof_shape: gram_zero_of_norms_zero: bind-only; consumer: rescaling_upper_three.
proof_shape: schattenNorm_smul: bind-only; consumer: schattenNorm_triangle, schattenPow_mix_le.
proof_shape: schattenNorm_rpow: bind-only; consumer: eigenPow_eq_norm_rpow, schattenPow_mix_le.
proof_shape: eigenPow_eq_norm_rpow: bind-only; consumer: schattenNorm_triangle.
proof_shape: schattenNorm_triangle: bind-only; consumer: schattenPow_mix_le.
proof_shape: schattenPow_mix_le: bind-only; consumer: schattenPow_weighted_convex.
proof_shape: schattenPow_weighted_convex: bind-only; consumer: rescaling_upper_three.
proof_shape: kernel_direction: bind-only; consumer: shrink_support.
proof_shape: kernel_has_signs: bind-only; consumer: shrink_support.
proof_shape: face_endpoint: bind-only; consumer: shrink_support.
proof_shape: split_weights: bind-only; consumer: shrink_support.
proof_shape: face_support_shrinks: bind-only; consumer: shrink_support.
proof_shape: face_moment: bind-only; consumer: shrink_support.
proof_shape: shrink_support: bind-only; consumer: concentrate_three.
proof_shape: concentrate_three: content; consumer: rescaling_upper_three.
proof_shape: sum_support: bind-only; consumer: selected_assemble_gram, selected_compressionGram.
proof_shape: selected_assemble_gram: bind-only; consumer: upper_three_columns.
proof_shape: selected_compressionGram: bind-only; consumer: upper_three_columns.
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.Data.Matrix.ColumnRowPartitioned

noncomputable section
namespace D5.S3.Quantum.NormCompression.UpperBranchReduction
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix
open Finset Polynomial Unitary
/-- The finite sum of real powers of singular values of a complex matrix. -/
def schattenPow {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ℝ) (A : Matrix m n ℂ) : ℝ :=
  ∑ i ∈ (Matrix.toEuclideanLin A).singularValues.support,
    ((Matrix.toEuclideanLin A).singularValues i) ^ p
/-- The Schatten norm obtained from the finite singular-value power sum. -/
def schattenNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ℝ) (A : Matrix m n ℂ) : ℝ := schattenPow p A ^ (1 / p)
/-- The sum of powers of the eigenvalues of a Hermitian matrix. -/
private def eigenPow {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ) (A : Matrix n n ℂ) : ℝ :=
  if hA : A.IsHermitian then ∑ i : n, (hA.eigenvalues i) ^ q else 0
section LinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
/-- A spectral expansion of the quadratic expectation. -/
private lemma expectation_eq_eigenvalue_sum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℂ E = n) (x : E) :
    (⟪x, T x⟫_ℂ).re =
      ∑ j : Fin n, ‖⟪hT.eigenvectorBasis hn j, x⟫_ℂ‖ ^ 2 * hT.eigenvalues hn j := by
  let b := hT.eigenvectorBasis hn
  have hexp : T x = ∑ j : Fin n,
      (⟪b j, x⟫_ℂ * (hT.eigenvalues hn j : ℂ)) • b j := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, b, hT.apply_eigenvectorBasis, smul_smul]
    rfl
  rw [hexp, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_right]
  rw [show ⟪b j, x⟫_ℂ * (hT.eigenvalues hn j : ℂ) * ⟪x, b j⟫_ℂ =
    (hT.eigenvalues hn j : ℂ) * (⟪b j, x⟫_ℂ * ⟪x, b j⟫_ℂ) by ring]
  rw [Complex.re_ofReal_mul]
  rw [show (⟪b j, x⟫_ℂ * ⟪x, b j⟫_ℂ).re =
    ‖⟪b j, x⟫_ℂ * ⟪x, b j⟫_ℂ‖ from inner_mul_symm_re_eq_norm (𝕜 := ℂ) (b j) x]
  rw [norm_mul]
  rw [← inner_conj_symm x (b j), RCLike.norm_conj]
  ring
/-- Jensen's inequality bounds the sum of diagonal powers in every orthonormal basis. -/
private theorem diagonal_power_le_eigenvalue_power {T : E →ₗ[ℂ] E} (hT : T.IsPositive)
    {n : ℕ} (hn : Module.finrank ℂ E = n) (b : OrthonormalBasis (Fin n) ℂ E)
    {q : ℝ} (hq : 1 ≤ q) :
    (∑ i : Fin n, (⟪b i, T (b i)⟫_ℂ).re ^ q) ≤
      ∑ j : Fin n, (hT.isSymmetric.eigenvalues hn j) ^ q := by
  let e := hT.isSymmetric.eigenvectorBasis hn
  have hpoint (i : Fin n) : (⟪b i, T (b i)⟫_ℂ).re ^ q ≤
      ∑ j : Fin n, ‖⟪e j, b i⟫_ℂ‖ ^ 2 * (hT.isSymmetric.eigenvalues hn j) ^ q := by
    rw [expectation_eq_eigenvalue_sum hT.isSymmetric hn]
    exact (convexOn_rpow hq).map_sum_le
      (fun _ _ => sq_nonneg _)
      (by simpa [OrthonormalBasis.norm_eq_one] using e.sum_sq_norm_inner_right (b i))
      (fun j _ => hT.nonneg_eigenvalues hn j)
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖⟪e j, b i⟫_ℂ‖ ^ 2 * (hT.isSymmetric.eigenvalues hn j) ^ q :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = ∑ j : Fin n, (hT.isSymmetric.eigenvalues hn j) ^ q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      simp [b.sum_sq_norm_inner_left, OrthonormalBasis.norm_eq_one]
end LinearMap
section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- Squaring a positive matrix doubles the exponent in its spectral power sum. -/
private theorem eigenPow_sq {A : Matrix n n ℂ} (hA : A.PosSemidef) (q : ℝ) :
    eigenPow (q / 2) (Aᴴ * A) = eigenPow q A := by
  have hG := Matrix.posSemidef_conjTranspose_mul_self A
  have hchar : (Aᴴ * A).charpoly =
      ∏ i : n, (X - C (((hA.isHermitian.eigenvalues i) ^ (2 : ℕ) : ℝ) : ℂ)) := by
    rw [hA.isHermitian.eq, ← sq]
    rw [← cfc_pow_id (R := ℝ) A 2 hA.isHermitian.isSelfAdjoint]
    exact hA.isHermitian.charpoly_cfc_eq (fun x : ℝ => x ^ (2 : ℕ))
  have hroots : (Aᴴ * A).charpoly.roots =
      Finset.univ.val.map (fun i : n =>
        (((hA.isHermitian.eigenvalues i) ^ (2 : ℕ) : ℝ) : ℂ)) := by
    rw [hchar, Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero _))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have hs := congrArg (fun s : Multiset ℂ => (s.map (fun z => z.re ^ (q / 2))).sum)
    (hG.isHermitian.roots_charpoly_eq_eigenvalues.symm.trans hroots)
  have hsum : (∑ i : n, (hG.isHermitian.eigenvalues i) ^ (q / 2)) =
      ∑ i : n, ((hA.isHermitian.eigenvalues i) ^ (2 : ℕ)) ^ (q / 2) := by
    have hcast (x : ℝ) : ((x : ℂ) ^ (2 : ℕ)).re = x ^ (2 : ℕ) := by
      simp [pow_two, Complex.mul_re]
    simpa [Multiset.map_map, Function.comp_def, hcast] using hs
  simp only [eigenPow, dif_pos hG.isHermitian, dif_pos hA.isHermitian]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.rpow_natCast_mul (hA.eigenvalues_nonneg i)]
  congr 1
  ring
/-- The trace of a positive real spectral power is convex on the PSD cone. -/
private theorem eigenPow_mix_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {q a b : ℝ} (hq : 1 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    eigenPow q (a • A + b • B) ≤ a * eigenPow q A + b * eigenPow q B := by
  let U : Matrix n n ℂ := a • A + b • B
  have hU : U.PosSemidef := (hA.smul ha).add (hB.smul hb)
  have hAT : (Matrix.toEuclideanLin A).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hBT : (Matrix.toEuclideanLin B).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hB
  have hUT : (Matrix.toEuclideanLin U).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hU
  let e := hUT.isSymmetric.eigenvectorBasis
    (finrank_euclideanSpace : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n)
  have hpoint (i : Fin (Fintype.card n)) :
      (hUT.isSymmetric.eigenvalues finrank_euclideanSpace i) ^ q ≤
        a * (⟪e i, Matrix.toEuclideanLin A (e i)⟫_ℂ).re ^ q +
        b * (⟪e i, Matrix.toEuclideanLin B (e i)⟫_ℂ).re ^ q := by
    have hexp : hUT.isSymmetric.eigenvalues finrank_euclideanSpace i =
      a * (⟪e i, Matrix.toEuclideanLin A (e i)⟫_ℂ).re +
      b * (⟪e i, Matrix.toEuclideanLin B (e i)⟫_ℂ).re := by
      have h := congrArg Complex.re (congrArg (fun x => ⟪e i, x⟫_ℂ)
        (hUT.isSymmetric.apply_eigenvectorBasis finrank_euclideanSpace i))
      have hu : Matrix.toEuclideanLin U =
        (a : ℂ) • Matrix.toEuclideanLin A + (b : ℂ) • Matrix.toEuclideanLin B := by
        change Matrix.toEuclideanLin ((a : ℂ) • A + (b : ℂ) • B) = _
        rw [map_add, map_smul, map_smul]
      have huapp (x : EuclideanSpace ℂ n) : Matrix.toEuclideanLin U x =
          (a : ℂ) • Matrix.toEuclideanLin A x +
          (b : ℂ) • Matrix.toEuclideanLin B x := by
        rw [hu, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
      change (⟪e i, Matrix.toEuclideanLin U (e i)⟫_ℂ).re =
        (⟪e i, (hUT.isSymmetric.eigenvalues finrank_euclideanSpace i : ℂ) • e i⟫_ℂ).re at h
      rw [huapp] at h
      simp only [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
        OrthonormalBasis.norm_eq_one, Complex.add_re, Complex.re_ofReal_mul] at h
      norm_num only [Complex.ofReal_one, RCLike.ofReal_one, one_pow,
        Complex.one_re, RCLike.one_re, mul_one] at h
      exact h.symm
    rw [hexp]
    exact (convexOn_rpow hq).2
      (hAT.re_inner_nonneg_right (e i)) (hBT.re_inner_nonneg_right (e i)) ha hb hab
  have hdiagA := diagonal_power_le_eigenvalue_power hAT finrank_euclideanSpace e hq
  have hdiagB := diagonal_power_le_eigenvalue_power hBT finrank_euclideanSpace e hq
  change eigenPow q U ≤ _
  simp only [eigenPow, dif_pos hU.isHermitian, dif_pos hA.isHermitian, dif_pos hB.isHermitian]
  rw [RHLinalg.sum_eigenvalues_reindex hU.isHermitian (· ^ q),
    RHLinalg.sum_eigenvalues_reindex hA.isHermitian (· ^ q),
    RHLinalg.sum_eigenvalues_reindex hB.isHermitian (· ^ q)]
  calc
    _ ≤ ∑ i : Fin (Fintype.card n),
        (a * (⟪e i, Matrix.toEuclideanLin A (e i)⟫_ℂ).re ^ q +
         b * (⟪e i, Matrix.toEuclideanLin B (e i)⟫_ℂ).re ^ q) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = a * (∑ i : Fin (Fintype.card n),
        (⟪e i, Matrix.toEuclideanLin A (e i)⟫_ℂ).re ^ q) +
      b * (∑ i : Fin (Fintype.card n),
        (⟪e i, Matrix.toEuclideanLin B (e i)⟫_ℂ).re ^ q) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hdiagA ha)
      (mul_le_mul_of_nonneg_left hdiagB hb)
end Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Polynomial Unitary
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
private lemma roots_smul (A : Matrix n n ℂ) (hA : A.IsHermitian) (a : ℝ) :
    (((a : ℂ) • A).charpoly).roots =
      Finset.univ.val.map (fun i : n => (a : ℂ) * (hA.eigenvalues i : ℂ)) := by
  have hchar : ((a : ℂ) • A).charpoly =
      ∏ i : n, (X - C ((a : ℂ) * (hA.eigenvalues i : ℂ))) := by
    conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← Matrix.smul_mul,
      ← Matrix.mul_smul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp [← Matrix.diagonal_smul, Matrix.charpoly_diagonal,
      Pi.smul_apply, Function.comp_def]
  rw [hchar, Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
    (fun i _ => Polynomial.X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
private lemma sum_eigenvalues_smul (A : Matrix n n ℂ) (hA : A.IsHermitian) (a : ℝ)
    (hS : ((a : ℂ) • A).IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (hS.eigenvalues i) = ∑ i, f (a * hA.eigenvalues i) := by
  have hroots := hS.roots_charpoly_eq_eigenvalues.symm.trans (roots_smul A hA a)
  have hf := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) hroots
  simpa [Multiset.map_map, Function.comp_def] using hf
private lemma sum_eigenvalues_gram (A : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ i, f ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i) =
      ∑ i, f ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
  have hchar := Matrix.charpoly_mul_comm' A Aᴴ
  have hr := congrArg Polynomial.roots hchar
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero), Polynomial.roots_X_pow, Polynomial.roots_X_pow,
    (Matrix.isHermitian_mul_conjTranspose_self A).roots_charpoly_eq_eigenvalues,
    (Matrix.isHermitian_conjTranspose_mul_self A).roots_charpoly_eq_eigenvalues] at hr
  have hs := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) hr
  simpa [Multiset.map_map, Function.comp_def, Multiset.map_nsmul, Multiset.sum_nsmul, hf] using hs
private lemma schattenPow_eq_columnGram (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenPow p A = ∑ i : n,
      ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) ^ (p / 2) := by
  let T := Matrix.toEuclideanLin A
  have hgram : T.adjoint ∘ₗ T = Matrix.toEuclideanLin (Aᴴ * A) := by
    dsimp [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change Matrix.toLpLin 2 2 Aᴴ ∘ₗ Matrix.toLpLin 2 2 A = _
    rw [← Matrix.toLpLin_mul_same]
  have hsupport : T.singularValues.support ⊆ Finset.range (Fintype.card n) := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra h
    have hz := T.singularValues_of_finrank_le (by
      simpa using Nat.le_of_not_gt h)
    exact (Finsupp.mem_support_iff.mp hi) hz
  have hext : schattenPow p A = ∑ i : Fin (Fintype.card n), (T.singularValues i) ^ p := by
    change T.singularValues.sum (fun _ x => x ^ p) = _
    rw [T.singularValues.sum_of_support_subset hsupport (fun _ x => x ^ p)
      (fun _ _ => Real.zero_rpow hp.ne')]
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hext, RHLinalg.sum_eigenvalues_reindex
    (Matrix.isHermitian_conjTranspose_mul_self A) (· ^ (p / 2))]
  apply Finset.sum_congr rfl
  intro i _
  have hs := T.singularValues_of_lt finrank_euclideanSpace i.isLt
  simp only [hgram] at hs
  rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul]
  · congr 1
    ring
  · have hn := T.isPositive_adjoint_comp_self.nonneg_eigenvalues finrank_euclideanSpace i
    simp only [hgram] at hn
    exact hn
private lemma schattenPow_eq_rowGram (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenPow p A = ∑ i : m,
      ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i) ^ (p / 2) := by
  rw [schattenPow_eq_columnGram p hp A]
  exact (sum_eigenvalues_gram A (· ^ (p / 2))
    (Real.zero_rpow (by positivity))).symm
private lemma schattenPow_eq_eigenPow_columnGram (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenPow p A = eigenPow (p / 2) (Aᴴ * A) := by
  rw [schattenPow_eq_columnGram p hp A, eigenPow,
    dif_pos (Matrix.isHermitian_conjTranspose_mul_self A)]
private lemma schattenPow_eq_eigenPow_rowGram (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenPow p A = eigenPow (p / 2) (A * Aᴴ) := by
  rw [schattenPow_eq_rowGram p hp A, eigenPow,
    dif_pos (Matrix.isHermitian_mul_conjTranspose_self A)]
private lemma schattenPow_eq_eigenPow (p : ℝ) (hp : 0 < p) (A : Matrix n n ℂ)
    (hA : A.PosSemidef) : schattenPow p A = eigenPow p A := by
  rw [schattenPow_eq_eigenPow_columnGram p hp A]
  exact eigenPow_sq hA p
private lemma schattenPow_nonneg (p : ℝ) (A : Matrix m n ℂ) : 0 ≤ schattenPow p A := by
  exact Finset.sum_nonneg (fun i _ =>
    Real.rpow_nonneg ((Matrix.toEuclideanLin A).singularValues_nonneg i) p)
private lemma schattenPow_zero_iff (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenPow p A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Real.rpow_nonneg ((Matrix.toEuclideanLin A).singularValues_nonneg i) p)).mp h
    have hzero : (Matrix.toEuclideanLin A).singularValues = 0 := by
      ext i
      by_cases hi : i ∈ (Matrix.toEuclideanLin A).singularValues.support
      · exact (Real.rpow_eq_zero ((Matrix.toEuclideanLin A).singularValues_nonneg i) hp.ne').mp
          (hall i hi)
      · exact Finsupp.notMem_support_iff.mp hi
    have hlin := (Matrix.toEuclideanLin A).singularValues_eq_zero_iff.mp hzero
    exact Matrix.toEuclideanLin.injective (hlin.trans (map_zero Matrix.toEuclideanLin).symm)
  · rintro rfl
    simp [schattenPow]
private lemma schattenPow_sqrt_smul (p : ℝ) (hp : 0 < p) (w : ℝ) (hw : 0 ≤ w)
    (A : Matrix m n ℂ) :
    schattenPow p ((Real.sqrt w : ℂ) • A) = w ^ (p / 2) * schattenPow p A := by
  have hgram : ((Real.sqrt w : ℂ) • A)ᴴ * ((Real.sqrt w : ℂ) • A) =
      (w : ℂ) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h : star (Real.sqrt w : ℂ) * (Real.sqrt w : ℂ) = (w : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt hw)
    rw [h]
  rw [schattenPow_eq_columnGram p hp]
  simp only [hgram]
  rw [sum_eigenvalues_smul (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A) w
    ((Matrix.isHermitian_conjTranspose_mul_self A).smul (by change star (w : ℂ) = (w : ℂ); simp)) (· ^ (p / 2))]
  simp_rw [Real.mul_rpow hw (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _)]
  rw [← Finset.mul_sum, schattenPow_eq_columnGram p hp]
private lemma schattenNorm_nonneg (p : ℝ) (A : Matrix m n ℂ) : 0 ≤ schattenNorm p A :=
  Real.rpow_nonneg (schattenPow_nonneg p A) _
private lemma schattenNorm_zero_iff (p : ℝ) (hp : 0 < p) (A : Matrix m n ℂ) :
    schattenNorm p A = 0 ↔ A = 0 := by
  exact (Real.rpow_eq_zero (schattenPow_nonneg p A) (by positivity)).trans
    (schattenPow_zero_iff p hp A)
private lemma schattenNorm_sqrt_smul (p : ℝ) (hp : 0 < p) (w : ℝ) (hw : 0 ≤ w)
    (A : Matrix m n ℂ) :
    schattenNorm p ((Real.sqrt w : ℂ) • A) = Real.sqrt w * schattenNorm p A := by
  unfold schattenNorm
  rw [schattenPow_sqrt_smul p hp w hw,
    Real.mul_rpow (Real.rpow_nonneg hw _) (schattenPow_nonneg p A), ← Real.rpow_mul hw]
  have hexp : p / 2 * (1 / p) = 1 / 2 := by
    field_simp
  rw [hexp, Real.sqrt_eq_rpow]
section Family
variable {J HA HB : Type*} [Fintype J] [Fintype HA] [Fintype HB]
  [DecidableEq J] [DecidableEq HA] [DecidableEq HB]
  {C : J → Type*} {j : J} [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]
/-- Concatenation of a family with arbitrary finite column spaces. -/
def assemble (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    Matrix (HA ⊕ HB) (Sigma C) ℂ :=
  fun i jk => Matrix.fromRows (A jk.1) (B jk.1) i jk.2
/-- Nonnegative square-root rescaling, including zero weights. -/
noncomputable def rescale {m n : Type*} (w : ℝ) (A : Matrix m n ℂ) : Matrix m n ℂ :=
  (Real.sqrt w : ℂ) • A
/-- The row-space Gram contribution of one compatible block column. -/
private def gram (A : Matrix HA (C j) ℂ) (B : Matrix HB (C j) ℂ) :
    Matrix (HA ⊕ HB) (HA ⊕ HB) ℂ :=
  Matrix.fromRows A B * (Matrix.fromRows A B)ᴴ
private lemma fromRows_rescale (w : ℝ) (A : Matrix HA (C j) ℂ) (B : Matrix HB (C j) ℂ) :
    Matrix.fromRows (rescale w A) (rescale w B) = (Real.sqrt w : ℂ) • Matrix.fromRows A B := by
  ext i k
  cases i <;> rfl
private lemma gram_rescale (w : ℝ) (hw : 0 ≤ w)
    (A : Matrix HA (C j) ℂ) (B : Matrix HB (C j) ℂ) :
    gram (rescale w A) (rescale w B) = (w : ℂ) • gram A B := by
  rw [gram, fromRows_rescale, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  have h : (Real.sqrt w : ℂ) * star (Real.sqrt w : ℂ) = (w : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt hw)
  rw [h]
  rfl
private lemma assemble_gram (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    assemble A B * (assemble A B)ᴴ = ∑ j, gram (A j) (B j) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    assemble, gram]
  rw [Fintype.sum_sigma]
private lemma rescaled_assemble_gram (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    assemble (fun j => rescale (w j) (A j)) (fun j => rescale (w j) (B j)) *
      (assemble (fun j => rescale (w j) (A j)) (fun j => rescale (w j) (B j)))ᴴ =
        ∑ j, (w j : ℂ) • gram (A j) (B j) := by
  rw [assemble_gram]
  exact Finset.sum_congr rfl (fun j _ => gram_rescale (w j) (hw j) (A j) (B j))
/-- Two-row compression with the Schatten norms of the blocks as entries. -/
def compression (p : ℝ) (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    Matrix (Fin 2) J ℂ :=
  fun i j => ((if i = 0 then schattenNorm p (A j) else schattenNorm p (B j) : ℝ) : ℂ)
/-- The compression Gram matrix lives on the fixed two-dimensional row space. -/
def compressionGram (p : ℝ) (A : ∀ j, Matrix HA (C j) ℂ)
    (B : ∀ j, Matrix HB (C j) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  compression p A B * (compression p A B)ᴴ
/-- Three real moments determine the compression Gram matrix. -/
private def profileMoment (p : ℝ) (A : ∀ j, Matrix HA (C j) ℂ)
    (B : ∀ j, Matrix HB (C j) ℂ) (j : J) : Fin 3 → ℝ :=
  ![schattenNorm p (A j) ^ 2, schattenNorm p (B j) ^ 2,
    schattenNorm p (A j) * schattenNorm p (B j)]
private lemma compression_rescale (p : ℝ) (hp : 0 < p) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ)
    (i : Fin 2) (j : J) :
    compression p (fun j => rescale (w j) (A j)) (fun j => rescale (w j) (B j)) i j =
      (Real.sqrt (w j) : ℂ) * compression p A B i j := by
  unfold compression rescale
  split_ifs <;> simp only [schattenNorm_sqrt_smul p hp _ (hw j), Complex.ofReal_mul]
private lemma compressionGram_rescale_apply (p : ℝ) (hp : 0 < p) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (A : ∀ j, Matrix HA (C j) ℂ)
    (B : ∀ j, Matrix HB (C j) ℂ) (i k : Fin 2) :
    compressionGram p (fun j => rescale (w j) (A j))
      (fun j => rescale (w j) (B j)) i k =
      ∑ j, (w j : ℂ) * (compression p A B i j * star (compression p A B k j)) := by
  unfold compressionGram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, compression_rescale p hp w hw A B,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Real.sqrt (w j) : ℂ) * (Real.sqrt (w j) : ℂ) = (w j : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt (hw j))
  calc
    _ = ((Real.sqrt (w j) : ℂ) * (Real.sqrt (w j) : ℂ)) *
      (compression p A B i j * star (compression p A B k j)) := by
        simp only [Complex.star_def]
        ring
    _ = _ := by simp only [hs, Complex.star_def]
private lemma compressionGram_rescale_eq_of_moments (p : ℝ) (hp : 0 < p) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (A : ∀ j, Matrix HA (C j) ℂ)
    (B : ∀ j, Matrix HB (C j) ℂ)
    (hm : ∀ k : Fin 3, ∑ j, w j * profileMoment p A B j k =
      ∑ j, profileMoment p A B j k) :
    compressionGram p (fun j => rescale (w j) (A j))
      (fun j => rescale (w j) (B j)) = compressionGram p A B := by
  ext i k
  rw [compressionGram_rescale_apply p hp w hw A B]
  have h0 := congrArg (fun x : ℝ => (x : ℂ)) (hm 0)
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hm 1)
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) (hm 2)
  simp [profileMoment] at h0 h1 h2
  fin_cases i <;> fin_cases k <;>
    simp [compressionGram, Matrix.mul_apply, Matrix.conjTranspose_apply, compression]
  · simpa [pow_two, Complex.ofReal_mul] using h0
  · simpa only [Complex.ofReal_mul] using h2
  · simpa [mul_comm, Complex.ofReal_mul] using h2
  · simpa [pow_two, Complex.ofReal_mul] using h1
private lemma gram_zero_of_norms_zero (p : ℝ) (hp : 0 < p)
    (A : Matrix HA (C j) ℂ) (B : Matrix HB (C j) ℂ)
    (hA : schattenNorm p A = 0) (hB : schattenNorm p B = 0) : gram A B = 0 := by
  rw [(schattenNorm_zero_iff p hp A).mp hA, (schattenNorm_zero_iff p hp B).mp hB]
  have hstack : Matrix.fromRows (0 : Matrix HA (C j) ℂ) (0 : Matrix HB (C j) ℂ) = 0 := by
    ext i k
    cases i <;> rfl
  simp [gram, hstack]
end Family
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma schattenNorm_smul {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (A : Matrix n n ℂ) : schattenNorm q (t • A) = t * schattenNorm q A := by
  have hcast : t • A = (t : ℂ) • A := by
    ext i j
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) t (A i j)
  rw [hcast]
  simpa only [Real.sqrt_sq ht] using
    schattenNorm_sqrt_smul q hq (t ^ (2 : ℕ)) (sq_nonneg t) A
private lemma schattenNorm_rpow {q : ℝ} (hq : 0 < q) (A : Matrix n n ℂ) :
    schattenNorm q A ^ q = schattenPow q A := by
  unfold schattenNorm
  rw [← Real.rpow_mul (schattenPow_nonneg q A)]
  have hexp : (1 / q) * q = 1 := by field_simp
  rw [hexp, Real.rpow_one]
private lemma eigenPow_eq_norm_rpow {q : ℝ} (hq : 0 < q) (A : Matrix n n ℂ)
    (hA : A.PosSemidef) : eigenPow q A = schattenNorm q A ^ q := by
  rw [schattenNorm_rpow hq, schattenPow_eq_eigenPow q hq A hA]
private theorem schattenNorm_triangle {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {q : ℝ} (hq : 1 ≤ q) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  by_cases hA0 : A = 0
  · subst A
    simpa only [zero_add] using
      le_add_of_nonneg_left (schattenNorm_nonneg q (0 : Matrix n n ℂ))
  by_cases hB0 : B = 0
  · subst B
    simpa only [add_zero] using
      le_add_of_nonneg_right (schattenNorm_nonneg q (0 : Matrix n n ℂ))
  let x := schattenNorm q A
  let y := schattenNorm q B
  let s := x + y
  have hx : 0 < x := (schattenNorm_nonneg q A).lt_of_ne'
    (fun hz => hA0 ((schattenNorm_zero_iff q hq0 A).mp hz))
  have hy : 0 < y := (schattenNorm_nonneg q B).lt_of_ne'
    (fun hz => hB0 ((schattenNorm_zero_iff q hq0 B).mp hz))
  have hs : 0 < s := add_pos hx hy
  let U : Matrix n n ℂ := x⁻¹ • A
  let V : Matrix n n ℂ := y⁻¹ • B
  have hU : U.PosSemidef := hA.smul (inv_nonneg.mpr hx.le)
  have hV : V.PosSemidef := hB.smul (inv_nonneg.mpr hy.le)
  have hnormU : schattenNorm q U = 1 := by
    rw [schattenNorm_smul hq0 (inv_nonneg.mpr hx.le)]
    exact inv_mul_cancel₀ hx.ne'
  have hnormV : schattenNorm q V = 1 := by
    rw [schattenNorm_smul hq0 (inv_nonneg.mpr hy.le)]
    exact inv_mul_cancel₀ hy.ne'
  have heU : eigenPow q U = 1 := by rw [eigenPow_eq_norm_rpow hq0 U hU, hnormU, Real.one_rpow]
  have heV : eigenPow q V = 1 := by rw [eigenPow_eq_norm_rpow hq0 V hV, hnormV, Real.one_rpow]
  have hab : x / s + y / s = 1 := by dsimp [s]; field_simp
  have hm := eigenPow_mix_le hU hV hq
    (div_nonneg hx.le hs.le) (div_nonneg hy.le hs.le) hab
  have hcA : x / s * x⁻¹ = s⁻¹ := by field_simp
  have hcB : y / s * y⁻¹ = s⁻¹ := by field_simp
  have hmix : (x / s) • U + (y / s) • V = s⁻¹ • (A + B) := by
    simp only [U, V, smul_smul, hcA, hcB, smul_add]
  rw [hmix, heU, heV, mul_one, mul_one, hab] at hm
  have hS : (s⁻¹ • (A + B)).PosSemidef := (hA.add hB).smul (inv_nonneg.mpr hs.le)
  rw [eigenPow_eq_norm_rpow hq0 _ hS,
    schattenNorm_smul hq0 (inv_nonneg.mpr hs.le)] at hm
  have hroot : s⁻¹ * schattenNorm q (A + B) ≤ 1 :=
    (Real.rpow_le_rpow_iff (mul_nonneg (inv_nonneg.mpr hs.le)
      (schattenNorm_nonneg q _)) zero_le_one hq0).mp (by simpa using hm)
  have hmul := mul_le_mul_of_nonneg_left hroot hs.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_one] using hmul
private theorem schattenPow_mix_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {q a b : ℝ} (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    schattenPow q (a • A + b • B) ≤ a * schattenPow q A + b * schattenPow q B := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ht := schattenNorm_triangle (hA.smul ha) (hB.smul hb) hq
  rw [schattenNorm_smul hq0 ha, schattenNorm_smul hq0 hb] at ht
  rw [← schattenNorm_rpow hq0, ← schattenNorm_rpow hq0, ← schattenNorm_rpow hq0]
  exact (Real.rpow_le_rpow (schattenNorm_nonneg q _) ht (le_of_lt hq0)).trans
    ((convexOn_rpow hq).2 (schattenNorm_nonneg q A) (schattenNorm_nonneg q B) ha hb hab)
private theorem schattenPow_weighted_convex {J : Type*} [Fintype J]
    (Q : J → Matrix n n ℂ) (hQ : ∀ j, (Q j).PosSemidef)
    {q : ℝ} (hq : 1 ≤ q) :
    ConvexOn ℝ {w : J → ℝ | ∀ j, 0 ≤ w j}
      (fun w => schattenPow q (∑ j, w j • Q j)) := by
  constructor
  · intro w hw z hz a b ha hb hab j
    exact add_nonneg (mul_nonneg ha (hw j)) (mul_nonneg hb (hz j))
  · intro w hw z hz a b ha hb hab
    change schattenPow q (∑ j, (a * w j + b * z j) • Q j) ≤
      a * schattenPow q (∑ j, w j • Q j) +
        b * schattenPow q (∑ j, z j • Q j)
    have heq : (∑ j, (a * w j + b * z j) • Q j) =
        a • (∑ j, w j • Q j) + b • (∑ j, z j • Q j) := by
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    rw [heq]
    exact schattenPow_mix_le
      (Matrix.posSemidef_sum _ (fun j _ => (hQ j).smul (hw j)))
      (Matrix.posSemidef_sum _ (fun j _ => (hQ j).smul (hz j)))
      hq ha hb hab
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma kernel_direction (v : ι → Fin 3 → ℝ) (s : Finset ι) (hs : 3 < s.card) :
    ∃ d : ι → ℝ, (∀ i, i ∉ s → d i = 0) ∧
      (∑ i, d i • v i) = 0 ∧ ∃ i ∈ s, d i ≠ 0 := by
  have hnot : ¬ LinearIndependent ℝ (fun i : s => v i) := by
    intro h
    have hc := h.fintype_card_le_finrank
    simp only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hc
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let d : ι → ℝ := fun j => if hj : j ∈ s then c ⟨j, hj⟩ else 0
  refine ⟨d, ?_, ?_, i, i.property, ?_⟩
  · intro j hj
    simp [d, hj]
  · have heq : (∑ j, d j • v j) = ∑ j ∈ s, d j • v j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      simp [d, hj]
    rw [heq, ← s.sum_attach]
    simpa [d] using hc
  · simpa [d, i.property] using hi
omit [DecidableEq ι] in
private lemma kernel_has_signs (d c : ι → ℝ) (hc : ∀ i, d i ≠ 0 → 0 < c i)
    (hzero : ∑ i, d i * c i = 0) (hne : ∃ i, d i ≠ 0) :
    (∃ i, 0 < d i) ∧ (∃ i, d i < 0) := by
  have hpositive : ∃ i, 0 < d i := by
    by_contra h
    push Not at h
    have hnzero : ∑ i, (-d i) * c i = 0 := by
      simp only [neg_mul, Finset.sum_neg_distrib, hzero, neg_zero]
    have hnonneg : ∀ i, 0 ≤ (-d i) * c i := by
      intro i
      by_cases hi : d i = 0
      · simp [hi]
      · exact mul_nonneg (by linarith [h i]) (le_of_lt (hc i hi))
    have hall : ∀ i ∈ (Finset.univ : Finset ι), (-d i) * c i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hnzero
    obtain ⟨i, hi⟩ := hne
    have hz := hall i (Finset.mem_univ i)
    have hcne : c i ≠ 0 := ne_of_gt (hc i hi)
    exact hi (by simpa using (mul_eq_zero.mp hz).resolve_right hcne)
  refine ⟨hpositive, ?_⟩
  by_contra h
  push Not at h
  have hnonneg : ∀ i, 0 ≤ d i * c i := by
    intro i
    by_cases hi : d i = 0
    · simp [hi]
    · exact mul_nonneg (h i) (le_of_lt (hc i hi))
  have hall : ∀ i ∈ (Finset.univ : Finset ι), d i * c i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero
  obtain ⟨i, hi⟩ := hne
  have hz := hall i (Finset.mem_univ i)
  exact hi ((mul_eq_zero.mp hz).resolve_right (ne_of_gt (hc i hi)))
omit [DecidableEq ι] in
private lemma face_endpoint (w d : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hd : ∀ i, w i = 0 → d i = 0) (hneg : ∃ i, d i < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ w i + t * d i) ∧
      (∀ i, w i = 0 → w i + t * d i = 0) ∧
      ∃ i, w i ≠ 0 ∧ w i + t * d i = 0 := by
  let s := Finset.univ.filter (fun i => d i < 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image (fun i => w i / (-d i)) hs
  have hjd : d j < 0 := (Finset.mem_filter.mp hj).2
  have hjw : 0 < w j := by
    have hn : w j ≠ 0 := by
      intro h
      have := hd j h
      linarith
    exact lt_of_le_of_ne (hw j) (Ne.symm hn)
  let t := w j / (-d j)
  have ht : 0 < t := div_pos hjw (by linarith)
  refine ⟨t, ht, ?_, ?_, j, ne_of_gt hjw, ?_⟩
  · intro i
    by_cases hi : d i < 0
    · have hm : t ≤ w i / (-d i) := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      have hm' : t * (-d i) ≤ w i := (le_div_iff₀ (by linarith : 0 < -d i)).mp hm
      linarith
    · have hp : 0 ≤ t * d i := mul_nonneg (le_of_lt ht) (le_of_not_gt hi)
      linarith [hw i]
  · intro i hi
    simp [hi, hd i hi]
  · dsimp [t]
    field_simp [ne_of_lt hjd]
    ring
omit [Fintype ι] [DecidableEq ι] in
private lemma split_weights (w d : ι → ℝ) (hp hm : ℝ) (hpp : 0 < hp) (hmp : 0 < hm) :
    w = (hm / (hp + hm)) • (fun i => w i + hp * d i) +
      (hp / (hp + hm)) • (fun i => w i - hm * d i) := by
  ext i
  dsimp
  have hne : hp + hm ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring
omit [DecidableEq ι] in
private lemma face_support_shrinks (w u : ι → ℝ)
    (hzero : ∀ i, w i = 0 → u i = 0)
    (hface : ∃ i, w i ≠ 0 ∧ u i = 0) :
    ((Function.support u).toFinite.toFinset).card < ((Function.support w).toFinite.toFinset).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    have hu : u i ≠ 0 := by simpa using hi
    simpa using (show u i ≠ 0 → w i ≠ 0 from fun _ hw => hu (hzero i hw)) hu
  · intro heq
    obtain ⟨i, hwi, hui⟩ := hface
    have hi : i ∈ (Function.support w).toFinite.toFinset := by simpa using hwi
    rw [← heq] at hi
    exact (show u i ≠ 0 by simpa using hi) hui
omit [DecidableEq ι] in
private lemma face_moment (v : ι → Fin 3 → ℝ) (w d : ι → ℝ) (t : ℝ)
    (hzero : ∑ i, d i • v i = 0) :
    (∑ i, (w i + t * d i) • v i) = ∑ i, w i • v i := by
  simp_rw [add_smul, mul_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, hzero, smul_zero, add_zero]
private lemma shrink_support (v : ι → Fin 3 → ℝ) (f : (ι → ℝ) → ℝ)
    (hf : ConvexOn ℝ (Set.Ici (0 : ι → ℝ)) f) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, w i ≠ 0 → 0 < v i 0 + v i 1)
    (hcard : 3 < ((Function.support w).toFinite.toFinset).card) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧
      (∑ i, u i • v i) = ∑ i, w i • v i ∧
      f w ≤ f u ∧ ((Function.support u).toFinite.toFinset).card < ((Function.support w).toFinite.toFinset).card ∧
      (∀ i, w i = 0 → u i = 0) := by
  obtain ⟨d, hd, hmoment, j, hj, hdj⟩ := kernel_direction v ((Function.support w).toFinite.toFinset) hcard
  have hdzero : ∀ i, w i = 0 → d i = 0 := by
    intro i hi
    exact hd i (by simp [hi])
  have hscalar : ∑ i, d i * (v i 0 + v i 1) = 0 := by
    have h := congrArg (fun x : Fin 3 → ℝ => x 0 + x 1) hmoment
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib] using h
  have hdpos : ∀ i, d i ≠ 0 → 0 < v i 0 + v i 1 := by
    intro i hi
    exact hv i (fun hwi => hi (hdzero i hwi))
  obtain ⟨hpos, hneg⟩ := kernel_has_signs d (fun i => v i 0 + v i 1) hdpos hscalar ⟨j, hdj⟩
  obtain ⟨tp, htp, hwp, hzp, hip⟩ := face_endpoint w d hw hdzero hneg
  obtain ⟨tm, htm, hwm, hzm, him⟩ := face_endpoint w (fun i => -d i) hw
    (fun i hi => by simp [hdzero i hi]) (by simpa using hpos)
  let wp : ι → ℝ := fun i => w i + tp * d i
  let wm : ι → ℝ := fun i => w i - tm * d i
  have hwm' : ∀ i, 0 ≤ wm i := by simpa [wm, mul_neg, sub_eq_add_neg] using hwm
  have hzm' : ∀ i, w i = 0 → wm i = 0 := by
    simpa [wm, mul_neg, sub_eq_add_neg] using hzm
  have him' : ∃ i, w i ≠ 0 ∧ wm i = 0 := by
    simpa [wm, mul_neg, sub_eq_add_neg] using him
  have hsplit := split_weights w d tp tm htp htm
  have hden : 0 < tp + tm := by linarith
  have ha : 0 ≤ tm / (tp + tm) := le_of_lt (div_pos htm hden)
  have hb : 0 ≤ tp / (tp + tm) := le_of_lt (div_pos htp hden)
  have hab : tm / (tp + tm) + tp / (tp + tm) = 1 := by
    field_simp
    ring
  have hc := hf.le_on_segment' hwp hwm' ha hb hab
  change f ((tm / (tp + tm)) • wp + (tp / (tp + tm)) • wm) ≤
    max (f wp) (f wm) at hc
  rw [← hsplit] at hc
  have hchoice : f w ≤ f wp ∨ f w ≤ f wm := le_max_iff.mp hc
  rcases hchoice with hp | hm
  · exact ⟨wp, hwp, face_moment v w d tp hmoment, hp,
      face_support_shrinks w wp hzp hip, hzp⟩
  · refine ⟨wm, hwm', ?_, hm, face_support_shrinks w wm hzm' him', hzm'⟩
    simpa [wm, neg_mul, sub_eq_add_neg] using face_moment v w d (-tm) hmoment
private theorem concentrate_three (v : ι → Fin 3 → ℝ) (f : (ι → ℝ) → ℝ)
    (hf : ConvexOn ℝ (Set.Ici (0 : ι → ℝ)) f) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, w i ≠ 0 → 0 < v i 0 + v i 1) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧
      (∑ i, u i • v i) = ∑ i, w i • v i ∧
      f w ≤ f u ∧ ((Function.support u).toFinite.toFinset).card ≤ 3 := by
  have hmain : ∀ n : ℕ, ∀ w : ι → ℝ, ((Function.support w).toFinite.toFinset).card = n →
      (∀ i, 0 ≤ w i) → (∀ i, w i ≠ 0 → 0 < v i 0 + v i 1) →
      ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧
        (∑ i, u i • v i) = ∑ i, w i • v i ∧
        f w ≤ f u ∧ ((Function.support u).toFinite.toFinset).card ≤ 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw hv
      by_cases hsmall : ((Function.support w).toFinite.toFinset).card ≤ 3
      · exact ⟨w, hw, rfl, le_rfl, hsmall⟩
      · obtain ⟨u, hu, hmoment, hobj, hcard, hzero⟩ :=
          shrink_support v f hf w hw hv (lt_of_not_ge hsmall)
        have hvu : ∀ i, u i ≠ 0 → 0 < v i 0 + v i 1 := by
          intro i hi
          exact hv i (fun hwi => hi (hzero i hwi))
        obtain ⟨z, hz, hzmoment, hzobj, hzcard⟩ :=
          ih ((Function.support u).toFinite.toFinset).card (by omega) u rfl hu hvu
        exact ⟨z, hz, hzmoment.trans hmoment, hobj.trans hzobj, hzcard⟩
  exact hmain ((Function.support w).toFinite.toFinset).card w rfl hw hv
end
open scoped BigOperators Matrix MatrixOrder ComplexOrder
section
universe uJ uA uB uC
variable {J : Type uJ} {HA : Type uA} {HB : Type uB} [Fintype J] [Fintype HA] [Fintype HB]
  [DecidableEq J] [DecidableEq HA] [DecidableEq HB]
  {C : J → Type uC} [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]
theorem rescaling_upper_three (p : ℝ) (hp : 2 ≤ p)
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧ ((Function.support w).toFinite.toFinset).card ≤ 3 ∧
      compressionGram p (fun j => rescale (w j) (A j))
        (fun j => rescale (w j) (B j)) = compressionGram p A B ∧
      schattenNorm p (assemble A B) ≤
        schattenNorm p (assemble (fun j => rescale (w j) (A j))
          (fun j => rescale (w j) (B j))) := by
  have hp0 : 0 < p := by linarith
  have hq : 1 ≤ p / 2 := by linarith
  let w₀ : J → ℝ := fun j => if A j = 0 ∧ B j = 0 then 0 else 1
  have hw₀ : ∀ j, 0 ≤ w₀ j := by
    intro j
    simp only [w₀]
    split_ifs <;> norm_num
  have hz (j : J) (h : A j = 0 ∧ B j = 0) :
      profileMoment p A B j = 0 ∧ gram (A j) (B j) = 0 := by
    have ha := (schattenNorm_zero_iff p hp0 (A j)).mpr h.1
    have hb := (schattenNorm_zero_iff p hp0 (B j)).mpr h.2
    constructor
    · simp [profileMoment, ha, hb]
    · exact gram_zero_of_norms_zero p hp0 (A j) (B j) ha hb
  have hmoment₀ : (∑ j, w₀ j • profileMoment p A B j) =
      ∑ j, profileMoment p A B j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : A j = 0 ∧ B j = 0
    · simp [w₀, h, (hz j h).1]
    · simp [w₀, h]
  have hgram₀ : (∑ j, w₀ j • gram (A j) (B j)) =
      ∑ j, gram (A j) (B j) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : A j = 0 ∧ B j = 0
    · rw [show w₀ j = 0 by simp [w₀, h], zero_smul, (hz j h).2]
    · simp [w₀, h]
  have hv₀ : ∀ j, w₀ j ≠ 0 →
      0 < profileMoment p A B j 0 + profileMoment p A B j 1 := by
    intro j hj
    have hnot : ¬ (A j = 0 ∧ B j = 0) := by
      intro h
      exact hj (by simp [w₀, h])
    simp only [profileMoment, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_contra h
    have ha : schattenNorm p (A j) = 0 := by
      nlinarith [sq_nonneg (schattenNorm p (B j))]
    have hb : schattenNorm p (B j) = 0 := by
      nlinarith [sq_nonneg (schattenNorm p (A j))]
    exact hnot ⟨(schattenNorm_zero_iff p hp0 (A j)).mp ha,
      (schattenNorm_zero_iff p hp0 (B j)).mp hb⟩
  have hQ : ∀ j, (gram (A j) (B j)).PosSemidef :=
    fun j => Matrix.posSemidef_self_mul_conjTranspose (Matrix.fromRows (A j) (B j))
  obtain ⟨w, hw, hm, ho, hs⟩ := concentrate_three (profileMoment p A B)
    (fun z => schattenPow (p / 2) (∑ j, z j • gram (A j) (B j)))
    (schattenPow_weighted_convex (fun j => gram (A j) (B j)) hQ hq)
    w₀ hw₀ hv₀
  refine ⟨w, hw, hs, ?_, ?_⟩
  · apply compressionGram_rescale_eq_of_moments p hp0 w hw A B
    intro k
    have hk := congrArg (fun f : Fin 3 → ℝ => f k) (hm.trans hmoment₀)
    simpa [Finset.sum_apply] using hk
  · have hGram : (assemble (fun j => rescale (w j) (A j))
        (fun j => rescale (w j) (B j))) *
        (assemble (fun j => rescale (w j) (A j))
          (fun j => rescale (w j) (B j)))ᴴ =
        ∑ j, w j • gram (A j) (B j) := by
      exact rescaled_assemble_gram w hw A B
    have hpos₀ : (∑ j, w₀ j • gram (A j) (B j)).PosSemidef :=
      Matrix.posSemidef_sum _ (fun j _ => (hQ j).smul (hw₀ j))
    have hpos : (∑ j, w j • gram (A j) (B j)).PosSemidef :=
      Matrix.posSemidef_sum _ (fun j _ => (hQ j).smul (hw j))
    rw [schattenPow_eq_eigenPow (p / 2) (by linarith) _ hpos₀,
      schattenPow_eq_eigenPow (p / 2) (by linarith) _ hpos] at ho
    rw [hgram₀] at ho
    unfold schattenNorm
    rw [schattenPow_eq_eigenPow_rowGram p hp0, assemble_gram,
      schattenPow_eq_eigenPow_rowGram p hp0, hGram]
    exact Real.rpow_le_rpow (by
      rw [← assemble_gram, ← schattenPow_eq_eigenPow_rowGram p hp0]
      exact schattenPow_nonneg p (assemble A B)) ho (by positivity)
omit [DecidableEq J] in
private lemma sum_support {M : Type*} [AddCommMonoid M] (u : J → ℝ) (g : J → M)
    (hz : ∀ j, u j = 0 → g j = 0) :
    (∑ j : (Function.support u).toFinite.toFinset, g j) = ∑ j, g j := by
  change (∑ j ∈ ((Function.support u).toFinite.toFinset).attach, g j.val) = ∑ j, g j
  rw [Finset.sum_attach]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hz j
  simpa using hj
private lemma selected_assemble_gram (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    assemble (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (A j))
      (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (B j)) *
      (assemble (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (A j))
        (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (B j)))ᴴ =
    assemble (fun j => rescale (u j) (A j)) (fun j => rescale (u j) (B j)) *
      (assemble (fun j => rescale (u j) (A j))
        (fun j => rescale (u j) (B j)))ᴴ := by
  erw [rescaled_assemble_gram (fun j : (Function.support u).toFinite.toFinset => u j) (fun j => hu j)
    (fun j : (Function.support u).toFinite.toFinset => A j) (fun j : (Function.support u).toFinite.toFinset => B j),
    rescaled_assemble_gram u hu A B]
  exact sum_support u (fun j => (u j : ℂ) • gram (A j) (B j))
    (fun j hj => by simp [hj])
private lemma selected_compressionGram (p : ℝ) (hp : 0 < p) (u : J → ℝ)
    (hu : ∀ j, 0 ≤ u j) (A : ∀ j, Matrix HA (C j) ℂ)
    (B : ∀ j, Matrix HB (C j) ℂ) :
    compressionGram p (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (A j))
      (fun j : (Function.support u).toFinite.toFinset => rescale (u j) (B j)) =
    compressionGram p (fun j => rescale (u j) (A j))
      (fun j => rescale (u j) (B j)) := by
  ext i k
  erw [compressionGram_rescale_apply p hp (fun j : (Function.support u).toFinite.toFinset => u j) (fun j => hu j)
    (fun j : (Function.support u).toFinite.toFinset => A j) (fun j : (Function.support u).toFinite.toFinset => B j) i k,
    compressionGram_rescale_apply p hp u hu A B i k]
  exact sum_support u (fun j => (u j : ℂ) *
    (compression p A B i j * star (compression p A B k j)))
    (fun j hj => by simp [hj])
theorem upper_three_columns (p : ℝ) (hp : 2 ≤ p)
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧ Fintype.card ((Function.support w).toFinite.toFinset) ≤ 3 ∧
      compressionGram p (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
        (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j)) = compressionGram p A B ∧
      schattenNorm p (assemble A B) ≤
        schattenNorm p (assemble (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
          (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j))) := by
  obtain ⟨w, hw, hs, hm, hn⟩ := rescaling_upper_three p hp A B
  have hp0 : 0 < p := by linarith
  refine ⟨w, hw, by simpa only [Fintype.card_coe] using hs, ?_, ?_⟩
  · exact (selected_compressionGram p hp0 w hw A B).trans hm
  · have heq : schattenNorm p
        (assemble (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
          (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j))) =
        schattenNorm p
          (assemble (fun j => rescale (w j) (A j)) (fun j => rescale (w j) (B j))) := by
      unfold schattenNorm
      rw [schattenPow_eq_eigenPow_rowGram p hp0,
        schattenPow_eq_eigenPow_rowGram p hp0, selected_assemble_gram w hw A B]
    exact hn.trans_eq heq.symm
theorem r1_upper (p : ℝ) (hp : 2 ≤ p)
    (h3 : ∀ {K : Type uJ} [Fintype K] [DecidableEq K]
      {D : K → Type uC} [∀ k, Fintype (D k)] [∀ k, DecidableEq (D k)]
      (A' : ∀ k, Matrix HA (D k) ℂ) (B' : ∀ k, Matrix HB (D k) ℂ),
      0 < Fintype.card K → Fintype.card K ≤ 3 →
      schattenNorm p (assemble A' B') ≤ schattenNorm p (compression p A' B'))
    (A : ∀ j, Matrix HA (C j) ℂ) (B : ∀ j, Matrix HB (C j) ℂ) :
    schattenNorm p (assemble A B) ≤ schattenNorm p (compression p A B) := by
  obtain ⟨w, hw, hs, hm, hn⟩ := upper_three_columns p hp A B
  have hp0 : 0 < p := by linarith
  by_cases hk : 0 < Fintype.card ((Function.support w).toFinite.toFinset)
  swap
  · have hz : Fintype.card ((Function.support w).toFinite.toFinset) = 0 := by omega
    haveI : IsEmpty ((Function.support w).toFinite.toFinset) := Fintype.card_eq_zero_iff.mp hz
    have hzero : assemble (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
        (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j)) = 0 := by
      ext i j
      exact isEmptyElim j.1
    have hnzero := (schattenNorm_zero_iff p hp0 _).mpr hzero
    rw [hnzero] at hn
    exact hn.trans (schattenNorm_nonneg p (compression p A B))
  have hsmall := h3 (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
    (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j)) hk hs
  have htarget : schattenNorm p
      (compression p (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
        (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j))) =
      schattenNorm p (compression p A B) := by
    unfold schattenNorm
    rw [schattenPow_eq_eigenPow_rowGram p hp0,
      schattenPow_eq_eigenPow_rowGram p hp0]
    change (eigenPow (p / 2)
      (compressionGram p (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (A j))
        (fun j : (Function.support w).toFinite.toFinset => rescale (w j) (B j)))) ^ (1 / p) =
      (eigenPow (p / 2) (compressionGram p A B)) ^ (1 / p)
    rw [hm]
  exact hn.trans (hsmall.trans_eq htarget)
end
end D5.S3.Quantum.NormCompression.UpperBranchReduction
