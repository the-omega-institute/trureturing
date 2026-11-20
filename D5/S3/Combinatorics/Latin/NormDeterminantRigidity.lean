/- GID: D5/S3/Combinatorics/Latin/NormDeterminantRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/NormDeterminantRigidity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Complex n-by-n factors of squared Frobenius norm n with a unitary product are unitary. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#198)
escape_witness: norm_det_le_one_and_rigid (if the squared Frobenius norm of a complex n-by-n
  matrix M is n, the eigenvalues of Mᴴ M are nonnegative, sum to n and multiply to ‖det M‖²;
  the bound x ≤ exp(x - 1) gives ‖det M‖ ≤ 1, and if ‖det M‖ = 1 the strict bound at x ≠ 1
  forces every eigenvalue to be 1, so Mᴴ M = 1 by the spectral theorem).
proof_shape:
  frob, claim: source definitions; consumers: norm_det_le_one_and_rigid, result.
  trace_gram, det_gram: bind-only helpers (entrywise expansion and z̄ z = ‖z‖²); consumers:
    eig_sum_prod, norm_det_unitary.
  eig_sum_prod: bind-only helper (trace and determinant as sum and product of eigenvalues);
    consumer: norm_det_le_one_and_rigid.
  norm_det_le_one_and_rigid: content; consumer: result.
  norm_det_unitary: bind-only helper (det of star U * U = 1); consumer: result.
  list_det: content (induction: a product of norms in [0, 1] equal to 1 has every factor 1);
    consumer: result.
  result: content.
Direct frozen dependencies: none (Mathlib only).
Search record (§3.1): Mathlib has the spectral theorem, Matrix.IsHermitian.det_eq_prod_eigenvalues,
  trace_eq_sum_eigenvalues and the weighted AM-GM inequality, and LinearMap.normDet with
  normDet_eq_prod_singularValues, but no bound of ‖det M‖ by the Frobenius norm with its
  equality case, and no Hadamard-type determinant inequality; D5 has no unitary-factor
  statement (D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization is classical).
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Norm–determinant rigidity of unitary products

For a complex `n × n` matrix `M` with squared Frobenius norm `n`, the eigenvalues `λᵢ ≥ 0` of
`Mᴴ M` satisfy `∑ λᵢ = n` and `∏ λᵢ = ‖det M‖²`. Since `λ ≤ exp(λ - 1)`, with equality only at
`λ = 1`, this gives `‖det M‖ ≤ 1`, and equality forces `Mᴴ M = 1`. If a product of such factors
is unitary, the determinant norms multiply to `1`, so every factor attains equality and is
unitary.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Latin.NormDeterminantRigidity

open Matrix
open scoped ComplexOrder

/-- The squared Frobenius norm `∑ᵢ ∑ⱼ ‖Mᵢⱼ‖²`. -/
noncomputable def frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Every factor of a unitary product of complex `n × n` matrices, each of squared Frobenius
norm `n`, is unitary. -/
def claim : Prop :=
  ∀ (n : ℕ) (L : List (Matrix (Fin n) (Fin n) ℂ)), (∀ M ∈ L, frob M = n) →
    L.prod ∈ unitaryGroup (Fin n) ℂ → ∀ M ∈ L, M ∈ unitaryGroup (Fin n) ℂ

private theorem trace_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Mᴴ * M).trace = (frob M : ℂ) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, frob]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]
  norm_cast

private theorem det_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Mᴴ * M).det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
  norm_cast

/-- The eigenvalues of `Mᴴ M` sum to the squared Frobenius norm and multiply to `‖det M‖²`. -/
private theorem eig_sum_prod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    let hH := isHermitian_conjTranspose_mul_self M
    (∑ i, hH.eigenvalues i = frob M) ∧ (∏ i, hH.eigenvalues i = ‖M.det‖ ^ 2) := by
  intro hH
  constructor
  · have := hH.trace_eq_sum_eigenvalues
    rw [trace_gram] at this
    apply Complex.ofReal_injective
    push_cast
    exact this.symm
  · have := hH.det_eq_prod_eigenvalues
    rw [det_gram] at this
    apply Complex.ofReal_injective
    rw [this]
    push_cast
    rfl

/-- **Norm–determinant rigidity.** If `‖M‖_F² = n`, then `‖det M‖ ≤ 1`, and equality forces `M`
to be unitary. -/
theorem norm_det_le_one_and_rigid {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : frob M = n) :
    ‖M.det‖ ≤ 1 ∧ (‖M.det‖ = 1 → M ∈ unitaryGroup (Fin n) ℂ) := by
  set hH := isHermitian_conjTranspose_mul_self M
  obtain ⟨hsum, hprod⟩ := eig_sum_prod M
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i :=
    fun i => (posSemidef_conjTranspose_mul_self M).eigenvalues_nonneg i
  have hexp : ∏ i, Real.exp (hH.eigenvalues i - 1) = 1 := by
    rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum, hM]; simp
  have hle : ∏ i, hH.eigenvalues i ≤ 1 := by
    rw [← hexp]
    refine Finset.prod_le_prod₀ (fun i _ => hnn i) fun i _ => ?_
    have := Real.add_one_le_exp (hH.eigenvalues i - 1)
    linarith
  have hdet_le : ‖M.det‖ ≤ 1 := by
    have : ‖M.det‖ ^ 2 ≤ 1 := hprod ▸ hle
    nlinarith [norm_nonneg M.det]
  refine ⟨hdet_le, fun h1 => ?_⟩
  have hp1 : ∏ i, hH.eigenvalues i = 1 := by rw [hprod, h1]; norm_num
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => by
    rcases (hnn i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ i, hH.eigenvalues i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      rw [hp1] at this; exact one_ne_zero this
  have hall : ∀ i, hH.eigenvalues i = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    have hlt : ∏ i, hH.eigenvalues i < ∏ i, Real.exp (hH.eigenvalues i - 1) := by
      refine Finset.prod_lt_prod₀ (fun i _ => hpos i) (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
      · have := Real.add_one_le_exp (hH.eigenvalues i - 1); linarith
      · have := Real.add_one_lt_exp (x := hH.eigenvalues j - 1) (sub_ne_zero.mpr hj); linarith
    rw [hp1, hexp] at hlt
    exact lt_irrefl _ hlt
  have hgram : Mᴴ * M = 1 := by
    rw [hH.spectral_theorem]
    have : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℂ) = fun _ => 1 := by
      funext i; simp [hall i]
    rw [this, diagonal_one, map_one]
  exact mem_unitaryGroup_iff'.mpr hgram

private theorem norm_det_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) : ‖U.det‖ = 1 := by
  have h := congrArg det (mem_unitaryGroup_iff'.mp hU)
  rw [det_one, star_eq_conjTranspose, det_gram] at h
  have h2 : ‖U.det‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [norm_nonneg U.det]

private theorem list_det {n : ℕ} (L : List (Matrix (Fin n) (Fin n) ℂ))
    (hL : ∀ M ∈ L, ‖M.det‖ ≤ 1) :
    ‖L.prod.det‖ ≤ 1 ∧ (‖L.prod.det‖ = 1 → ∀ M ∈ L, ‖M.det‖ = 1) := by
  induction L with
  | nil => simp
  | cons B L ih =>
    obtain ⟨hle, hone⟩ := ih fun M hM => hL M (List.mem_cons_of_mem B hM)
    have hB := hL B List.mem_cons_self
    rw [List.prod_cons, det_mul, norm_mul]
    have h0 := norm_nonneg B.det
    have h0' := norm_nonneg L.prod.det
    refine ⟨by nlinarith, fun h1 M hM => ?_⟩
    have hB1 : ‖B.det‖ = 1 := by nlinarith
    have hL1 : ‖L.prod.det‖ = 1 := by nlinarith
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hB1
    · exact hone hL1 M hM

/-- The claim holds for every size `n` and every finite list of factors. -/
theorem result : claim := by
  intro n L hfrob hU M hM
  have hle := fun M hM => (norm_det_le_one_and_rigid M (hfrob M hM)).1
  exact (norm_det_le_one_and_rigid M (hfrob M hM)).2
    ((list_det L hle).2 (norm_det_unitary hU) M hM)

end D5.S3.Combinatorics.Latin.NormDeterminantRigidity
