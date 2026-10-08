/- GID: D5/S3/SpectralTopology/HermitianEigenvaluePerturbation
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/HermitianEigenvaluePerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weyl bounds for the sorted eigenvalues of finite Hermitian matrices. -/

/- Judgement form (implementation assessment; each helper retains its own classification).
   proof_shape: abs_eigenvalue_sub_eigenvalue_le_norm: content; consumer=UniformPerturbedParameters.Anchor.perturbed_kernel_stability; same-delivery-content=D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le.
   proof_shape: norm_toEuclideanLin_le_of_entry_le: content; consumer=MaximalBirankEdgeStates.Finite.entry_norm_bound.
   proof_shape: abs_eigenvalues0_sub_le_norm: content; consumer=HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le; same-delivery-content=D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le_norm.
   proof_shape: abs_eigenvalues0_sub_le_of_entry_le: content; consumer=UniformParameterAnchor.Uniform.negative_eigenvalue_perturbation; same-delivery-content=D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm.
   escape_witness: abs_eigenvalues0_sub_le_norm, via the two spectral subspaces and their nonzero intersection.
   Classification totals: 8 content; 7 bind-only.
   admission_basis: escape-witness
   Direct frozen dependencies: none; dependencies are pinned Mathlib and same-delivery modules.
   Ported proofs: LeanPool (github.com/LeanPool/lean-pool, Apache-2.0,
   Copyright (c) 2026 Kitware, Inc.).
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Chebyshev

/-!
Weyl's inequality bounds each decreasingly sorted Hermitian eigenvalue by the
Euclidean operator norm of the matrix difference. The entrywise bound is used by
ChoiKiemKye.UniformParameterAnchor; the operator bound is used by
ChoiKiemKye.UniformPerturbedParameters.
The proofs are transplants from https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8.
CourantFischer source: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean
EntrywiseOpNorm source: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean
EntrywiseEigenvalue source: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/Matrix/EntrywiseEigenvalue.lean
BasisSpan source: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean
BasisSpan SHA-256: bdbdde4470cf4354308d0a482c232bb459fbbcb47a796b69ff262293df2e4170
Source SHA-256s:
CourantFischer: 6c8d454870a1c6eb4c7b8eaff1558ad3e6b0de152d8e2a6f26fe4841ddbc48fa
EntrywiseOpNorm: e4726f011648df9d3186bd1395fe80e526c6cee367a408aa0e9033d4b1593ce4
EntrywiseEigenvalue: 5d96c803d89720d52621674fbba13f8a710672dcf099c6055928fc8ea6ea5b1f
The complete Apache-2.0 LICENSE and NOTICE chain are retained in
`docs/reports/brooks-suppliers/daviskahan-LICENSE.txt` and `daviskahan-NOTICE.txt`.
When pinned Mathlib provides these statements, replace the consumers with direct applications.
-/

noncomputable section
open Module (finrank)
open scoped InnerProductSpace
namespace D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}

/- Source unit: LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
private theorem finrank_span_image (b : OrthonormalBasis (Fin n) ℂ E) (s : Finset (Fin n)) :
    finrank ℂ (Submodule.span ℂ (b '' (s : Set (Fin n)))) = s.card := by
  have h := finrank_span_eq_card
    (b.orthonormal.linearIndependent.comp (fun i : ↥(↑s : Set (Fin n)) => (i : Fin n))
      Subtype.val_injective)
  rw [Set.image_eq_range]
  simpa [Function.comp_def] using h

private theorem repr_zero_of_mem_span (b : OrthonormalBasis (Fin n) ℂ E)
    {s : Set (Fin n)} {x : E} (hx : x ∈ Submodule.span ℂ (b '' s))
    {i : Fin n} (hi : i ∉ s) : b.repr x i = 0 := by
  have hs := b.toBasis.repr_support_subset_of_mem_span s (by simpa using hx)
  have hn : i ∉ (b.toBasis.repr x).support := fun h => hi (hs h)
  simpa using Finsupp.notMem_support_iff.mp hn

/- Source unit: LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
variable [FiniteDimensional ℂ E] {T S : E →ₗ[ℂ] E}

omit [FiniteDimensional ℂ E] in
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) ℂ E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

private theorem re_inner_apply_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_ℂ
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_ℂ
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
    rfl
  rw [key]
  exact Complex.ofReal_re _

private theorem re_inner_apply_self_le_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' s)) :
    RCLike.re ⟪T x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_apply_self_eq_sum_eigenvalues_mul_sq hT hn x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_zero_of_mem_span b hx hp]; simp

private theorem le_re_inner_apply_self_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' s)) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_apply_self_eq_sum_eigenvalues_mul_sq hT hn x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_zero_of_mem_span b hx hp]; simp

private theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (k : Fin n)
    (V : Submodule ℂ E) (hV : finrank ℂ V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_ℂ ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := Submodule.span ℂ (b '' ↑(Finset.Ici k)) with hW
  have hWdim : finrank ℂ W = n - (k : ℕ) := by
    rw [hW, finrank_span_image b, Fin.card_Ici]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank ℂ V + finrank ℂ W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ :=
    (fun hbot => (not_le_of_gt (by omega : finrank ℂ E < finrank ℂ V + finrank ℂ W))
      (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot)))
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  -- The unit vector still lies in `W`; on `W` the selected eigenvalues are all `≤ λₖ`
  -- (antitone), so the spectral-subspace bound gives `re ⟪T x, x⟫ ≤ λₖ · ‖x‖² = λₖ`.
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_ℂ
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        re_inner_apply_self_le_of_mem_spanIndices hT hn
          (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

private theorem exists_submodule_forall_unit_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (k : Fin n) :
    ∃ V : Submodule ℂ E, finrank ℂ V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  set b := hT.eigenvectorBasis hn
  refine ⟨Submodule.span ℂ (b '' ↑(Finset.Iic k)), ?_, ?_⟩
  · rw [finrank_span_image b, Fin.card_Iic]
  · intro x hxV hnx
    -- On this subspace the selected eigenvalues are all `≥ λₖ` (antitone), so the dual
    -- spectral-subspace bound gives `λₖ = λₖ · ‖x‖² ≤ re ⟪T x, x⟫`.
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_ℂ :=
          le_re_inner_apply_self_of_mem_spanIndices hT hn
            (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxV

private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℂ E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    exists_submodule_forall_unit_eigenvalue_le_re_inner hS hn k
  obtain ⟨x, hxV, hnx, hTup⟩ :=
    exists_unit_vector_re_inner_le_eigenvalue hT hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_ℂ := hVlow x hxV hnx
  -- `λₖ(S) − λₖ(T) ≤ re ⟪Sx,x⟫ − re ⟪Tx,x⟫ = re ⟪(S−T)x,x⟫ ≤ ‖(S−T)x‖ ≤ ε`.
  have hdiff : RCLike.re ⟪S x, x⟫_ℂ - RCLike.re ⟪T x, x⟫_ℂ
      = RCLike.re ⟪(S - T) x, x⟫_ℂ := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_ℂ ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    have := hε x
    simpa only [hnx, mul_one] using this
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_ℂ - RCLike.re ⟪T x, x⟫_ℂ := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_ℂ := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

private theorem abs_eigenvalue_sub_eigenvalue_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank ℂ E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- The two directions of `eigenvalues_sub_le`, with the roles of `T` and `S`
  -- swapped, using `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

theorem abs_eigenvalue_sub_eigenvalue_le_norm
    {d : ℕ} {T S : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)}
    (hT : LinearMap.IsSymmetric (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)))
    (hS : LinearMap.IsSymmetric (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)))
    (hn : finrank ℂ (EuclideanSpace ℂ (Fin d)) = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ‖T - S‖ := by
  refine abs_eigenvalue_sub_eigenvalue_le hT hS hn (fun x => ?_) k
  simpa using (T - S).le_opNorm x

/- Source unit: LeanPool/DavisKahan/ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
private theorem sum_norm_le_sqrt_card_mul_norm {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt (Fintype.card ι) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ i, ‖x i‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    have hrw : (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
    rw [hrw, hnorm]; exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

theorem norm_toEuclideanLin_le_of_entry_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : Matrix.toEuclideanLin A x = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    simp
  · have heps : 0 ≤ ε := (norm_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    have hrow : ∀ i : Fin n,
        ‖(Matrix.toEuclideanLin A x) i‖ ≤ ε * (Real.sqrt n * ‖x‖) := by
      intro i
      have happ : (Matrix.toEuclideanLin A x) i = ∑ j : Fin n, A i j * x j := by
        change (A.mulVec (WithLp.ofLp x)) i = _
        simp [Matrix.mulVec, dotProduct]
      calc
        ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : Fin n, A i j * x j‖ := by rw [happ]
        _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
        _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
        _ ≤ ∑ j : Fin n, ε * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
        _ = ε * ∑ j : Fin n, ‖x j‖ := by rw [Finset.mul_sum]
        _ ≤ ε * (Real.sqrt n * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using sum_norm_le_sqrt_card_mul_norm x) heps
    have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        ∑ i : Fin n, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
            ≤ ∑ _i : Fin n, (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
        _ = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hsq_eq : ((n : ℝ) * ε * ‖x‖) ^ 2 =
        (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      simp only [mul_pow, hs]
      ring
    have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ ((n : ℝ) * ε * ‖x‖) ^ 2 := by
      rw [hsq_eq]
      exact hnorm_sq
    exact (abs_le_of_sq_le_sq' hle (by positivity)).2

/-- Weyl's inequality for the decreasingly sorted eigenvalues of Hermitian matrices. -/
theorem abs_eigenvalues0_sub_le_norm
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card (Fin n))) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A - B)‖ := by
  have h := abs_eigenvalue_sub_eigenvalue_le_norm
    (T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (S := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace k
  simpa only [Matrix.IsHermitian.eigenvalues₀, map_sub] using h

/- Source unit: LeanPool/DavisKahan/ForTauCeti/Analysis/Matrix/EntrywiseEigenvalue.lean -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
theorem abs_eigenvalues0_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, ‖Ahat i j - A i j‖ ≤ ε)
    (k : Fin (Fintype.card (Fin n))) :
    |hAhat.eigenvalues₀ k - hA.eigenvalues₀ k| ≤ (n : ℝ) * ε := by
  have hε : 0 ≤ (n : ℝ) * ε := by
    have hn := k.isLt
    have hpos : 0 < n := by simpa only [Fintype.card_fin] using k.pos
    have hnonneg := (norm_nonneg _).trans (hentry ⟨0, hpos⟩ ⟨0, hpos⟩)
    positivity
  exact (abs_eigenvalues0_sub_le_norm hAhat hA k).trans
    (ContinuousLinearMap.opNorm_le_bound _ hε (fun x =>
      norm_toEuclideanLin_le_of_entry_le (fun i j => hentry i j) x))

end D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
