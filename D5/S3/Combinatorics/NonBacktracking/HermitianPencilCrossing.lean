/- GID: D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A symmetric Hermitian pencil has a singular point when endpoint subspace signs cross. -/

/- Judgement form.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15386.
   proof_shape: pencil_singular_of_subspaces: content
   escape_witness: pencil_singular_of_subspaces (ordered-eigenvalue sign crossing and dimension obstruction)
   admission_basis: escape-witness
   Owner declaration identities (producing Lean report; public API re-pin): D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue (statement_id sha256:db7411fc038dde55051b605a75e04c276d83ca7452caed40cdd2030bacb1f2ad); D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner (statement_id sha256:f65fbfeb07a19a6b00f0d2cbf90c03cabdaaea7530d966173716ea7d506cfae3); D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le (statement_id sha256:914d96cba49b1649c8d13bfe19d14cc7ba7385bd42ae1eee1e570b770e1600f6).
-/

import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
open Module (finrank)
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Combinatorics.NonBacktracking.HermitianPencilCrossing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem continuous_eigenvalues0_affine (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card ι)) :
    Continuous (fun t : ℝ => (hA.sub (hB.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))).eigenvalues₀ k) := by
  let f (t : ℝ) := (hA.sub (hB.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))).eigenvalues₀ k
  let c := ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B‖
  have hbound (s t : ℝ) : |f s - f t| ≤ c * |s-t| := by
    apply (D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.sub (hB.smul (show IsSelfAdjoint (s : ℂ) from by simp [IsSelfAdjoint]))))
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.sub (hB.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))))
      finrank_euclideanSpace (ε := c * |s-t|) (fun x => ?_) k)
    have he : (Matrix.toEuclideanLin (A - (s : ℂ) • B) - Matrix.toEuclideanLin (A - (t : ℂ) • B)) x =
        ((t-s : ℝ) : ℂ) • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B x := by
      change (Matrix.toEuclideanLin (A - (s : ℂ) • B) - Matrix.toEuclideanLin (A - (t : ℂ) • B)) x =
        ((t-s : ℝ) : ℂ) • Matrix.toEuclideanLin B x
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
      push_cast
      module
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have hb := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B).le_opNorm x
    dsimp [c]
    nlinarith [abs_nonneg (s-t)]
  have hl : LipschitzWith ⟨c, norm_nonneg _⟩ f := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro s t
    change |f s - f t| ≤ c * |s-t|
    exact hbound s t
  exact hl.continuous

private theorem eigenvalue_nonpos_of_large_nonpos_subspace
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card ι))
    (W : Submodule ℂ (EuclideanSpace ℂ ι))
    (hW : finrank ℂ W + (k : ℕ) + 1 > Fintype.card ι)
    (hneg : ∀ x ∈ W, RCLike.re ⟪Matrix.toEuclideanLin A x, x⟫_ℂ ≤ 0) :
    hA.eigenvalues₀ k ≤ 0 := by
  by_contra! hp
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  obtain ⟨V, hV, hq⟩ := D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner hT finrank_euclideanSpace k
  have hd : Disjoint V W := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    obtain ⟨hxV, hxW⟩ := Submodule.mem_inf.mp hx
    by_contra hx0
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let y := (‖x‖⁻¹ : ℂ) • x
    have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_inv, hn.ne', abs_of_pos hn]
    have hyV : y ∈ V := V.smul_mem _ hxV
    have hyW : y ∈ W := W.smul_mem _ hxW
    have hh := hq y hyV hy
    have hl := hneg y hyW
    exact (not_le_of_gt hp) (hh.trans hl)
  have hh := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [hV, finrank_euclideanSpace] at hh
  omega

private theorem eigenvalue_pos_of_pos_subspace
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : Fin (Fintype.card ι))
    (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (hV : finrank ℂ V = (k : ℕ) + 1)
    (hpos : ∀ x ∈ V, x ≠ 0 → 0 < RCLike.re ⟪Matrix.toEuclideanLin A x, x⟫_ℂ) :
    0 < hA.eigenvalues₀ k := by
  obtain ⟨x, hx, hn, he⟩ := D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_unit_vector_re_inner_le_eigenvalue
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace k V hV
  exact (hpos x hx (by intro h; simp [h] at hn)).trans_le he

theorem pencil_singular_of_subspaces (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (a b : ℝ) (hab : a ≤ b) (k : Fin (Fintype.card ι))
    (W V : Submodule ℂ (EuclideanSpace ℂ ι))
    (hW : finrank ℂ W + (k : ℕ) + 1 > Fintype.card ι)
    (hV : finrank ℂ V = (k : ℕ) + 1)
    (hneg : ∀ x ∈ W, RCLike.re ⟪Matrix.toEuclideanLin (A-(a : ℂ) • B) x,x⟫_ℂ ≤ 0)
    (hpos : ∀ x ∈ V, x ≠ 0 → 0 < RCLike.re ⟪Matrix.toEuclideanLin (A-(b : ℂ) • B) x,x⟫_ℂ) :
    ∃ t ∈ Set.Ico a b, ∃ x : ι → ℂ, x ≠ 0 ∧ (A-(t : ℂ) • B) *ᵥ x = 0 := by
  let f (t : ℝ) := (hA.sub (hB.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))).eigenvalues₀ k
  have ha : f a ≤ 0 := eigenvalue_nonpos_of_large_nonpos_subspace _ _ W hW hneg
  have hb : 0 < f b := eigenvalue_pos_of_pos_subspace _ _ V hV hpos
  obtain ⟨t, ht, hf⟩ := intermediate_value_Icc hab
    (continuous_eigenvalues0_affine A B hA hB k).continuousOn ⟨ha, hb.le⟩
  have htb : t < b := lt_of_le_of_ne ht.2 (by intro he; subst t; simp_all [f])
  let hH := hA.sub (hB.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))
  let j : ι := (Fintype.equivOfCardEq (Fintype.card_fin _)) k
  have hj : hH.eigenvalues j = 0 := by simpa [Matrix.IsHermitian.eigenvalues, j, f] using hf
  refine ⟨t, ⟨ht.1, htb⟩, ⇑(hH.eigenvectorBasis j), ?_, ?_⟩
  · intro hz
    have hz' : hH.eigenvectorBasis j = 0 := by exact (WithLp.ofLp_injective 2) hz
    have := hH.eigenvectorBasis.orthonormal.1 j
    simp [hz'] at this
  · rw [hH.mulVec_eigenvectorBasis, hj, zero_smul]

#print axioms pencil_singular_of_subspaces
end D5.S3.Combinatorics.NonBacktracking.HermitianPencilCrossing
