/- GID: D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/SignedVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed orthonormal pairings are bounded by the Ky Fan singular-value sum. -/

import D5.S3.Combinatorics.Graph.KyFanGap.Defs

/-! Signed variational interfaces for Ky Fan sums. -/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace D5.S3.Combinatorics.Graph.KyFanGap

open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

structure SignedWitness (k n : ℕ) where
  vectors : Fin k → EuclideanSpace ℝ (Fin n)
  orthonormal_vectors : Orthonormal ℝ vectors
  signs : Fin k → ℝ
  signs_sq : ∀ i, signs i ^ 2 = 1

def signedPairing {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, W.signs i * (⟪W.vectors i, Matrix.toEuclideanLin M (W.vectors i)⟫_ℝ)

/-- Signed orthonormal testing is bounded by the singular-value prefix. -/
theorem signed_pairing_le_kyFan {k n : ℕ} (W : SignedWitness k n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    signedPairing W M ≤ kyFan k M := by
  classical
  have hk : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using W.orthonormal_vectors.linearIndependent.fintype_card_le_finrank
  have hu : Orthonormal ℝ (fun i => W.signs i • W.vectors i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right,
      orthonormal_iff_ite.mp W.orthonormal_vectors]
    split_ifs with hij
    · subst j
      simpa [pow_two] using W.signs_sq i
    · simp
  have h := re_sum_inner_map_le_ky_fan_sum
    (A := Matrix.toEuclideanLin M) hk hu W.orthonormal_vectors
  simpa [signedPairing, kyFan, real_inner_smul_left] using h

theorem exists_signed_pairing_eq_kyFan {k n : ℕ} (hk : k ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    ∃ W : SignedWitness k n, signedPairing W M = kyFan k M := by
  classical
  let A := Matrix.toEuclideanLin M
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hA : A.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hM)
  let lam := hA.eigenvalues hn
  let σ : Equiv.Perm (Fin n) :=
    Fin.revPerm.trans (Tuple.sort (fun i => |lam i|))
  let b := (hA.eigenvectorBasis hn).reindex σ.symm
  let μ : Fin n → ℝ := fun i => lam (σ i) ^ 2
  have hb (i : Fin n) : A (b i) = lam (σ i) • b i := by
    simp [b, lam, OrthonormalBasis.reindex_apply]
  have habs : Antitone (fun i : Fin n => |lam (σ i)|) := by
    intro i j hij
    exact (Tuple.monotone_sort (fun i => |lam i|)) (Fin.rev_le_rev.mpr hij)
  have hμ : Antitone μ := by
    intro i j hij
    have hh := habs hij
    have hp := mul_nonneg (sub_nonneg.mpr hh)
      (add_nonneg (abs_nonneg (lam (σ i))) (abs_nonneg (lam (σ j))))
    dsimp [μ]
    nlinarith [sq_abs (lam (σ i)), sq_abs (lam (σ j))]
  let Q := LinearMap.adjoint A ∘ₗ A
  have hQ : Q.IsSymmetric := A.isSymmetric_adjoint_comp_self
  have hadj : LinearMap.adjoint A = A :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint A).mp hA
  have hQb (i : Fin n) : Q (b i) = μ i • b i := by
    simp only [Q, LinearMap.comp_apply, hadj, hb, map_smul, smul_smul, μ, pow_two]
  have hmatrix : Q.toMatrix b.toBasis b.toBasis = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, hQb]
    · simp [LinearMap.toMatrix_apply, hQb, hij]
  have hchar : Q.charpoly = ∏ i, (Polynomial.X - Polynomial.C (μ i)) := by
    rw [← Q.charpoly_toMatrix b.toBasis, hmatrix, Matrix.charpoly_diagonal]
  have hroots : Q.charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ μ) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  have hspectrum : hQ.eigenvalues hn = μ := by
    rw [← List.ofFn_inj, ← hQ.sort_roots_charpoly_eq_eigenvalues hn]
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    convert! List.mergeSort_of_pairwise ?_
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  have hsing (i : Fin n) : A.singularValues i = |lam (σ i)| := by
    rw [A.singularValues_fin hn i]
    change Real.sqrt (hQ.eigenvalues hn i) = _
    rw [hspectrum]
    exact Real.sqrt_sq_eq_abs _
  let v : Fin k → EuclideanSpace ℝ (Fin n) := fun i => b (Fin.castLE hk i)
  let ε : Fin k → ℝ := fun i => if 0 ≤ lam (σ (Fin.castLE hk i)) then 1 else -1
  let W : SignedWitness k n :=
    { vectors := v
      orthonormal_vectors := b.orthonormal.comp _ (Fin.castLE_injective hk)
      signs := ε
      signs_sq := by intro i; dsimp [ε]; split_ifs <;> norm_num }
  refine ⟨W, ?_⟩
  change (∑ i : Fin k, ε i * ⟪v i, A (v i)⟫_ℝ) =
    ∑ i : Fin k, A.singularValues (i : ℕ)
  apply Finset.sum_congr rfl
  intro i _
  have hvnorm : ‖v i‖ = 1 := b.orthonormal.norm_eq_one (Fin.castLE hk i)
  have hvi : A (v i) = lam (σ (Fin.castLE hk i)) • v i := hb _
  have hi := hsing (Fin.castLE hk i)
  rw [show A.singularValues (i : ℕ) = |lam (σ (Fin.castLE hk i))| from hi,
    hvi, real_inner_smul_right, real_inner_self_eq_norm_sq, hvnorm]
  simp only [one_pow, mul_one]
  dsimp [ε]
  split_ifs with hh
  · simp [abs_of_nonneg hh]
  · simp [abs_of_neg (lt_of_not_ge hh)]

end D5.S3.Combinatorics.Graph.KyFanGap
