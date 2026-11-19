/- GID: D5/S3/Quantum/AURICOmega/GramRankFeatureMap
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/GramRankFeatureMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Gram rank at most r is equivalent to a feature map into Euclidean r-space. -/

import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-! Finite-rank feature maps for the reading of a ternary comparison structure.

The reading of a ternary comparison structure is a symmetric real kernel with nonnegative finite
Gram forms. Its finite Gram matrices all have rank at most `r` exactly when it is the Gram kernel
of a map into Euclidean `r`-space. The forward direction passes through the reproducing kernel
Hilbert space of the reading: a maximal linearly independent family of kernel functions has at
most `r` members and spans all kernel functions, and an orthonormal basis of that span, padded
by zero coordinates, gives the map. -/

open scoped InnerProductSpace

namespace D5.S3.Quantum.AURICOmega.GramRankFeatureMap

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

/-- A real kernel viewed as a matrix of scalar operators on the real line. -/
private noncomputable def scalarKernel {M : Type*} (k : M → M → ℝ) :
    Matrix M M (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ

/-- A symmetric real kernel whose finite Gram forms are nonnegative is a positive semidefinite
operator-valued kernel. -/
private theorem posSemidef_scalarKernel {M : Type*} (k : M → M → ℝ)
    (hsymm : ∀ x y : M, k x y = k y x)
    (hgram : ∀ (n : ℕ) (x : Fin n → M) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (x i) (x j)) :
    (scalarKernel k).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext x y
    simp [scalarKernel, Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_id, hsymm x y]
  · set e := vv.support.equivFin
    let x : Fin vv.support.card → M := fun i => (e.symm i : M)
    have hsum : ∀ g : M → ℝ, ∑ a ∈ vv.support, g a = ∑ i, g (x i) := fun g => by
      rw [← Finset.sum_coe_sort]
      exact (e.symm.sum_comp (fun a : vv.support => g a)).symm
    simp only [scalarKernel, Matrix.of_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Finsupp.sum, RCLike.re_to_real,
      RCLike.inner_apply, conj_trivial]
    rw [hsum]
    simp_rw [hsum]
    refine (hgram _ x fun i => vv (x i)).trans_eq
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [hsymm (x j) (x i)]
    ring

/-- A map into Euclidean `e`-space is carried, with the same Gram kernel, into Euclidean
`r`-space for any `r ≥ e` by appending zero coordinates. -/
private theorem exists_euclidean_of_le {M : Type*} {e r : ℕ}
    (v : M → EuclideanSpace ℝ (Fin e)) (h : e ≤ r) :
    ∃ φ : M → EuclideanSpace ℝ (Fin r), ∀ x y : M, ⟪φ x, φ y⟫_ℝ = ⟪v x, v y⟫_ℝ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨fun y => WithLp.toLp 2 (Fin.append (v y).ofLp 0), fun x y => ?_⟩
  simp only [PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, add_zero]

/-- If all finite Gram matrices of a map into a real inner product space have rank at most `r`,
the same Gram kernel is realized by a map into Euclidean `r`-space. -/
private theorem exists_euclidean_of_gram_rank_le {M E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ψ : M → E) (r : ℕ)
    (hrank : ∀ (n : ℕ) (x : Fin n → M), (Matrix.gram ℝ (ψ ∘ x)).rank ≤ r) :
    ∃ φ : M → EuclideanSpace ℝ (Fin r), ∀ x y : M, ⟪φ x, φ y⟫_ℝ = ⟪ψ x, ψ y⟫_ℝ := by
  classical
  have hbound : ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℝ (ψ ∘ x) → n ≤ r := by
    intro n x hx
    have hdet := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).mpr hx
    have hunit : IsUnit (Matrix.gram ℝ (ψ ∘ x)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    simpa [Matrix.rank_of_isUnit _ hunit] using hrank n x
  let P : ℕ → Prop := fun d => ∃ x : Fin d → M, LinearIndependent ℝ (ψ ∘ x)
  have hP0 : P 0 := ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨xs, hxs⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le r) hP0
  have hspan : ∀ y : M, ψ y ∈ Submodule.span ℝ (Set.range (ψ ∘ xs)) := by
    intro y
    by_contra hy
    have hli : LinearIndependent ℝ (ψ ∘ Fin.snoc xs y) := by
      rw [Fin.comp_snoc]
      exact linearIndependent_finSnoc.mpr ⟨hxs, hy⟩
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ _ hli) ⟨_, hli⟩
  set U := Submodule.span ℝ (Set.range (ψ ∘ xs))
  have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hU : Module.finrank ℝ U ≤ r :=
    (finrank_range_le_card (R := ℝ) (ψ ∘ xs)).trans
      ((Fintype.card_fin _).trans_le (Nat.findGreatest_le r))
  let b := stdOrthonormalBasis ℝ U
  obtain ⟨φ, hφ⟩ := exists_euclidean_of_le (fun y => b.repr ⟨ψ y, hspan y⟩) hU
  refine ⟨φ, fun x y => ?_⟩
  rw [hφ, b.repr.inner_map_map, Submodule.coe_inner]

/-- For the reading of a ternary comparison structure, every finite Gram matrix has rank at most
`r` if and only if the reading is the Gram kernel of a map into Euclidean `r`-space. -/
theorem gramRankLE_iff_hasFeatureRank {M : Type*} (C : TernaryComparison M) (r : ℕ) :
    C.GramRankLE r ↔ C.HasFeatureRank r := by
  constructor
  · intro h
    have : Fact (scalarKernel C.kappa).PosSemidef :=
      ⟨posSemidef_scalarKernel C.kappa C.kappa_symm C.kappa_gram_nonneg⟩
    let ψ : M → RKHS.OfKernel (scalarKernel C.kappa) := fun x => RKHS.kerFun _ x 1
    have hψ : ∀ x y : M, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y := by
      intro x y
      rw [← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
      simp [scalarKernel, C.kappa_symm y x]
    obtain ⟨φ, hφ⟩ := exists_euclidean_of_gram_rank_le ψ r fun n x => by
      have hG : Matrix.gram ℝ (ψ ∘ x) = Matrix.of fun i j => C.kappa (x i) (x j) := by
        ext i j
        simp [Matrix.gram_apply, hψ]
      rw [hG]
      exact h n x
    exact ⟨φ, fun x y => by rw [hφ, hψ]⟩
  · rintro ⟨φ, hφ⟩ n x
    have hG : (Matrix.of fun i j : Fin n => C.kappa (x i) (x j)) = Matrix.gram ℝ (φ ∘ x) := by
      ext i j
      simp [Matrix.gram_apply, hφ]
    rw [hG, Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin r) ℝ)]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _)

end D5.S3.Quantum.AURICOmega.GramRankFeatureMap
