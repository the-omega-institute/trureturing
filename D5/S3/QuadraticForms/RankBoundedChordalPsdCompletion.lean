/- GID: D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RankBoundedChordalPsdCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chordal clique PSD rank bounds extend to global PSD completions. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/licenses/TauCeti-LICENSE.txt.
Authors: The Tau Ceti contributors, Jon Crall, Claude Fable 5
-/

/-!
The private local factorization and Gram-rigidity suppliers are adapted from
TauCetiProject/TauCeti, revision 0ae45cec5df3d83669e6a8403d229ddbf562d89c:
* TauCeti/LinearAlgebra/Matrix/Rank.lean
* TauCeti/Analysis/Matrix/GramFactorization.lean
* TauCeti/Analysis/InnerProductSpace/LinearCombination.lean
* TauCeti/Analysis/InnerProductSpace/Gram/Rigidity.lean
Only the consumed declaration closure is retained. Adaptations are private names,
imports and pinned-Mathlib API compatibility. These suppliers carry no claim of
new mathematical content. Remove each transplanted supplier when this repository's
own pinned Mathlib contains an equivalent full statement and its consumers compile
by direct application of that statement, including the zero-dimensional cases.
The new construction is simplicial extension in unchanged dimension followed by
finite-cardinality induction. It uses no computational utility.
-/

universe u
noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder MatrixOrder

namespace D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion

section Suppliers
open Matrix
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

private theorem exists_eq_mul_fin_rank (A : Matrix m n K) :
    ∃ (L : Matrix m (Fin A.rank) K) (R : Matrix (Fin A.rank) n K), A = L * R := by
  classical
  let e : LinearMap.range A.mulVecLin ≃ₗ[K] (Fin A.rank → K) :=
    (Module.finBasis K (LinearMap.range A.mulVecLin)).equivFun
  let l := (LinearMap.range A.mulVecLin).subtype.comp e.symm.toLinearMap
  let r := e.toLinearMap.comp A.mulVecLin.rangeRestrict
  have h : l.comp r = A.mulVecLin := by
    ext v i
    simp [l, r, LinearMap.comp_apply]
  refine ⟨LinearMap.toMatrix' l, LinearMap.toMatrix' r, ?_⟩
  rw [← LinearMap.toMatrix'_comp, h, ← toLin'_apply', LinearMap.toMatrix'_toLin']

/-- A rank bound gives a factorization through `Fin r`, padding an exact-rank factorization
with zero columns and rows when necessary. -/
private theorem exists_eq_mul_of_rank_le (A : Matrix m n K) {r : ℕ} (h : A.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) K) (R : Matrix (Fin r) n K), A = L * R := by
  classical
  obtain ⟨L, R, hA⟩ := exists_eq_mul_fin_rank A
  let e : Fin r ≃ Fin A.rank ⊕ Fin (r - A.rank) :=
    (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm
  refine ⟨(fromCols L (0 : Matrix m (Fin (r - A.rank)) K)).submatrix id e,
    (fromRows R (0 : Matrix (Fin (r - A.rank)) n K)).submatrix e id, ?_⟩
  simpa only [submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
    submatrix_id_id] using hA

end Suppliers

section Factor
open Matrix
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

private theorem posSemidef_iff_eq_conjTranspose_mul_self {B : Matrix n n 𝕜} :
    B.PosSemidef ↔ ∃ A : Matrix n n 𝕜, B = Aᴴ * A := by
  classical
  refine ⟨fun hB ↦ ?_, fun ⟨A, hA⟩ ↦ hA ▸ posSemidef_conjTranspose_mul_self A⟩
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  exact ⟨A, star_eq_conjTranspose A ▸ hA⟩

/-- A PSD matrix of rank at most `Fintype.card m` is the Gram matrix `Aᴴ * A` of
a matrix `A` with rows indexed by `m`. -/
private theorem exists_eq_conjTranspose_mul_self_of_rank_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B.rank ≤ Fintype.card m) : ∃ A : Matrix m n 𝕜, B = Aᴴ * A := by
  classical
  obtain ⟨X, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hB
  rw [rank_conjTranspose_mul_self] at h
  obtain ⟨L, R, rfl⟩ := exists_eq_mul_of_rank_le X h
  obtain ⟨C, hC⟩ :=
    posSemidef_iff_eq_conjTranspose_mul_self.mp (posSemidef_conjTranspose_mul_self L)
  refine ⟨(C * R).submatrix (Fintype.equivFin m) id, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id]
  calc (L * R)ᴴ * (L * R) = Rᴴ * (Lᴴ * L) * R := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (C * R)ᴴ * (C * R) := by rw [hC]; simp only [conjTranspose_mul, Matrix.mul_assoc]

end Factor

section Rigidity
variable {𝕜 M E F ι α : Type*} [RCLike 𝕜]
  [AddCommGroup M] [Module 𝕜 M]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem inner_linearCombination_eq_of_inner_eq (f g : α →₀ 𝕜) {φ : α → E} {ψ : α → F}
    (h : ∀ a b, ⟪φ a, φ b⟫_𝕜 = ⟪ψ a, ψ b⟫_𝕜) :
    ⟪Finsupp.linearCombination 𝕜 φ f, Finsupp.linearCombination 𝕜 φ g⟫_𝕜 =
      ⟪Finsupp.linearCombination 𝕜 ψ f, Finsupp.linearCombination 𝕜 ψ g⟫_𝕜 := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left,
    inner_smul_right, h]

private theorem ker_eq_of_inner_self_eq {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x, ⟪S x, S x⟫_𝕜 = ⟪T x, T x⟫_𝕜) : S.ker = T.ker := by
  ext x
  have hzero : ⟪S x, S x⟫_𝕜 = 0 ↔ ⟪T x, T x⟫_𝕜 = 0 := by rw [h x]
  simpa only [LinearMap.mem_ker, inner_self_eq_zero] using hzero

private def rangeEquivOfInnerEq {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) : S.range ≃ₗᵢ[𝕜] T.range :=
  (S.quotKerEquivRange.symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (ker_eq_of_inner_self_eq fun x => h x x) ≪≫ₗ
      T.quotKerEquivRange).isometryOfInner <| by
    rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hy
    simpa using (h x y).symm

/-- The range isometry sends each image under the first map to the corresponding image
under the second map. -/
@[simp]
private theorem rangeEquivOfInnerEq_apply {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) (x : M) :
    rangeEquivOfInnerEq h ⟨S x, LinearMap.mem_range_self S x⟩ =
      ⟨T x, LinearMap.mem_range_self T x⟩ :=
  Subtype.ext <| by simp [rangeEquivOfInnerEq]

private def spanEquivOfInnerEq {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    Submodule.span 𝕜 (Set.range v) ≃ₗᵢ[𝕜] Submodule.span 𝕜 (Set.range w) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := v) 𝕜).symm).trans
    ((rangeEquivOfInnerEq (S := Finsupp.linearCombination 𝕜 v)
      (T := Finsupp.linearCombination 𝕜 w)
        fun a b => inner_linearCombination_eq_of_inner_eq a b h).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := w) 𝕜)))

/-- The canonical span isometry sends corresponding family vectors to each other. -/
@[simp]
private theorem spanEquivOfInnerEq_apply {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) (i : ι) :
    spanEquivOfInnerEq h ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  simp only [spanEquivOfInnerEq, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  convert congrArg Subtype.val (rangeEquivOfInnerEq_apply
    (fun a b => inner_linearCombination_eq_of_inner_eq a b h) (Finsupp.single i 1))
    using 2 <;> simp [Subtype.ext_iff]

theorem exists_linearIsometryEquiv_of_inner_eq [FiniteDimensional 𝕜 E] {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    ∃ e : E ≃ₗᵢ[𝕜] E, ∀ i, e (v i) = w i := by
  let L :=
    (Submodule.span 𝕜 (Set.range w)).subtypeₗᵢ.comp (spanEquivOfInnerEq h).toLinearIsometry
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  change L.extend (v i) = w i
  calc
    L.extend (v i) = L ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
      L.extend_apply ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
    _ = w i := congrArg Subtype.val (spanEquivOfInnerEq_apply h i)

end Rigidity

attribute [local instance] Fintype.ofFinite

theorem gram_factor_rank {V : Type*} [Finite V] (d : ℕ)
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (hr : A.rank ≤ d) :
    ∃ p : V → EuclideanSpace ℝ (Fin d), ∀ i j, ⟪p i, p j⟫_ℝ = A i j := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨X, hX⟩ := exists_eq_conjTranspose_mul_self_of_rank_le
    (m := Fin d) hA (by simpa using hr)
  refine ⟨fun i => WithLp.toLp 2 (fun k => X k i), ?_⟩
  intro i j
  rw [hX]
  simp [PiLp.inner_apply, Matrix.mul_apply, mul_comm]

/-- Extend a realization across a simplicial vertex without increasing the ambient dimension. -/
private theorem extend_simplicial {V : Type*} [Finite V] (d : ℕ)
    (G : SimpleGraph V) (v : V) (hv : G.IsSimplicial v)
    (A : Matrix V V ℝ)
    (hA : ∀ C : Set V, G.IsClique C →
      (A.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).PosSemidef ∧
      (A.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).rank ≤ d)
    (x : {i : V // i ≠ v} → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i j, i = j ∨ G.Adj i.val j.val → ⟪x i, x j⟫_ℝ = A i.val j.val) :
    ∃ p : V → EuclideanSpace ℝ (Fin d),
      ∀ i j, i = j ∨ G.Adj i j → ⟪p i, p j⟫_ℝ = A i j := by
  classical
  let := Fintype.ofFinite V
  let C : Set V := insert v (G.neighborSet v)
  have hC : G.IsClique C := by
    intro i hi j hj hij
    rcases hi with rfl | hi
    · rcases hj with rfl | hj
      · exact (hij rfl).elim
      · exact hj
    · rcases hj with rfl | hj
      · exact hi.symm
      · exact hv hi hj hij
  obtain ⟨y, hy⟩ := gram_factor_rank d _ (hA C hC).1 (hA C hC).2
  simp only [Matrix.submatrix_apply] at hy
  let N := {i : V // G.Adj v i}
  let old (k : N) : {i : V // i ≠ v} := ⟨k.val, (G.ne_of_adj k.property).symm⟩
  let loc (k : N) : C := ⟨k.val, Or.inr k.property⟩
  let root : C := ⟨v, Or.inl rfl⟩
  have hg (i j : N) : ⟪y (loc i), y (loc j)⟫_ℝ = ⟪x (old i), x (old j)⟫_ℝ := by
    rw [hy]
    symm
    apply hx
    by_cases hij : i.val = j.val
    · exact Or.inl (Subtype.ext hij)
    · exact Or.inr (hv i.property j.property hij)
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_inner_eq hg
  have hmix (k : N) : ⟪e (y root), x (old k)⟫_ℝ = A v k.val := by
    rw [← he, e.inner_map_map, hy]
  let p (i : V) : EuclideanSpace ℝ (Fin d) :=
    if h : i = v then e (y root) else x ⟨i, h⟩
  refine ⟨p, ?_⟩
  intro i j hij
  by_cases hi : i = v
  · subst i
    by_cases hj : j = v
    · subst j
      simpa only [p, dite_eq_left rfl, e.inner_map_map] using hy root root
    · have hvj : G.Adj v j := hij.resolve_left (Ne.symm hj)
      simpa [p, hj, old] using hmix (⟨j, hvj⟩ : N)
  · by_cases hj : j = v
    · subst j
      have hvi : G.Adj v i := (hij.resolve_left hi).symm
      have hsym : A v i = A i v := by
        calc
          A v i = ⟪y root, y (loc ⟨i, hvi⟩)⟫_ℝ := (hy root (loc ⟨i, hvi⟩)).symm
          _ = ⟪y (loc ⟨i, hvi⟩), y root⟫_ℝ := real_inner_comm _ _
          _ = A i v := hy (loc ⟨i, hvi⟩) root
      rw [real_inner_comm]
      simpa [p, hi, old, hsym] using hmix (⟨i, hvi⟩ : N)
    · simp only [p, dite_eq_right hi, dite_eq_right hj]
      apply hx
      exact hij.imp (fun h => Subtype.ext h) id

set_option maxHeartbeats 800000 in
/-- Every finite real table whose clique blocks are PSD of rank at most `d`
on a chordal graph has a PSD completion of rank at most `d`, preserving all
specified diagonals and edges. Zero dimension and empty carriers are included. -/
theorem exists_posSemidef_completion_rank_le {V : Type u} [Finite V]
    (d : ℕ) (G : SimpleGraph V) (hG : G.IsChordal) (A : Matrix V V ℝ)
    (hA : ∀ C : Set V, G.IsClique C →
      (A.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).PosSemidef ∧
      (A.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).rank ≤ d) :
    ∃ B : Matrix V V ℝ, B.PosSemidef ∧ B.rank ≤ d ∧
      ∀ i j, i = j ∨ G.Adj i j → B i j = A i j := by
  classical
  let := Fintype.ofFinite V
  have assembly : ∀ n : ℕ, ∀ {W : Type u} [Fintype W], Fintype.card W = n →
      ∀ (H : SimpleGraph W), H.IsChordal → ∀ (T : Matrix W W ℝ),
      (∀ C : Set W, H.IsClique C →
        (T.submatrix (Subtype.val : C → W) (Subtype.val : C → W)).PosSemidef ∧
        (T.submatrix (Subtype.val : C → W) (Subtype.val : C → W)).rank ≤ d) →
      ∃ p : W → EuclideanSpace ℝ (Fin d),
        ∀ i j, i = j ∨ H.Adj i j → ⟪p i, p j⟫_ℝ = T i j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ hcard H hH T hT
      by_cases hne : Nonempty W
      · let := hne
        obtain ⟨v, hv⟩ := hH.exists_isSimplicial
        let S : Set W := {i | i ≠ v}
        have hsmall : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := v) (not_not.mpr rfl)
        have hTS (C : Set S) (hC : (H.induce S).IsClique C) :
            ((T.submatrix (Subtype.val : S → W) (Subtype.val : S → W)).submatrix
              (Subtype.val : C → S) (Subtype.val : C → S)).PosSemidef ∧
            ((T.submatrix (Subtype.val : S → W) (Subtype.val : S → W)).submatrix
              (Subtype.val : C → S) (Subtype.val : C → S)).rank ≤ d := by
          let D : Set W := Subtype.val '' C
          have hD : H.IsClique D := SimpleGraph.isClique_induce_iff.mp hC
          let f : C → D := fun i => ⟨i.val.val, ⟨i.val, i.property, rfl⟩⟩
          have hp := (hT D hD).1.submatrix f
          have hrD : (T.submatrix (Subtype.val : D → W) (Subtype.val : D → W)).rank ≤ d := by
            simpa only [Matrix.rank_eq_finrank_span_cols] using (hT D hD).2
          have hr := (Matrix.rank_submatrix_le
            (T.submatrix (Subtype.val : D → W) (Subtype.val : D → W)) f f).trans hrD
          simpa only [Matrix.rank_eq_finrank_span_cols, Matrix.submatrix_submatrix,
            Function.comp_def, f] using And.intro hp hr
        obtain ⟨x, hx⟩ := ih (Fintype.card S) hsmall rfl
          (H.induce S) (hH.induce S) (T.submatrix Subtype.val Subtype.val) hTS
        exact extend_simplicial d H v hv T
          (by simpa only [Matrix.rank_eq_finrank_span_cols] using hT) x hx
      · have : IsEmpty W := not_nonempty_iff.mp hne
        exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  obtain ⟨p, hp⟩ := assembly (Fintype.card V) rfl G hG A
    (by simpa only [Matrix.rank_eq_finrank_span_cols] using hA)
  let X : Matrix (Fin d) V ℝ := fun k i => p i k
  have hgram : Matrix.gram ℝ p = X.conjTranspose * X := by
    ext i j
    change ⟪p i, p j⟫_ℝ = ∑ k, star (X k i) * X k j
    simp [PiLp.inner_apply, X, mul_comm]
  refine ⟨Matrix.gram ℝ p, Matrix.posSemidef_gram ℝ p, ?_, hp⟩
  rw [hgram, Matrix.rank_conjTranspose_mul_self]
  simpa using X.rank_le_card_height

end D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion
