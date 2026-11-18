/- GID: D5/S3/QuadraticForms/ChordalPsdCompletion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ChordalPsdCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clique-positive real tables on finite chordal graphs admit PSD completions. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import D5.S3.QuadraticForms.WeightedGramContraction
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Real positive semidefinite completion, including singular clique blocks.
Reference: Vandenberghe and Andersen, Chordal Graphs and Semidefinite
Optimization, Theorem 10.1. The construction eliminates a simplicial vertex,
aligns its neighbour Gram family with a recursively completed family using
the existing equal-Gram contraction, and adds one residual coordinate.

Admission: escape-witness. The public completion theorem is content via the
whole recursive compatible-completion construction. The private Gram factor
adapter is bind-only and consumed by extend_simplicial; that constructive
extension is consumed by exists_posSemidef_completion. Neither factor
normalization nor the exposure of the original contraction is new content.
This is a general existential structural theorem, with utility none.
-/

universe u

noncomputable section
open scoped InnerProductSpace BigOperators

namespace D5.S3.QuadraticForms.ChordalPsdCompletion

private theorem gram_factor {V : Type*} [Finite V] (A : Matrix V V ℝ)
    (hA : A.PosSemidef) :
    ∃ n : ℕ, ∃ p : V → EuclideanSpace ℝ (Fin n), ∀ i j, ⟪p i, p j⟫_ℝ = A i j := by
  classical
  obtain ⟨n, q, hq⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  refine ⟨n, fun i => WithLp.toLp 2 (fun k => q k i), ?_⟩
  intro i j
  rw [hq]
  simp [PiLp.inner_apply, Matrix.sum_apply, Matrix.vecMulVec, mul_comm]

private theorem extend_simplicial {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) (hv : G.IsSimplicial v)
    (A : Matrix V V ℝ)
    (hA : ∀ C : Set V, G.IsClique C → (A.submatrix (Subtype.val : C → V) Subtype.val).PosSemidef)
    (B : Matrix {i : V // i ≠ v} {i : V // i ≠ v} ℝ) (hB : B.PosSemidef)
    (hagree : ∀ i j, i = j ∨ G.Adj i.val j.val → B i j = A i.val j.val) :
    ∃ B' : Matrix V V ℝ, B'.PosSemidef ∧
      ∀ i j, i = j ∨ G.Adj i j → B' i j = A i j := by
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
  obtain ⟨n, x, hx⟩ := gram_factor B hB
  obtain ⟨m, y, hy⟩ := gram_factor _ (hA C hC)
  simp only [Matrix.submatrix_apply] at hy
  let N := {i : V // G.Adj v i}
  let old (k : N) : {i : V // i ≠ v} := ⟨k.val, (G.ne_of_adj k.property).symm⟩
  let loc (k : N) : C := ⟨k.val, Or.inr k.property⟩
  let root : C := ⟨v, Or.inl rfl⟩
  have hg (i j : N) : ⟪x (old i), x (old j)⟫_ℝ = ⟪y (loc i), y (loc j)⟫_ℝ := by
    rw [hx, hy]
    apply hagree
    by_cases hij : i.val = j.val
    · exact Or.inl (Subtype.ext hij)
    · exact Or.inr (hv i.property j.property hij)
  obtain ⟨Z, hZ, hmap⟩ :=
    WeightedGramContraction.contraction_of_gram (fun k => x (old k)) (fun k => y (loc k)) hg
  have hnorm (k : N) : ‖Z (y (loc k))‖ = ‖y (loc k)‖ := by
    rw [hmap]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hg]
  have hb (t : EuclideanSpace ℝ (Fin m)) : ‖Z t‖ ≤ ‖t‖ := by
    calc
      ‖Z t‖ ≤ ‖Z‖ * ‖t‖ := Z.le_opNorm t
      _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hZ (norm_nonneg _)
      _ = ‖t‖ := one_mul _
  have hadj (k : N) : (ContinuousLinearMap.adjoint Z) (x (old k)) = y (loc k) := by
    rw [← hmap]
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
    · calc
        ‖(ContinuousLinearMap.adjoint Z) (Z (y (loc k)))‖ ≤
            ‖ContinuousLinearMap.adjoint Z‖ * ‖Z (y (loc k))‖ :=
          (ContinuousLinearMap.adjoint Z).le_opNorm _
        _ = ‖Z‖ * ‖y (loc k)‖ := by rw [ContinuousLinearMap.adjoint.norm_map, hnorm]
        _ ≤ 1 * ‖y (loc k)‖ := mul_le_mul_of_nonneg_right hZ (norm_nonneg _)
        _ = ‖y (loc k)‖ := one_mul _
    · rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hnorm]
      rfl
  have hmix (k : N) : ⟪Z (y root), x (old k)⟫_ℝ = A v k.val := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hy]
  let r : ℝ := Real.sqrt (‖y root‖ ^ 2 - ‖Z (y root)‖ ^ 2)
  have hr : r ^ 2 = ‖y root‖ ^ 2 - ‖Z (y root)‖ ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (hb _) 2))
  let p (i : V) : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
    if h : i = v then WithLp.toLp 2 (Z (y root), r)
    else WithLp.toLp 2 (x ⟨i, h⟩, 0)
  refine ⟨Matrix.gram ℝ p, Matrix.posSemidef_gram ℝ p, ?_⟩
  intro i j hij
  change ⟪p i, p j⟫_ℝ = A i j
  by_cases hi : i = v
  · subst i
    by_cases hj : j = v
    · subst j
      simp only [p, dite_eq_left rfl, WithLp.prod_inner_apply,
        real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      have hroot : ‖y root‖ ^ 2 = A v v := by
        simpa only [real_inner_self_eq_norm_sq] using hy root root
      linarith [hr]
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
    · simp only [p, dite_eq_right hi, dite_eq_right hj, WithLp.prod_inner_apply,
        inner_zero_left, add_zero]
      rw [hx]
      apply hagree
      exact hij.imp (fun h => Subtype.ext h) id

/-- Every real clique-positive table on a finite chordal graph has a positive
semidefinite completion preserving all diagonals and all graph edges.
The carrier may be empty, and no clique block is required to be nonsingular. -/
theorem exists_posSemidef_completion {V : Type u} [Finite V]
    (G : SimpleGraph V) (hG : G.IsChordal) (A : Matrix V V ℝ)
    (hA : ∀ C : Set V, G.IsClique C →
      (A.submatrix (Subtype.val : C → V) Subtype.val).PosSemidef) :
    ∃ B : Matrix V V ℝ, B.PosSemidef ∧
      ∀ i j, i = j ∨ G.Adj i j → B i j = A i j := by
  classical
  let := Fintype.ofFinite V
  suffices h : ∀ n : ℕ, ∀ {W : Type u} [Fintype W], Fintype.card W = n →
      ∀ (H : SimpleGraph W), H.IsChordal → ∀ (T : Matrix W W ℝ),
      (∀ C : Set W, H.IsClique C →
        (T.submatrix (Subtype.val : C → W) Subtype.val).PosSemidef) →
      ∃ B : Matrix W W ℝ, B.PosSemidef ∧
        ∀ i j, i = j ∨ H.Adj i j → B i j = T i j by
    exact h (Fintype.card V) rfl G hG A hA
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
          ((T.submatrix (Subtype.val : S → W) Subtype.val).submatrix
            (Subtype.val : C → S) Subtype.val).PosSemidef := by
        let D : Set W := Subtype.val '' C
        have hD : H.IsClique D := SimpleGraph.isClique_induce_iff.mp hC
        let f : C → D := fun i => ⟨i.val.val, ⟨i.val, i.property, rfl⟩⟩
        simpa only [Matrix.submatrix_submatrix, Function.comp_def, f] using (hT D hD).submatrix f
      obtain ⟨B, hB, hagree⟩ := ih (Fintype.card S) hsmall rfl
        (H.induce S) (hH.induce S) (T.submatrix Subtype.val Subtype.val) hTS
      exact extend_simplicial H v hv T hT B hB hagree
    · have : IsEmpty W := not_nonempty_iff.mp hne
      refine ⟨0, Matrix.PosSemidef.zero, ?_⟩
      intro i
      exact isEmptyElim i

end D5.S3.QuadraticForms.ChordalPsdCompletion
