/- GID: D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Isomorphic bipartite double covers have the same main eigenvalues. -/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Real.Basic

/-! Collins–Sciriha, arXiv:1906.05790v1, Question 5.8 and journal Question 16.
The lift and fiber sum specialize Teranishi's equitable quotient method as
presented by Yan and Wang, arXiv:2201.01101v1, Lemma 3. -/

open scoped BigOperators
open Matrix

namespace D5.S3.Combinatorics.SpectralGraph.CollinsScirihaMainSpectrum

public section

/-- A real adjacency eigenvector with nonzero coordinate sum witnesses mainness. -/
@[expose] def IsMain {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (lam : ℝ) : Prop :=
  ∃ x : V → ℝ, (∀ v, (G.adjMatrix ℝ *ᵥ x) v = lam * x v) ∧ (∑ v, x v) ≠ 0

variable {V W : Type*}

private theorem cover_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.bipartiteDoubleCover.adjMatrix ℝ =
      Matrix.fromBlocks 0 (G.adjMatrix ℝ) (G.adjMatrix ℝ) 0 := by
  ext (v | v) (w | w) <;> rfl

private theorem cover_mulVec [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V ⊕ V → ℝ) :
    G.bipartiteDoubleCover.adjMatrix ℝ *ᵥ y =
      Sum.elim (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inr)) (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inl)) := by
  rw [cover_adjMatrix, Matrix.fromBlocks_mulVec]
  simp

private theorem main_cover_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (lam : ℝ) :
    IsMain G.bipartiteDoubleCover lam ↔ IsMain G lam := by
  constructor
  · rintro ⟨y, hy, hsum⟩
    refine ⟨fun v ↦ y (Sum.inl v) + y (Sum.inr v), ?_, ?_⟩
    · intro v
      have hleft := hy (Sum.inl v)
      have hright := hy (Sum.inr v)
      rw [cover_mulVec] at hleft hright
      change (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inr)) v = lam * y (Sum.inl v) at hleft
      change (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inl)) v = lam * y (Sum.inr v) at hright
      calc
        (G.adjMatrix ℝ *ᵥ (fun w ↦ y (Sum.inl w) + y (Sum.inr w))) v =
            (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inr)) v + (G.adjMatrix ℝ *ᵥ (y ∘ Sum.inl)) v := by
          simp only [SimpleGraph.adjMatrix_mulVec_apply, Function.comp_apply,
            Finset.sum_add_distrib, add_comm]
        _ = lam * (y (Sum.inl v) + y (Sum.inr v)) := by rw [hleft, hright, mul_add]
    · simpa only [Fintype.sum_sum_type, Finset.sum_add_distrib] using hsum
  · rintro ⟨x, hx, hsum⟩
    refine ⟨Sum.elim x x, ?_, ?_⟩
    · intro v
      rw [cover_mulVec]
      cases v with
      | inl v => exact hx v
      | inr v => exact hx v
    · rw [Fintype.sum_sum_type]
      change (∑ v, x v) + (∑ v, x v) ≠ 0
      rw [← two_mul]
      exact mul_ne_zero two_ne_zero hsum

private theorem main_pullback [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) {lam : ℝ}
    (h : IsMain H lam) : IsMain G lam := by
  obtain ⟨y, hy, hsum⟩ := h
  refine ⟨y ∘ e, ?_, ?_⟩
  · intro v
    have hmatrix : (H.adjMatrix ℝ).submatrix e e.toEquiv = G.adjMatrix ℝ :=
      e.toEmbedding.submatrix_adjMatrix ℝ
    have hvec := Matrix.submatrix_mulVec_equiv (H.adjMatrix ℝ) (y ∘ e) e e.toEquiv
    rw [hmatrix] at hvec
    have hcancel : (y ∘ e) ∘ e.toEquiv.symm = y := by
      funext w
      change y (e.toEquiv (e.toEquiv.symm w)) = y w
      rw [Equiv.apply_symm_apply]
    rw [hcancel] at hvec
    exact (congrFun hvec v).trans (hy (e v))
  · change (∑ v, y (e.toEquiv v)) ≠ 0
    rw [e.toEquiv.sum_comp y]
    exact hsum

open Classical in
/-- Isomorphic bipartite double covers preserve mainness in both directions. -/
theorem result {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G.bipartiteDoubleCover ≃g H.bipartiteDoubleCover) (lam : ℝ) :
    (IsMain G lam → IsMain H lam) ∧ (IsMain H lam → IsMain G lam) := by
  constructor
  · intro h
    exact (main_cover_iff H lam).mp (main_pullback e.symm ((main_cover_iff G lam).mpr h))
  · intro h
    exact (main_cover_iff G lam).mp (main_pullback e ((main_cover_iff H lam).mpr h))


end

end D5.S3.Combinatorics.SpectralGraph.CollinsScirihaMainSpectrum
