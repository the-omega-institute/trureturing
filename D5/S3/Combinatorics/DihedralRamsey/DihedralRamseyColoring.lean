/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyColoring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyColoring
   mirror-E: none(waiver:finite-degeneracy-colouring)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite]
   utility: none
   digest: Greedy colouring from hereditary ordered induced edge bounds. -/

import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open Finset

/-- Deleting a low-degree vertex and choosing a missing neighbour colour gives a colouring. -/
theorem colorable_of_sparse_induces {n d : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (sparse : ∀ (m : ℕ) (e : Fin m ↪o Fin n),
      2 * (G.comap e).edgeFinset.card ≤ d * m) : G.Colorable (d + 1) := by
  classical
  induction n with
  | zero =>
      exact ⟨SimpleGraph.Coloring.mk Fin.elim0 (by intro x; exact Fin.elim0 x)⟩
  | succ n ih =>
      have bound : ∑ v, G.degree v ≤ (n + 1) * d := by
        rw [G.sum_degrees_eq_twice_card_edges]
        have h := sparse (n + 1) (OrderIso.refl _).toOrderEmbedding
        change 2 * G.edgeFinset.card ≤ d * (n + 1) at h
        simpa [Nat.mul_comm] using h
      have bound' : ∑ v, G.degree v ≤ ∑ _ : Fin (n + 1), d := by
        simpa using bound
      obtain ⟨v, _, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty bound'
      let e := Fin.succAboveOrderEmb v
      obtain ⟨C⟩ := ih (G.comap e) (by
        intro m f
        exact sparse m (f.trans e))
      let neighbours := Finset.univ.filter fun i : Fin n => G.Adj v (e i)
      have neighbours_card : neighbours.card ≤ G.degree v := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_le_card_of_injOn e
        · intro i hi
          exact (G.mem_neighborFinset v (e i)).mpr (Finset.mem_filter.mp hi).2
        · intro i hi j hj hij
          exact e.injective hij
      have missing : (neighbours.image C).card < (Finset.univ : Finset (Fin (d + 1))).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt ((Finset.card_image_le).trans (neighbours_card.trans hv))
          (Nat.lt_succ_self d)
      obtain ⟨free, _, hfree⟩ := Finset.exists_mem_notMem_of_card_lt_card missing
      let c : Fin (n + 1) → Fin (d + 1) := v.insertNth free C
      refine ⟨SimpleGraph.Coloring.mk c ?_⟩
      intro x y hxy
      by_cases hx : x = v
      · subst x
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (G.ne_of_adj hxy).symm
        simp only [c, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        intro heq
        exact hfree (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hxy⟩, heq.symm⟩)
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
        by_cases hy : y = v
        · subst y
          simp only [c, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
          intro heq
          exact hfree (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hxy.symm⟩, heq⟩)
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hy
          simp only [c, Fin.insertNth_apply_succAbove]
          exact C.valid hxy

end D5.S3.Combinatorics.DihedralRamsey
