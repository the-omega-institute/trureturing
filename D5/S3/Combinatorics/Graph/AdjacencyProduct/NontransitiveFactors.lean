/- GID: D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: Two non-vertex-transitive simple graph factors of the complete graph on 17 vertices. -/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import OmegaBuild.Commands

/-! Akbari, Elahimanesh and Miraftab, arXiv:2512.24864v1, Section 5, item 2. -/

compile_only_with_mathlib

namespace D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors

open SimpleGraph Matrix

private def neighborsB : Vector (List (Fin 17)) 17 :=
  ⟨#[[1, 2, 3, 4],
    [0, 8, 13, 16],
    [0, 5, 10, 13],
    [0, 4, 8, 13],
    [0, 3, 5, 10],
    [2, 4, 8, 13],
    [7, 10, 11, 15],
    [6, 9, 12, 16],
    [1, 3, 5, 14],
    [7, 10, 12, 15],
    [2, 4, 6, 9],
    [6, 12, 15, 16],
    [7, 9, 11, 14],
    [1, 2, 3, 5],
    [8, 12, 15, 16],
    [6, 9, 11, 14],
    [1, 7, 11, 14]], rfl⟩

private def neighborsC : Vector (List (Fin 17)) 17 :=
  ⟨#[[5, 6, 7, 8],
    [4, 5, 11, 12],
    [3, 6, 7, 8],
    [2, 10, 14, 16],
    [1, 9, 13, 15],
    [0, 1, 9, 15],
    [0, 2, 12, 14],
    [0, 2, 14, 15],
    [0, 2, 11, 12],
    [4, 5, 11, 16],
    [3, 11, 12, 13],
    [1, 8, 9, 10],
    [1, 6, 8, 10],
    [4, 10, 14, 16],
    [3, 6, 7, 13],
    [4, 5, 7, 16],
    [3, 9, 13, 15]], rfl⟩

private def adjacent (rows : Vector (List (Fin 17)) 17) (i j : Fin 17) : Prop :=
  (rows.get i).contains j = true

private instance (rows : Vector (List (Fin 17)) 17) : DecidableRel (adjacent rows) :=
  fun i j => inferInstanceAs (Decidable ((rows.get i).contains j = true))

private def graphB : SimpleGraph (Fin 17) where
  Adj := adjacent neighborsB
  symm := ⟨fun i j => (show ∀ i j, adjacent neighborsB i j → adjacent neighborsB j i
    from by decide) i j⟩
  loopless := ⟨by decide⟩

private def graphC : SimpleGraph (Fin 17) where
  Adj := adjacent neighborsC
  symm := ⟨fun i j => (show ∀ i j, adjacent neighborsC i j → adjacent neighborsC j i
    from by decide) i j⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel graphB.Adj :=
  inferInstanceAs (DecidableRel (adjacent neighborsB))

private instance : DecidableRel graphC.Adj :=
  inferInstanceAs (DecidableRel (adjacent neighborsC))

private theorem diagonal_pow_invariant {G : SimpleGraph (Fin 17)} [DecidableRel G.Adj]
    (e : G ≃g G) (n : ℕ) (i : Fin 17) :
    (G.adjMatrix ℤ ^ n) (e i) (e i) = (G.adjMatrix ℤ ^ n) i i := by
  let p := e.toEquiv
  have hAdj : (G.adjMatrix ℤ).submatrix p p = G.adjMatrix ℤ :=
    e.toEmbedding.submatrix_adjMatrix ℤ
  have h : (G.adjMatrix ℤ ^ n).submatrix p p = G.adjMatrix ℤ ^ n := by
    induction n with
    | zero => simpa only [pow_zero] using (Matrix.submatrix_one_equiv (α := ℤ) p)
    | succ n ih =>
      simp only [pow_succ, ← Matrix.submatrix_mul_equiv _ _ p p p, ih, hAdj]
  exact congrFun (congrFun h i) i

private theorem product_entry : ∀ i j : Fin 17,
    (graphB.adjMatrix ℤ * graphC.adjMatrix ℤ) i j = if i = j then 0 else 1 := by decide

private theorem walkB_zero : (graphB.adjMatrix ℤ ^ 3) 0 0 = 2 := by decide

private theorem walkB_one : (graphB.adjMatrix ℤ ^ 3) 1 1 = 0 := by decide

private theorem walkC_zero : (graphC.adjMatrix ℤ ^ 4) 0 0 = 40 := by
  rw [show (4 : ℕ) = 2 + 2 by decide, pow_add]
  decide

private theorem walkC_two : (graphC.adjMatrix ℤ ^ 4) 2 2 = 42 := by
  rw [show (4 : ℕ) = 2 + 2 by decide, pow_add]
  decide

/-- Two non-vertex-transitive simple graphs on the same 17 vertices have integer
adjacency matrices whose ordinary product is the all-ones matrix minus the identity. -/
theorem result :
    ∃ H K : SimpleGraph (Fin 17),
      ∃ (dH : DecidableRel H.Adj) (dK : DecidableRel K.Adj),
        letI : DecidableRel H.Adj := dH
        letI : DecidableRel K.Adj := dK
        H.adjMatrix ℤ * K.adjMatrix ℤ = (Matrix.of 1 - 1) ∧
        (¬ ∀ i j, ∃ e : H ≃g H, e i = j) ∧
        (¬ ∀ i j, ∃ e : K ≃g K, e i = j) := by
  refine ⟨graphB, graphC, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · ext i j
    rw [product_entry, Matrix.sub_apply, Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij]
  · intro h
    obtain ⟨e, he⟩ := h 0 1
    have hw := diagonal_pow_invariant e 3 0
    rw [he, walkB_one, walkB_zero] at hw
    exact (by decide : (0 : ℤ) ≠ 2) hw
  · intro h
    obtain ⟨e, he⟩ := h 0 2
    have hw := diagonal_pow_invariant e 4 0
    rw [he, walkC_two, walkC_zero] at hw
    exact (by decide : (42 : ℤ) ≠ 40) hw

end D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors
