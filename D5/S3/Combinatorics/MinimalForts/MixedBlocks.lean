/- GID: D5/S3/Combinatorics/MinimalForts/MixedBlocks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/MixedBlocks
   mirror-E: none(waiver:explicit-graph-counting-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: Connected mixed complete and octahedral blocks have an exact full minimal-fort count. -/

import D5.S3.Combinatorics.MinimalForts.CompleteRooted
import D5.S3.Combinatorics.MinimalForts.RootedProduct
import D5.S3.Combinatorics.MinimalForts.ConeCount
import D5.S3.Combinatorics.MinimalForts.OctahedronBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.MixedBlocks

open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.MinimalForts.DisjointSum
open D5.S3.Combinatorics.MinimalForts.RootedProduct
open D5.S3.Combinatorics.MinimalForts.CompleteBlock
open D5.S3.Combinatorics.MinimalForts.CompleteRooted
open D5.S3.Combinatorics.MinimalForts.ConeCount
open D5.S3.Combinatorics.MinimalForts.OctahedronBlock

private structure Block where
  V : Type
  finite : Fintype V
  eqDec : DecidableEq V
  graph : SimpleGraph V
  adjDec : DecidableRel graph.Adj
  noIsolated : ∀ v, ∃ w, graph.Adj v w

attribute [instance] Block.finite Block.eqDec Block.adjDec

private def sum (A B : Block) : Block where
  V := A.V ⊕ B.V
  finite := inferInstance
  eqDec := inferInstance
  graph := A.graph ⊕g B.graph
  adjDec := inferInstance
  noIsolated := by
    intro v
    cases v with
    | inl v => obtain ⟨w, hw⟩ := A.noIsolated v; exact ⟨.inl w, hw⟩
    | inr v => obtain ⟨w, hw⟩ := B.noIsolated v; exact ⟨.inr w, hw⟩

private def empty : Block where
  V := Fin 0
  finite := inferInstance
  eqDec := inferInstance
  graph := ⊥
  adjDec := inferInstance
  noIsolated := fun v => Fin.elim0 v

private def copies (A : Block) : ℕ → Block
  | 0 => empty
  | n + 1 => sum A (copies A n)

private def complete (r : ℕ) : Block where
  V := Fin (r + 2)
  finite := inferInstance
  eqDec := inferInstance
  graph := ⊤
  adjDec := inferInstance
  noIsolated := by
    intro v
    haveI : Nontrivial (Fin (r + 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨w, hw⟩ := exists_ne v
    exact ⟨w, by simpa using hw.symm⟩

private def oct : Block where
  V := Fin 3 × Fin 2
  finite := inferInstance
  eqDec := inferInstance
  graph := octahedron
  adjDec := inferInstance
  noIsolated := octahedron_block.2.2.2

private theorem copies_metrics (A : Block) (n : ℕ) :
    Fintype.card (copies A n).V = n * Fintype.card A.V ∧
    (minimalForts (copies A n).graph).card = n * (minimalForts A.graph).card ∧
    (rootedChoices (copies A n).graph).card = (rootedChoices A.graph).card ^ n := by
  induction n with
  | zero =>
    change Fintype.card (Fin 0) = 0 * Fintype.card A.V ∧
      (minimalForts (⊥ : SimpleGraph (Fin 0))).card = 0 * (minimalForts A.graph).card ∧
      (rootedChoices (⊥ : SimpleGraph (Fin 0))).card = (rootedChoices A.graph).card ^ 0
    norm_num
    decide +kernel
  | succ n ih =>
    change Fintype.card (A.V ⊕ (copies A n).V) = _ ∧
      (minimalForts (A.graph ⊕g (copies A n).graph)).card = _ ∧
      (rootedChoices (A.graph ⊕g (copies A n).graph)).card = _
    rw [Fintype.card_sum, minimalFort_sum_count,
      rootedChoices_sum_count _ _ A.noIsolated (copies A n).noIsolated,
      ih.1, ih.2.1, ih.2.2]
    constructor
    · omega
    constructor
    · omega
    · exact (pow_succ' _ _).symm

private theorem complete_metrics (r : ℕ) :
    Fintype.card (complete r).V = r + 2 ∧
    (minimalForts (complete r).graph).card = (r + 2).choose 2 ∧
    (rootedChoices (complete r).graph).card = r + 2 := by
  haveI : Nontrivial (Fin (r + 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact ⟨Fintype.card_fin _, by simpa [complete] using (complete_block (V := Fin (r + 2))).2,
    by simpa [complete] using (complete_rooted_count (V := Fin (r + 2)))⟩

private def base (x y z r : ℕ) : Block :=
  sum (copies (complete 4) x)
    (sum (copies (complete 1) (2 * y)) (sum (copies oct z) (complete r)))

/-- The actual labelled vertex type, including its universal root. -/
abbrev Vertex (x y z r : ℕ) := Option (base x y z r).V

instance (x y z r : ℕ) : Fintype (Vertex x y z r) := inferInstanceAs (Fintype (Option _))
instance (x y z r : ℕ) : DecidableEq (Vertex x y z r) := inferInstanceAs (DecidableEq (Option _))

/-- The cone over x complete six-blocks, 2y triangles, z octahedra and one K_(r+2). -/
def graph (x y z r : ℕ) : SimpleGraph (Vertex x y z r) := cone (base x y z r).graph

instance (x y z r : ℕ) : DecidableRel (graph x y z r).Adj :=
  inferInstanceAs (DecidableRel (cone (base x y z r).graph).Adj)

/-- Exact order, connectedness, and the count of every actual minimal fort. -/
theorem mixed_graph_count (x y z r : ℕ) :
    Fintype.card (Vertex x y z r) = 6 * (x + y + z) + r + 3 ∧
    (graph x y z r).Connected ∧
    (minimalForts (graph x y z r)).card =
      (r + 2) * 6 ^ x * 9 ^ y * 12 ^ z + 15 * x + 6 * y + 11 * z + (r + 2).choose 2 := by
  have hx := copies_metrics (complete 4) x
  have hy := copies_metrics (complete 1) (2 * y)
  have hz := copies_metrics oct z
  have hc4 := complete_metrics 4
  have hc1 := complete_metrics 1
  have hcr := complete_metrics r
  have ho : Fintype.card oct.V = 6 ∧ (minimalForts oct.graph).card = 11 ∧
      (rootedChoices oct.graph).card = 12 :=
    ⟨octahedron_block.1, octahedron_block.2.1, octahedron_block.2.2.1⟩
  refine ⟨?_, cone_connected _, ?_⟩
  · change Fintype.card (Option ((copies (complete 4) x).V ⊕
      ((copies (complete 1) (2 * y)).V ⊕ ((copies oct z).V ⊕ (complete r).V)))) = _
    simp only [Fintype.card_option, Fintype.card_sum, hx.1, hy.1, hz.1,
      hc4.1, hc1.1, ho.1, hcr.1]
    omega
  · change (minimalForts (cone (base x y z r).graph)).card = _
    rw [cone_minimalFort_count _ (base x y z r).noIsolated]
    simp only [base, sum, minimalFort_sum_count,
      rootedChoices_sum_count _ _ (copies (complete 4) x).noIsolated
        (sum (copies (complete 1) (2 * y)) (sum (copies oct z) (complete r))).noIsolated,
      rootedChoices_sum_count _ _ (copies (complete 1) (2 * y)).noIsolated
        (sum (copies oct z) (complete r)).noIsolated,
      rootedChoices_sum_count _ _ (copies oct z).noIsolated (complete r).noIsolated,
      hx.2.1, hy.2.1, hz.2.1, hx.2.2, hy.2.2, hz.2.2,
      hc4.2.1, hc1.2.1, hcr.2.1, hc4.2.2, hc1.2.2, hcr.2.2, ho.2.1, ho.2.2]
    norm_num [pow_mul]
    ring

end D5.S3.Combinatorics.MinimalForts.MixedBlocks
