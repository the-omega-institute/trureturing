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

/-! Disjoint labelled blocks retain their actual vertex subsets throughout counting. -/

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
  blockGraph : SimpleGraph V
  adjDec : DecidableRel blockGraph.Adj
  noIsolated : ∀ v, ∃ w, blockGraph.Adj v w

attribute [instance] Block.finite Block.eqDec Block.adjDec

private def sum (A B : Block) : Block where
  V := A.V ⊕ B.V
  finite := inferInstance
  eqDec := inferInstance
  blockGraph := A.blockGraph ⊕g B.blockGraph
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
  blockGraph := ⊥
  adjDec := inferInstance
  noIsolated := fun v => Fin.elim0 v

private def copies (A : Block) : ℕ → Block
  | 0 => empty
  | n + 1 => sum A (copies A n)

private def complete (r : ℕ) : Block where
  V := Fin (r + 2)
  finite := inferInstance
  eqDec := inferInstance
  blockGraph := ⊤
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
  blockGraph := SimpleGraph.completeEquipartiteGraph 3 2
  adjDec := inferInstance
  noIsolated := (equipartite_block 3 (by omega)).2.2.2

private theorem copies_metrics (A : Block) (n : ℕ) :
    Fintype.card (copies A n).V = n * Fintype.card A.V ∧
    (minimalForts (copies A n).blockGraph).card = n * (minimalForts A.blockGraph).card ∧
    (rootedChoices (copies A n).blockGraph).card = (rootedChoices A.blockGraph).card ^ n := by
  induction n with
  | zero =>
    change Fintype.card (Fin 0) = 0 * Fintype.card A.V ∧
      (minimalForts (⊥ : SimpleGraph (Fin 0))).card = 0 * (minimalForts A.blockGraph).card ∧
      (rootedChoices (⊥ : SimpleGraph (Fin 0))).card = (rootedChoices A.blockGraph).card ^ 0
    norm_num
    decide +kernel
  | succ n ih =>
    change Fintype.card (A.V ⊕ (copies A n).V) = _ ∧
      (minimalForts (A.blockGraph ⊕g (copies A n).blockGraph)).card = _ ∧
      (rootedChoices (A.blockGraph ⊕g (copies A n).blockGraph)).card = _
    rw [Fintype.card_sum, minimalFort_sum_count,
      rootedChoices_sum_count _ _ A.noIsolated (copies A n).noIsolated,
      ih.1, ih.2.1, ih.2.2]
    constructor
    · ring
    constructor
    · ring
    · exact (pow_succ' _ _).symm

private theorem complete_metrics (r : ℕ) :
    Fintype.card (complete r).V = r + 2 ∧
    (minimalForts (complete r).blockGraph).card = (r + 2).choose 2 ∧
    (rootedChoices (complete r).blockGraph).card = r + 2 := by
  haveI : Nontrivial (Fin (r + 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine ⟨Fintype.card_fin _, ?_, ?_⟩
  · convert (complete_block (V := Fin (r + 2))).2 using 1 <;> try simp only [Fintype.card_fin]
    congr 3
  · convert (complete_rooted_count (V := Fin (r + 2))) using 1 <;> try simp only [Fintype.card_fin]
    congr 3

private theorem sum_metrics (A B : Block) :
    (minimalForts (sum A B).blockGraph).card = (minimalForts A.blockGraph).card + (minimalForts B.blockGraph).card ∧
    (rootedChoices (sum A B).blockGraph).card = (rootedChoices A.blockGraph).card * (rootedChoices B.blockGraph).card := by
  constructor
  · convert (minimalFort_sum_count A.blockGraph B.blockGraph) using 1
    congr 3
  · convert (rootedChoices_sum_count A.blockGraph B.blockGraph A.noIsolated B.noIsolated) using 1
    congr 3

private def base (x y z r : ℕ) : Block :=
  sum (copies (complete 4) x)
    (sum (copies (complete 1) (2 * y)) (sum (copies oct z) (complete r)))

/-- The actual labelled vertex type, including its universal root. -/
abbrev Vertex (x y z r : ℕ) := Option (base x y z r).V

instance (x y z r : ℕ) : Fintype (Vertex x y z r) := inferInstanceAs (Fintype (Option _))
instance (x y z r : ℕ) : DecidableEq (Vertex x y z r) := inferInstanceAs (DecidableEq (Option _))

/-- The cone over x complete six-blocks, 2y triangles, z octahedra and one K_(r+2). -/
def graph (x y z r : ℕ) : SimpleGraph (Vertex x y z r) := cone (base x y z r).blockGraph

instance (x y z r : ℕ) : DecidableRel (graph x y z r).Adj :=
  inferInstanceAs (DecidableRel (cone (base x y z r).blockGraph).Adj)

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
  have ho : Fintype.card oct.V = 6 ∧ (minimalForts oct.blockGraph).card = 11 ∧
      (rootedChoices oct.blockGraph).card = 12 := by
    have h := equipartite_block 3 (by omega)
    have h0 : Fintype.card (Fin 3 × Fin 2) = 6 ∧
        (minimalForts (SimpleGraph.completeEquipartiteGraph 3 2)).card = 11 ∧
        (rootedChoices (SimpleGraph.completeEquipartiteGraph 3 2)).card = 12 := by
      simpa only [show 2 * 3 = 6 by rfl, show Nat.choose 3 3 = 1 by decide,
        Nat.mul_one, show 3 + 8 = 11 by rfl, show Nat.choose 3 2 = 3 by decide,
        show 4 * 3 = 12 by rfl] using And.intro h.1 (And.intro h.2.1 h.2.2.1)
    convert h0 using 1 <;> congr 3
  refine ⟨?_, cone_connected _, ?_⟩
  · change Fintype.card (Option ((copies (complete 4) x).V ⊕
      ((copies (complete 1) (2 * y)).V ⊕ ((copies oct z).V ⊕ (complete r).V)))) = _
    simp only [Fintype.card_option, Fintype.card_sum, hx.1, hy.1, hz.1,
      hc4.1, hc1.1, ho.1, hcr.1]
    omega
  · change (minimalForts (cone (base x y z r).blockGraph)).card = _
    rw [cone_minimalFort_count _ (base x y z r).noIsolated]
    change (minimalForts (sum (copies (complete 4) x)
      (sum (copies (complete 1) (2 * y)) (sum (copies oct z) (complete r)))).blockGraph).card +
      (rootedChoices (sum (copies (complete 4) x)
      (sum (copies (complete 1) (2 * y)) (sum (copies oct z) (complete r)))).blockGraph).card = _
    rw [(sum_metrics _ _).1, (sum_metrics _ _).2,
      (sum_metrics (copies (complete 1) (2 * y)) _).1,
      (sum_metrics (copies (complete 1) (2 * y)) _).2,
      (sum_metrics (copies oct z) (complete r)).1,
      (sum_metrics (copies oct z) (complete r)).2,
      hx.2.1, hy.2.1, hz.2.1, hx.2.2, hy.2.2, hz.2.2,
      hc4.2.1, hc1.2.1, hcr.2.1, hc4.2.2, hc1.2.2, hcr.2.2, ho.2.1, ho.2.2]
    norm_num [pow_mul, show Nat.choose 6 2 = 15 by decide, show Nat.choose 3 2 = 3 by decide]
    ring

end D5.S3.Combinatorics.MinimalForts.MixedBlocks
