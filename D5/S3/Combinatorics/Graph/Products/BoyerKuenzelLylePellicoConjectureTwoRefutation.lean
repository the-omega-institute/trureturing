/- GID: D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim; result=D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result; claim=D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim
   digest: The full general Conjecture 2 fails on the 3 by 3 rook graph, whose maximal induced bipartite sets have orders five and six. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.Graph.Products.BoyerKuenzelLylePellicoConjectureTwoRefutation

open Finset SimpleGraph

private def ProperColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (j : ℕ) (S : Finset V) : Prop :=
  ∃ c : V → Fin j, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

private instance properColorableDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (S : Finset V) :
    Decidable (ProperColorable G j S) := by
  unfold ProperColorable
  infer_instance

private def MaximalColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (j : ℕ) (S : Finset V) : Prop :=
  ProperColorable G j S ∧ ∀ x, x ∉ S → ¬ ProperColorable G j (insert x S)

private instance maximalColorableDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (S : Finset V) :
    Decidable (MaximalColorable G j S) := by
  unfold MaximalColorable
  infer_instance

private def WellHued {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∀ S T : Finset V,
    MaximalColorable G j S → MaximalColorable G j T → S.card = T.card

private def HasSequence {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ S : Finset V,
    MaximalColorable G j S → S.card = j * G.indepNum

private def HasChromaticNumber {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin k)) ∧ ∀ j : ℕ, j < k → ¬ Nonempty (G.Coloring (Fin j))

private def BalancedMultipartiteSubgraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Finset V,
    (∀ i, (parts i).card = G.indepNum) ∧
    (∀ i, G.IsIndepSet (parts i : Set V)) ∧
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    (∀ v, ∃ i, v ∈ parts i)

private def AntiNeighborhoodFree {V : Type*} [Finite V]
    (G : SimpleGraph V) : Prop :=
  ∀ u, ¬ ∃ I : Finset V,
    I.card = G.indepNum ∧ G.IsIndepSet (I : Set V) ∧
      ∀ x, x ∈ I → x ≠ u ∧ ¬ G.Adj u x

private def LeftSide {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.Connected ∧ WellHued G ∧ HasSequence G k ∧ HasChromaticNumber G k

private def RightSide {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  BalancedMultipartiteSubgraph G k ∧ AntiNeighborhoodFree G

/-- Boyer--Kuenzel--Lyle--Pellico, *Well-hued graphs with first difference two*,
Section 3, Conjecture 2 (printed page 10), with its unrestricted finite-graph and
positive-k quantifiers. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    0 < k → (LeftSide G k ↔ RightSide G k)

private def rookGraph : SimpleGraph (Fin 3 × Fin 3) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)
  symm := by aesop_graph
  loopless := by aesop_graph

private instance : DecidableRel rookGraph.Adj := by
  intro p q
  unfold rookGraph
  infer_instance

private def S : Finset (Fin 3 × Fin 3) :=
  {(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)}

private def T : Finset (Fin 3 × Fin 3) :=
  {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)}

private theorem rook_alpha : rookGraph.indepNum = 3 := by
  obtain ⟨M, hM⟩ := rookGraph.maximumIndepSet_exists
  have hcard : M.card = rookGraph.indepNum :=
    rookGraph.maximumIndepSet_card_eq_indepNum M hM
  have hupper : M.card ≤ 3 := by
    have hgrid : ∀ I : Finset (Fin 3 × Fin 3), rookGraph.IsIndepSet (I : Set _) → I.card ≤ 3 := by
      decide
    exact hgrid M hM.isIndepSet
  let diag : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 1), (2, 2)}
  have hdiag : rookGraph.IsIndepSet (diag : Set _) := by
    decide
  have hlower : 3 ≤ rookGraph.indepNum := by
    have h := hdiag.card_le_indepNum
    simpa [diag] using h
  omega

private theorem rook_right : RightSide rookGraph 3 := by
  rw [RightSide]
  constructor
  · refine ⟨(fun c : Fin 3 => (Finset.univ.filter (fun p : Fin 3 × Fin 3 =>
        (p.1.val + p.2.val) % 3 = c.val))), ?_, ?_, ?_, ?_⟩
    · intro i
      rw [rook_alpha]
      fin_cases i <;> decide
    · intro i
      fin_cases i <;> decide
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> decide
    · intro v
      fin_cases v <;> decide
  · intro u hu
    obtain ⟨I, hcard, hind, haway⟩ := hu
    have hnot : u ∉ I := by
      intro hmem
      exact (haway u hmem).1 rfl
    let J : Finset (Fin 3 × Fin 3) := insert u I
    have hind' : rookGraph.IsIndepSet (J : Set (Fin 3 × Fin 3)) := by
      intro a ha b hb hab
      dsimp [J] at ha hb
      simp only [Finset.mem_coe, mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact (haway _ hb).2
      · exact fun h => (haway _ ha).2 h.symm
      · exact hind ha hb hab
    have hle := hind'.card_le_indepNum
    change J.card ≤ rookGraph.indepNum at hle
    dsimp [J] at hle
    rw [card_insert_of_notMem hnot, hcard] at hle
    omega

/-- The supplied 3 by 3 rook graph has maximal induced bipartite sets of
orders five and six, so it is not well-hued. -/
theorem result : ¬ claim := by
  intro h
  have hiff := h (Fin 3 × Fin 3) rookGraph 3 (by decide)
  have hleft : LeftSide rookGraph 3 := hiff.mpr rook_right
  have hw := hleft.2.1 2 (by decide)
  have hS : MaximalColorable rookGraph 2 S := by
    decide
  have hT : MaximalColorable rookGraph 2 T := by
    decide
  have heq := hw S T hS hT
  have hScard : S.card = 5 := by decide
  have hTcard : T.card = 6 := by decide
  omega

#print axioms result

end D5.S3.Combinatorics.Graph.Products.BoyerKuenzelLylePellicoConjectureTwoRefutation
