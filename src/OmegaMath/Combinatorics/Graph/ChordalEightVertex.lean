import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

compile_only_with_mathlib

/-! Omega original.

# The eight-vertex, modulus-eight abelian budget obstruction

Source: wave7/oracle/oracle_q5b_grp4_two_vs_three_answer.md, Sections 3--4.
This file proves the actual finite-group obstruction, by a complete normalized
potential search with proved pruning. All closed finite certificates use `decide`;
there is no external solver assumption. The metric interpretation is separate.

Coordinates are numbered 0--10 (source f_1--f_11). The unit-ball indices are
0 = zero, 1--16 = the displayed positive triangle defects, and 17--32 = their
negatives, in the same order. Every search variable ranges over these 33 indices.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ChordalEightVertex

open SimpleGraph

abbrev V := Fin 8
abbrev H := Fin 11 → ZMod 8

/-- The five actual maximal bags, in the order 0123,0124,0135,0236,1237. -/
def bag : Fin 5 → Finset V := ![{0,1,2,3}, {0,1,2,4}, {0,1,3,5},
  {0,2,3,6}, {1,2,3,7}]

def adjacent (u v : V) : Prop := u ≠ v ∧ ∃ k : Fin 5, u ∈ bag k ∧ v ∈ bag k

instance (u v : V) : Decidable (adjacent u v) := inferInstanceAs
  (Decidable (u ≠ v ∧ ∃ k : Fin 5, u ∈ bag k ∧ v ∈ bag k))

def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨fun _ _ h => ⟨h.1.symm, by obtain ⟨k, hu, hv⟩ := h.2; exact ⟨k, hv, hu⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent _ _))

/-- Increasing cotree edges; the seven remaining edges have gain zero. -/
def chord : Fin 11 → V × V := ![(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),
  (2,6),(2,7),(3,5),(3,6),(3,7)]

def basis (i : Fin 11) : H := fun j => if j = i then 1 else 0

/-- The coordinatewise gain table, including negative reverse gains and zero diagonal. -/
def gain (u v : V) : H := fun i =>
  if (u,v) = chord i then 1 else if (v,u) = chord i then -1 else 0

/-- The sixteen increasing triangles, ordered to match the sixteen source generators. -/
def triangle : Fin 16 → V × V × V := ![(0,1,2),(0,1,3),(0,1,4),(0,1,5),
  (0,2,3),(0,2,4),(0,2,6),(0,3,5),(0,3,6),
  (1,2,3),(1,2,4),(1,2,7),(1,3,5),(1,3,7),(2,3,6),(2,3,7)]

/-- Exactly the sixteen vectors S from the source, with 0-based coordinates. -/
def generator : Fin 16 → H := ![basis 0, basis 1, basis 2, basis 3, basis 4,
  basis 5, basis 6, basis 8, basis 9,
  basis 0 - basis 1 + basis 4,
  basis 0 - basis 2 + basis 5,
  basis 0 + basis 7,
  basis 1 - basis 3 + basis 8,
  basis 1 + basis 10,
  basis 4 - basis 6 + basis 9,
  basis 4 - basis 7 + basis 10]

def ball : Fin 33 → H := ![0, generator 0, generator 1, generator 2, generator 3,
  generator 4, generator 5, generator 6, generator 7, generator 8,
  generator 9, generator 10, generator 11, generator 12, generator 13,
  generator 14, generator 15,
  -generator 0, -generator 1, -generator 2, -generator 3,
  -generator 4, -generator 5, -generator 6, -generator 7,
  -generator 8, -generator 9, -generator 10, -generator 11,
  -generator 12, -generator 13, -generator 14, -generator 15]

/-- Word budget at most one: zero or one signed triangle generator. -/
def Unit (x : H) : Prop := ∃ i : Fin 33, ball i = x
instance (x : H) : Decidable (Unit x) := inferInstanceAs (Decidable (∃ i : Fin 33, ball i = x))

theorem gain_reverse : ∀ u v : V, gain v u = -gain u v := by decide

/-- Covers all orientations, not just the sixteen increasing ones. -/
theorem all_triangle_defects_unit : ∀ a b c : V,
    graph.Adj a b → graph.Adj b c → graph.Adj a c →
      Unit (gain a b + gain b c - gain a c) := by decide

/-- The root is a clique, and the four leaves form an independent set. -/
theorem split_partition :
    (∀ a b : V, a.val < 4 → b.val < 4 → a ≠ b → graph.Adj a b) ∧
    (∀ a b : V, 4 ≤ a.val → 4 ≤ b.val → ¬ graph.Adj a b) := by decide

/-- Every clique lies in one of the five displayed bags, and all five bags are cliques. -/
theorem clique_bags :
    (∀ s : Finset V, (∀ u ∈ s, ∀ v ∈ s, u ≠ v → graph.Adj u v) →
      ∃ k : Fin 5, s ⊆ bag k) ∧
    (∀ k : Fin 5, ∀ u ∈ bag k, ∀ v ∈ bag k, u ≠ v → graph.Adj u v) := by decide

theorem bag_sizes : ∀ k : Fin 5, (bag k).card = 4 := by decide

/-- Simpliciality in reverse numerical order. -/
theorem elimination_cliques : ∀ z x y : V, x.val ≤ z.val → y.val ≤ z.val →
    graph.Adj z x → graph.Adj z y → x ≠ y → graph.Adj x y := by
  -- Numerical order is reversed below: later means smaller vertex label.
  decide

/-- The displayed graph is chordal in the repository's walk-based definition. -/
theorem graph_chordal : graph.IsChordal := by
  classical
  let key : V → ℕ := fun v => 7 - v.val
  have later : ∀ z, graph.IsClique {x | key z ≤ key x ∧ graph.Adj z x} := by
    intro z x hx y hy hne
    have hz := z.isLt
    have hxx := x.isLt
    have hyy := y.isLt
    exact elimination_cliques z x y (by dsimp [key] at hx; omega)
      (by dsimp [key] at hy; omega) hx.2 hy.2 hne
  intro v c hc hl
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image c.support.toFinset key ⟨v, by simp⟩
  have hzs : z ∈ c.support := by simpa using hz
  let d := c.rotate z hzs
  have hd : d.IsCycle := hc.rotate hzs
  have hn : 4 ≤ d.length := by simpa [d] using hl
  have support (x : V) (hx : x ∈ d.support) : x ∈ c.support := by
    rw [← Walk.cons_tail_support] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hzs
    · exact List.mem_of_mem_tail ((c.support_rotate z hzs).mem_iff.mp hx)
  have hs := support d.snd (d.getVert_mem_support 1)
  have hp := support d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hs, hp, later z
    ⟨hmin _ (by simpa using hs), d.adj_snd hd.not_nil⟩
    ⟨hmin _ (by simpa using hp), (d.adj_penultimate hd.not_nil).symm⟩
    hd.snd_ne_penultimate, ?_⟩
  intro edge
  have mem := Walk.adj_toSubgraph_iff_mem_edges.mpr
    ((c.rotate_edges z hzs).mem_iff.mpr edge)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at mem
  rw [hd.neighborSet_toSubgraph_internal (by omega) (by omega)] at mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.sub_self] at mem
  rcases mem with hm | hm <;>
    have eq := hd.getVert_injOn' (by simp : d.length - 1 ∈ {n | n ≤ d.length - 1})
      (by simp <;> omega) hm <;> omega

theorem clique_card_le_four (s : Finset V) (hs : graph.IsClique (s : Set V)) :
    s.card ≤ 4 := by
  obtain ⟨k, hk⟩ := clique_bags.1 s (fun u hu v hv hne => hs hu hv hne)
  exact (Finset.card_le_card hk).trans_eq (bag_sizes k)

theorem ball_neg : ∀ i : Fin 33, Unit (-ball i) := by decide

theorem zero_star_adj : ∀ v : V, v.val ≤ 6 → v ≠ 0 → graph.Adj 0 v := by decide

theorem zero_star_gain : ∀ v : V, v.val ≤ 6 → gain 0 v = 0 := by decide

theorem unit_neg {x : H} (hx : Unit x) : Unit (-x) := by
  obtain ⟨i, rfl⟩ := hx
  exact ball_neg i

/-- A finite audit of the padded ball against the signed source generators. -/
theorem ball_signed : ∀ i : Fin 33, ball i = 0 ∨
    ∃ t : Fin 16, ball i = generator t ∨ ball i = -generator t := by decide

/-- Every standard basis vector is a sum of two padded signed generators. -/
theorem basis_two_units : ∀ i : Fin 11, ∃ a b : Fin 33,
    basis i = ball a + ball b := by decide

theorem basis_expansion (x : H) : ∑ i : Fin 11, (x i).val • basis i = x := by
  funext j
  simp only [Finset.sum_apply]
  change (∑ i : Fin 11, (x i).val • (if j = i then (1 : ZMod 8) else 0)) = x j
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, nsmul_eq_mul, mul_one]
  exact ZMod.natCast_zmod_val (x j)

/-- The sixteen displayed defects generate the whole group, not a proper subgroup. -/
theorem generators_generate : AddSubgroup.closure (Set.range generator) = ⊤ := by
  let K := AddSubgroup.closure (Set.range generator)
  have ball_mem (i : Fin 33) : ball i ∈ K := by
    rcases ball_signed i with hz | ⟨t, ht | ht⟩
    · rw [hz]
      exact K.zero_mem
    · rw [ht]
      exact AddSubgroup.subset_closure ⟨t, rfl⟩
    · rw [ht]
      exact K.neg_mem (AddSubgroup.subset_closure ⟨t, rfl⟩)
  have basis_mem (i : Fin 11) : basis i ∈ K := by
    obtain ⟨a,b,he⟩ := basis_two_units i
    rw [he]
    exact K.add_mem (ball_mem a) (ball_mem b)
  apply top_unique
  intro x _
  rw [← basis_expansion x]
  exact K.sum_mem (fun i _ => K.nsmul_mem (basis_mem i) _)

/-- Compatibility across a chord of gain f_(k+1). -/
def EdgeUnit (k : Fin 11) (a b : Fin 33) : Prop := Unit (ball a + basis k - ball b)
instance (k : Fin 11) (a b : Fin 33) : Decidable (EdgeUnit k a b) :=
  inferInstanceAs (Decidable (Unit (ball a + basis k - ball b)))

/-- A leaf adjacent to zero and two chosen root potentials can be filled. -/
def Leaf (i j : Fin 11) (a b : H) : Prop :=
  ∃ d : Fin 33, Unit (a + basis i - ball d) ∧ Unit (b + basis j - ball d)
instance (i j : Fin 11) (a b : H) : Decidable (Leaf i j a b) :=
  inferInstanceAs (Decidable (∃ d : Fin 33, Unit (a + basis i - ball d) ∧ Unit (b + basis j - ball d)))

/-- All root (1,2) choices satisfying edge 12; checked complete below. -/
def rootPairs : List (Fin 33 × Fin 33) := [
    (0, 0), (0, 1), (1, 1), (2, 1), (2, 2), (3, 1),
    (3, 3), (4, 1), (4, 4), (5, 1), (5, 2), (5, 5),
    (5, 10), (6, 1), (6, 3), (6, 6), (6, 11), (7, 1),
    (7, 7), (8, 1), (8, 8), (9, 1), (9, 9), (10, 1),
    (10, 10), (11, 1), (11, 11), (12, 1), (12, 12), (13, 1),
    (13, 13), (14, 1), (14, 14), (15, 1), (15, 15), (16, 1),
    (16, 16), (17, 0), (17, 1), (17, 2), (17, 3), (17, 4),
    (17, 5), (17, 6), (17, 7), (17, 8), (17, 9), (17, 10),
    (17, 11), (17, 12), (17, 13), (17, 14), (17, 15), (17, 16),
    (17, 17), (17, 18), (17, 19), (17, 20), (17, 21), (17, 22),
    (17, 23), (17, 24), (17, 25), (17, 26), (17, 27), (17, 28),
    (17, 29), (17, 30), (17, 31), (17, 32), (18, 1), (18, 10),
    (18, 18), (18, 21), (19, 1), (19, 11), (19, 19), (19, 22),
    (20, 1), (20, 20), (21, 1), (21, 21), (22, 1), (22, 22),
    (23, 1), (23, 23), (24, 1), (24, 24), (25, 1), (25, 25),
    (26, 1), (26, 2), (26, 21), (26, 26), (27, 1), (27, 3),
    (27, 22), (27, 27), (28, 1), (28, 28), (29, 1), (29, 29),
    (30, 1), (30, 30), (31, 1), (31, 31), (32, 1), (32, 32)]

/-- All root (1,2,3) choices satisfying edges 12,13,23; checked complete below. -/
def rootTriples : List (Fin 33 × Fin 33 × Fin 33) := [
    (0, 0, 0), (0, 1, 2), (1, 1, 1), (1, 1, 2), (2, 1, 2), (2, 2, 2),
    (3, 1, 2), (3, 3, 3), (4, 1, 2), (4, 4, 4), (5, 1, 2), (5, 1, 5),
    (5, 2, 2), (5, 2, 5), (5, 5, 5), (5, 10, 5), (6, 1, 2), (6, 6, 6),
    (7, 1, 2), (7, 7, 7), (8, 1, 2), (8, 8, 8), (9, 1, 2), (9, 9, 9),
    (10, 1, 1), (10, 1, 2), (10, 1, 5), (10, 1, 10), (10, 10, 5), (10, 10, 10),
    (11, 1, 2), (11, 11, 11), (12, 1, 2), (12, 12, 12), (13, 1, 2), (13, 13, 13),
    (14, 1, 2), (14, 14, 14), (15, 1, 2), (15, 15, 15), (16, 1, 2), (16, 16, 16),
    (17, 0, 5), (17, 1, 2), (17, 1, 5), (17, 2, 2), (17, 2, 5), (17, 3, 5),
    (17, 4, 5), (17, 5, 5), (17, 6, 5), (17, 7, 5), (17, 8, 5), (17, 9, 5),
    (17, 10, 5), (17, 11, 5), (17, 12, 5), (17, 13, 5), (17, 14, 5), (17, 15, 5),
    (17, 16, 5), (17, 17, 5), (17, 17, 17), (17, 18, 5), (17, 18, 17), (17, 19, 5),
    (17, 20, 5), (17, 21, 2), (17, 21, 5), (17, 21, 17), (17, 21, 26), (17, 22, 5),
    (17, 23, 5), (17, 24, 5), (17, 25, 5), (17, 26, 2), (17, 26, 5), (17, 26, 17),
    (17, 26, 26), (17, 27, 5), (17, 28, 5), (17, 29, 5), (17, 30, 5), (17, 31, 5),
    (17, 32, 5), (18, 1, 1), (18, 1, 2), (18, 1, 5), (18, 1, 10), (18, 10, 5),
    (18, 10, 10), (18, 18, 5), (18, 18, 10), (18, 18, 17), (18, 18, 18), (18, 21, 0),
    (18, 21, 1), (18, 21, 2), (18, 21, 3), (18, 21, 4), (18, 21, 5), (18, 21, 6),
    (18, 21, 7), (18, 21, 8), (18, 21, 9), (18, 21, 10), (18, 21, 11), (18, 21, 12),
    (18, 21, 13), (18, 21, 14), (18, 21, 15), (18, 21, 16), (18, 21, 17), (18, 21, 18),
    (18, 21, 19), (18, 21, 20), (18, 21, 21), (18, 21, 22), (18, 21, 23), (18, 21, 24),
    (18, 21, 25), (18, 21, 26), (18, 21, 27), (18, 21, 28), (18, 21, 29), (18, 21, 30),
    (18, 21, 31), (18, 21, 32), (19, 1, 2), (19, 19, 19), (20, 1, 2), (20, 20, 20),
    (21, 1, 1), (21, 1, 2), (21, 21, 1), (21, 21, 2), (21, 21, 21), (21, 21, 26),
    (22, 1, 2), (22, 22, 22), (23, 1, 2), (23, 23, 23), (24, 1, 2), (24, 24, 24),
    (25, 1, 2), (25, 25, 25), (26, 1, 2), (26, 2, 2), (26, 21, 2), (26, 21, 26),
    (26, 26, 2), (26, 26, 26), (27, 1, 2), (27, 27, 27), (28, 1, 2), (28, 28, 28),
    (29, 1, 2), (29, 29, 29), (30, 1, 2), (30, 30, 30), (31, 1, 2), (31, 31, 31),
    (32, 1, 2), (32, 32, 32)]

/-- 33^2 cases, with the antecedent computing exact membership in the 33-element ball. -/
theorem pair_cover : ∀ a b : Fin 33, EdgeUnit 0 a b → (a,b) ∈ rootPairs := by decide

/-- For each of the 108 stored pairs, all 33 choices of vertex 3 are checked. -/
private theorem triple_cover_part_0 :
    (rootPairs.drop 0 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_1 :
    (rootPairs.drop 10 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_2 :
    (rootPairs.drop 20 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_3 :
    (rootPairs.drop 30 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_4 :
    (rootPairs.drop 40 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_5 :
    (rootPairs.drop 50 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_6 :
    (rootPairs.drop 60 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_7 :
    (rootPairs.drop 70 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_8 :
    (rootPairs.drop 80 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_9 :
    (rootPairs.drop 90 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

private theorem triple_cover_part_10 :
    (rootPairs.drop 100 |>.take 10).all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by decide

theorem triple_cover : rootPairs.all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples)) = true := by
  have blocks : rootPairs =
      (rootPairs.drop 0 |>.take 10) ++ (rootPairs.drop 10 |>.take 10) ++ (rootPairs.drop 20 |>.take 10) ++
      (rootPairs.drop 30 |>.take 10) ++ (rootPairs.drop 40 |>.take 10) ++ (rootPairs.drop 50 |>.take 10) ++
      (rootPairs.drop 60 |>.take 10) ++ (rootPairs.drop 70 |>.take 10) ++ (rootPairs.drop 80 |>.take 10) ++
      (rootPairs.drop 90 |>.take 10) ++ (rootPairs.drop 100 |>.take 10) := rfl
  refine (congrArg (fun xs => xs.all (fun ab => decide (∀ c : Fin 33,
    EdgeUnit 1 ab.1 c → EdgeUnit 4 ab.2 c → (ab.1,ab.2,c) ∈ rootTriples))) blocks).trans ?_
  simp only [List.all_append,
    triple_cover_part_0, triple_cover_part_1, triple_cover_part_2, triple_cover_part_3, triple_cover_part_4, triple_cover_part_5,
    triple_cover_part_6, triple_cover_part_7, triple_cover_part_8, triple_cover_part_9, triple_cover_part_10, Bool.and_self]


/-- Exact leaf pruning: vertex 4, then 5, then 6, then 7. Each existential
checks all 33 possible leaf potentials. Vertex 7 is gauged relative to vertex 1. -/
private theorem no_root_extension_part_0 :
    (rootTriples.drop 0 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_1 :
    (rootTriples.drop 10 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_2 :
    (rootTriples.drop 20 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_3 :
    (rootTriples.drop 30 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_4 :
    (rootTriples.drop 40 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_5 :
    (rootTriples.drop 50 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_6 :
    (rootTriples.drop 60 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_7 :
    (rootTriples.drop 70 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_8 :
    (rootTriples.drop 80 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_9 :
    (rootTriples.drop 90 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_10 :
    (rootTriples.drop 100 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_11 :
    (rootTriples.drop 110 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_12 :
    (rootTriples.drop 120 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_13 :
    (rootTriples.drop 130 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_14 :
    (rootTriples.drop 140 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_15 :
    (rootTriples.drop 150 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

private theorem no_root_extension_part_16 :
    (rootTriples.drop 160 |>.take 10).all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by decide

theorem no_root_extension : rootTriples.all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1)))) = true := by
  have blocks : rootTriples =
      (rootTriples.drop 0 |>.take 10) ++ (rootTriples.drop 10 |>.take 10) ++ (rootTriples.drop 20 |>.take 10) ++
      (rootTriples.drop 30 |>.take 10) ++ (rootTriples.drop 40 |>.take 10) ++ (rootTriples.drop 50 |>.take 10) ++
      (rootTriples.drop 60 |>.take 10) ++ (rootTriples.drop 70 |>.take 10) ++ (rootTriples.drop 80 |>.take 10) ++
      (rootTriples.drop 90 |>.take 10) ++ (rootTriples.drop 100 |>.take 10) ++ (rootTriples.drop 110 |>.take 10) ++
      (rootTriples.drop 120 |>.take 10) ++ (rootTriples.drop 130 |>.take 10) ++ (rootTriples.drop 140 |>.take 10) ++
      (rootTriples.drop 150 |>.take 10) ++ (rootTriples.drop 160 |>.take 10) := rfl
  refine (congrArg (fun xs => xs.all (fun t => decide (¬
    (Leaf 2 5 (ball t.1) (ball t.2.1) ∧
     Leaf 3 8 (ball t.1) (ball t.2.2) ∧
     Leaf 6 9 (ball t.2.1) (ball t.2.2) ∧
     Leaf 7 10 (ball t.2.1 - ball t.1) (ball t.2.2 - ball t.1))))) blocks).trans ?_
  simp only [List.all_append,
    no_root_extension_part_0, no_root_extension_part_1, no_root_extension_part_2, no_root_extension_part_3, no_root_extension_part_4, no_root_extension_part_5,
    no_root_extension_part_6, no_root_extension_part_7, no_root_extension_part_8, no_root_extension_part_9, no_root_extension_part_10, no_root_extension_part_11, no_root_extension_part_12, no_root_extension_part_13, no_root_extension_part_14, no_root_extension_part_15, no_root_extension_part_16, Bool.and_self]


/-- No potential has all residuals in {0} ∪ S ∪ -S, for this actual gain table. -/
theorem no_unit_potential (p : V → H) :
    ¬ (∀ u v, graph.Adj u v → Unit (p u + gain u v - p v)) := by
  intro hp
  let q : V → H := fun v => p v - p 0
  have hq (u v : V) (huv : graph.Adj u v) : Unit (q u + gain u v - q v) := by
    have he : q u + gain u v - q v = p u + gain u v - p v := by dsimp [q]; abel
    rw [he]
    exact hp u v huv
  have qmem (v : V) (h : v.val ≤ 6) : Unit (q v) := by
    by_cases hv : v = 0
    · subst v
      exact ⟨0, by simp [q, ball]⟩
    · have hadj : graph.Adj 0 v := zero_star_adj v h hv
      have hz : gain 0 v = 0 := zero_star_gain v h
      have hh := unit_neg (hq 0 v hadj)
      simpa [q, hz] using hh
  obtain ⟨a, ha⟩ := qmem 1 (by decide)
  obtain ⟨b, hb⟩ := qmem 2 (by decide)
  obtain ⟨c, hc⟩ := qmem 3 (by decide)
  have he (u v : V) (k : Fin 11) (hadj : graph.Adj u v) (hg : gain u v = basis k) :
      Unit (q u + basis k - q v) := by simpa [hg] using hq u v hadj
  have hab : EdgeUnit 0 a b := by
    simpa only [EdgeUnit, ha, hb] using he 1 2 0 (by decide) (by decide)
  have hac : EdgeUnit 1 a c := by
    simpa only [EdgeUnit, ha, hc] using he 1 3 1 (by decide) (by decide)
  have hbc : EdgeUnit 4 b c := by
    simpa only [EdgeUnit, hb, hc] using he 2 3 4 (by decide) (by decide)
  have hpairs := pair_cover a b hab
  have ht : (a,b,c) ∈ rootTriples :=
    (of_decide_eq_true (List.all_eq_true.mp triple_cover (a,b) hpairs)) c hac hbc
  have h4 : Leaf 2 5 (ball a) (ball b) := by
    obtain ⟨d, hd⟩ := qmem 4 (by decide)
    refine ⟨d, ?_, ?_⟩
    · simpa only [ha, hd] using he 1 4 2 (by decide) (by decide)
    · simpa only [hb, hd] using he 2 4 5 (by decide) (by decide)
  have h5 : Leaf 3 8 (ball a) (ball c) := by
    obtain ⟨d, hd⟩ := qmem 5 (by decide)
    refine ⟨d, ?_, ?_⟩
    · simpa only [ha, hd] using he 1 5 3 (by decide) (by decide)
    · simpa only [hc, hd] using he 3 5 8 (by decide) (by decide)
  have h6 : Leaf 6 9 (ball b) (ball c) := by
    obtain ⟨d, hd⟩ := qmem 6 (by decide)
    refine ⟨d, ?_, ?_⟩
    · simpa only [hb, hd] using he 2 6 6 (by decide) (by decide)
    · simpa only [hc, hd] using he 3 6 9 (by decide) (by decide)
  have h7 : Leaf 7 10 (ball b - ball a) (ball c - ball a) := by
    have h17 := hq 1 7 (by decide)
    have hu : Unit (q 7 - q 1) := by
      have hh := unit_neg h17
      simpa only [show gain 1 7 = 0 by decide, add_zero, neg_sub] using hh
    obtain ⟨d, hd⟩ := hu
    refine ⟨d, ?_, ?_⟩
    · rw [hb, ha, hd]
      have hh := he 2 7 7 (by decide) (by decide)
      convert hh using 1; abel
    · rw [hc, ha, hd]
      have hh := he 3 7 10 (by decide) (by decide)
      convert hh using 1; abel
  exact (of_decide_eq_true (List.all_eq_true.mp no_root_extension (a,b,c) ht)) ⟨h4,h5,h6,h7⟩

/-- The obstruction in the gain-minus-potential-difference convention. -/
theorem exists_nonunit_residual (p : V → H) :
    ∃ u v, graph.Adj u v ∧ ¬ Unit (gain u v - (p v - p u)) := by
  classical
  by_contra h
  push Not at h
  apply no_unit_potential p
  intro u v huv
  have he : p u + gain u v - p v = gain u v - (p v - p u) := by abel
  rw [he]
  exact h u v huv


end ChordalEightVertex
