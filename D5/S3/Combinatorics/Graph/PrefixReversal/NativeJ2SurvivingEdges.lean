/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Work in progress on the actual F2 six-cut graph and literal J2 paths. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
import D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

/-- The six independent actual b cuts, rather than positions in a chosen walk. -/
def MarkedCut (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ∃ p : Fin 3 × Bool, e = markedEdge m p

/-- This is the independent full F2 inventory with exactly the six marked cuts
removed. A c edge must belong to an actual T/E seam to survive. -/
def SurvivingEdge (m : ℕ) (e : Sym2 (Configuration m)) : Prop :=
  ((F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧ ¬ MarkedCut m e

def survivingGraph (m : ℕ) : SimpleGraph (Configuration m) :=
  SimpleGraph.fromEdgeSet {e | SurvivingEdge m e}

private theorem surviving_adj_iff (m : ℕ) (x y : Configuration m) :
    (survivingGraph m).Adj x y ↔ SurvivingEdge m s(x, y) ∧ x ≠ y := by
  exact SimpleGraph.fromEdgeSet_adj

private theorem below_cycle_degree {V : Type*} [Finite V]
    {G H : SimpleGraph V} {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hsub : ∀ x y, H.Adj x y → p.toSubgraph.Adj x y) :
    ∀ x, (H.neighborSet x).ncard ≤ 2 := by
  classical
  intro x
  have hs : H.neighborSet x ⊆ p.toSubgraph.neighborSet x := fun y hy => hsub x y hy
  by_cases hx : x ∈ p.support
  · calc
      (H.neighborSet x).ncard ≤ (p.toSubgraph.neighborSet x).ncard :=
        Set.ncard_le_ncard hs
      _ = 2 := hp.ncard_neighborSet_toSubgraph_eq_two hx
  · have he : H.neighborSet x = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro y hy
      exact hx (p.fst_mem_support_of_mem_edges
        (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hsub x y hy)))
    simp only [he, Set.ncard_empty, Nat.zero_le]

private theorem below_cycle_missing_neighbor {V : Type*} [Finite V]
    {G H : SimpleGraph V} {a x y : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hsub : ∀ u v, H.Adj u v → p.toSubgraph.Adj u v)
    (hxy : p.toSubgraph.Adj x y) (hmissing : ¬ H.Adj x y) :
    (H.neighborSet x).Subsingleton := by
  classical
  apply Set.ncard_le_one_iff_subsingleton.mp
  have hx : x ∈ p.support := p.fst_mem_support_of_mem_edges
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hxy)
  have hs : H.neighborSet x ⊆ p.toSubgraph.neighborSet x \ {y} := by
    intro z hz
    refine ⟨hsub x z hz, ?_⟩
    intro he
    exact hmissing ((Set.mem_singleton_iff.mp he) ▸ hz)
  calc
    (H.neighborSet x).ncard ≤ (p.toSubgraph.neighborSet x \ {y}).ncard :=
      Set.ncard_le_ncard hs
    _ = 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem hxy,
        hp.ncard_neighborSet_toSubgraph_eq_two hx]

private theorem actual_surviving_cycle_model {m : ℕ} (hm : 5 ≤ m) :
    ∃ baseVertex : Configuration m,
      ∃ p : (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Walk
        baseVertex baseVertex,
        p.IsCycle ∧
          (∀ x y, (survivingGraph m).Adj x y → p.toSubgraph.Adj x y) ∧
          ∀ q : Fin 3 × Bool, markedEdge m q ∈ p.edges := by
  obtain ⟨base, w, hw, hinv, _, hmarked⟩ :=
    native_j2_hamiltonian_cycle_with_marked_edges hm
  let f : domainGraph (F2Domain m) →g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    ⟨Subtype.val, fun h => h⟩
  let p := w.map f
  have hedges : p.edges = w.edges.map (Sym2.map Subtype.val) := by
    exact SimpleGraph.Walk.edges_map f w
  refine ⟨base.val, p, hw.isCycle.map Subtype.val_injective, ?_, ?_⟩
  · intro x y hxy
    apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
    rw [hedges]
    exact (hinv s(x, y)).mpr ((surviving_adj_iff m x y).mp hxy).1.1
  · intro q
    rw [hedges]
    exact hmarked q

private theorem actual_surviving_degree {m : ℕ} (hm : 5 ≤ m) :
    ∀ x, ((survivingGraph m).neighborSet x).ncard ≤ 2 := by
  obtain ⟨a, p, hp, hsub, _⟩ := actual_surviving_cycle_model hm
  exact below_cycle_degree p hp hsub

private theorem actual_port_leaf {m : ℕ} (hm : 5 ≤ m)
    (q : Fin 3 × Bool × Bool) :
    ((survivingGraph m).neighborSet (port m q)).Subsingleton := by
  classical
  obtain ⟨a, p, hp, hsub, hmarked⟩ := actual_surviving_cycle_model hm
  rcases q with ⟨i, t, u⟩
  let y := port m (i, t, !u)
  have he : s(port m (i, t, u), y) = markedEdge m (i, t) := by
    cases u
    · rfl
    · exact Sym2.eq_swap
  apply below_cycle_missing_neighbor p hp hsub
  · apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
    rw [he]
    exact hmarked (i, t)
  · intro hadj
    exact ((surviving_adj_iff m _ _).mp hadj).1.2 ⟨(i, t), he⟩

/-- An internal application bridge for the future actual J2 component theorem.
The map need not be injective: a repeated graph vertex would repeat its mapped
value, and cancellation of two literal steps then contradicts the word law. -/
private theorem literal_trace_nonbacktracking
    {V H : Type*} [Group H] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (val : V → H) (letters : List H)
    (htrace : p.support.map val = List.scanl (· * ·) (val a) letters)
    (hletters : letters.IsChain (fun g h => g * h ≠ 1)) : Nonbacktracking p := by
  have hlen : p.length = letters.length := by
    have h := congrArg List.length htrace
    simp only [List.length_map, List.length_scanl, SimpleGraph.Walk.length_support] at h
    omega
  have hget (j : ℕ) (hj : j ≤ p.length) :
      val (p.getVert j) = (List.scanl (· * ·) (val a) letters)[j]'(by
        simp only [List.length_scanl]
        omega) := by
    rw [← htrace, List.getElem_map, SimpleGraph.Walk.support_getElem_eq_getVert]
  have hstep (j : ℕ) (hj : j < letters.length) :
      val (p.getVert (j + 1)) = val (p.getVert j) * letters[j] := by
    calc
      _ = (List.scanl (· * ·) (val a) letters)[j + 1]'(by
        simp only [List.length_scanl]; omega) := hget (j + 1) (by omega)
      _ = (List.scanl (· * ·) (val a) letters)[j] * letters[j] :=
        List.getElem_succ_scanl (by simp only [List.length_scanl]; omega)
      _ = _ := by rw [← hget j (by omega)]
  intro i hi he
  have hne := hletters.getElem i (by omega : i + 1 < letters.length)
  apply hne
  have hprod : val (p.getVert i) * (letters[i] * letters[i + 1]) =
      val (p.getVert i) * 1 := by
    rw [← mul_assoc, ← hstep i (by omega), ← hstep (i + 1) (by omega), ← he, mul_one]
  exact mul_left_cancel hprod

/- The next exact native obligation is, for every m ≥ 5 and i : Fin 5,

  (List.scanl (· * ·) (wordStart m i) (word m i)).IsChain (survivingGraph m).Adj.

It must be proved from the literal native-circle rows and T/E seam owners,
not supplied as a path hypothesis. The a steps use the two exact normalized
cuts in native_f2_a_cut_classification; the b steps use the complete selected
terminal/circle classification in native_f2_b_cut_classification. Each c step
must be identified in F2Seam, and every step must avoid all six MarkedCut edges.

After this law and the independent marked-edge occurrence are proved, obtain
actual walks with exactly these scanl supports. Their letter chains feed the
private bridge above, and the actual degree-two/leaf facts feed
nonbacktracking_leaf_full_component. Finally six disjoint cuts in the same
certified F2 Hamilton circle supply six paths, so the unused two ports give
the sixth path and no hidden component is left. -/

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
