/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual six-cut inventories, cycle degree bounds and literal nonbacktracking. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
import D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open Equiv Fin.NatCast
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
  exact SimpleGraph.fromEdgeSet_adj {e | SurvivingEdge m e}

private theorem markedCut_injective {m : ℕ} (hm : 5 ≤ m) :
    Function.Injective (markedEdge m) := by
  intro p q hpq
  by_contra hne
  have hp : port m (p.1, p.2, false) ∈ markedEdge m p := Sym2.mem_mk_left _ _
  have hq : port m (p.1, p.2, false) ∈ markedEdge m q := hpq ▸ hp
  exact Set.disjoint_left.mp (native_j2_marked_disjoint hm p q hne) hp hq

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
      apply Set.ext
      intro y
      constructor
      · intro hy
        exact (hx (p.fst_mem_support_of_mem_edges
          (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hsub x y hy)))).elim
      · intro hy
        exact hy.elim
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
      have hy : y ∈ p.toSubgraph.neighborSet x := hxy
      rw [Set.ncard_sdiff_singleton_of_mem hy,
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
    have h := List.getElem_of_eq htrace (i := j) (by
      simp only [List.length_map, SimpleGraph.Walk.length_support]
      omega)
    simpa only [List.getElem_map, SimpleGraph.Walk.support_getElem_eq_getVert] using h
  have hstep (j : ℕ) (hj : j < letters.length) :
      val (p.getVert (j + 1)) = val (p.getVert j) * letters[j] := by
    calc
      _ = (List.scanl (· * ·) (val a) letters)[j + 1]'(by
        simp only [List.length_scanl]; omega) := hget (j + 1) (by omega)
      _ = (List.scanl (· * ·) (val a) letters)[j]'(by
        simp only [List.length_scanl]; omega) * letters[j] :=
        List.getElem_succ_scanl (by simp only [List.length_scanl]; omega)
      _ = _ := by rw [← hget j (by omega)]
  intro i hi he
  have hne := hletters.getElem i (by omega : i + 1 < letters.length)
  apply hne
  have hprod : val (p.getVert i) * (letters[i] * letters[i + 1]) =
      val (p.getVert i) * 1 := by
    rw [← mul_assoc, ← hstep i (by omega), ← hstep (i + 1) (by omega), ← he, mul_one]
  exact mul_left_cancel hprod

private def LetterShape {H : Type*} [Group H] (l : List H) (x y : H) : Prop :=
  l.IsChain (fun g h => g * h ≠ 1) ∧ l.head? = some x ∧ l.getLast? = some y

private theorem letterShape_append {H : Type*} [Group H] {l r : List H}
    {a b c d : H} (hl : LetterShape l a b) (hr : LetterShape r c d)
    (hbc : b * c ≠ 1) : LetterShape (l ++ r) a d := by
  rcases hl with ⟨hl, hheadl, hlastl⟩
  rcases hr with ⟨hr, hheadr, hlastr⟩
  refine ⟨hl.append hr ?_, ?_, ?_⟩
  · intro x hx y hy
    simp only [hlastl, Option.mem_some_iff] at hx
    simp only [hheadr, Option.mem_some_iff] at hy
    subst x
    subst y
    exact hbc
  · simp only [List.head?_append, hheadl, Option.some_or]
  · simp only [List.getLast?_append, hlastr, Option.some_or]

private theorem letterShape_replicate {H : Type*} [Group H] {l : List H}
    {a b : H} (hl : LetterShape l a b) (hba : b * a ≠ 1) (k : ℕ) :
    LetterShape (List.replicate (k + 1) l).flatten a b := by
  induction k with
  | zero => simpa only [Nat.zero_add, List.replicate_one, List.flatten_cons, List.flatten_nil,
      List.append_nil] using hl
  | succ k ih =>
    simpa only [List.replicate_succ, List.flatten_cons] using
      letterShape_append hl ih hba

private theorem involution_product_ne_one {H : Type*} [Group H] {x y : H}
    (hx : x * x = 1) (hne : x ≠ y) : x * y ≠ 1 := by
  intro h
  have he := congrArg (x * ·) h
  rw [← mul_assoc, hx, one_mul, mul_one] at he
  exact hne he.symm

private theorem literal_j2_letters {m : ℕ} (hm : 5 ≤ m) (i : Fin 5) :
    (word m i).IsChain (fun g h => g * h ≠ 1) := by
  have hab : a m ≠ b m := by
    intro h
    have he := congrArg (fun f : Configuration m => (f (Fin.last m)).val) h
    simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, b_last] at he
    omega
  have hac : a m ≠ c m := by
    intro h
    have he := congrArg (fun f : Configuration m => (f (Fin.last m)).val) h
    simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, c_apply,
      if_neg (by omega : ¬ m < m - 1)] at he
    omega
  have hbc : b m ≠ c m := by
    intro h
    let j : Fin (m + 1) := ⟨m - 1, by omega⟩
    have he := congrArg (fun f : Configuration m => (f j).val) h
    simp only [b_apply, c_apply, j, Fin.val_mk,
      if_pos (by omega : m - 1 < m), lt_self_iff_false, if_false] at he
    omega
  have hbsq : b m * b m = 1 := by
    apply Equiv.ext
    intro j
    exact PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
      (L := m) (by omega) j
  have ab := involution_product_ne_one (a_sq m) hab
  have ba := involution_product_ne_one hbsq hab.symm
  have ac := involution_product_ne_one (a_sq m) hac
  have ca := involution_product_ne_one (c_sq m) hac.symm
  have bc := involution_product_ne_one hbsq hbc
  have sa : LetterShape [a m] (a m) (a m) := by simp [LetterShape]
  have sc : LetterShape [c m] (c m) (c m) := by simp [LetterShape]
  have sab : LetterShape [a m, b m] (a m) (b m) := by
    simp [LetterShape, ab]
  have saba : LetterShape [a m, b m, a m] (a m) (a m) := by
    simp [LetterShape, ab, ba]
  have hu : ∀ k, LetterShape (uWord m k) (a m) (a m) := by
    intro k
    induction k with
    | zero => exact sa
    | succ k ih =>
      exact letterShape_append sab ih ba
  have sch := letterShape_append sc (hu m) ca
  have hrep : LetterShape
      (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten (c m) (a m) := by
    simpa only [show m - 4 + 1 = m - 3 by omega] using
      letterShape_replicate sch ac (m - 4)
  have habrep : LetterShape (List.replicate (m - 1) [a m, b m]).flatten
      (a m) (b m) := by
    simpa only [show m - 2 + 1 = m - 1 by omega] using
      letterShape_replicate sab ba (m - 2)
  have sabc := letterShape_append sab sc bc
  have sca := letterShape_append sc sa ca
  have scaba := letterShape_append sc saba ca
  have sac := letterShape_append sa sc ac
  fin_cases i
  · simpa only [word, Fin.val_mk, List.append_assoc, List.cons_append, List.nil_append] using
      (letterShape_append
        (letterShape_append (letterShape_append sabc (hu (m - 2)) ca) sc ac)
        (hu (m - 1)) ca).1
  · simpa only [word, Fin.val_mk, List.append_assoc, List.cons_append, List.nil_append] using
      (letterShape_append (letterShape_append habrep hrep bc) sca ac).1
  · simpa only [word, Fin.val_mk, List.append_assoc, List.cons_append, List.nil_append] using
      (letterShape_append (letterShape_append sa hrep ac) scaba ac).1
  · simpa only [word, Fin.val_mk, List.cons_append, List.nil_append] using
      (letterShape_append sac (hu (m - 2)) ca).1
  · simpa only [word, Fin.val_mk, List.cons_append, List.nil_append] using
      (letterShape_append sabc (hu (m - 1)) ca).1



end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
