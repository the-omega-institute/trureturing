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
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
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
    have h := List.getElem_of_eq htrace (i := j) (by
      simp only [List.length_map, SimpleGraph.Walk.length_support]
      omega)
    simpa only [List.getElem_map, SimpleGraph.Walk.support_getElem_eq_getVert] using h
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
  | zero => simpa only [List.replicate_one, List.flatten_cons, List.flatten_nil,
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
  · simpa only [word, Fin.val_mk, List.append_assoc] using
      (letterShape_append
        (letterShape_append (letterShape_append sabc (hu (m - 2)) ca) sc ac)
        (hu (m - 1)) ca).1
  · simpa only [word, Fin.val_mk, List.append_assoc] using
      (letterShape_append (letterShape_append habrep hrep bc) sca ac).1
  · simpa only [word, Fin.val_mk, List.append_assoc] using
      (letterShape_append (letterShape_append sa hrep ac) scaba ac).1
  · simpa only [word, Fin.val_mk] using (letterShape_append sac (hu (m - 2)) ca).1
  · simpa only [word, Fin.val_mk] using (letterShape_append sabc (hu (m - 1)) ca).1

private def j2Contact {m : Nat} (hm : 5 ≤ m) : Fin (m - 2) :=
  ⟨m - 3, by omega⟩

private theorem j2_swap_val {m : Nat} (x y i : Fin (m + 1)) :
    ((Equiv.swap x y) i).val =
      if i.val = x.val then y.val else if i.val = y.val then x.val else i.val := by
  classical
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

private theorem j2_rotate_val (m k : Nat) (i : Fin (m + 1)) :
    ((finRotate (m + 1) ^ k) i).val = (i.val + k) % (m + 1) := by
  simp only [rotate_pow_eq_cycle, finCycle_apply, Fin.val_add, Fin.val_natCast]
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem j2_mod_two_cases {x n : Nat} (_hn : 0 < n) (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp only [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ x),
      Nat.mod_eq_of_lt (by omega : x - n < n)]

/-- Only fixed-size offsets are split; m is arbitrary, not bounded. -/
macro "solve_j2_seam_coordinate" m:term : tactic => `(tactic| {
  simp only [wordStart, wordFinish, rightPort, leftPort, bar,
    NativeCoreSplicing.cutStart, cutGenerator, tCircleAnchor, lowerPort, gapAnchor, j2Contact,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, uWord_product, ab_eq_rotate]
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hi := i.isLt
  have hposition : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = $m - 3 ∨ i.val = $m - 2 ∨ i.val = $m - 1 ∨ i.val = $m ∨
      (4 ≤ i.val ∧ i.val < $m - 3) := by omega
  rcases hposition with h | h | h | h | h | h | h | h | h
  all_goals
    simp (disch := omega) only [h, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      pow_one, a_apply, Fin.val_rev,
      b_apply, c_apply, j2_rotate_val, native_bc_pow_val (by omega : 2 ≤ $m),
      j2_swap_val, contactAnchor_val, Fin.val_mk, Fin.val_last, Fin.val_zero,
      j2_mod_two_cases, if_pos, if_neg, ite_true, ite_false]
    <;> omega
})

private theorem j2_h_product (m : Nat) : (uWord m m).prod = b m := by
  rw [uWord_product, rotate_pow_eq_cycle, b_eq_cycle_a]
  congr 1
  have hr : (m : Fin (m + 1)) = Fin.last m := by apply Fin.ext; simp
  rw [hr, ← Fin.neg_last m, neg_neg]

private theorem j2_cb_pow_succ (m t : Nat) :
    (c m * b m) ^ (t + 1) = c m * (b m * c m) ^ t * b m := by
  induction t with
  | zero => simp only [pow_one, pow_zero, mul_one]
  | succ t ih =>
    calc
      _ = (c m * b m) ^ (t + 1) * (c m * b m) := pow_succ _ _
      _ = (c m * (b m * c m) ^ t * b m) * (c m * b m) := by rw [ih]
      _ = c m * ((b m * c m) ^ t * (b m * c m)) * b m := by
        simp only [mul_assoc]
      _ = c m * (b m * c m) ^ (t + 1) * b m := by rw [pow_succ]

private theorem j2_b_cb_pow (m t : Nat) :
    b m * (c m * b m) ^ t = (b m * c m) ^ t * b m := by
  induction t with
  | zero => simp only [pow_zero, mul_one, one_mul]
  | succ t ih =>
    calc
      _ = (b m * (c m * b m) ^ t) * (c m * b m) := by
        rw [pow_succ, mul_assoc]
      _ = ((b m * c m) ^ t * b m) * (c m * b m) := by rw [ih]
      _ = (b m * c m) ^ (t + 1) * b m := by
        rw [pow_succ]
        simp only [mul_assoc]

private theorem j2_bc_order {m : Nat} (hm : 5 ≤ m) :
    (b m * c m) ^ m = 1 := by
  simpa only [eWord, List.prod_flatten, List.map_replicate, List.prod_replicate,
    List.prod_cons, List.prod_nil, mul_one] using
    (native_e_simple_trace (by omega : 3 ≤ m) (1 : Configuration m)).1

/-- Actual c starting vertices before any repeated blocks. These six exact
identities are the seeds for all five word traces. -/
private theorem j2_word0_first_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 0 * a m * b m = 1 := by
  solve_j2_seam_coordinate m

private theorem j2_word0_second_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 0 * a m * b m * c m * (uWord m (m - 2)).prod =
      contactAnchor (j2Contact hm) := by
  solve_j2_seam_coordinate m

private theorem j2_word1_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 * (a m * b m) ^ (m - 1) = a m := by
  solve_j2_seam_coordinate m

private theorem j2_word2_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 * a m = contactAnchor (j2Contact hm) * b m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 * a m =
      contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1) := by
  solve_j2_seam_coordinate m

private theorem j2_word4_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 4 * a m * b m =
      Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
  solve_j2_seam_coordinate m

private theorem j2_reverse_t_seam {m : Nat}
    (p : Fin m ⊕ Fin (m - 2)) (x : Configuration m)
    (hx : x = NativeCoreSplicing.cutStart p * cutGenerator p * c m) :
    F2Seam m s(x, x * c m) := by
  left
  refine ⟨p, ?_⟩
  rw [hx]
  simp only [mul_assoc, c_sq, mul_one]
  exact Sym2.eq_swap

private theorem j2_reverse_e_seam {m : Nat} (j : Fin (m - 2)) (i : Fin m)
    (x : Configuration m)
    (hx : x = gapAnchor (contactAnchor j) i * b m * c m) :
    F2Seam m s(x, x * c m) := by
  right
  refine ⟨j, i, ?_⟩
  rw [hx]
  simp only [mul_assoc, c_sq, mul_one]
  exact Sym2.eq_swap

private theorem j2_lower_t_seam {m : Nat} (hm : 5 ≤ m) (j : Fin (m - 2)) :
    F2Seam m s(lowerPort j * b m, lowerPort j * b m * c m) := by
  have hj := j.isLt
  left
  refine ⟨Sum.inl ⟨j.val, by omega⟩, ?_⟩
  simp [NativeCoreSplicing.cutStart, cutGenerator, tCircleAnchor, gapAnchor, lowerPort,
    show j.val ≠ m - 1 by omega, show ¬ m - 2 ≤ j.val by omega]

private theorem j2_first_t_seam {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(a m, a m * c m) := by
  left
  refine ⟨Sum.inl ⟨m - 1, by omega⟩, ?_⟩
  simp [NativeCoreSplicing.cutStart, cutGenerator, show m - 2 ≤ m - 1 by omega]

/-- Word 1 has m-2 c steps. The initial one is the first core seam;
the remaining steps traverse the lower T chain in its actual direction. -/
private theorem j2_word1_repeated_c {m : Nat} (hm : 5 ≤ m) (t : Fin (m - 2)) :
    F2Seam m s(a m * (c m * b m) ^ t.val,
      a m * (c m * b m) ^ t.val * c m) := by
  by_cases ht : t.val = 0
  · simpa only [ht, pow_zero, mul_one] using j2_first_t_seam hm
  · let j : Fin (m - 2) := ⟨t.val - 1, by have ht' := t.isLt; omega⟩
    have he : a m * (c m * b m) ^ t.val = lowerPort j * b m := by
      rw [show t.val = (t.val - 1) + 1 by omega, j2_cb_pow_succ]
      simp only [lowerPort, j, mul_assoc]
    rw [he]
    exact j2_lower_t_seam hm j

/-- Word 2 has m-2 c steps, all from one complete actual contact supplier.
The gap index is exactly the ordinal of the c step, including the final c. -/
private theorem j2_word2_repeated_c {m : Nat} (hm : 5 ≤ m) (t : Fin (m - 2)) :
    F2Seam m
      s(contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val,
        contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val * c m) := by
  let i : Fin m := ⟨t.val, by have ht := t.isLt; omega⟩
  have he : contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val =
      gapAnchor (contactAnchor (j2Contact hm)) i * b m := by
    rw [mul_assoc, j2_b_cb_pow]
    simp only [gapAnchor, i, mul_assoc]
  rw [he]
  exact Or.inr ⟨j2Contact hm, i, rfl⟩

private theorem j2_word0_first_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s((1 : Configuration m), c m) := by
  let p : Fin m ⊕ Fin (m - 2) := Sum.inr (j2Contact hm)
  have he : NativeCoreSplicing.cutStart p * cutGenerator p * c m = 1 := by
    dsimp only [p]
    solve_j2_seam_coordinate m
  simpa only [one_mul] using j2_reverse_t_seam p 1 he.symm

private theorem j2_word0_second_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(contactAnchor (j2Contact hm), contactAnchor (j2Contact hm) * c m) := by
  let i : Fin m := ⟨m - 1, by omega⟩
  apply j2_reverse_e_seam (j2Contact hm) i _
  simp only [gapAnchor, i, mul_assoc, ← pow_succ,
    show m - 1 + 1 = m by omega, j2_bc_order hm, mul_one]

private theorem j2_word3_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1),
      contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1) * c m) := by
  let i : Fin m := ⟨m - 2, by omega⟩
  apply j2_reverse_e_seam (j2Contact hm) i _
  simp only [gapAnchor, i, mul_assoc, ← pow_succ,
    show m - 2 + 1 = m - 1 by omega]

private theorem j2_word4_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m
      s(Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
        Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * c m) := by
  let p : Fin m ⊕ Fin (m - 2) := Sum.inl ⟨m - 3, by omega⟩
  have he : NativeCoreSplicing.cutStart p * cutGenerator p * c m =
      Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
    dsimp only [p]
    solve_j2_seam_coordinate m
  exact j2_reverse_t_seam p _ he.symm

private theorem j2_edge_generator_unique {m : Nat} (x y g h : Configuration m)
    (hg : g * g = 1) (he : s(x, x * g) = s(y, y * h)) : g = h := by
  rcases Sym2.eq_iff.mp he with ⟨hxy, hend⟩ | ⟨hxy, hend⟩
  · subst y
    exact mul_left_cancel hend
  · rw [← hend] at hxy
    have hgh : g * h = 1 := mul_left_cancel (by
      simpa only [mul_assoc, mul_one] using hxy.symm)
    have ht := congrArg (g * ·) hgh
    simpa only [← mul_assoc, hg, one_mul, mul_one] using ht.symm

/-- Every actual c step avoids all six marked b cuts, regardless of its owner. -/
private theorem j2_c_not_marked {m : Nat} (hm : 5 ≤ m) (x : Configuration m) :
    ¬ MarkedCut m s(x, x * c m) := by
  rintro ⟨p, he⟩
  rw [native_j2_marked_edge] at he
  have hcb : c m = b m := j2_edge_generator_unique _ _ _ _ (c_sq m) he
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hv := congrArg (fun f : Configuration m => (f i).val) hcb
  simp only [c_apply, b_apply, i, lt_self_iff_false, if_false, Nat.sub_self] at hv
  rw [if_pos (by omega : m - 1 < m)] at hv
  omega

private theorem j2_c_ne_one {m : Nat} (hm : 5 ≤ m) : c m ≠ 1 := by
  intro he
  have hv := congrArg (fun z : Configuration m => (z (0 : Fin (m + 1))).val) he
  simp only [c_apply, Fin.val_zero, Equiv.Perm.one_apply] at hv
  rw [if_pos (by omega : 0 < m - 1)] at hv
  omega

/-- All the above seam witnesses produce edges in the very same independent
F2-minus-six-cuts graph used by the actual component theorem. -/
private theorem j2_c_survives {m : Nat} (hm : 5 ≤ m) (x : Configuration m)
    (hs : F2Seam m s(x, x * c m)) :
    (survivingGraph m).Adj x (x * c m) := by
  change (SimpleGraph.fromEdgeSet {e | SurvivingEdge m e}).Adj _ _
  apply SimpleGraph.fromEdgeSet_adj.mpr
  refine ⟨⟨Or.inr hs, j2_c_not_marked hm x⟩, ?_⟩
  intro he
  apply j2_c_ne_one hm
  exact mul_left_cancel (by simpa only [mul_one] using he.symm)


private theorem word_foldl {m : ℕ} (z : Configuration m)
    (l : List (Configuration m)) : l.foldl (· * ·) z = z * l.prod := by
  induction l generalizing z with
  | nil => simp
  | cons g gs ih => simp [ih, mul_assoc]

/-- Once actual step legality is earned, no path, simplicity, or component
coverage hypothesis is needed to obtain the complete J2 path component. -/
private theorem actual_j2_word_full_component {m : ℕ} (hm : 5 ≤ m) (i : Fin 5)
    (hchain : (List.scanl (· * ·) (wordStart m i) (word m i)).IsChain
      (survivingGraph m).Adj) :
    ∃ w : (survivingGraph m).Walk (wordStart m i) (wordFinish m i),
      w.IsPath ∧ w.length = wordLength m i ∧
        w.support = List.scanl (· * ·) (wordStart m i) (word m i) ∧
        (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (wordStart m i) x) ∧
        ∀ x y, (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (wordStart m i) x ↔ s(x, y) ∈ w.edges := by
  classical
  let xs := List.scanl (· * ·) (wordStart m i) (word m i)
  have hne : xs ≠ [] := List.scanl_ne_nil
  let raw := SimpleGraph.Walk.ofSupport xs hne hchain
  let w := raw.copy (List.head_scanl hne)
    (by rw [List.getLast_scanl, word_foldl, native_j2_word_endpoints hm i])
  have hsupport : w.support = xs := by simp [w, raw]
  have hlength : w.length = wordLength m i := by
    have he := congrArg List.length hsupport
    simp only [SimpleGraph.Walk.length_support, xs, List.length_scanl,
      native_j2_word_lengths hm i] at he
    omega
  have hpositive : 0 < wordLength m i := by
    have hquad : 4 * m + 7 ≤ 2 * m * m := by nlinarith
    fin_cases i <;> simp only [wordLength, Fin.val_mk] <;> omega
  have hnil : ¬w.Nil := by
    intro h
    have he := h.length_eq_zero
    omega
  have hsleaf : ((survivingGraph m).neighborSet (wordStart m i)).Subsingleton := by
    fin_cases i
    · exact actual_port_leaf hm (0, false, false)
    · exact actual_port_leaf hm (0, false, true)
    · exact actual_port_leaf hm (1, false, false)
    · exact actual_port_leaf hm (2, false, true)
    · exact actual_port_leaf hm (0, true, false)
  have hfleaf : ((survivingGraph m).neighborSet (wordFinish m i)).Subsingleton := by
    fin_cases i
    · exact actual_port_leaf hm (2, false, false)
    · exact actual_port_leaf hm (1, true, true)
    · exact actual_port_leaf hm (2, true, true)
    · exact actual_port_leaf hm (2, true, false)
    · exact actual_port_leaf hm (1, true, false)
  have hnb := literal_trace_nonbacktracking w id (word m i)
    (by simpa only [List.map_id_fun] using hsupport) (literal_j2_letters hm i)
  obtain ⟨hp, _, _, _, hvertices, hedges⟩ :=
    nonbacktracking_leaf_full_component w (actual_surviving_degree hm)
      hsleaf hfleaf hnil hnb
  exact ⟨w, hp, hlength, hsupport, hvertices, hedges⟩

#print axioms actual_j2_word_full_component
#print axioms j2_word1_repeated_c
#print axioms j2_word2_repeated_c
#print axioms j2_c_survives

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
