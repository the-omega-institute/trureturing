/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.Conjecture52; result=D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.not_conjecture52; claim=D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.Conjecture52
   digest: The sequential CDF exceeds the static CDF on a tree of maximum degree three. -/

import D5.S3.Combinatorics.Graph.Brooks.ColoringExtension
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-! The discrete parking CDFs and a counterexample to Conjecture 5.2 of
Higuita-Diaz, López and Roldán-Correa (arXiv:2611.14718v2). -/

namespace Parking

open private SimpleGraph.Maximal.exists_adj_of_notMem from
  D5.S3.Combinatorics.Graph.Brooks.ColoringExtension

variable {V : Type*} [DecidableEq V]

/-- The boolean membership test for the closed neighborhood of v. -/
private def closed (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) : Bool :=
  decide (v = w) || decide (G.Adj v w)

private theorem closed_iff (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) :
    closed G v w = true ↔ v = w ∨ G.Adj v w := by
  simp [closed]

/-- The available vertices after parking at v and removing its closed neighborhood. -/
def after (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : Finset V :=
  s.filter (fun w => !closed G v w)



/-- Probability of parking at most k more vertices. The empty state succeeds.
A nonempty state at cutoff zero must park another vertex, so its event is false. -/
def seq (G : SimpleGraph V) [DecidableRel G.Adj] : Nat → Finset V → ℚ
  | 0, s => if s = ∅ then 1 else 0
  | k + 1, s =>
    if s = ∅ then 1 else (∑ v ∈ s, seq G k (after G s v)) / (s.card : ℚ)

private def seqList (G : SimpleGraph V) [DecidableRel G.Adj] : Nat → List V → ℚ
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _ + 1, [] => 1
  | k + 1, v :: vs =>
    let s := v :: vs
    ((s.map fun w => seqList G k (s.filter fun x => !closed G w x)).sum) /
      (s.length : ℚ)

private theorem after_toFinset (G : SimpleGraph V) [DecidableRel G.Adj] (s : List V) (v : V) :
    (s.filter fun w => !closed G v w).toFinset = after G s.toFinset v := by
  ext w
  simp [after]

private theorem seqList_eq (G : SimpleGraph V) [DecidableRel G.Adj] (k : Nat)
    (s : List V) (hs : s.Nodup) : seqList G k s = seq G k s.toFinset := by
  induction k generalizing s with
  | zero => cases s <;> simp [seqList, seq]
  | succ k ih =>
    cases s with
    | nil => simp [seqList, seq]
    | cons v vs =>
      rw [seqList, seq]
      simp only [List.toFinset_cons, Finset.insert_ne_empty, ite_false]
      rw [← List.toFinset_cons, List.toFinset_card_of_nodup hs]
      congr 1
      rw [List.sum_toFinset _ hs]
      congr 1
      apply List.map_congr_left
      intro w _
      exact (ih _ (hs.filter _)).trans (congrArg (seq G k) (after_toFinset G _ _))

/-- Independent sets that cannot be extended by adding vertices. -/
def jammed (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal G.IsIndepSet (s : Set V)

omit [DecidableEq V] in
private theorem jammed_iff (G : SimpleGraph V) (s : Finset V) :
    jammed G s ↔
      (∀ v ∈ s, ∀ w ∈ s, ¬G.Adj v w) ∧
      (∀ w : V, ∃ v ∈ s, v = w ∨ G.Adj v w) := by
  constructor
  · intro maximal
    refine ⟨fun v hv w hw hadj => maximal.1 hv hw hadj.ne hadj, fun w => ?_⟩
    by_cases hw : w ∈ s
    · exact ⟨w, hw, Or.inl rfl⟩
    · obtain ⟨v, hv, ha⟩ :=
        SimpleGraph.Maximal.exists_adj_of_notMem maximal (show w ∉ (s : Set V) from hw)
      exact ⟨v, hv, Or.inr ha.symm⟩
  · rintro ⟨hi, hd⟩
    have independent : G.IsIndepSet (s : Set V) :=
      fun hv hw _ => hi _ hv _ hw
    refine ⟨independent, fun {t} ht hst x hx => ?_⟩
    obtain ⟨v, hv, he | ha⟩ := hd x
    · exact he ▸ hv
    · exact (ht (hst hv) hx ha.ne ha).elim

section Finite
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private instance jammedDecidable (s : Finset V) : Decidable (jammed G s) :=
  decidable_of_iff _ (jammed_iff G s).symm

/-- Eq. (3), the number of qualifying jammed sets divided by the number of all jammed sets. -/
def static (k : Nat) : ℚ :=
  let m := (Finset.univ : Finset V).powerset.filter (jammed G)
  ((m.filter fun s => s.card ≤ k).card : ℚ) / (m.card : ℚ)

private def staticCount (keep : Finset V → Prop) [DecidablePred keep] : Nat :=
  ((Finset.univ : Finset V).powerset.filter fun s => jammed G s ∧ keep s).card

private theorem static_eq (k : Nat) :
    static G k = (staticCount G (fun s => s.card ≤ k) : ℚ) /
      (staticCount G (fun _ => True) : ℚ) := by
  simp only [static, staticCount, Finset.filter_filter, and_comm, true_and]

end Finite

/-- Definition 2.1 and Conjecture 5.2. The graphs are arbitrary finite simple graphs. -/
def Conjecture52 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ 3 → ∀ k : Nat, seq G k Finset.univ ≤ static G k

/- The finite witness uses closed-neighborhood bit masks on the natural labels. -/
private def closedMasks : List Nat :=
  [4225,4354,8708,9224,18448,4128,8256,16513,258,16900,1032,2064,4131,8268,17040]

private def packedClosed (u v : Fin 15) : Bool :=
  (closedMasks[u.val]?.getD 0).testBit v.val

private theorem packedClosed_symm : ∀ u v : Fin 15, packedClosed u v = packedClosed v u := by
  decide +kernel

private def witness : SimpleGraph (Fin 15) where
  Adj u v := u ≠ v ∧ packedClosed u v = true
  symm := ⟨fun {u v} h => ⟨Ne.symm h.1, packedClosed_symm u v ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance witnessAdj : DecidableRel witness.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ packedClosed u v = true))


private theorem witness_maxDegree_le : witness.maxDegree ≤ 3 := by
  apply witness.maxDegree_le_of_forall_degree_le
  decide +kernel


private theorem seq_witness_list :
    seq witness 6 Finset.univ = seqList witness 6 (List.finRange 15) := by
  rw [seqList_eq _ _ _ (List.nodup_finRange 15), List.toFinset_finRange]

variable {V : Type*} [DecidableEq V]

private theorem powerset_list_val (l : List V) (hl : l.Nodup) :
    (Finset.mk (l : Multiset V) hl).powerset.val =
      ((l.sublists').map List.toFinset : List (Finset V)) := by
  simp only [Finset.powerset, Multiset.powerset_coe']
  apply congrArg (fun s : List (Finset V) => (s : Multiset (Finset V)))
  refine (List.pmap_map _).trans ?_
  calc
    _ = List.pmap (P := List.Nodup) (fun s _ => s.toFinset) l.sublists'
        (fun s hm => hl.sublist (List.mem_sublists'.mp hm)) := by
      apply List.pmap_congr_left
      intro s hs h₁ h₂
      ext v
      change (v ∈ s) ↔ v ∈ s.toFinset
      simp
    _ = _ := List.pmap_eq_map _

/-- Boolean, executable form of independence and coverage by closed neighborhoods. -/
private def jamList (G : SimpleGraph V) [DecidableRel G.Adj] (vertices picked : List V) : Bool :=
  (picked.all fun v => picked.all fun w => !decide (G.Adj v w)) &&
    (vertices.all fun w => picked.any fun v => closed G v w)

private theorem jamList_iff (G : SimpleGraph V) [DecidableRel G.Adj] (vertices picked : List V)
    (cover : ∀ w, w ∈ vertices) :
    jamList G vertices picked = true ↔ jammed G picked.toFinset := by
  simp only [jamList, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, closed_iff, jammed_iff, List.mem_toFinset]
  simp [cover]

/-- Count sublists by partitioning on whether the head is selected. -/
private def countSubsets (test : List V → Bool) : List V → Nat
  | [] => if test [] then 1 else 0
  | v :: vs => countSubsets test vs + countSubsets (fun s => test (v :: s)) vs


omit [DecidableEq V] in
private theorem countSubsets_eq (test : List V → Bool) (l : List V) :
    countSubsets test l = l.sublists'.countP test := by
  induction l generalizing test with
  | nil => cases h : test [] <;> simp [countSubsets, h]
  | cons v vs ih =>
    simp only [countSubsets, List.sublists'_cons, List.countP_append, List.countP_map, ih]
    rfl

private theorem staticCount_list [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : List V) (hl : l.Nodup) (cover : ∀ v, v ∈ l)
    (keep : Finset V → Prop) [DecidablePred keep] (test : List V → Bool)
    (test_correct : ∀ s : List V, s.Nodup → (test s = true ↔ keep s.toFinset)) :
    staticCount G keep = countSubsets (fun s => jamList G l s && test s) l := by
  have h : (Finset.univ : Finset V) = ⟨(l : Multiset V), hl⟩ := by
    ext v
    exact iff_of_true (Finset.mem_univ v) (cover v)
  simp only [staticCount, Finset.card, Finset.filter_val, h, powerset_list_val,
    Multiset.filter_coe, Multiset.coe_card, ← List.countP_eq_length_filter, List.countP_map,
    countSubsets_eq]
  apply List.countP_congr
  intro s hs
  simp only [Function.comp_apply, decide_eq_true_eq, Bool.and_eq_true,
    jamList_iff G l s cover, test_correct s (hl.sublist (List.mem_sublists'.mp hs))]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem static_count : staticCount witness (fun _ => True) = 55 := by
  rw [staticCount_list witness _ (List.nodup_finRange 15) List.mem_finRange _ (fun _ => true)
    (by simp)]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem static_small_count : staticCount witness (fun s => s.card ≤ 6) = 1 := by
  rw [staticCount_list witness _ (List.nodup_finRange 15) List.mem_finRange _
    (fun s => decide (s.length ≤ 6))
    (by intro s hs; simp [List.toFinset_card_of_nodup hs])]
  decide +kernel

private theorem static_exact : static witness 6 = (1 / 55 : ℚ) := by
  rw [static_eq, static_small_count, static_count]
  rfl

section SequentialCertificate

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

-- Evaluate each possible first choice separately. Each child uses the exact
-- list recurrence on the available vertices after that choice.
private theorem seq_after_0 : seqList witness 5 [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14] = 0 := by
  decide +kernel

private theorem seq_after_1 : seqList witness 5 [0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14] = 0 := by
  decide +kernel

private theorem seq_after_2 : seqList witness 5 [0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14] = 0 := by
  decide +kernel

private theorem seq_after_3 : seqList witness 5 [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 14] = 0 := by
  decide +kernel

private theorem seq_after_4 : seqList witness 5 [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13] = 0 := by
  decide +kernel

private theorem seq_after_5 : seqList witness 5 [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14] = 0 := by
  decide +kernel

private theorem seq_after_6 : seqList witness 5 [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14] = 0 := by
  decide +kernel

private theorem seq_after_7 : seqList witness 5 [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13] = 0 := by
  decide +kernel

private theorem seq_after_8 : seqList witness 5 [0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14] = (16 / 675) := by
  decide +kernel

private theorem seq_after_9 : seqList witness 5 [0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13] = 0 := by
  decide +kernel

private theorem seq_after_10 : seqList witness 5 [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14] = (16 / 675) := by
  decide +kernel

private theorem seq_after_11 : seqList witness 5 [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14] = (16 / 675) := by
  decide +kernel

private theorem seq_after_12 : seqList witness 5 [2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14] = (16 / 225) := by
  decide +kernel

private theorem seq_after_13 : seqList witness 5 [0, 1, 4, 5, 7, 8, 9, 10, 11, 12, 14] = (16 / 225) := by
  decide +kernel

private theorem seq_after_14 : seqList witness 5 [0, 1, 2, 3, 5, 6, 8, 10, 11, 12, 13] = (16 / 225) := by
  decide +kernel

private theorem seq_full_list : seqList witness 6 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = (64 / 3375) := by
  change ([seqList witness 5 [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14],
        seqList witness 5 [0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14],
        seqList witness 5 [0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14],
        seqList witness 5 [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 14],
        seqList witness 5 [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13],
        seqList witness 5 [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14],
        seqList witness 5 [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14],
        seqList witness 5 [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13],
        seqList witness 5 [0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14],
        seqList witness 5 [0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13],
        seqList witness 5 [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14],
        seqList witness 5 [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14],
        seqList witness 5 [2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14],
        seqList witness 5 [0, 1, 4, 5, 7, 8, 9, 10, 11, 12, 14],
        seqList witness 5 [0, 1, 2, 3, 5, 6, 8, 10, 11, 12, 13]].sum / 15) = (64 / 3375)
  rw [seq_after_0, seq_after_1, seq_after_2, seq_after_3, seq_after_4, seq_after_5, seq_after_6, seq_after_7, seq_after_8, seq_after_9, seq_after_10, seq_after_11, seq_after_12, seq_after_13, seq_after_14]
  decide +kernel

private theorem sequential_exact : seq witness 6 Finset.univ = (64 / 3375 : ℚ) := by
  rw [seq_witness_list]
  exact seq_full_list

end SequentialCertificate

/-- The fifteen-vertex witness violates the CDF inequality at cutoff six. -/
theorem not_conjecture52 : ¬ Conjecture52 := by
  intro h
  have comparison := h (Fin 15) witness witness_maxDegree_le 6
  rw [static_exact, sequential_exact] at comparison
  exact (by decide +kernel : ¬ (64 / 3375 : ℚ) ≤ 1 / 55) comparison

end Parking
