/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal full configurations determine shifted ports, new cut prefixes and exact independent child ownership. -/
/- candidate for the actual J(k+1) propagation.
   Frames are made from the previous literal full label list. Positive new
   mark indices are the old P marks shifted by one; index zero is in Q.
   This proves the native tuple/domain part of that propagation, without
   assuming the next pairing, next walk, or any abstract realization. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open private circle_b_reversal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open private native_special_port_domain from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly
open private childGap_bijective frame_base_not_reverse from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains

private theorem next_full_perm {α : Type*} (S A : List α) (u v : α) :
    ((u :: S) ++ A ++ [v]).Perm (S ++ (A ++ [u]) ++ [v]) := by
  simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
    (show ([u] ++ (S ++ A)).Perm ((S ++ A) ++ [u]) from
      List.perm_append_comm).append_right [v]

private theorem outer_full_perm {α : Type*} (S A : List α) (u v : α) :
    (S ++ (A ++ [v]) ++ [u]).Perm (S ++ (A ++ [u]) ++ [v]) := by
  simpa only [List.append_assoc] using
    (show ([v] ++ [u]).Perm ([u] ++ [v]) from
      List.perm_append_comm).append_left (S ++ A)

/-- The new marked frame is (u,S,A;v). The two marked orders are obtained
by applying this constructor to the two old orders in exchanged order. -/
def nextFrame {m k : ℕ} (F : SupplyFrame m k) (A : List (Fin (m + 1)))
    (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) : SupplyFrame m (k + 1) where
  selected := u :: F.selected
  base := A
  terminal := F.terminal
  selected_length := by simp only [List.length_cons, F.selected_length]
  prefix_length := by
    have hp := F.prefix_length
    rw [hbase] at hp
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hp ⊢
    omega
  full_nodup := by
    apply (next_full_perm F.selected A u F.terminal).nodup_iff.mpr
    simpa only [hbase] using F.full_nodup
  full_labels := by
    intro x
    apply (next_full_perm F.selected A u F.terminal).mem_iff.mpr
    simpa only [hbase] using F.full_labels x

/-- The actual outer u supply is (S,A,v;u). Its gap zero is Q and the
gap immediately before v is P; all other gaps remain independently indexed. -/
def outerFrame {m k : ℕ} (F : SupplyFrame m k) (A : List (Fin (m + 1)))
    (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) : SupplyFrame m k where
  selected := F.selected
  base := A ++ [F.terminal]
  terminal := u
  selected_length := F.selected_length
  prefix_length := by
    have hp := F.prefix_length
    rw [hbase] at hp
    simpa only [List.length_append, List.length_singleton] using hp
  full_nodup := by
    apply (outer_full_perm F.selected A u F.terminal).nodup_iff.mpr
    simpa only [hbase] using F.full_nodup
  full_labels := by
    intro x
    apply (outer_full_perm F.selected A u F.terminal).mem_iff.mpr
    simpa only [hbase] using F.full_labels x

private theorem tuple_ext {m : ℕ} {x y : Configuration m}
    (h : List.ofFn x = List.ofFn y) : x = y :=
  Equiv.ext (congrFun (List.ofFn_injective h))

/-- Literal rotation gives the actual Phi identity. No symbolic port
identification is assumed: the full permutations are equal. -/
theorem native_marked_index_shift {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (i : ℕ) :
    rightPort (nextFrame F A u hbase) (i + 1) = rightPort F i ∧
      leftPort (nextFrame F A u hbase) (i + 1) = leftPort F i := by
  have hrot : ((u :: F.selected) ++ A).rotate (i + 1) =
      (F.selected ++ F.base).rotate i := by
    simp only [List.cons_append, List.rotate_cons_succ, hbase, List.append_assoc]
  constructor
  · apply tuple_ext
    rw [((native_anchored_supply_coordinates hm (nextFrame F A u hbase)).1 (i + 1)).1,
      ((native_anchored_supply_coordinates hm F).1 i).1]
    exact congrArg (· ++ [F.terminal]) hrot
  · apply tuple_ext
    rw [((native_anchored_supply_coordinates hm (nextFrame F A u hbase)).1 (i + 1)).2.1,
      ((native_anchored_supply_coordinates hm F).1 i).2.1]
    exact congrArg (fun L => L.reverse ++ [F.terminal]) hrot

/-- The Q prefixes in (58.36) are actual a then b generator steps.
Applying this to both old orders gives the two new index-zero cut prefixes. -/
theorem native_q_index_zero_prefix {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) :
    leftPort (outerFrame F A u hbase) 0 * a m =
        rightPort (nextFrame F A u hbase) 0 ∧
      rightPort (nextFrame F A u hbase) 0 * b m =
        leftPort (nextFrame F A u hbase) 0 := by
  constructor
  · apply tuple_ext
    rw [full_reverse_list,
      ((native_anchored_supply_coordinates hm (outerFrame F A u hbase)).1 0).2.1,
      ((native_anchored_supply_coordinates hm (nextFrame F A u hbase)).1 0).1]
    simp only [outerFrame, nextFrame, List.rotate_zero, List.reverse_append,
      List.reverse_reverse, List.reverse_cons, List.reverse_singleton, List.reverse_nil,
      List.nil_append, List.singleton_append,
      List.cons_append, List.append_assoc]
  · rfl

/-- The P prefix in (58.33) is the actual old left-zero vertex, its
actual a step, then precisely the final b cut of the outer u supply. -/
theorem native_p_parent_cut_prefix {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) :
    leftPort F 0 * a m = rightPort (outerFrame F A u hbase) (m - 1) ∧
      rightPort (outerFrame F A u hbase) (m - 1) * b m =
        leftPort (outerFrame F A u hbase) (m - 1) ∧
      leftPort F 0 = leftPort (nextFrame F A u hbase) 1 := by
  have hlength : (F.selected ++ A).length = m - 1 := by
    have hp := F.prefix_length
    rw [hbase] at hp
    simp only [List.length_append, List.length_singleton] at hp ⊢
    omega
  have hrot : (F.selected ++ (A ++ [F.terminal])).rotate (m - 1) =
      F.terminal :: (F.selected ++ A) := by
    rw [← List.append_assoc, ← hlength, List.rotate_append_length_eq]
    rfl
  refine ⟨?_, rfl, (native_marked_index_shift hm F A u hbase 0).2.symm⟩
  apply tuple_ext
  rw [full_reverse_list, ((native_anchored_supply_coordinates hm F).1 0).2.1,
    ((native_anchored_supply_coordinates hm (outerFrame F A u hbase)).1 (m - 1)).1]
  simp only [outerFrame, hbase, List.rotate_zero, List.reverse_append,
    List.reverse_reverse, List.reverse_singleton, List.append_assoc]
  rw [hrot]
  simp only [List.singleton_append, List.nil_append, List.cons_append, List.append_assoc]

private theorem p_circle_eq {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) :
    (childGap F ⟨0, by simp only [hbase, List.length_append, List.length_singleton]; omega⟩).val =
      (childGap (outerFrame F A u hbase)
        ⟨A.length, by simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩).val := by
  dsimp only [childGap, outerFrame, gapCircle, Fin.val_mk]
  simp only [List.rotate_zero]
  change ((F.terminal :: F.base : List (Fin (m + 1))) : Cycle (Fin (m + 1))) =
    ((u :: (A ++ [F.terminal]).rotate A.length : List (Fin (m + 1))) : Cycle (Fin (m + 1)))
  rw [hbase, List.rotate_append_length_eq]
  apply Cycle.coe_eq_coe.mpr
  simpa only [List.cons_append, List.singleton_append, List.nil_append] using
    List.isRotated_append (l := F.terminal :: A) (l' := [u])

private theorem layer_a {m : ℕ} (S : Finset (Fin (m + 1)))
    (C : Cycle (Fin (m + 1))) {x : Configuration m} (hx : Layer S C x) :
    Layer S C (x * a m) := by
  change _ = _ ∨ _ = _
  rw [native_configurationCycle_reversal, erase_reverse]
  rcases hx with hx | hx
  · exact Or.inr (congrArg Cycle.reverse hx)
  · exact Or.inl (by rw [hx, Cycle.reverse_reverse])

private theorem layer_b {m : ℕ} (S : Finset (Fin (m + 1)))
    (C : Cycle (Fin (m + 1))) {x : Configuration m} (hx : Layer S C x) :
    Layer S C (x * b m) := by
  change _ = _ ∨ _ = _
  rw [circle_b_reversal, erase_reverse]
  rcases hx with hx | hx
  · exact Or.inr (congrArg Cycle.reverse hx)
  · exact Or.inl (by rw [hx, Cycle.reverse_reverse])

/-- Actual new mark zero belongs to Q; every positive new mark belongs
to P. Both endpoints are classified through deletion of native tuples.
No assertion about their place on the next cycle is used. -/
theorem native_new_marked_cut_domains {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) (i : Fin (k + 2)) :
    let O := outerFrame F A u hbase
    let N := nextFrame F A u hbase
    let j : Fin O.base.length :=
      ⟨if i.val = 0 then 0 else A.length, by
        simp only [O, outerFrame, List.length_append, List.length_singleton]
        split_ifs <;> omega⟩
    ChildDomain (childGap O j) (rightPort N i.val) ∧
      ChildDomain (childGap O j) (leftPort N i.val) := by
  dsimp only
  by_cases hi : i.val = 0
  · simp only [hi, if_pos rfl]
    let zero : Fin m := ⟨0, by omega⟩
    have hp := native_supply_cut_child_domain hm (outerFrame F A u hbase)
      (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) zero
    have hg : supplyGap (outerFrame F A u hbase)
        (by simp only [outerFrame, List.length_append, List.length_singleton]; omega) zero =
          ⟨0, by simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩ := by
      apply Fin.ext
      simp only [supplyGap, zero, Fin.val_mk, Nat.zero_le, ↓reduceIte]
    rw [hg] at hp
    dsimp only [zero, Fin.val_mk] at hp
    have ha := layer_a _ _ hp.2
    rw [(native_q_index_zero_prefix hm F A u hbase).1] at ha
    exact ⟨ha, layer_b _ _ ha⟩
  · simp only [if_neg hi]
    have hbase_len : 3 ≤ F.base.length := by
      simp only [hbase, List.length_append, List.length_singleton]; omega
    let r : Fin (k + 1) := ⟨i.val - 1, by have h := i.isLt; omega⟩
    have hs := native_marked_index_shift hm F A u hbase r.val
    have hr : r.val + 1 = i.val := by dsimp only [r]; omega
    rw [hr] at hs
    have hR := native_special_port_domain hm F hbase_len (r, 0)
    have hL := native_special_port_domain hm F hbase_len (r, 1)
    simp only [specialPort, Fin.val_zero, Fin.val_one, if_pos rfl,
      if_neg (by decide : ¬ (1 : Fin 2).val = 0)] at hR hL
    change Layer F.selected.toFinset _ _ at hR hL
    rw [p_circle_eq F A u hbase] at hR hL
    exact ⟨hs.1.symm ▸ hR, hs.2.symm ▸ hL⟩

/-- Full child uniqueness turns the above native calculation into the
exact ownership law. A new mark has no endpoint in any third child. -/
theorem native_new_marked_cut_owner_iff {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (i : Fin (k + 2)) (j : Fin (outerFrame F A u hbase).base.length) :
    (ChildDomain (childGap (outerFrame F A u hbase) j)
        (rightPort (nextFrame F A u hbase) i.val) ↔
      j.val = if i.val = 0 then 0 else A.length) ∧
    (ChildDomain (childGap (outerFrame F A u hbase) j)
        (leftPort (nextFrame F A u hbase) i.val) ↔
      j.val = if i.val = 0 then 0 else A.length) := by
  let O := outerFrame F A u hbase
  let r : Fin O.base.length := ⟨if i.val = 0 then 0 else A.length, by
    simp only [O, outerFrame, List.length_append, List.length_singleton]
    split_ifs <;> omega⟩
  have hB : 3 ≤ O.base.length := by
    simp only [O, outerFrame, List.length_append, List.length_singleton]; omega
  have hP := frame_base_not_reverse O hB
  have hinj := (childGap_bijective O (by omega)).1
  have hd := native_new_marked_cut_domains hm F A u hbase hA i
  have howner (x : Configuration m) (hx : ChildDomain (childGap O r) x) :
      ChildDomain (childGap O j) x ↔ j.val = r.val := by
    constructor
    · intro hj
      exact congrArg Fin.val (hinj (childDomain_unique hP _ _ hj hx))
    · intro hj
      exact (Fin.ext hj).symm ▸ hx
  exact ⟨howner _ hd.1, howner _ hd.2⟩

#print axioms native_marked_index_shift
#print axioms native_q_index_zero_prefix
#print axioms native_p_parent_cut_prefix
#print axioms native_new_marked_cut_domains
#print axioms native_new_marked_cut_owner_iff

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
