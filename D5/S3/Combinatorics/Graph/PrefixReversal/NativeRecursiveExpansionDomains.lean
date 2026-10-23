/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal native deletion assigns every supplied cut to exactly one independent insertion child. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
import D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

private theorem frame_base_nodup {m k : Nat} (F : SupplyFrame m k) :
    F.base.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp F.full_nodup).1).2.1

private theorem frame_selected_base_disjoint {m k : Nat} (F : SupplyFrame m k) :
    List.Disjoint F.selected F.base :=
  (List.nodup_append'.mp (List.nodup_append'.mp F.full_nodup).1).2.2

private theorem frame_terminal_fresh {m k : Nat} (F : SupplyFrame m k) :
    F.terminal ∉ F.selected ++ F.base := by
  intro ht
  exact List.disjoint_left.mp (List.nodup_append'.mp F.full_nodup).2.2 ht
    (by simp only [List.mem_singleton])

private theorem frame_residual_labels {m k : Nat} (F : SupplyFrame m k)
    (y : Fin (m + 1)) :
    (y ∈ F.base ∨ y = F.terminal) ↔ y ∉ F.selected.toFinset := by
  simp only [List.mem_toFinset]
  constructor
  · rintro (hy | rfl) hs
    · exact List.disjoint_left.mp (frame_selected_base_disjoint F) hs hy
    · exact frame_terminal_fresh F (List.mem_append.mpr (Or.inl hs))
  · intro hs
    have hy := F.full_labels y
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with (hy | hy) | hy
    · exact (hs hy).elim
    · exact Or.inl hy
    · exact Or.inr hy

private theorem frame_base_not_reverse {m k : Nat} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) : (F.base : Cycle (Fin (m + 1))) ≠
      (F.base : Cycle (Fin (m + 1))).reverse := by
  intro he
  have hw : DeleteWalk [] (F.base : Cycle (Fin (m + 1)))
      (F.base : Cycle (Fin (m + 1))).reverse := by
    rw [← he]
    exact DeleteWalk.nil _
  have hb := negative_walk_support_bound hw
    (Cycle.nodup_coe_iff.mpr (frame_base_nodup F))
  rw [Cycle.coe_toFinset, List.toFinset_card_of_nodup (frame_base_nodup F)] at hb
  simp only [List.toFinset_nil, Finset.card_empty, Nat.zero_add] at hb
  omega

/-- The actual positive residual circle of a child. All cyclic gaps occur. -/
def childGap {m k : Nat} (F : SupplyFrame m k) (j : Fin F.base.length) :
    ChildCircle F.selected.toFinset F.terminal (F.base : Cycle (Fin (m + 1))) := by
  let C := gapCircle F.base F.terminal j
  have ht : F.terminal ∉ F.base := fun h =>
    frame_terminal_fresh F (List.mem_append.mpr (Or.inr h))
  have hn : C.Nodup := by
    apply Cycle.nodup_coe_iff.mpr
    exact List.nodup_cons.mpr
      ⟨fun h => ht (List.mem_rotate.mp h), List.nodup_rotate.mpr (frame_base_nodup F)⟩
  have hlabels : ∀ y, y ∈ C ↔ y ∉ F.selected.toFinset := by
    intro y
    simp only [C, gapCircle, Cycle.mem_coe_iff, List.mem_cons, List.mem_rotate]
    exact or_comm.trans (frame_residual_labels F y)
  have hs : erase F.selected.toFinset C = C := by
    change (((F.terminal :: F.base.rotate j.val).filter
      (fun y => decide (y ∉ F.selected.toFinset))) : Cycle (Fin (m + 1))) = C
    have hf : (F.terminal :: F.base.rotate j.val).filter
        (fun y => decide (y ∉ F.selected.toFinset)) =
        F.terminal :: F.base.rotate j.val := by
      apply List.filter_eq_self.mpr
      intro y hy
      exact decide_eq_true ((hlabels y).mp (Cycle.mem_coe_iff.mpr hy))
    rw [hf]
    rfl
  have hd : delete F.terminal C = (F.base : Cycle (Fin (m + 1))) := by
    have hf : (F.base.rotate j.val).filter
        (fun y => decide (y ≠ F.terminal)) = F.base.rotate j.val := by
      apply List.filter_eq_self.mpr
      intro y hy
      apply decide_eq_true
      intro he
      subst y
      exact ht (List.mem_rotate.mp hy)
    change (((F.terminal :: F.base.rotate j.val).filter
      (fun y => decide (y ≠ F.terminal))) : Cycle (Fin (m + 1))) = _
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, hf]
    exact Cycle.coe_eq_coe.mpr (List.IsRotated.forall F.base j.val)
  exact ⟨C, hn, hlabels, hs, hd⟩

private theorem childGap_bijective {m k : Nat} (F : SupplyFrame m k)
    (hB : 0 < F.base.length) : Function.Bijective (childGap F) := by
  have ht : F.terminal ∉ F.base := fun h =>
    frame_terminal_fresh F (List.mem_append.mpr (Or.inr h))
  have hB0 : F.base ≠ [] := List.length_pos_iff.mp hB
  have hex (D : ChildCircle F.selected.toFinset F.terminal
      (F.base : Cycle (Fin (m + 1)))) :
      ∃! j : Fin F.base.length, D.val = gapCircle F.base F.terminal j := by
    apply (gapCircle_fiber (frame_base_nodup F) hB0 ht D.val).mp
    refine ⟨D.property.1, ?_, D.property.2.2.2⟩
    apply (D.property.2.1 F.terminal).mpr
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh F (List.mem_append.mpr (Or.inl h))
  constructor
  · intro j l he
    have hj := hex (childGap F j)
    obtain ⟨r, hr, huniq⟩ := hj
    have hjr : j = r := huniq j rfl
    have hlr : l = r := huniq l (congrArg Subtype.val he)
    exact hjr.trans hlr.symm
  · intro D
    obtain ⟨j, hj, _⟩ := hex D
    exact ⟨j, Subtype.ext hj.symm⟩

/-- Complete independently specified parent coverage, indexed by actual gaps. -/
theorem native_child_gap_partition {m k : Nat} (F : SupplyFrame m k)
    (hB : 3 ≤ F.base.length) (v : Configuration m) :
    Layer (insert F.terminal F.selected.toFinset) (F.base : Cycle (Fin (m + 1))) v ↔
      ∃! j : Fin F.base.length, ChildDomain (childGap F j) v := by
  have hP := frame_base_not_reverse F hB
  have hbij := childGap_bijective F (by omega)
  constructor
  · intro hv
    obtain ⟨D, hD, _⟩ := (insertionLayer_partition hP v).mp hv
    obtain ⟨j, rfl⟩ := hbij.2 D
    refine ⟨j, hD, ?_⟩
    intro l hl
    exact hbij.1 (childDomain_unique hP _ _ hl hD)
  · rintro ⟨j, hj, _⟩
    exact childDomain_parent _ hj

/-- Supply positions 0..k all hit gap zero; the others hit distinct positive gaps. -/
def supplyGap {m k : Nat} (F : SupplyFrame m k) (hB : 0 < F.base.length)
    (i : Fin m) : Fin F.base.length :=
  ⟨if i.val ≤ k then 0 else i.val - k, by
    have hp := F.prefix_length
    simp only [List.length_append, F.selected_length] at hp
    have hi := i.isLt
    split_ifs <;> omega⟩

private theorem filter_rotate_join {α : Type} (p : α → Bool) (S B : List α)
    (hS : ∀ y ∈ S, p y = false) (hB : ∀ y ∈ B, p y = true)
    (i : Nat) (hi : i ≤ (S ++ B).length) :
    ((S ++ B).rotate i).filter p =
      if i ≤ S.length then B else B.rotate (i - S.length) := by
  have hfS (L : List α) (hL : ∀ y ∈ L, y ∈ S) : L.filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy
    simp only [hS y (hL y hy), Bool.false_eq_true, not_false_eq_true]
  have hfB (L : List α) (hL : ∀ y ∈ L, y ∈ B) : L.filter p = L := by
    apply List.filter_eq_self.mpr
    intro y hy
    exact hB y (hL y hy)
  by_cases hs : i ≤ S.length
  · rw [if_pos hs, List.rotate_eq_drop_append_take hi,
      List.drop_append_of_le_length hs, List.take_append_of_le_length hs]
    simp only [List.filter_append,
      hfS (S.drop i) (fun _ h => List.mem_of_mem_drop h),
      hfS (S.take i) (fun _ h => List.mem_of_mem_take h),
      hfB B (fun _ h => h), List.nil_append, List.append_nil]
  · have hrot : (S ++ B).rotate i = (B ++ S).rotate (i - S.length) := by
      calc
        _ = (S ++ B).rotate (S.length + (i - S.length)) := by
          congr 1
          omega
        _ = ((S ++ B).rotate S.length).rotate (i - S.length) :=
          (List.rotate_rotate _ _ _).symm
        _ = _ := by rw [List.rotate_append_length_eq]
    rw [if_neg hs, hrot]
    have ht : i - S.length ≤ B.length := by
      simp only [List.length_append] at hi
      omega
    rw [List.rotate_eq_drop_append_take (show i - S.length ≤ (B ++ S).length by
        simp only [List.length_append]; omega),
      List.drop_append_of_le_length ht, List.take_append_of_le_length ht]
    simp only [List.filter_append,
      hfB (B.drop (i - S.length)) (fun _ h => List.mem_of_mem_drop h),
      hfB (B.take (i - S.length)) (fun _ h => List.mem_of_mem_take h),
      hfS S (fun _ h => h), List.append_nil]
    rw [List.rotate_eq_drop_append_take ht]

private theorem frame_rotation_filter {m k : Nat} (F : SupplyFrame m k)
    (hB : 0 < F.base.length) (i : Fin m) :
    ((F.selected ++ F.base).rotate i.val).filter
        (fun y => decide (y ∉ F.selected.toFinset)) =
      F.base.rotate (supplyGap F hB i).val := by
  have hf := filter_rotate_join (fun y => decide (y ∉ F.selected.toFinset))
    F.selected F.base
    (fun y hy => by simp only [List.mem_toFinset, hy, not_true_eq_false, decide_false])
    (fun y hy => decide_eq_true ((frame_residual_labels F y).mp (Or.inl hy)))
    i.val (by rw [F.prefix_length]; exact Nat.le_of_lt i.isLt)
  by_cases hi : i.val ≤ k
  · simpa only [supplyGap, F.selected_length, if_pos hi, List.rotate_zero] using hf
  · simpa only [supplyGap, F.selected_length, if_neg hi] using hf

private theorem cycle_terminal_front {α : Type} (L : List α) (u : α) :
    ((L ++ [u] : List α) : Cycle α) = (u :: L : List α) := by
  exact Cycle.coe_eq_coe.mpr (List.isRotated_append (l := L) (l' := [u]))

/-- Native deletion computes each actual right/left port's unique child owner. -/
theorem native_supply_child_coordinates {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 0 < F.base.length) (i : Fin m) :
    erase F.selected.toFinset (configurationCycle (rightPort F i.val)) =
        (childGap F (supplyGap F hB i)).val ∧
      erase F.selected.toFinset (configurationCycle (leftPort F i.val)) =
        (childGap F (supplyGap F hB i)).val.reverse := by
  have hc := (native_anchored_supply_coordinates hm F).1 i.val
  have ht : decide (F.terminal ∉ F.selected.toFinset) = true := by
    apply decide_eq_true
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh F (List.mem_append.mpr (Or.inl h))
  constructor
  · change erase F.selected.toFinset (List.ofFn (rightPort F i.val) : Cycle _) = _
    rw [hc.1, erase_coe, List.filter_append, frame_rotation_filter F hB i]
    simp only [List.filter_cons, List.filter_nil, ht, ↓reduceIte]
    exact cycle_terminal_front _ _
  · change erase F.selected.toFinset (List.ofFn (leftPort F i.val) : Cycle _) = _
    rw [hc.2.1, erase_coe, List.filter_append, List.filter_reverse,
      frame_rotation_filter F hB i]
    simp only [List.filter_cons, List.filter_nil, ht, ↓reduceIte]
    have hgap : (childGap F (supplyGap F hB i)).val =
        ((F.terminal :: F.base.rotate (supplyGap F hB i).val : List (Fin (m + 1))) :
          Cycle (Fin (m + 1))) := rfl
    rw [hgap, Cycle.reverse_coe, List.reverse_cons]

/-- In particular, both endpoints of every actual b cut have the computed
full child domain. They are not assigned by an abstract skeleton edge. -/
theorem native_supply_cut_child_domain {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 0 < F.base.length) (i : Fin m) :
    ChildDomain (childGap F (supplyGap F hB i)) (rightPort F i.val) ∧
      ChildDomain (childGap F (supplyGap F hB i)) (leftPort F i.val) := by
  have hc := native_supply_child_coordinates hm F hB i
  exact ⟨Or.inl hc.1, Or.inr hc.2⟩

/-- Full-domain uniqueness upgrades the explicit deletion calculation to an
iff: neither endpoint of a supplied b cut can hide in another child. -/
theorem native_supply_cut_owner_iff {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (i : Fin m) (j : Fin F.base.length) :
    (ChildDomain (childGap F j) (rightPort F i.val) ↔
        supplyGap F (by omega) i = j) ∧
      (ChildDomain (childGap F j) (leftPort F i.val) ↔
        supplyGap F (by omega) i = j) := by
  have hc := native_supply_cut_child_domain hm F (by omega) i
  have hP := frame_base_not_reverse F hB
  have hinj := (childGap_bijective F (by omega)).1
  constructor
  · constructor
    · intro hv
      exact hinj (childDomain_unique hP _ _ hc.1 hv)
    · intro he
      exact he ▸ hc.1
  · constructor
    · intro hv
      exact hinj (childDomain_unique hP _ _ hc.2 hv)
    · intro he
      exact he ▸ hc.2

/-- Exactly the first k+1 literal cuts belong to the special child. -/
theorem native_special_child_cut_indices {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) (i : Fin m) :
    (ChildDomain (childGap F ⟨0, by omega⟩) (rightPort F i.val) ↔ i.val ≤ k) ∧
      (ChildDomain (childGap F ⟨0, by omega⟩) (leftPort F i.val) ↔ i.val ≤ k) := by
  have hc := native_supply_cut_owner_iff hm F hB i ⟨0, by omega⟩
  have hcode : supplyGap F (by omega) i = ⟨0, by omega⟩ ↔ i.val ≤ k := by
    rw [Fin.ext_iff]
    simp only [supplyGap, Fin.val_mk]
    split_ifs <;> omega
  exact ⟨hc.1.trans hcode, hc.2.trans hcode⟩

/-- Every other independent child has exactly one literal supplier b cut,
at position k+j. This conclusion uses tuple deletion, not a cut count. -/
theorem native_other_child_unique_cut {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val) :
    ∃! i : Fin m, ChildDomain (childGap F j) (rightPort F i.val) := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  let i : Fin m := ⟨k + j.val, by have h := j.isLt; omega⟩
  have hcode : supplyGap F (by omega) i = j := by
    apply Fin.ext
    simp only [supplyGap, i, Fin.val_mk, if_neg (by omega : ¬ k + j.val ≤ k)]
    omega
  refine ⟨i, (native_supply_cut_owner_iff hm F hB i j).1.mpr hcode, ?_⟩
  intro l hl
  have he := congrArg Fin.val ((native_supply_cut_owner_iff hm F hB l j).1.mp hl)
  simp only [supplyGap, Fin.val_mk] at he
  apply Fin.ext
  change l.val = k + j.val
  split_ifs at he <;> omega

#print axioms native_child_gap_partition
#print axioms native_supply_child_coordinates
#print axioms native_supply_cut_child_domain
#print axioms native_supply_cut_owner_iff
#print axioms native_special_child_cut_indices
#print axioms native_other_child_unique_cut

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
