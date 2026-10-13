/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete F2 suppliers exhaust the independently specified two-label insertion layer. -/

import D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
import D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2Coverage

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap

private def baseLabels (m : ℕ) : List (Fin (m + 1)) :=
  List.ofFn (fun i : Fin (m - 1) => ⟨i.val + 1, by have hi := i.isLt; omega⟩)

private theorem baseLabels_nodup (m : ℕ) : (baseLabels m).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [Fin.val_mk] at he
  omega

private theorem baseLabels_avoids {m : ℕ} (x : Fin (m + 1)) (hx : x ∈ baseLabels m) :
    x ≠ 0 ∧ x ≠ Fin.last m := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have hi := i.isLt
  constructor <;> intro he <;> have hv := congrArg Fin.val he
  · simp only [Fin.val_mk, Fin.val_zero] at hv
    omega
  · simp only [Fin.val_mk, Fin.val_last] at hv
    omega

private theorem identity_tuple {m : ℕ} (hm : 1 ≤ m) :
    List.ofFn (1 : Configuration m) = (0 :: baseLabels m) ++ [Fin.last m] := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons,
      List.length_nil, baseLabels]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, Equiv.Perm.one_apply]
    by_cases hib : i < (0 :: baseLabels m).length
    · rw [List.getElem_append_left hib]
      cases i with
      | zero => rfl
      | succ i =>
        simp only [List.getElem_cons_succ, baseLabels, List.getElem_ofFn]
    · rw [List.getElem_append_right (by omega)]
      have hei : i = m := by
        simp only [List.length_cons, baseLabels, List.length_ofFn] at hib
        simp only [List.length_ofFn] at hi
        omega
      have hidx : i - (0 :: baseLabels m).length = 0 := by
        simp only [List.length_cons, baseLabels, List.length_ofFn]
        omega
      simp only [hidx, List.getElem_cons_zero]
      exact Fin.ext hei

private theorem erased_identity {m : ℕ} (hm : 1 ≤ m) :
    erase ({0, Fin.last m} : Finset (Fin (m + 1)))
      (configurationCycle (1 : Configuration m)) = (baseLabels m : Cycle (Fin (m + 1))) := by
  have hf : (baseLabels m).filter (fun x => decide (x ∉ ({0, Fin.last m} : Finset _))) =
      baseLabels m := by
    apply List.filter_eq_self.mpr
    intro x hx
    have ha := baseLabels_avoids x hx
    simp [ha.1, ha.2]
  change (((List.ofFn (1 : Configuration m)).filter
    (fun x => decide (x ∉ ({0, Fin.last m} : Finset _)))) : Cycle (Fin (m + 1))) = _
  rw [identity_tuple hm, List.filter_append, List.filter_cons, hf]
  simp

private theorem erase_singleton {α : Type} [DecidableEq α] (x : α) (C : Cycle α) :
    erase {x} C = delete x C := by
  unfold erase delete
  congr 1
  funext y
  simp

private theorem lower_last {m : ℕ} (hm : 3 ≤ m) :
    (a m * c m) (Fin.last m) = 0 := by
  apply Fin.ext
  rw [native_ac_apply_val hm]
  simp

private theorem lower_gap {m : ℕ} (hm : 4 ≤ m) :
    (residualList (a m * c m) : Cycle (Fin (m + 1))) =
      gapCircle (baseLabels m) (Fin.last m) ⟨0, by simp [baseLabels]; omega⟩ := by
  apply Cycle.coe_eq_coe.mpr
  refine ⟨m - 2, ?_⟩
  change (residualList (a m * c m)).rotate (m - 2) = Fin.last m :: (baseLabels m).rotate 0
  rw [List.rotate_zero]
  apply List.ext_getElem
  · simp only [residualList, baseLabels, List.length_rotate, List.length_ofFn,
      List.length_cons]
    omega
  · intro i hi hj
    apply Fin.ext
    simp only [residualList, List.getElem_rotate, List.length_ofFn,
      List.getElem_ofFn, native_ac_apply_val (by omega : 3 ≤ m), Fin.val_castSucc,
      Fin.val_mk]
    cases i with
    | zero =>
      simp only [Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : m - 2 < m)]
      simp only [if_pos (by omega : m - 2 < m - 1), List.getElem_cons_zero, Fin.val_last]
      omega
    | succ i =>
      simp only [List.getElem_cons_succ, baseLabels, List.getElem_ofFn, Fin.val_mk]
      simp only [residualList, List.length_rotate, List.length_ofFn] at hi
      by_cases hi0 : i = 0
      · subst i
        rw [Nat.mod_eq_of_lt (by omega : 1 + (m - 2) < m),
          if_neg (by omega : ¬1 + (m - 2) < m - 1)]
        omega
      · rw [show i + 1 + (m - 2) = (i - 1) + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < m),
          if_pos (by omega : i - 1 < m - 1)]
        omega

private theorem contact_val {m : ℕ} (j : Fin (m - 2)) (i : Fin (m + 1)) :
    (contactAnchor j i).val = if i.val < j.val + 1 then i.val + 1
      else if i.val = j.val + 1 then m else if i.val < m then i.val else 0 := rfl

private theorem contact_last {m : ℕ} (j : Fin (m - 2)) :
    contactAnchor j (Fin.last m) = 0 := by
  have hj := j.isLt
  apply Fin.ext
  rw [contact_val]
  simp only [Fin.val_last, Fin.val_zero]
  split_ifs <;> omega

private theorem contact_gap {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (residualList (contactAnchor j) : Cycle (Fin (m + 1))) =
      gapCircle (baseLabels m) (Fin.last m)
        ⟨j.val + 1, by simp only [baseLabels, List.length_ofFn]; have hj := j.isLt; omega⟩ := by
  have hj := j.isLt
  apply Cycle.coe_eq_coe.mpr
  refine ⟨j.val + 1, ?_⟩
  change (residualList (contactAnchor j)).rotate (j.val + 1) =
    Fin.last m :: (baseLabels m).rotate (j.val + 1)
  apply List.ext_getElem
  · simp only [residualList, baseLabels, List.length_rotate, List.length_ofFn,
      List.length_cons]
    omega
  · intro i hi hk
    apply Fin.ext
    simp only [residualList, List.getElem_rotate, List.length_ofFn, List.getElem_ofFn,
      contact_val, Fin.val_castSucc, Fin.val_mk]
    cases i with
    | zero =>
      simp only [Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : j.val + 1 < m)]
      simp only [List.getElem_cons_zero, Fin.val_last]
      split_ifs <;> omega
    | succ i =>
      simp only [List.getElem_cons_succ, baseLabels, List.getElem_rotate,
        List.length_ofFn, List.getElem_ofFn, Fin.val_mk]
      simp only [residualList, List.length_rotate, List.length_ofFn] at hi
      by_cases hit : i + (j.val + 1) < m - 1
      · rw [Nat.mod_eq_of_lt hit, Nat.mod_eq_of_lt (by omega : i + 1 + (j.val + 1) < m)]
        split_ifs <;> omega
      · rw [show i + (j.val + 1) = (i + j.val + 2 - m) + (m - 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i + j.val + 2 - m < m - 1),
          show i + 1 + (j.val + 1) = (i + j.val + 2 - m) + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i + j.val + 2 - m < m)]
        split_ifs <;> omega

private theorem gap_delete {m : ℕ} (r : Fin (baseLabels m).length) :
    delete (Fin.last m) (gapCircle (baseLabels m) (Fin.last m) r) =
      (baseLabels m : Cycle (Fin (m + 1))) := by
  have hf : ((baseLabels m).rotate r.val).filter (fun x => decide (x ≠ Fin.last m)) =
      (baseLabels m).rotate r.val := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true ((baseLabels_avoids x (List.mem_rotate.mp hx)).2)
  change (((Fin.last m :: (baseLabels m).rotate r.val).filter
    (fun x => decide (x ≠ Fin.last m))) : Cycle (Fin (m + 1))) = _
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, hf]
  exact Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)

private theorem upper_residual {m : ℕ} (hm : 4 ≤ m) :
    (residualList (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) :
      Cycle (Fin (m + 1))) = (0 :: baseLabels m : List (Fin (m + 1))) := by
  let t : Configuration m := Equiv.swap 0 (Fin.last m)
  have he : residualList (t * (a m * c m)) = (residualList (a m * c m)).map t := by
    exact List.ofFn_comp' (fun i : Fin m => (a m * c m) i.castSucc) t
  have hmap : (baseLabels m).map t = baseLabels m := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_map]
      have ha := baseLabels_avoids ((baseLabels m)[i]) (List.getElem_mem hj)
      exact Equiv.swap_apply_of_ne_of_ne ha.1 ha.2
  change (residualList (t * (a m * c m)) : Cycle (Fin (m + 1))) = _
  rw [he, ← Cycle.map_coe, lower_gap hm]
  simp only [gapCircle, List.rotate_zero, Fin.val_zero]
  change Cycle.map t ((Fin.last m :: baseLabels m : List (Fin (m + 1))) : Cycle _) = _
  rw [Cycle.map_coe, List.map_cons, hmap]
  simp only [t, Equiv.swap_apply_right]

private theorem upper_delete {m : ℕ} (hm : 4 ≤ m) :
    delete (0 : Fin (m + 1))
      (residualList (Equiv.swap 0 (Fin.last m) * (a m * c m)) : Cycle (Fin (m + 1))) =
        (baseLabels m : Cycle (Fin (m + 1))) := by
  rw [upper_residual hm]
  have hf : (baseLabels m).filter (fun x => decide (x ≠ 0)) = baseLabels m := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true ((baseLabels_avoids x hx).1)
  change (((0 :: baseLabels m).filter (fun x => decide (x ≠ 0))) : Cycle (Fin (m + 1))) = _
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, hf]

private theorem upper_last {m : ℕ} (hm : 4 ≤ m) :
    (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) (Fin.last m) =
      Fin.last m := by
  rw [Equiv.Perm.mul_apply, lower_last (by omega : 3 ≤ m)]
  exact Equiv.swap_apply_left _ _

private theorem supplier_in_layer {m : ℕ} (z v : Configuration m)
    (t x : Fin (m + 1)) (hs : insert x {t} = ({0, Fin.last m} : Finset _))
    (hlast : z (Fin.last m) = t)
    (hbase : delete x (residualList z : Cycle (Fin (m + 1))) =
      (baseLabels m : Cycle (Fin (m + 1)))) (hv : SupplierStar z v) :
    Layer {0, Fin.last m} (baseLabels m : Cycle (Fin (m + 1))) v := by
  change Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v at hv
  rw [hlast] at hv
  rcases hv with hv | hv
  · left
    rw [← hs, erase_insert, erase_singleton, hv, hbase]
  · right
    rw [← hs, erase_insert, erase_singleton, hv, delete_reverse, hbase]

/-- The actual two-star core and all concrete contact suppliers exhaust precisely
the layer specified independently by deleting labels zero and m from the identity circle. -/
theorem native_f2_layer_iff {m : ℕ} (hm : 4 ≤ m) (v : Configuration m) :
    F2Domain m v ↔ Layer ({0, Fin.last m} : Finset (Fin (m + 1)))
      (erase {0, Fin.last m} (configurationCycle (1 : Configuration m))) v := by
  rw [erased_identity (by omega : 1 ≤ m)]
  have hset : insert (Fin.last m) {0} = ({0, Fin.last m} : Finset (Fin (m + 1))) := by
    ext x
    simp [or_comm]
  constructor
  · intro hv
    change (SupplierStar (a m * c m) v ∨
      SupplierStar (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v) ∨
      (∃ j : Fin (m - 2), j.val < m - 2 ∧ SupplierStar (contactAnchor j) v) at hv
    rcases hv with (hl | hu) | ⟨j, _, hj⟩
    · apply supplier_in_layer (a m * c m) v 0 (Fin.last m) hset
        (lower_last (by omega : 3 ≤ m)) _ hl
      rw [lower_gap hm]
      exact gap_delete _
    · exact supplier_in_layer _ v (Fin.last m) 0 rfl (upper_last hm) (upper_delete hm) hu
    · apply supplier_in_layer (contactAnchor j) v 0 (Fin.last m) hset
        (contact_last j) _ hj
      rw [contact_gap hm j]
      exact gap_delete _
  · intro hv
    have hparent : Layer (insert (Fin.last m) {0})
        (baseLabels m : Cycle (Fin (m + 1))) v := by
      simpa only [hset] using hv
    obtain ⟨D, hD⟩ := childDomain_exists hparent
    have hB0 : baseLabels m ≠ [] := by
      intro he
      have hlen := congrArg List.length he
      simp only [baseLabels, List.length_ofFn, List.length_nil] at hlen
      omega
    have hx : Fin.last m ∉ baseLabels m := by
      intro hx
      exact (baseLabels_avoids _ hx).2 rfl
    have hlast0 : Fin.last m ≠ (0 : Fin (m + 1)) := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_zero] at hval
      omega
    have hxD : Fin.last m ∈ D.val := (D.property.2.1 _).mpr (by simp [hlast0])
    obtain ⟨r, hr, _⟩ := (gapCircle_fiber (baseLabels_nodup m) hB0 hx D.val).mp
      ⟨D.property.1, hxD, D.property.2.2.2⟩
    change erase {0} (configurationCycle v) = D.val ∨
      erase {0} (configurationCycle v) = D.val.reverse at hD
    rw [erase_singleton] at hD
    by_cases hr0 : r.val = 0
    · have he : r = ⟨0, by simp only [baseLabels, List.length_ofFn]; omega⟩ := Fin.ext hr0
      have hres : (residualList (a m * c m) : Cycle (Fin (m + 1))) = D.val := by
        rw [lower_gap hm, ← he]
        exact hr.symm
      have hs : SupplierStar (a m * c m) v := by
        change Star ((a m * c m) (Fin.last m))
          (residualList (a m * c m) : Cycle (Fin (m + 1))) v
        rw [lower_last (by omega : 3 ≤ m), hres]
        exact hD
      exact Or.inl (Or.inl hs)
    · have hrlt : r.val < m - 1 := by simpa only [baseLabels, List.length_ofFn] using r.isLt
      let j : Fin (m - 2) := ⟨r.val - 1, by omega⟩
      have hindex : (⟨j.val + 1, by
          simp only [baseLabels, List.length_ofFn]; have hj := j.isLt; omega⟩ :
          Fin (baseLabels m).length) = r := by
        apply Fin.ext
        simp only [j, Fin.val_mk]
        omega
      have hres : (residualList (contactAnchor j) : Cycle (Fin (m + 1))) = D.val := by
        rw [contact_gap hm j, hindex]
        exact hr.symm
      have hs : SupplierStar (contactAnchor j) v := by
        change Star (contactAnchor j (Fin.last m))
          (residualList (contactAnchor j) : Cycle (Fin (m + 1))) v
        rw [contact_last, hres]
        exact hD
      exact Or.inr ⟨j, j.isLt, hs⟩

#print axioms native_f2_layer_iff

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2Coverage
