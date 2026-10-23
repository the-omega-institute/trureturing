/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical opposite marked order exchanges only the final two protected labels and commutes with literal recursive frame constructors. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders

open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains

private theorem selected_nodup {m k : ℕ} (F : SupplyFrame m k) :
    F.selected.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp F.full_nodup).1).1

private theorem swap_mem {α : Type*} [DecidableEq α] (L : List α) (p q x : α)
    (hp : p ∈ L) (hq : q ∈ L) : Equiv.swap p q x ∈ L ↔ x ∈ L := by
  by_cases hxp : x = p
  · subst x; simp [hp, hq]
  by_cases hxq : x = q
  · subst x; simp [hp, hq]
  rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]

private theorem swap_selected_perm {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) :
    (F.selected.map (Equiv.swap (protectedP F hk) (protectedQ F hk))).Perm
      F.selected := by
  have hp := (native_protected_labels F hk).2.1
  have hq := (native_protected_labels F hk).2.2.1
  apply (List.perm_ext_iff_of_nodup
    ((selected_nodup F).map (Equiv.swap (protectedP F hk) (protectedQ F hk)).injective)
    (selected_nodup F)).mpr
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (swap_mem F.selected (protectedP F hk) (protectedQ F hk) y hp hq).mpr hy
  · intro hx
    apply List.mem_map.mpr
    refine ⟨Equiv.swap (protectedP F hk) (protectedQ F hk) x,
      (swap_mem F.selected (protectedP F hk) (protectedQ F hk) x hp hq).mpr hx, ?_⟩
    simp

/-- This exchanges the two protected labels in the selected list only.
The independent base and terminal remain their literal original values. -/
def oppositeSelectedFrame {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) :
    SupplyFrame m k where
  selected := F.selected.map (Equiv.swap (protectedP F hk) (protectedQ F hk))
  base := F.base
  terminal := F.terminal
  selected_length := by simp only [List.length_map, F.selected_length]
  prefix_length := by simpa only [List.length_append, List.length_map] using F.prefix_length
  full_nodup := ((swap_selected_perm F hk).append_right F.base |>.append_right [F.terminal]).nodup_iff.mpr F.full_nodup
  full_labels := fun x =>
    ((swap_selected_perm F hk).append_right F.base |>.append_right [F.terminal]).mem_iff.mpr
      (F.full_labels x)

private theorem frame_ext {m k : ℕ} {F G : SupplyFrame m k}
    (hs : F.selected = G.selected) (hb : F.base = G.base) (ht : F.terminal = G.terminal) :
    F = G := by
  cases F; cases G
  cases hs; cases hb; cases ht
  rfl

/-- The protected pair is exchanged, with no set-level relaxation. -/
theorem native_opposite_protected_labels {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) :
    protectedP (oppositeSelectedFrame F hk) hk = protectedQ F hk ∧
      protectedQ (oppositeSelectedFrame F hk) hk = protectedP F hk := by
  constructor
  · simp only [protectedP, oppositeSelectedFrame, List.getElem_map]
    exact Equiv.swap_apply_left _ _
  · simp only [protectedQ, oppositeSelectedFrame, List.getElem_map]
    exact Equiv.swap_apply_right _ _

/-- Every selected position before the protected pair retains its exact
label. Thus an induction instance cannot silently choose a different
ordering of the selected prefix. -/
theorem native_opposite_selected_prefix {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) :
    (oppositeSelectedFrame F hk).selected.take (k - 2) = F.selected.take (k - 2) := by
  apply List.ext_getElem
  · simp only [List.length_take, oppositeSelectedFrame, List.length_map]
  · intro i hi hj
    have hi' : i < k - 2 := by
      simp only [List.length_take] at hi
      omega
    have hif : i < F.selected.length := by rw [F.selected_length]; omega
    simp only [oppositeSelectedFrame, List.getElem_take, List.getElem_map]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he
      have hidx := (selected_nodup F).getElem_inj_iff.mp he
      omega
    · intro he
      have hidx := (selected_nodup F).getElem_inj_iff.mp he
      omega

/-- The canonical operation is an involution on complete literal frames. -/
theorem native_opposite_selected_involutive {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) : oppositeSelectedFrame (oppositeSelectedFrame F hk) hk = F := by
  apply frame_ext
  · change (F.selected.map (Equiv.swap (protectedP F hk) (protectedQ F hk))).map
      (Equiv.swap (protectedP (oppositeSelectedFrame F hk) hk)
        (protectedQ (oppositeSelectedFrame F hk) hk)) = F.selected
    rw [(native_opposite_protected_labels F hk).1,
      (native_opposite_protected_labels F hk).2, Equiv.swap_comm, List.map_map]
    simpa only [Function.comp_def, Equiv.swap_apply_self] using List.map_id' F.selected
  · rfl
  · rfl

/-- At the exceptional second order the two protected labels are the
whole selected list. The canonical exchange is exactly the existing
J2 reverseSelected frame, with its original base and port indexing. -/
theorem native_opposite_selected_two {m : ℕ} (F : SupplyFrame m 2) :
    oppositeSelectedFrame F (by omega) =
      D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport.reverseSelected F := by
  obtain ⟨p, q, hs⟩ : ∃ p q, F.selected = [p, q] := by
    have hlen := F.selected_length
    cases h : F.selected with
    | nil => simp [h] at hlen
    | cons p rest =>
      cases hr : rest with
      | nil => simp [h, hr] at hlen
      | cons q tail =>
        have ht : tail = [] := List.length_eq_zero_iff.mp (by
          simp only [h, hr, List.length_cons] at hlen
          omega)
        exact ⟨p, q, by rw [ht]⟩
  have hp : protectedP F (by omega) = p := by simp [protectedP, hs]
  have hq : protectedQ F (by omega) = q := by simp [protectedQ, hs]
  apply frame_ext
  · change F.selected.map (Equiv.swap (protectedP F (by omega))
      (protectedQ F (by omega))) = F.selected.reverse
    simp [hs, hp, hq]
  · rfl
  · rfl

private theorem opposite_prepend_selected {m k : ℕ} (F : SupplyFrame m k)
    (G : SupplyFrame m (k + 1)) (hk : 2 ≤ k) (u : Fin (m + 1))
    (hs : G.selected = u :: F.selected) :
    (oppositeSelectedFrame G (by omega)).selected =
      u :: (oppositeSelectedFrame F hk).selected := by
  have hu : u ∉ F.selected := by
    have hn := selected_nodup G
    rw [hs] at hn
    exact (List.nodup_cons.mp hn).1
  have hpq := native_protected_labels_prepend F G hk u hs
  change G.selected.map _ = u :: F.selected.map _
  rw [hs, List.map_cons, hpq.1, hpq.2]
  have hp := (native_protected_labels F hk).2.1
  have hq := (native_protected_labels F hk).2.2.1
  have hup : u ≠ protectedP F hk := fun he => hu (he.symm ▸ hp)
  have huq : u ≠ protectedQ F hk := fun he => hu (he.symm ▸ hq)
  rw [Equiv.swap_apply_of_ne_of_ne hup huq]

/-- Prepending the new marked label commutes with exchanging the fixed
protected pair; the new label itself is not exchanged. -/
theorem native_opposite_next_frame {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) :
    oppositeSelectedFrame (nextFrame F A u hbase) (by omega) =
      nextFrame (oppositeSelectedFrame F hk) A u hbase := by
  apply frame_ext
  · exact opposite_prepend_selected F (nextFrame F A u hbase) hk u rfl
  · rfl
  · rfl

/-- The outer supplier changes only the base and terminal. Its opposite
order is therefore the literal outer supplier of the opposite frame. -/
theorem native_opposite_outer_frame {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) :
    oppositeSelectedFrame (outerFrame F A u hbase) hk =
      outerFrame (oppositeSelectedFrame F hk) A u hbase := by
  apply frame_ext <;> rfl

/-- Every independent child rotates exactly the same original base in
both orders. The canonical opposite operation commutes with that rotation. -/
theorem native_opposite_child_frame {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (j : Fin F.base.length) :
    oppositeSelectedFrame (nativeChildFrame F j) hk =
      nativeChildFrame (oppositeSelectedFrame F hk) j := by
  apply frame_ext <;> rfl

#print axioms native_opposite_protected_labels
#print axioms native_opposite_selected_prefix
#print axioms native_opposite_selected_involutive
#print axioms native_opposite_selected_two
#print axioms native_opposite_next_frame
#print axioms native_opposite_outer_frame
#print axioms native_opposite_child_frame

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
