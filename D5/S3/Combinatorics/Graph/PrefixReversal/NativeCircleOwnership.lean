/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement]
   utility: none
   digest: Native T cuts have genuinely distinct complete circle owners. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open Equiv
open Fin.NatCast

private theorem tuple_nodup {m : ℕ} (z : Configuration m) :
    (List.ofFn z).Nodup := List.nodup_ofFn.mpr z.injective

private theorem tuple_mem {m : ℕ} (z : Configuration m) (x : Fin (m + 1)) :
    x ∈ List.ofFn z := List.mem_ofFn.mpr ⟨z.symm x, z.apply_symm_apply x⟩

def nextLabel {m : ℕ} (z : Configuration m) (x : Fin (m + 1)) : Fin (m + 1) :=
  (List.ofFn z).next x (tuple_mem z x)

def prevLabel {m : ℕ} (z : Configuration m) (x : Fin (m + 1)) : Fin (m + 1) :=
  (List.ofFn z).prev x (tuple_mem z x)

private theorem nextLabel_apply {m : ℕ} (z : Configuration m) (i : Fin (m + 1)) :
    nextLabel z (z i) = z ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ := by
  have h := List.next_getElem (List.ofFn z) (List.nodup_ofFn.mpr z.injective)
    i.val (by simpa using i.isLt)
  simpa only [nextLabel, List.getElem_ofFn, List.length_ofFn] using h

private theorem prevLabel_apply {m : ℕ} (z : Configuration m) (i : Fin (m + 1)) :
    prevLabel z (z i) = z ⟨(i.val + m) % (m + 1), Nat.mod_lt _ (by omega)⟩ := by
  have h := List.prev_getElem (List.ofFn z) (List.nodup_ofFn.mpr z.injective)
    i.val (by simpa using i.isLt)
  simpa only [prevLabel, List.getElem_ofFn, List.length_ofFn, Nat.add_sub_cancel] using h

theorem circle_neighbours {m : ℕ} (z v : Configuration m) (h : Circle z v)
    (x : Fin (m + 1)) :
    (nextLabel v x = nextLabel z x ∧ prevLabel v x = prevLabel z x) ∨
      (nextLabel v x = prevLabel z x ∧ prevLabel v x = nextLabel z x) := by
  rcases h with h | h
  · left
    exact ⟨List.isRotated_next_eq (Cycle.coe_eq_coe.mp h) (tuple_nodup v)
      (tuple_mem v x), List.isRotated_prev_eq (Cycle.coe_eq_coe.mp h)
        (tuple_nodup v) (tuple_mem v x)⟩
  · right
    have hr : (List.ofFn v).IsRotated (List.ofFn z).reverse := Cycle.coe_eq_coe.mp h
    exact ⟨(List.isRotated_next_eq hr (tuple_nodup v) (tuple_mem v x)).trans
        (List.next_reverse_eq_prev (List.ofFn z) (tuple_nodup z) x (tuple_mem z x)),
      (List.isRotated_prev_eq hr (tuple_nodup v) (tuple_mem v x)).trans
        (List.prev_reverse_eq_next (List.ofFn z) (tuple_nodup z) x (tuple_mem z x))⟩

private theorem circle_common {m : ℕ} (z w v : Configuration m)
    (hz : Circle z v) (hw : Circle w v) : Circle z w := by
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact Or.inl (hw.symm.trans hz)
  · right
    have h := congrArg Cycle.reverse (hw.symm.trans hz)
    simpa only [Cycle.reverse_reverse] using h
  · exact Or.inr (hw.symm.trans hz)
  · left
    have h := congrArg Cycle.reverse (hw.symm.trans hz)
    simpa only [Cycle.reverse_reverse] using h

private theorem circle_repr {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (hv : Circle z v) : ∃ p : Fin (m + 1) × Bool, circleCoordinate z p = v := by
  let p := (circleEquiv hm z).symm ⟨v, hv⟩
  refine ⟨p, ?_⟩
  exact congrArg Subtype.val ((circleEquiv hm z).apply_symm_apply ⟨v, hv⟩)

private theorem gap_circle_common {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (i j : Fin m) (hi : Circle (gapAnchor z i) v) (hj : Circle (gapAnchor z j) v) :
    i = j := by
  obtain ⟨p, hp⟩ := circle_repr hm (gapAnchor z i) v hi
  obtain ⟨q, hq⟩ := circle_repr hm (gapAnchor z j) v hj
  have hc : coordinateEquiv hm z (i, p) = coordinateEquiv hm z (j, q) := by
    apply Subtype.ext
    change coordinate z (i, p) = coordinate z (j, q)
    exact hp.trans hq.symm
  exact congrArg Prod.fst ((coordinateEquiv hm z).injective hc)

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open Equiv
open Fin.NatCast

/-- Distinct insertion gaps give distinct complete native circles. -/
theorem native_circle_gap_disjoint {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint {v : Configuration m | Circle (gapAnchor z i) v}
      {v : Configuration m | Circle (gapAnchor z j) v} := by
  rw [Set.disjoint_left]
  intro v hi hj
  exact hij (gap_circle_common hm z v i j hi hj)


end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
