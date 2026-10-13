/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
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

private theorem bc_pow_val {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (i : Fin (m + 1)) :
    (((b m * c m) ^ k) i).val =
      if i.val < m then (i.val + k) % m else i.val := by
  have hmpos : 0 < m := by omega
  induction k with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply, Nat.add_zero]
    by_cases hi : i.val < m
    · simp only [if_pos hi, Nat.mod_eq_of_lt hi]
    · simp only [if_neg hi]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, bc_apply hm]
    by_cases hi : i.val < m
    · have hv : (((b m * c m) ^ k) i).val = (i.val + k) % m := by
        simpa only [if_pos hi] using ih
      simp only [hv, Nat.mod_lt _ hmpos, dite_true, Fin.val_mk, if_pos hi]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rfl
    · have hv : (((b m * c m) ^ k) i).val = i.val := by
        simpa only [if_neg hi] using ih
      simp only [hv, hi, dite_false, if_false]

/-- Distinct insertion gaps give distinct complete native circles. -/
theorem native_circle_gap_disjoint {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint {v : Configuration m | Circle (gapAnchor z i) v}
      {v : Configuration m | Circle (gapAnchor z j) v} := by
  rw [Set.disjoint_left]
  intro v hi hj
  exact hij (gap_circle_common hm z v i j hi hj)

private def lowerPort {m : ℕ} (j : Fin (m - 2)) : Configuration m :=
  a m * c m * (b m * c m) ^ j.val

private def upperPort {m : ℕ} (j : Fin (m - 2)) : Configuration m :=
  Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * lowerPort j

private theorem ac_apply_val {m : ℕ} (hm : 3 ≤ m) (i : Fin (m + 1)) :
    ((a m * c m) i).val = if i.val < m - 1 then i.val + 2 else m - i.val := by
  change (a m (c m i)).val = _
  rw [a_apply]
  simp only [Fin.val_rev, c_apply]
  split <;> omega

private theorem lowerPort_val {m : ℕ} (hm : 3 ≤ m) (j : Fin (m - 2))
    (i : Fin (m + 1)) (hi : i.val < m) :
    (lowerPort j i).val = if (i.val + j.val) % m < m - 1 then
      (i.val + j.val) % m + 2 else m - (i.val + j.val) % m := by
  change (((a m * c m) (((b m * c m) ^ j.val) i))).val = _
  rw [ac_apply_val hm, bc_pow_val (by omega : 2 ≤ m), if_pos hi]

private theorem lower_m_position {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    lowerPort j ⟨m - 2 - j.val, by have hj := j.isLt; omega⟩ = Fin.last m := by
  have hj := j.isLt
  apply Fin.ext
  rw [lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk]; omega)]
  simp only [Fin.val_mk, Fin.val_last,
    show m - 2 - j.val + j.val = m - 2 by omega,
    Nat.mod_eq_of_lt (by omega : m - 2 < m),
    if_pos (by omega : m - 2 < m - 1)]
  omega

private theorem lower_next {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (nextLabel (lowerPort j) (Fin.last m)).val = 1 := by
  have hj := j.isLt
  let i : Fin (m + 1) := ⟨m - 2 - j.val, by omega⟩
  have hn := nextLabel_apply (lowerPort j) i
  rw [show lowerPort j i = Fin.last m from lower_m_position hm j] at hn
  have hidx : (i.val + 1) % (m + 1) = m - 1 - j.val := by
    dsimp [i]
    rw [Nat.mod_eq_of_lt (by omega : m - 2 - j.val + 1 < m + 1)]
    omega
  rw [hn]
  rw [lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk, hidx]; omega)]
  simp only [Fin.val_mk, hidx, show m - 1 - j.val + j.val = m - 1 by omega,
    Nat.mod_eq_of_lt (by omega : m - 1 < m), lt_self_iff_false, if_false]
  omega

private theorem lower_prev {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (prevLabel (lowerPort j) (Fin.last m)).val = m - 1 := by
  have hj := j.isLt
  let i : Fin (m + 1) := ⟨m - 2 - j.val, by omega⟩
  have hp := prevLabel_apply (lowerPort j) i
  rw [show lowerPort j i = Fin.last m from lower_m_position hm j] at hp
  have hidx : (i.val + m) % (m + 1) = m - 3 - j.val := by
    dsimp [i]
    rw [show m - 2 - j.val + m = (m - 3 - j.val) + (m + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hp]
  rw [lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk, hidx]; omega)]
  simp only [Fin.val_mk, hidx, show m - 3 - j.val + j.val = m - 3 by omega,
    Nat.mod_eq_of_lt (by omega : m - 3 < m), if_pos (by omega : m - 3 < m - 1)]
  omega

private theorem lower_last {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    lowerPort j (Fin.last m) = 0 := by
  apply Fin.ext
  change (((a m * c m) (((b m * c m) ^ j.val) (Fin.last m)))).val = 0
  rw [ac_apply_val (by omega : 3 ≤ m), bc_pow_val (by omega : 2 ≤ m)]
  simp only [Fin.val_last, lt_self_iff_false, if_false,
    if_neg (by omega : ¬ m < m - 1), Nat.sub_self]

private theorem upper_last {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    upperPort j (Fin.last m) = Fin.last m := by
  change Equiv.swap (0 : Fin (m + 1)) (Fin.last m) (lowerPort j (Fin.last m)) = _
  rw [lower_last hm j, Equiv.swap_apply_left]

private theorem upper_next {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (nextLabel (upperPort j) (Fin.last m)).val = j.val + 2 := by
  have hj := j.isLt
  have hn := nextLabel_apply (upperPort j) (Fin.last m)
  rw [upper_last hm j] at hn
  have hz : (lowerPort j (0 : Fin (m + 1))).val = j.val + 2 := by
    rw [lowerPort_val (by omega : 3 ≤ m) j _ (by simp; omega)]
    simp only [Fin.val_zero, zero_add, Nat.mod_eq_of_lt (by omega : j.val < m),
      if_pos (by omega : j.val < m - 1)]
  have hz0 : lowerPort j (0 : Fin (m + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    rw [hz] at hv
    simp only [Fin.val_zero] at hv
    omega
  have hzm : lowerPort j (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro he
    have hv := congrArg Fin.val he
    rw [hz] at hv
    simp only [Fin.val_last] at hv
    omega
  have hzero : (⟨((Fin.last m).val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ :
      Fin (m + 1)) = 0 := by
    apply Fin.ext
    simp
  rw [hn, hzero]
  change ((Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) (lowerPort j 0)).val = _
  rw [Equiv.swap_apply_of_ne_of_ne hz0 hzm]
  exact hz

private theorem upper_prev {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (prevLabel (upperPort j) (Fin.last m)).val = if j.val = 0 then 1 else j.val + 1 := by
  have hj := j.isLt
  have hp := prevLabel_apply (upperPort j) (Fin.last m)
  rw [upper_last hm j] at hp
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hidx : (⟨((Fin.last m).val + m) % (m + 1), Nat.mod_lt _ (by omega)⟩ :
      Fin (m + 1)) = i := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_mk]
    rw [show m + m = (m - 1) + (m + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hz : (lowerPort j i).val = if j.val = 0 then 1 else j.val + 1 := by
    rw [lowerPort_val (by omega : 3 ≤ m) j i (by dsimp [i]; omega)]
    dsimp only [i]
    by_cases hj0 : j.val = 0
    · simp only [hj0, Nat.add_zero, Nat.mod_eq_of_lt (by omega : m - 1 < m),
        lt_self_iff_false, if_false, if_pos rfl]
      simp only [if_true]
      omega
    · have hmod : (m - 1 + j.val) % m = j.val - 1 := by
        rw [show m - 1 + j.val = (j.val - 1) + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hmod, if_pos (by omega : j.val - 1 < m - 1), if_neg hj0]
      omega
  have hz0 : lowerPort j i ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    rw [hz] at hv
    simp only [Fin.val_zero] at hv
    split_ifs at hv <;> omega
  have hzm : lowerPort j i ≠ Fin.last m := by
    intro he
    have hv := congrArg Fin.val he
    rw [hz] at hv
    simp only [Fin.val_last] at hv
    split_ifs at hv <;> omega
  rw [hp, hidx]
  change ((Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) (lowerPort j i)).val = _
  rw [Equiv.swap_apply_of_ne_of_ne hz0 hzm]
  exact hz

/-- The actual noncore cuts from the two T suppliers have disjoint complete
rotation-and-reversal circle domains, for the all-size F₂ range. -/
theorem native_t_cross_circle_disjoint {m : ℕ} (hm : 4 ≤ m)
    (i j : Fin (m - 2)) :
    Disjoint {v : Configuration m | Circle (a m * c m * (b m * c m) ^ i.val) v}
      {v : Configuration m | Circle (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) *
        (a m * c m * (b m * c m) ^ j.val)) v} := by
  rw [Set.disjoint_left]
  intro v hi hj
  have hc := circle_common (lowerPort i) (upperPort j) v hi hj
  have hn := circle_neighbours (lowerPort i) (upperPort j) hc (Fin.last m)
  rcases hn with hn | hn
  · have he := congrArg Fin.val hn.1
    rw [upper_next hm j, lower_next hm i] at he
    omega
  · have he1 := congrArg Fin.val hn.1
    have he2 := congrArg Fin.val hn.2
    rw [upper_next hm j, lower_prev hm i] at he1
    rw [upper_prev hm j, lower_next hm i] at he2
    split_ifs at he2 <;> omega

#print axioms native_t_cross_circle_disjoint

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
