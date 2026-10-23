/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native T cuts have genuinely distinct complete circle owners. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement

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

theorem native_nextLabel_apply {m : ℕ} (z : Configuration m) (i : Fin (m + 1)) :
    nextLabel z (z i) = z ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ := by
  have h := List.next_getElem (List.ofFn z) (List.nodup_ofFn.mpr z.injective)
    i.val (by simpa using i.isLt)
  simpa only [nextLabel, List.getElem_ofFn, List.length_ofFn] using h

theorem native_prevLabel_apply {m : ℕ} (z : Configuration m) (i : Fin (m + 1)) :
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
open Equiv
open Fin.NatCast

theorem native_bc_pow_val {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (i : Fin (m + 1)) :
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

def lowerPort {m : ℕ} (j : Fin (m - 2)) : Configuration m :=
  a m * c m * (b m * c m) ^ j.val

def upperPort {m : ℕ} (j : Fin (m - 2)) : Configuration m :=
  Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * lowerPort j

theorem native_ac_apply_val {m : ℕ} (hm : 3 ≤ m) (i : Fin (m + 1)) :
    ((a m * c m) i).val = if i.val < m - 1 then i.val + 2 else m - i.val := by
  change (a m (c m i)).val = _
  rw [a_apply]
  simp only [Fin.val_rev, c_apply]
  split <;> omega

theorem native_lowerPort_val {m : ℕ} (hm : 3 ≤ m) (j : Fin (m - 2))
    (i : Fin (m + 1)) (hi : i.val < m) :
    (lowerPort j i).val = if (i.val + j.val) % m < m - 1 then
      (i.val + j.val) % m + 2 else m - (i.val + j.val) % m := by
  change (((a m * c m) (((b m * c m) ^ j.val) i))).val = _
  rw [native_ac_apply_val hm, native_bc_pow_val (by omega : 2 ≤ m), if_pos hi]

theorem native_lower_m_position {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    lowerPort j ⟨m - 2 - j.val, by have hj := j.isLt; omega⟩ = Fin.last m := by
  have hj := j.isLt
  apply Fin.ext
  rw [native_lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk]; omega)]
  simp only [Fin.val_mk, Fin.val_last,
    show m - 2 - j.val + j.val = m - 2 by omega,
    Nat.mod_eq_of_lt (by omega : m - 2 < m),
    if_pos (by omega : m - 2 < m - 1)]
  omega

theorem native_lower_next {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (nextLabel (lowerPort j) (Fin.last m)).val = 1 := by
  have hj := j.isLt
  let i : Fin (m + 1) := ⟨m - 2 - j.val, by omega⟩
  have hn := native_nextLabel_apply (lowerPort j) i
  rw [show lowerPort j i = Fin.last m from native_lower_m_position hm j] at hn
  have hidx : (i.val + 1) % (m + 1) = m - 1 - j.val := by
    dsimp [i]
    rw [Nat.mod_eq_of_lt (by omega : m - 2 - j.val + 1 < m + 1)]
    omega
  rw [hn]
  rw [native_lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk, hidx]; omega)]
  simp only [Fin.val_mk, hidx, show m - 1 - j.val + j.val = m - 1 by omega,
    Nat.mod_eq_of_lt (by omega : m - 1 < m), lt_self_iff_false, if_false]
  omega

theorem native_lower_prev {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (prevLabel (lowerPort j) (Fin.last m)).val = m - 1 := by
  have hj := j.isLt
  let i : Fin (m + 1) := ⟨m - 2 - j.val, by omega⟩
  have hp := native_prevLabel_apply (lowerPort j) i
  rw [show lowerPort j i = Fin.last m from native_lower_m_position hm j] at hp
  have hidx : (i.val + m) % (m + 1) = m - 3 - j.val := by
    dsimp [i]
    rw [show m - 2 - j.val + m = (m - 3 - j.val) + (m + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hp]
  rw [native_lowerPort_val (by omega : 3 ≤ m) j _ (by simp only [Fin.val_mk, hidx]; omega)]
  simp only [Fin.val_mk, hidx, show m - 3 - j.val + j.val = m - 3 by omega,
    Nat.mod_eq_of_lt (by omega : m - 3 < m), if_pos (by omega : m - 3 < m - 1)]
  omega

theorem native_lower_last {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    lowerPort j (Fin.last m) = 0 := by
  apply Fin.ext
  change (((a m * c m) (((b m * c m) ^ j.val) (Fin.last m)))).val = 0
  rw [native_ac_apply_val (by omega : 3 ≤ m), native_bc_pow_val (by omega : 2 ≤ m)]
  simp only [Fin.val_last, lt_self_iff_false, if_false,
    if_neg (by omega : ¬ m < m - 1), Nat.sub_self]

theorem native_upper_last {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    upperPort j (Fin.last m) = Fin.last m := by
  change Equiv.swap (0 : Fin (m + 1)) (Fin.last m) (lowerPort j (Fin.last m)) = _
  rw [native_lower_last hm j, Equiv.swap_apply_left]

theorem native_upper_next {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (nextLabel (upperPort j) (Fin.last m)).val = j.val + 2 := by
  have hj := j.isLt
  have hn := native_nextLabel_apply (upperPort j) (Fin.last m)
  rw [native_upper_last hm j] at hn
  have hz : (lowerPort j (0 : Fin (m + 1))).val = j.val + 2 := by
    rw [native_lowerPort_val (by omega : 3 ≤ m) j _ (by simp; omega)]
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

theorem native_upper_prev {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    (prevLabel (upperPort j) (Fin.last m)).val = if j.val = 0 then 1 else j.val + 1 := by
  have hj := j.isLt
  have hp := native_prevLabel_apply (upperPort j) (Fin.last m)
  rw [native_upper_last hm j] at hp
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hidx : (⟨((Fin.last m).val + m) % (m + 1), Nat.mod_lt _ (by omega)⟩ :
      Fin (m + 1)) = i := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_mk]
    rw [show m + m = (m - 1) + (m + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hz : (lowerPort j i).val = if j.val = 0 then 1 else j.val + 1 := by
    rw [native_lowerPort_val (by omega : 3 ≤ m) j i (by dsimp [i]; omega)]
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
    rw [native_upper_next hm j, native_lower_next hm i] at he
    omega
  · have he1 := congrArg Fin.val hn.1
    have he2 := congrArg Fin.val hn.2
    rw [native_upper_next hm j, native_lower_prev hm i] at he1
    rw [native_upper_prev hm j, native_lower_next hm i] at he2
    split_ifs at he2 <;> omega

#print axioms native_t_cross_circle_disjoint

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership


namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open Equiv
open Fin.NatCast

/-- An independently deletion-defined supplier star consists exactly of its
complete native insertion-gap circles. -/
theorem native_star_circle_partition {m : ℕ} (hm : 3 ≤ m)
    (z v : Configuration m) :
    Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v ↔
      ∃ i : Fin m, Circle (gapAnchor z i) v := by
  constructor
  · intro hv
    let p := (coordinateEquiv hm z).symm ⟨v, hv⟩
    have hp := congrArg Subtype.val ((coordinateEquiv hm z).apply_symm_apply ⟨v, hv⟩)
    change coordinate z p = v at hp
    refine ⟨p.1, ?_⟩
    have hc := ((circleEquiv hm (gapAnchor z p.1)) p.2).property
    change Circle (gapAnchor z p.1) (coordinate z p) at hc
    exact hp ▸ hc
  · rintro ⟨i, hi⟩
    obtain ⟨p, hp⟩ := circle_repr hm (gapAnchor z i) v hi
    have hc := (coordinateEquiv hm z (i, p)).property
    change Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1)))
      (circleCoordinate (gapAnchor z i) p) at hc
    exact hp ▸ hc

private theorem circle_rotation {m : ℕ} (z : Configuration m) :
    configurationCycle (z * finRotate (m + 1)) = configurationCycle z := by
  apply Cycle.coe_eq_coe.mpr
  rw [show List.ofFn (z * finRotate (m + 1)) = (List.ofFn z).rotate 1 from
    by simpa only [pow_one] using rotate_pow_list z 1]
  exact List.IsRotated.symm ⟨1, rfl⟩

private theorem lower_core_swap {m : ℕ} (hm : 4 ≤ m) :
    gapAnchor (a m * c m) ⟨m - 2, by omega⟩ =
      Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  change ((a m * c m) (((b m * c m) ^ (m - 2)) i)).val = _
  rw [native_ac_apply_val (by omega : 3 ≤ m), native_bc_pow_val (by omega : 2 ≤ m)]
  rw [Equiv.swap_apply_def]
  by_cases hi0 : i = 0
  · subst i
    simp only [Fin.val_zero, zero_add, if_pos (by omega : 0 < m),
      Nat.mod_eq_of_lt (by omega : m - 2 < m),
      if_pos (by omega : m - 2 < m - 1), ↓reduceIte, Fin.val_last]
    omega
  · by_cases hil : i = Fin.last m
    · subst i
      simp only [Fin.val_last, lt_self_iff_false, if_false,
        if_neg (by omega : ¬ m < m - 1), if_neg hi0, ↓reduceIte, Fin.val_zero]
      omega
    · have hi : i.val < m := by
        have hb := i.isLt
        have hn : i.val ≠ m := fun h => hil (Fin.ext h)
        omega
      have hi0v : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      simp only [if_pos hi, if_neg hi0, if_neg hil]
      by_cases hi1 : i.val = 1
      · rw [hi1, show 1 + (m - 2) = m - 1 by omega,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        simp only [lt_self_iff_false, if_false]
        omega
      · have hmod : (i.val + (m - 2)) % m = i.val - 2 := by
          rw [show i.val + (m - 2) = (i.val - 2) + m by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod, if_pos (by omega : i.val - 2 < m - 1)]
        omega

private theorem lower_core_rotation {m : ℕ} (hm : 4 ≤ m) :
    gapAnchor (a m * c m) ⟨m - 1, by omega⟩ = finRotate (m + 1) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  change ((a m * c m) (((b m * c m) ^ (m - 1)) i)).val = _
  rw [native_ac_apply_val (by omega : 3 ≤ m), native_bc_pow_val (by omega : 2 ≤ m),
    finRotate_apply]
  simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
  by_cases hil : i = Fin.last m
  · subst i
    simp only [Fin.val_last, lt_self_iff_false, if_false,
      if_neg (by omega : ¬ m < m - 1)]
    rw [Nat.mod_self]
    omega
  · have hi : i.val < m := by
      have hb := i.isLt
      have hn : i.val ≠ m := fun h => hil (Fin.ext h)
      omega
    simp only [if_pos hi]
    rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
    by_cases hi0 : i.val = 0
    · rw [hi0, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      simp only [lt_self_iff_false, if_false]
      omega
    · have hmod : (i.val + (m - 1)) % m = i.val - 1 := by
        rw [show i.val + (m - 1) = (i.val - 1) + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, if_pos (by omega : i.val - 1 < m - 1)]
      omega


private theorem upper_core_one {m : ℕ} (hm : 4 ≤ m) :
    gapAnchor (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
      ⟨m - 2, by omega⟩ = 1 := by
  rw [gapAnchor, mul_assoc, ← gapAnchor, lower_core_swap hm]
  exact Equiv.swap_mul_self _ _

private theorem upper_core_rotation {m : ℕ} (hm : 4 ≤ m) :
    gapAnchor (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
      ⟨m - 1, by omega⟩ =
        Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * finRotate (m + 1) := by
  rw [gapAnchor, mul_assoc, ← gapAnchor, lower_core_rotation hm]

private theorem lower_last_circle {m : ℕ} (hm : 4 ≤ m) (v : Configuration m) :
    Circle (gapAnchor (a m * c m) ⟨m - 1, by omega⟩) v ↔ Circle 1 v := by
  have hr := circle_rotation (1 : Configuration m)
  simp only [one_mul] at hr
  rw [lower_core_rotation hm]
  simp only [Circle, hr]

private theorem upper_last_circle {m : ℕ} (hm : 4 ≤ m) (v : Configuration m) :
    Circle (gapAnchor (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
      ⟨m - 1, by omega⟩) v ↔
        Circle (Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) v := by
  rw [upper_core_rotation hm]
  simp only [Circle, circle_rotation]

private theorem lower_upper_gap_disjoint {m : ℕ} (hm : 4 ≤ m)
    (k : Fin m) (j : Fin (m - 2)) :
    Disjoint {v : Configuration m | Circle (gapAnchor (a m * c m) k) v}
      {v : Configuration m | Circle (upperPort j) v} := by
  by_cases hk : k.val < m - 2
  · simpa only [gapAnchor, lowerPort, upperPort] using
      native_t_cross_circle_disjoint hm ⟨k.val, hk⟩ j
  · rw [Set.disjoint_left]
    intro v hv hu
    have hu' : Circle
        (gapAnchor (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
          ⟨j.val, by have hj := j.isLt; omega⟩) v := by
      simpa only [Set.mem_setOf_eq, upperPort, lowerPort, gapAnchor, mul_assoc] using hu
    by_cases hk2 : k.val = m - 2
    · have he : k = ⟨m - 2, by omega⟩ := Fin.ext hk2
      rw [he, lower_core_swap hm] at hv
      have hv' := (upper_last_circle hm v).mpr hv
      have h := gap_circle_common (by omega : 3 ≤ m)
        (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v
        ⟨m - 1, by omega⟩ ⟨j.val, by have hj := j.isLt; omega⟩ hv' hu'
      have heq := congrArg Fin.val h
      have hj := j.isLt
      simp only [Fin.val_mk] at heq
      omega
    · have he : k = ⟨m - 1, by omega⟩ :=
        Fin.ext (by change k.val = m - 1; have hb := k.isLt; omega)
      rw [he] at hv
      have hv' : Circle
          (gapAnchor (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
            ⟨m - 2, by omega⟩) v := by
        rw [upper_core_one hm]
        exact (lower_last_circle hm v).mp hv
      have h := gap_circle_common (by omega : 3 ≤ m)
        (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v
        ⟨m - 2, by omega⟩ ⟨j.val, by have hj := j.isLt; omega⟩ hv' hu'
      have heq := congrArg Fin.val h
      have hj := j.isLt
      simp only [Fin.val_mk] at heq
      omega

/-- The two independently defined T supplier stars have exactly the two
complete actual core circles in common. -/
theorem native_t_core_intersection {m : ℕ} (hm : 4 ≤ m) (v : Configuration m) :
    (Star ((a m * c m) (Fin.last m))
        (residualList (a m * c m) : Cycle (Fin (m + 1))) v ∧
      Star ((Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) (Fin.last m))
        (residualList (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) :
          Cycle (Fin (m + 1))) v) ↔
      Circle (1 : Configuration m) v ∨
        Circle (Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) v := by
  rw [native_star_circle_partition (by omega : 3 ≤ m),
    native_star_circle_partition (by omega : 3 ≤ m)]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    by_cases hjn : j.val < m - 2
    · have hj' : Circle (upperPort ⟨j.val, hjn⟩) v := by
        simpa only [upperPort, lowerPort, gapAnchor, mul_assoc] using hj
      exact (Set.disjoint_left.mp (lower_upper_gap_disjoint hm i ⟨j.val, hjn⟩)
        hi hj').elim
    · by_cases hj2 : j.val = m - 2
      · have he : j = ⟨m - 2, by omega⟩ := Fin.ext hj2
        rw [he, upper_core_one hm] at hj
        exact Or.inl hj
      · have he : j = ⟨m - 1, by omega⟩ :=
          Fin.ext (by change j.val = m - 1; have hb := j.isLt; omega)
        rw [he] at hj
        exact Or.inr ((upper_last_circle hm v).mp hj)
  · intro h
    rcases h with h | h
    · refine ⟨⟨⟨m - 1, by omega⟩, (lower_last_circle hm v).mpr h⟩,
        ⟨⟨m - 2, by omega⟩, ?_⟩⟩
      rwa [upper_core_one hm]
    · refine ⟨⟨⟨m - 2, by omega⟩, ?_⟩,
        ⟨⟨m - 1, by omega⟩, (upper_last_circle hm v).mpr h⟩⟩
      rwa [lower_core_swap hm]

#print axioms native_t_core_intersection


/-- Complete lower-supplier circles and upper-supplier noncore circles form the
actual T cut-owner inventory. The lower family includes both shared cores. -/
def tCircleAnchor {m : ℕ} : Fin m ⊕ Fin (m - 2) → Configuration m
  | .inl i => gapAnchor (a m * c m) i
  | .inr j => Equiv.swap (0 : Fin (m + 1)) (Fin.last m) *
      (a m * c m * (b m * c m) ^ j.val)

private theorem upperPort_gap {m : ℕ} (j : Fin (m - 2)) :
    upperPort j = gapAnchor
      (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m))
      ⟨j.val, by have hj := j.isLt; omega⟩ := by
  simp only [upperPort, lowerPort, gapAnchor, mul_assoc]

theorem native_t_circle_owner_unique {m : ℕ} (hm : 4 ≤ m) (v : Configuration m)
    (p q : Fin m ⊕ Fin (m - 2))
    (hp : Circle (tCircleAnchor p) v) (hq : Circle (tCircleAnchor q) v) : p = q := by
  cases p with
  | inl i =>
    cases q with
    | inl j =>
      exact congrArg Sum.inl (gap_circle_common (by omega : 3 ≤ m)
        (a m * c m) v i j hp hq)
    | inr j =>
      exact (Set.disjoint_left.mp (lower_upper_gap_disjoint hm i j) hp hq).elim
  | inr i =>
    cases q with
    | inl j =>
      exact (Set.disjoint_left.mp (lower_upper_gap_disjoint hm j i) hq hp).elim
    | inr j =>
      change Circle (upperPort i) v at hp
      change Circle (upperPort j) v at hq
      rw [upperPort_gap] at hp hq
      have h := gap_circle_common (by omega : 3 ≤ m)
        (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v
        ⟨i.val, by have hi := i.isLt; omega⟩
        ⟨j.val, by have hj := j.isLt; omega⟩ hp hq
      have heq : i.val = j.val := congrArg (fun x : Fin m => x.val) h
      exact congrArg Sum.inr (Fin.ext heq)

/-- Every actual vertex in the independently defined two-star union belongs
to exactly one full circle from the T cut inventory. -/
theorem native_t_circle_partition {m : ℕ} (hm : 4 ≤ m) (v : Configuration m) :
    (Star ((a m * c m) (Fin.last m))
        (residualList (a m * c m) : Cycle (Fin (m + 1))) v ∨
      Star ((Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) (Fin.last m))
        (residualList (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) :
          Cycle (Fin (m + 1))) v) ↔
      ∃! p : Fin m ⊕ Fin (m - 2), Circle (tCircleAnchor p) v := by
  rw [native_star_circle_partition (by omega : 3 ≤ m),
    native_star_circle_partition (by omega : 3 ≤ m)]
  constructor
  · intro h
    have hex : ∃ p : Fin m ⊕ Fin (m - 2), Circle (tCircleAnchor p) v := by
      rcases h with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨.inl i, hi⟩
      · by_cases hjn : j.val < m - 2
        · refine ⟨.inr ⟨j.val, hjn⟩, ?_⟩
          simpa only [tCircleAnchor, gapAnchor, mul_assoc] using hj
        · by_cases hj2 : j.val = m - 2
          · have he : j = ⟨m - 2, by omega⟩ := Fin.ext hj2
            rw [he, upper_core_one hm] at hj
            exact ⟨.inl ⟨m - 1, by omega⟩, (lower_last_circle hm v).mpr hj⟩
          · have he : j = ⟨m - 1, by omega⟩ :=
              Fin.ext (by change j.val = m - 1; have hb := j.isLt; omega)
            rw [he] at hj
            have hc := (upper_last_circle hm v).mp hj
            refine ⟨.inl ⟨m - 2, by omega⟩, ?_⟩
            change Circle (gapAnchor (a m * c m) ⟨m - 2, by omega⟩) v
            rwa [lower_core_swap hm]
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, hp, fun q hq => native_t_circle_owner_unique hm v q p hq hp⟩
  · rintro ⟨p, hp, _⟩
    cases p with
    | inl i => exact Or.inl ⟨i, hp⟩
    | inr j =>
      refine Or.inr ⟨⟨j.val, by have hj := j.isLt; omega⟩, ?_⟩
      simpa only [tCircleAnchor, gapAnchor, mul_assoc] using hp

#print axioms native_t_circle_partition

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
