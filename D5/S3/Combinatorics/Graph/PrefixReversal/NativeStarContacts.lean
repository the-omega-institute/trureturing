/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete insertion stars have unique native contacts with the two-star core. -/

import D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open Equiv

private def contactLabel {m : ℕ} (j : Fin (m - 2))
    (i : Fin (m + 1)) : Fin (m + 1) :=
  ⟨if i.val < j.val + 1 then i.val + 1
    else if i.val = j.val + 1 then m
    else if i.val < m then i.val else 0, by
    have hj := j.isLt
    split_ifs <;> omega⟩

private theorem contactLabel_injective {m : ℕ} (j : Fin (m - 2)) :
    Function.Injective (contactLabel j) := by
  intro i k h
  have hj := j.isLt
  have he := congrArg Fin.val h
  simp only [contactLabel, Fin.val_mk] at he
  apply Fin.ext
  split_ifs at he <;> omega

/-- The literal tuple is `(1,...,j+1,m,j+2,...,m-1,0)`; the finite index
therefore enumerates precisely the contact labels from 1 through m-2. -/
noncomputable def contactAnchor {m : ℕ} (j : Fin (m - 2)) : Configuration m :=
  Equiv.ofBijective (contactLabel j)
    ⟨contactLabel_injective j, Finite.surjective_of_injective (contactLabel_injective j)⟩

private theorem contactAnchor_val {m : ℕ} (j : Fin (m - 2))
    (i : Fin (m + 1)) :
    (contactAnchor j i).val = if i.val < j.val + 1 then i.val + 1
      else if i.val = j.val + 1 then m
      else if i.val < m then i.val else 0 := rfl

private theorem contactAnchor_last {m : ℕ} (j : Fin (m - 2)) :
    contactAnchor j (Fin.last m) = 0 := by
  have hj := j.isLt
  apply Fin.ext
  rw [contactAnchor_val]
  simp only [Fin.val_last, Fin.val_zero]
  split_ifs <;> omega

private theorem contactAnchor_first {m : ℕ} (j : Fin (m - 2)) :
    contactAnchor j 0 = (1 : Fin (m + 1)) := by
  have hj := j.isLt
  apply Fin.ext
  rw [contactAnchor_val]
  simp only [Fin.val_zero, zero_lt_one, Nat.zero_lt_succ, if_pos,
    zero_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m + 1)]

private theorem contactAnchor_penultimate {m : ℕ} (j : Fin (m - 2)) :
    contactAnchor j ⟨m - 1, by have hj := j.isLt; omega⟩ =
      ⟨m - 1, by have hj := j.isLt; omega⟩ := by
  have hj := j.isLt
  apply Fin.ext
  rw [contactAnchor_val]
  simp only [Fin.val_mk]
  split_ifs <;> omega

private theorem contactAnchor_mark {m : ℕ} (j : Fin (m - 2)) :
    contactAnchor j ⟨j.val + 1, by have hj := j.isLt; omega⟩ = Fin.last m := by
  apply Fin.ext
  rw [contactAnchor_val]
  simp only [Fin.val_mk, lt_self_iff_false, if_false, if_true, Fin.val_last]

private theorem contact_mark_mem {m : ℕ} (j : Fin (m - 2)) :
    Fin.last m ∈ residualList (contactAnchor j) := by
  refine List.mem_ofFn.mpr ⟨⟨j.val + 1, by have hj := j.isLt; omega⟩, ?_⟩
  exact contactAnchor_mark j

private theorem contact_residual_next {m : ℕ} (j : Fin (m - 2)) :
    ((residualList (contactAnchor j)).next (Fin.last m) (contact_mark_mem j)).val =
      j.val + 2 := by
  have hj := j.isLt
  have hn := List.next_getElem (List.ofFn fun i : Fin m => contactAnchor j i.castSucc)
    (native_residual_nodup _) (j.val + 1) (by simp only [List.length_ofFn]; omega)
  simp only [List.getElem_ofFn, List.length_ofFn] at hn
  have hmark : contactAnchor j (⟨j.val + 1, by omega⟩ : Fin m).castSucc =
      Fin.last m := contactAnchor_mark j
  simp only [hmark] at hn
  change ((List.ofFn fun i : Fin m => contactAnchor j i.castSucc).next
    (Fin.last m) _).val = _
  rw [hn, contactAnchor_val]
  simp only [Fin.val_castSucc, Fin.val_mk,
    Nat.mod_eq_of_lt (by omega : j.val + 1 + 1 < m)]
  split_ifs <;> omega

private theorem contact_residual_prev {m : ℕ} (j : Fin (m - 2)) :
    ((residualList (contactAnchor j)).prev (Fin.last m) (contact_mark_mem j)).val =
      j.val + 1 := by
  have hj := j.isLt
  have hp := List.prev_getElem (List.ofFn fun i : Fin m => contactAnchor j i.castSucc)
    (native_residual_nodup _) (j.val + 1) (by simp only [List.length_ofFn]; omega)
  simp only [List.getElem_ofFn, List.length_ofFn] at hp
  have hmark : contactAnchor j (⟨j.val + 1, by omega⟩ : Fin m).castSucc =
      Fin.last m := contactAnchor_mark j
  simp only [hmark] at hp
  change ((List.ofFn fun i : Fin m => contactAnchor j i.castSucc).prev
    (Fin.last m) _).val = _
  rw [hp, contactAnchor_val]
  simp only [Fin.val_castSucc, Fin.val_mk,
    show j.val + 1 + (m - 1) = j.val + m by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val < m)]
  split_ifs <;> omega

private theorem residual_common {α : Type} [DecidableEq α]
    {C L K : Cycle α} (hL : C = L ∨ C = L.reverse)
    (hK : C = K ∨ C = K.reverse) : L = K ∨ L = K.reverse := by
  rcases hL with hL | hL <;> rcases hK with hK | hK
  · exact Or.inl (hL.symm.trans hK)
  · exact Or.inr (hL.symm.trans hK)
  · right
    have h := congrArg Cycle.reverse (hL.symm.trans hK)
    simpa only [Cycle.reverse_reverse] using h
  · left
    have h := congrArg Cycle.reverse (hL.symm.trans hK)
    simpa only [Cycle.reverse_reverse] using h

private theorem list_circle_neighbours {α : Type} [DecidableEq α]
    (L K : List α) (hL : L.Nodup) (hK : K.Nodup)
    (hc : (L : Cycle α) = (K : Cycle α) ∨ (L : Cycle α) = (K : Cycle α).reverse)
    (x : α) (hxL : x ∈ L) (hxK : x ∈ K) :
    (L.next x hxL = K.next x hxK ∧ L.prev x hxL = K.prev x hxK) ∨
      (L.next x hxL = K.prev x hxK ∧ L.prev x hxL = K.next x hxK) := by
  rcases hc with hc | hc
  · left
    exact ⟨List.isRotated_next_eq (Cycle.coe_eq_coe.mp hc) hL hxL,
      List.isRotated_prev_eq (Cycle.coe_eq_coe.mp hc) hL hxL⟩
  · right
    have hr : L.IsRotated K.reverse := Cycle.coe_eq_coe.mp hc
    exact ⟨(List.isRotated_next_eq hr hL hxL).trans
      (List.next_reverse_eq_prev K hK x hxK),
      (List.isRotated_prev_eq hr hL hxL).trans
      (List.prev_reverse_eq_next K hK x hxK)⟩

/-- Different concrete contacts specify disjoint complete deletion stars. -/
theorem contact_stars_pairwise_disjoint {m : ℕ} (i j : Fin (m - 2)) (hij : i ≠ j) :
    Disjoint {v : Configuration m | SupplierStar (contactAnchor i) v}
      {v : Configuration m | SupplierStar (contactAnchor j) v} := by
  rw [Set.disjoint_left]
  intro v hi hj
  unfold SupplierStar D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement.Star at hi hj
  rw [contactAnchor_last] at hi hj
  have hc := residual_common hi hj
  have hn := list_circle_neighbours (residualList (contactAnchor i))
    (residualList (contactAnchor j)) (native_residual_nodup _) (native_residual_nodup _)
    hc (Fin.last m) (contact_mark_mem i) (contact_mark_mem j)
  rcases hn with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · have he := congrArg Fin.val hn
    rw [contact_residual_next, contact_residual_next] at he
    exact hij (Fin.ext (by omega))
  · have he := congrArg Fin.val hn
    have he' := congrArg Fin.val hp
    rw [contact_residual_next, contact_residual_prev] at he
    rw [contact_residual_prev, contact_residual_next] at he'
    omega

#print axioms contact_stars_pairwise_disjoint

private theorem upperPort_val {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (i : Fin (m + 1)) :
    (upperPort j i).val = if i.val = m then m else
      if (i.val + j.val) % m = m - 2 then 0 else
        if (i.val + j.val) % m = m - 1 then 1 else (i.val + j.val) % m + 2 := by
  by_cases hi : i.val = m
  · have hie : i = Fin.last m := Fin.ext hi
    rw [hie, native_upper_last hm j]
    simp
  · have him : i.val < m := by have hb := i.isLt; omega
    have hmod : (i.val + j.val) % m < m := Nat.mod_lt _ (by omega)
    have hv := native_lowerPort_val (by omega : 3 ≤ m) j i him
    have hn0 : lowerPort j i ≠ 0 := by
      intro he
      have he' := congrArg Fin.val he
      rw [hv] at he'
      simp only [Fin.val_zero] at he'
      split_ifs at he' <;> omega
    have hnm : lowerPort j i = Fin.last m ↔ (i.val + j.val) % m = m - 2 := by
      constructor
      · intro he
        have he' := congrArg Fin.val he
        rw [hv] at he'
        simp only [Fin.val_last] at he'
        split_ifs at he' <;> omega
      · intro he
        apply Fin.ext
        rw [hv, he, if_pos (by omega : m - 2 < m - 1)]
        simp only [Fin.val_last]
        omega
    change ((swap (0 : Fin (m + 1)) (Fin.last m)) (lowerPort j i)).val = _
    simp only [swap_apply_def, if_neg hn0, hnm, if_neg hi]
    split_ifs <;> first | rfl | (rw [hv]; split_ifs <;> omega)

private theorem contact_upper_rotation {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    contactAnchor j = upperPort j *
      finCycle (⟨m - 1 - j.val, by have hj := j.isLt; omega⟩ : Fin (m + 1)) := by
  have hj := j.isLt
  apply Equiv.ext
  intro i
  have hi := i.isLt
  apply Fin.ext
  rw [contactAnchor_val, Equiv.Perm.mul_apply, upperPort_val hm j]
  simp only [finCycle_apply, Fin.val_add, Fin.val_mk]
  by_cases hi0 : i.val = 0
  · simp only [hi0, zero_add]
    rw [Nat.mod_eq_of_lt (by omega : m - 1 - j.val < m + 1),
      show m - 1 - j.val + j.val = m - 1 by omega,
      Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    split_ifs <;> omega
  · by_cases hib : i.val < j.val + 1
    · have ht : (i.val + (m - 1 - j.val)) % (m + 1) = i.val + (m - 1 - j.val) :=
        Nat.mod_eq_of_lt (by omega)
      rw [ht]
      have hq : (i.val + (m - 1 - j.val) + j.val) % m = i.val - 1 := by
        rw [show i.val + (m - 1 - j.val) + j.val = (i.val - 1) + m by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hq]
      split_ifs <;> omega
    · by_cases hie : i.val = j.val + 1
      · rw [hie, show j.val + 1 + (m - 1 - j.val) = m by omega,
          Nat.mod_eq_of_lt (by omega : m < m + 1)]
        split_ifs <;> omega
      · have ht : (i.val + (m - 1 - j.val)) % (m + 1) = i.val - j.val - 2 := by
          rw [show i.val + (m - 1 - j.val) = (i.val - j.val - 2) + (m + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [ht]
        have hq : (i.val - j.val - 2 + j.val) % m = i.val - 2 := by
          rw [show i.val - j.val - 2 + j.val = i.val - 2 by omega,
            Nat.mod_eq_of_lt (by omega)]
        rw [hq]
        split_ifs <;> omega

private theorem contact_circle_upper {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (v : Configuration m) : Circle (contactAnchor j) v ↔ Circle (upperPort j) v := by
  rw [contact_upper_rotation hm j]
  simp only [Circle, native_configurationCycle_rotation]

private theorem circle_in_star {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (hv : Circle z v) : SupplierStar z v := by
  apply (native_star_circle_partition hm z v).mpr
  refine ⟨⟨0, by omega⟩, ?_⟩
  simpa only [gapAnchor, pow_zero, mul_one] using hv

private theorem lower_mark_mem {m : ℕ} (hm : 4 ≤ m) :
    Fin.last m ∈ residualList (a m * c m) := by
  refine List.mem_ofFn.mpr ⟨⟨m - 2, by omega⟩, ?_⟩
  simpa only [lowerPort, pow_zero, mul_one, Nat.sub_zero, Fin.castSucc_mk] using
    native_lower_m_position hm (⟨0, by omega⟩ : Fin (m - 2))

private theorem lower_residual_neighbours {m : ℕ} (hm : 4 ≤ m) :
    ((residualList (a m * c m)).next (Fin.last m) (lower_mark_mem hm)).val = 1 ∧
      ((residualList (a m * c m)).prev (Fin.last m) (lower_mark_mem hm)).val = m - 1 := by
  have hmark : (a m * c m) (⟨m - 2, by omega⟩ : Fin m).castSucc = Fin.last m := by
    simpa only [lowerPort, pow_zero, mul_one, Nat.sub_zero, Fin.castSucc_mk] using
      native_lower_m_position hm (⟨0, by omega⟩ : Fin (m - 2))
  constructor
  · have hn := List.next_getElem (List.ofFn fun i : Fin m => (a m * c m) i.castSucc)
      (native_residual_nodup _) (m - 2) (by simp only [List.length_ofFn]; omega)
    simp only [List.getElem_ofFn, List.length_ofFn, hmark] at hn
    change ((List.ofFn fun i : Fin m => (a m * c m) i.castSucc).next
      (Fin.last m) _).val = _
    rw [hn, native_ac_apply_val (by omega : 3 ≤ m)]
    simp only [Fin.val_castSucc, show m - 2 + 1 = m - 1 by omega,
      Nat.mod_eq_of_lt (by omega : m - 1 < m), lt_self_iff_false, if_false]
    omega
  · have hp := List.prev_getElem (List.ofFn fun i : Fin m => (a m * c m) i.castSucc)
      (native_residual_nodup _) (m - 2) (by simp only [List.length_ofFn]; omega)
    simp only [List.getElem_ofFn, List.length_ofFn, hmark] at hp
    change ((List.ofFn fun i : Fin m => (a m * c m) i.castSucc).prev
      (Fin.last m) _).val = _
    rw [hp, native_ac_apply_val (by omega : 3 ≤ m)]
    simp only [Fin.val_castSucc, show m - 2 + (m - 1) = (m - 3) + m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : m - 3 < m),
      if_pos (by omega : m - 3 < m - 1)]
    omega

/-- None of the remaining concrete insertion stars meets the lower supplier. -/
theorem contact_star_lower_disjoint {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    Disjoint {v : Configuration m | SupplierStar (contactAnchor j) v}
      {v : Configuration m | SupplierStar (a m * c m) v} := by
  rw [Set.disjoint_left]
  intro v hc hl
  unfold SupplierStar D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement.Star at hc hl
  have hlast : (a m * c m) (Fin.last m) = 0 := by
    simpa only [lowerPort, pow_zero, mul_one] using
      native_lower_last hm (⟨0, by omega⟩ : Fin (m - 2))
  rw [contactAnchor_last] at hc
  rw [hlast] at hl
  have he := residual_common hc hl
  have hn := list_circle_neighbours (residualList (contactAnchor j))
    (residualList (a m * c m)) (native_residual_nodup _) (native_residual_nodup _)
    he (Fin.last m) (contact_mark_mem j) (lower_mark_mem hm)
  rcases hn with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · have h := congrArg Fin.val hn
    rw [contact_residual_next, (lower_residual_neighbours hm).1] at h
    omega
  · have h := congrArg Fin.val hn
    have h' := congrArg Fin.val hp
    rw [contact_residual_next, (lower_residual_neighbours hm).2] at h
    rw [contact_residual_prev, (lower_residual_neighbours hm).1] at h'
    omega

/-- The upper supplier meets each remaining star in exactly its actual contact circle. -/
theorem contact_star_upper_intersection {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (v : Configuration m) :
    (SupplierStar (contactAnchor j) v ∧
      SupplierStar (swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v) ↔
      Circle (contactAnchor j) v := by
  constructor
  · rintro ⟨hc, hu⟩
    have hpartition := (native_t_circle_partition hm v).mp (Or.inr hu)
    obtain ⟨p, hp, _⟩ := hpartition
    cases p with
    | inl i =>
      have hl : SupplierStar (a m * c m) v :=
        (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) v).mpr ⟨i, hp⟩
      exact (Set.disjoint_left.mp (contact_star_lower_disjoint hm j) hc hl).elim
    | inr k =>
      have hk : Circle (contactAnchor k) v := (contact_circle_upper hm k v).mpr hp
      have hs := circle_in_star (by omega : 3 ≤ m) (contactAnchor k) v hk
      have hjk : j = k := by
        by_contra hne
        exact Set.disjoint_left.mp (contact_stars_pairwise_disjoint j k hne) hc hs
      exact hjk.symm ▸ hk
  · intro hc
    refine ⟨circle_in_star (by omega : 3 ≤ m) (contactAnchor j) v hc, ?_⟩
    apply (native_star_circle_partition (by omega : 3 ≤ m)
      (swap (0 : Fin (m + 1)) (Fin.last m) * (a m * c m)) v).mpr
    refine ⟨⟨j.val, by have hj := j.isLt; omega⟩, ?_⟩
    simpa only [upperPort, lowerPort, gapAnchor, mul_assoc] using
      (contact_circle_upper hm j v).mp hc

/-- The independently specified two-star core has exactly one full-circle contact. -/
theorem contact_star_core_intersection {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2))
    (v : Configuration m) :
    (CoreDomain m v ∧ SupplierStar (contactAnchor j) v) ↔ Circle (contactAnchor j) v := by
  constructor
  · rintro ⟨hl | hu, hc⟩
    · exact (Set.disjoint_left.mp (contact_star_lower_disjoint hm j) hc hl).elim
    · exact (contact_star_upper_intersection hm j v).mp ⟨hc, hu⟩
  · intro hc
    obtain ⟨hs, hu⟩ := (contact_star_upper_intersection hm j v).mpr hc
    exact ⟨Or.inr hu, hs⟩

private theorem circle_generator_mem {m : ℕ} (hm : 3 ≤ m) (z g : Configuration m)
    (hg : g = a m ∨ g = b m) : Circle z (z * g) := by
  rcases hg with rfl | rfl
  · obtain ⟨w, _, _, _, hs⟩ := native_a_complement hm z
    exact (hs (z * a m)).mp w.end_mem_support
  · obtain ⟨w, _, _, _, hs⟩ := native_b_complement hm z
    exact (hs (z * b m)).mp w.end_mem_support

/-- The literal b contact edge is among the retained native edges of the T core. -/
theorem contact_b_edge_not_deleted {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) :
    ¬ CoreDeletedEdge m s(contactAnchor j, contactAnchor j * b m) := by
  rintro ⟨p, hp⟩
  have hc : SupplierStar (contactAnchor j) (contactAnchor j) :=
    circle_in_star (by omega : 3 ≤ m) _ _ (Or.inl rfl)
  cases p with
  | inl i =>
    have hstart : SupplierStar (a m * c m) (NativeCoreSplicing.cutStart (.inl i)) := by
      apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) _).mpr
      exact ⟨i, (native_cut_circle_iff hm (.inl i) _).mp (Or.inl rfl)⟩
    have hg : NativeCoreSplicing.cutGenerator (.inl i) = a m ∨
        NativeCoreSplicing.cutGenerator (.inl i) = b m := by
      simp only [NativeCoreSplicing.cutGenerator]
      split <;> simp
    have hend : SupplierStar (a m * c m)
        (NativeCoreSplicing.cutStart (.inl i) * NativeCoreSplicing.cutGenerator (.inl i)) := by
      apply (native_star_circle_partition (by omega : 3 ≤ m) (a m * c m) _).mpr
      exact ⟨i, (native_cut_circle_iff hm (.inl i) _).mp
        (circle_generator_mem (by omega : 3 ≤ m) _ _ hg)⟩
    rcases Sym2.eq_iff.mp hp with ⟨he, _⟩ | ⟨he, _⟩
    · exact Set.disjoint_left.mp (contact_star_lower_disjoint hm j) hc (he.symm ▸ hstart)
    · exact Set.disjoint_left.mp (contact_star_lower_disjoint hm j) hc (he.symm ▸ hend)
  | inr k =>
    have hstart : NativeCoreSplicing.cutStart (.inr k) (Fin.last m) = Fin.last m :=
      native_upper_last hm k
    have hend : (NativeCoreSplicing.cutStart (.inr k) *
        NativeCoreSplicing.cutGenerator (.inr k)) (Fin.last m) = Fin.last m := by
      change upperPort k (b m (Fin.last m)) = Fin.last m
      have hb : b m (Fin.last m) = Fin.last m := by
        apply Fin.ext
        rw [b_apply]
        simp
      rw [hb, native_upper_last hm k]
    rcases Sym2.eq_iff.mp hp with ⟨he, _⟩ | ⟨he, _⟩
    · have h := congrArg (fun z : Configuration m => (z (Fin.last m)).val) he
      rw [contactAnchor_last, hstart] at h
      simp only [Fin.val_zero, Fin.val_last] at h
      omega
    · have h := congrArg (fun z : Configuration m => (z (Fin.last m)).val) he
      rw [contactAnchor_last, hend] at h
      simp only [Fin.val_zero, Fin.val_last] at h
      omega

#print axioms contact_star_lower_disjoint
#print axioms contact_star_upper_intersection
#print axioms contact_star_core_intersection
#print axioms contact_b_edge_not_deleted

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
