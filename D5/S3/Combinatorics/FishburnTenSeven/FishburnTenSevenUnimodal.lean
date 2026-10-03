/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal
   mirror-E: none(waiver:valley-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Avoiding both valley triples characterizes the increasing and decreasing peak blocks. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import D5.S3.Combinatorics.Fishburn.FishburnBasicAscents
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenUnimodal

open D5.S3.Combinatorics Nonnesting

theorem unimodal_iff (left right : List ℕ) (peak : ℕ)
    (hnodup : (left ++ peak :: right).Nodup)
    (hmax : ∀ value ∈ left ++ right, value < peak) :
    (¬ NonnestingDefs.Occurs [2, 1, 3] (left ++ peak :: right) ∧
      ¬ NonnestingDefs.Occurs [3, 1, 2] (left ++ peak :: right)) ↔
      left.Pairwise (· < ·) ∧ right.Pairwise (· > ·) := by
  let word := left ++ peak :: right
  have hleftnodup : left.Nodup := (List.nodup_append.mp hnodup).1
  have hrightnodup : right.Nodup :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).2
  have hmake (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3])
      (values : ℕ → ℕ)
      (hstep : ∀ rank, 1 ≤ rank → rank < 3 → values rank < values (rank + 1))
      (hsub : (pattern.map values).Sublist word) :
      ArrowWilfDefs.Contains pattern [] 3 word := by
    refine ⟨values, hstep, ?_, hsub, by simp⟩
    intro rank hlo hhi
    apply hsub.subset
    apply List.mem_map.mpr
    refine ⟨rank, hpattern.mem_iff.mpr ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  constructor
  · rintro ⟨h213, h312⟩
    constructor
    · apply List.pairwise_iff_forall_sublist.mpr
      intro first second hpair
      have hne : first ≠ second := by
        have hp := hleftnodup.sublist hpair
        simpa using hp
      by_contra hnot
      have hfirst := hpair.subset (show first ∈ [first, second] by simp)
      have hbound := hmax first (by simp [hfirst])
      have hsub : [first, second, peak].Sublist word :=
        hpair.append ((List.singleton_sublist.mpr (by simp) :
          [peak].Sublist (peak :: right)))
      let values : ℕ → ℕ := fun rank => if rank = 1 then second
        else if rank = 2 then first else peak
      apply h213
      change ArrowWilfDefs.Contains [2, 1, 3] [] 3 word
      apply hmake _ (by decide) values
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 := by omega
        rcases hc with rfl | rfl <;> simp only [values, ↓reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd] <;> omega
      · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
          Nat.reduceEqDiff] using hsub
    · apply List.pairwise_iff_forall_sublist.mpr
      intro first second hpair
      have hne : first ≠ second := by
        have hp := hrightnodup.sublist hpair
        simpa using hp
      by_contra hnot
      have hsecond := hpair.subset (show second ∈ [first, second] by simp)
      have hbound := hmax second (by simp [hsecond])
      have hsub : [peak, first, second].Sublist word :=
        (hpair.cons_cons peak).trans (List.sublist_append_right left (peak :: right))
      let values : ℕ → ℕ := fun rank => if rank = 1 then first
        else if rank = 2 then second else peak
      apply h312
      change ArrowWilfDefs.Contains [3, 1, 2] [] 3 word
      apply hmake _ (by decide) values
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 := by omega
        rcases hc with rfl | rfl <;> simp only [values, ↓reduceIte,
          Nat.reduceEqDiff, Nat.reduceAdd] <;> omega
      · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
          Nat.reduceEqDiff] using hsub
  · rintro ⟨hleft, hright⟩
    have hlength : word.length = left.length + 1 + right.length := by
      simp only [word, List.length_append, List.length_cons]
      omega
    have hbefore (index : ℕ) (hindex : index < left.length) :
        word.getD index 0 = left.getD index 0 := List.getD_append _ _ _ _ hindex
    have hat : word.getD left.length 0 = peak := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hafter (index : ℕ) (hindex : left.length < index) :
        word.getD index 0 = right.getD (index - left.length - 1) 0 := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hdiff : index - left.length = (index - left.length - 1) + 1 := by omega
      rw [hdiff]
      rfl
    have hbound (index : ℕ) (hindex : index < word.length)
        (hne : index ≠ left.length) : word.getD index 0 < peak := by
      by_cases hlt : index < left.length
      · rw [hbefore index hlt]
        apply hmax
        apply List.mem_append_left
        rw [List.getD_eq_getElem left 0 hlt]
        exact List.getElem_mem hlt
      · rw [hafter index (by omega)]
        apply hmax
        apply List.mem_append_right
        rw [List.getD_eq_getElem right 0 (by omega)]
        exact List.getElem_mem (by omega)
    have hindices (first middle last : ℕ)
        (hsub : [first, middle, last].Sublist word) :
        ∃ earlier center later, earlier < center ∧ center < later ∧ later < word.length ∧
          word.getD earlier 0 = first ∧ word.getD center 0 = middle ∧
          word.getD later 0 = last := by
      obtain ⟨positions, hpositions⟩ :=
        List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let earlier := positions ⟨0, by simp⟩
      let center := positions ⟨1, by simp⟩
      let later := positions ⟨2, by simp⟩
      refine ⟨earlier.val, center.val, later.val, ?_, ?_, later.is_lt, ?_, ?_, ?_⟩
      · exact positions.strictMono (by change (0 : ℕ) < 1; omega)
      · exact positions.strictMono (by change (1 : ℕ) < 2; omega)
      · rw [List.getD_eq_get]
        simpa [earlier] using (hpositions ⟨0, by simp⟩).symm
      · rw [List.getD_eq_get]
        simpa [center] using (hpositions ⟨1, by simp⟩).symm
      · rw [List.getD_eq_get]
        simpa [later] using (hpositions ⟨2, by simp⟩).symm
    have hnovalley (first middle last : ℕ) (hlower : middle < first)
        (hupper : middle < last) (hsub : [first, middle, last].Sublist word) : False := by
      obtain ⟨earlier, center, later, hec, hcl, hb, hvfirst, hvmiddle, hvlast⟩ :=
        hindices first middle last hsub
      rcases lt_trichotomy center left.length with hbeforepeak | heq | hafterpeak
      · have hinc := List.pairwise_iff_getElem.mp hleft earlier center
          (by omega) hbeforepeak hec
        have hfirstval := hbefore earlier (by omega)
        have hmiddleval := hbefore center hbeforepeak
        rw [List.getD_eq_getElem left 0 (by omega)] at hfirstval
        rw [List.getD_eq_getElem left 0 hbeforepeak] at hmiddleval
        omega
      · have hpeak := hat
        have hlast := hbound later hb (by omega)
        subst center
        omega
      · have hdec := List.pairwise_iff_getElem.mp hright
          (center - left.length - 1) (later - left.length - 1)
          (by omega) (by omega) (by omega)
        have hmiddleval := hafter center hafterpeak
        have hlastval := hafter later (by omega)
        rw [List.getD_eq_getElem right 0 (by omega)] at hmiddleval hlastval
        omega
    constructor
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 := hstep 1 (by omega) (by change 1 < 3; omega)
      have h23 := hstep 2 (by omega) (by change 2 < 3; omega)
      norm_num only [Nat.reduceAdd] at h12 h23
      simp only [List.map_cons, List.map_nil] at hsub
      exact hnovalley _ _ _ h12 (lt_trans h12 h23) hsub
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 := hstep 1 (by omega) (by change 1 < 3; omega)
      have h23 := hstep 2 (by omega) (by change 2 < 3; omega)
      norm_num only [Nat.reduceAdd] at h12 h23
      simp only [List.map_cons, List.map_nil] at hsub
      exact hnovalley _ _ _ (lt_trans h12 h23) h12 hsub

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenUnimodal
