/- GID: D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification
   mirror-E: none(waiver:tall-entry-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Pattern avoidance forces the tall entries into an initial block and the maximum. -/

import D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionBasic
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion

open D5.S3.Combinatorics
open FranklinInversionDefs

def Tall (p : List ℕ) (index : ℕ) : Prop :=
  ∃ later, index < later ∧ later < p.length ∧ p.getD later 0 < p.getD index 0

theorem tall_ltrMax (p : List ℕ) (hnodup : p.Nodup)
    (h321 : ¬ Nonnesting.NonnestingDefs.Occurs [3, 2, 1] p)
    (index : ℕ) (hi : index < p.length) (htall : Tall p index) :
    ArrowWilfDefs.IsLtrMax p index := by
  obtain ⟨later, hil, hl, hli⟩ := htall
  intro prior hpi
  have hp : prior < p.length := by omega
  by_contra hnot
  have hne : p.getD prior 0 ≠ p.getD index 0 := by
    rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hi]
    intro heq
    have := hnodup.getElem_inj_iff.mp heq
    omega
  have hip : p.getD index 0 < p.getD prior 0 := by omega
  apply h321
  let values : ℕ → ℕ := fun rank =>
    if rank = 1 then p.getD later 0 else
      if rank = 2 then p.getD index 0 else p.getD prior 0
  refine ⟨values, ?_, ?_, ?_, by simp⟩
  · intro rank hpositive hbound
    have : rank = 1 ∨ rank = 2 := by
      simp [Nonnesting.NonnestingDefs.letters] at hbound
      omega
    rcases this with rfl | rfl
    · simpa [values] using hli
    · simpa [values] using hip
  · intro rank hpositive hbound
    have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
      simp [Nonnesting.NonnestingDefs.letters] at hbound
      omega
    rcases this with rfl | rfl | rfl
    · change p.getD later 0 ∈ p
      rw [List.getD_eq_getElem _ _ hl]
      exact List.getElem_mem hl
    · change p.getD index 0 ∈ p
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · change p.getD prior 0 ∈ p
      rw [List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
  · change [p.getD prior 0, p.getD index 0, p.getD later 0].Sublist p
    let embedding : Fin 3 ↪o Fin p.length := OrderEmbedding.ofMapLEIff
      (fun rank => if rank.val = 0 then ⟨prior, hp⟩ else
        if rank.val = 1 then ⟨index, hi⟩ else ⟨later, hl⟩)
      (by intro left right; fin_cases left <;> fin_cases right <;> simp <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨embedding, ?_⟩
    intro rank
    fin_cases rank <;> simp [embedding, hp, hi, hl]

theorem tall_block_structure (p : List ℕ) (n : ℕ)
    (hperm : p.Perm (List.range' 1 n)) (hindecomp : Indecomposable p)
    (h321 : ¬ Nonnesting.NonnestingDefs.Occurs [3, 2, 1] p)
    (h1342 : ¬ Nonnesting.NonnestingDefs.Occurs [1, 3, 4, 2] p)
    (hn : 1 ≤ n) (hnotstar : p.getD 0 0 ≠ n) :
    ∃ r m later, 1 ≤ r ∧ r ≤ m ∧ m < p.length ∧ p.getD m 0 = n ∧
      m < later ∧ later < p.length ∧ p.getD later 0 < p.getD 0 0 ∧
      ∀ index < p.length, Tall p index ↔ index < r ∨ index = m := by
  classical
  have hlength : p.length = n := by simpa using hperm.length_eq
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
  have hbounds (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hmem := hperm.mem_iff.mp (List.getElem_mem hi)
    rw [List.getD_eq_getElem _ _ hi]
    simp only [List.mem_range', Nat.one_mul] at hmem
    obtain ⟨offset, hoff, heq⟩ := hmem
    omega
  have hneq (left right : ℕ) (hl : left < p.length) (hr : right < p.length)
      (hne : left ≠ right) : p.getD left 0 ≠ p.getD right 0 := by
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hr]
    intro heq
    exact hne (hnodup.getElem_inj_iff.mp heq)
  have hshort (left right : ℕ) (hl : left < p.length) (hr : right < p.length)
      (hlr : left < right) (hleft : ¬ Tall p left) :
      p.getD left 0 < p.getD right 0 := by
    have hne := hneq left right hl hr (by omega)
    have hnot : ¬ p.getD right 0 < p.getD left 0 := by
      intro hlt
      exact hleft ⟨right, hlr, hr, hlt⟩
    omega
  have hcross (cut : ℕ) (hc : 1 ≤ cut) (hproper : cut < p.length) :
      ∃ left right, left < cut ∧ cut ≤ right ∧ right < p.length ∧
        p.getD right 0 < p.getD left 0 := by
    have hprefixnodup : (p.take cut).Nodup := hnodup.sublist (List.take_sublist cut p)
    have hprefixlength : (p.take cut).length = cut := by simp; omega
    have hhigh : ¬ p.take cut ⊆ List.range' 1 cut := by
      intro hsub
      have hsubperm := List.subperm_of_subset hprefixnodup hsub
      exact hindecomp cut hc hproper
        (hsubperm.perm_of_length_le (by simp [hprefixlength]))
    have hlow : ¬ List.range' 1 cut ⊆ p.take cut := by
      intro hsub
      have hsubperm := List.subperm_of_subset List.nodup_range' hsub
      exact hindecomp cut hc hproper
        (hsubperm.perm_of_length_le (by simp [hprefixlength])).symm
    simp only [List.subset_def, not_forall] at hhigh hlow
    obtain ⟨high, hhighmem, hhighnot⟩ := hhigh
    obtain ⟨low, hlowmem, hlownot⟩ := hlow
    obtain ⟨left, hl, hleft⟩ := List.mem_take_iff_getElem.mp hhighmem
    have hlowbounds : 1 ≤ low ∧ low ≤ cut := by
      simp only [List.mem_range', Nat.one_mul] at hlowmem
      obtain ⟨offset, hoff, heq⟩ := hlowmem
      omega
    have hlowfull : low ∈ p := by
      apply hperm.mem_iff.mpr
      simp only [List.mem_range', Nat.one_mul]
      refine ⟨low - 1, by omega, by omega⟩
    obtain ⟨right, hr, hright⟩ := List.mem_iff_getElem.mp hlowfull
    have hl' : left < p.length := by omega
    have hhighpositive : 1 ≤ high := by
      have := (hbounds left hl').1
      rwa [List.getD_eq_getElem _ _ hl', hleft] at this
    have hhighbound : cut < high := by
      simp only [List.mem_range', Nat.one_mul, not_exists, not_and] at hhighnot
      by_contra hnot
      have := hhighnot (high - 1) (by omega)
      omega
    refine ⟨left, right, by omega, ?_, hr, ?_⟩
    · by_contra hnot
      apply hlownot
      exact List.mem_take_iff_getElem.mpr ⟨right, by omega, hright⟩
    · rw [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hr, hleft, hright]
      omega
  have hquad (first second third fourth : ℕ)
      (hf : first < p.length) (hs : second < p.length)
      (ht : third < p.length) (hfourth : fourth < p.length)
      (hfs : first < second) (hst : second < third) (htf : third < fourth)
      (hfv : p.getD first 0 < p.getD fourth 0)
      (hvs : p.getD fourth 0 < p.getD second 0)
      (hsv : p.getD second 0 < p.getD third 0) : False := by
    apply h1342
    let values : ℕ → ℕ := fun rank =>
      if rank = 1 then p.getD first 0 else if rank = 2 then p.getD fourth 0 else
        if rank = 3 then p.getD second 0 else p.getD third 0
    refine ⟨values, ?_, ?_, ?_, by simp⟩
    · intro rank hpositive hbound
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
        simp [Nonnesting.NonnestingDefs.letters] at hbound
        omega
      rcases this with rfl | rfl | rfl
      · simpa [values] using hfv
      · simpa [values] using hvs
      · simpa [values] using hsv
    · intro rank hpositive hbound
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        simp [Nonnesting.NonnestingDefs.letters] at hbound
        omega
      rcases this with rfl | rfl | rfl | rfl
      · change p.getD first 0 ∈ p
        rw [List.getD_eq_getElem _ _ hf]
        exact List.getElem_mem hf
      · change p.getD fourth 0 ∈ p
        rw [List.getD_eq_getElem _ _ hfourth]
        exact List.getElem_mem hfourth
      · change p.getD second 0 ∈ p
        rw [List.getD_eq_getElem _ _ hs]
        exact List.getElem_mem hs
      · change p.getD third 0 ∈ p
        rw [List.getD_eq_getElem _ _ ht]
        exact List.getElem_mem ht
    · change [p.getD first 0, p.getD second 0, p.getD third 0, p.getD fourth 0].Sublist p
      let embedding : Fin 4 ↪o Fin p.length := OrderEmbedding.ofMapLEIff
        (fun rank => if rank.val = 0 then ⟨first, hf⟩ else
          if rank.val = 1 then ⟨second, hs⟩ else
            if rank.val = 2 then ⟨third, ht⟩ else ⟨fourth, hfourth⟩)
        (by intro left right; fin_cases left <;> fin_cases right <;> simp <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨embedding, ?_⟩
      intro rank
      fin_cases rank <;> simp [embedding, hf, hs, ht, hfourth]
  have hnmem : n ∈ p := by
    apply hperm.mem_iff.mpr
    simpa using hn
  let m := p.idxOf n
  have hm : m < p.length := List.idxOf_lt_length_iff.mpr hnmem
  have hmvalue : p.getD m 0 = n := by
    rw [List.getD_eq_getElem _ _ hm]
    exact List.getElem_idxOf hm
  have hmpositive : 0 < m := by
    by_contra hnot
    have : m = 0 := by omega
    exact hnotstar (this ▸ hmvalue)
  have hnotlast : m + 1 < p.length := by
    by_contra hnot
    obtain ⟨left, right, hl, hr, hrbound, hinv⟩ := hcross m (by omega) hm
    have hright : right = m := by omega
    rw [hright, hmvalue] at hinv
    have := (hbounds left (by omega)).2
    omega
  have hmtall : Tall p m := by
    refine ⟨m + 1, by omega, hnotlast, ?_⟩
    have hb := (hbounds (m + 1) hnotlast).2
    have hne := hneq (m + 1) m hnotlast hm (by omega)
    rw [hmvalue] at *
    omega
  have hafter (index : ℕ) (hi : index < p.length) (hmi : m < index) : ¬ Tall p index := by
    intro htall
    have hlt := tall_ltrMax p hnodup h321 index hi htall m hmi
    rw [hmvalue] at hlt
    have := (hbounds index hi).2
    omega
  have hzerotall : Tall p 0 := by
    obtain ⟨left, right, hl, hr, hrbound, hinv⟩ := hcross 1 (by omega) (by omega)
    have : left = 0 := by omega
    exact ⟨right, by omega, hrbound, this ▸ hinv⟩
  let last := Nat.findGreatest (fun index => index < m ∧ Tall p index) m
  have hlastspec : last < m ∧ Tall p last :=
    Nat.findGreatest_spec (P := fun index => index < m ∧ Tall p index)
      (by omega : 0 ≤ m) ⟨hmpositive, hzerotall⟩
  have hlastbound : last < p.length := by omega
  have hlast (index : ℕ) (hi : last < index) (him : index < m) : ¬ Tall p index := by
    have := Nat.findGreatest_is_greatest hi (by omega : index ≤ m)
    exact fun htall => this ⟨him, htall⟩
  obtain ⟨left, later, hl, hlater, hlaterbound, hinv⟩ := hcross m (by omega) hm
  have hleftbound : left < p.length := by omega
  have hlefttall : Tall p left := ⟨later, by omega, hlaterbound, hinv⟩
  have hleftlast : left ≤ last := by
    by_contra hnot
    exact hlast left (by omega) hl hlefttall
  have hlastvalue : p.getD left 0 ≤ p.getD last 0 := by
    by_cases heq : left = last
    · simp [heq]
    · exact (tall_ltrMax p hnodup h321 last hlastbound hlastspec.2 left (by omega)).le
  have hlatervalue : p.getD later 0 < p.getD last 0 := by omega
  have hmlater : m < later := by
    by_contra hnot
    have : later = m := by omega
    rw [this, hmvalue] at hlatervalue
    have := (hbounds last hlastbound).2
    omega
  have hlastmax : p.getD last 0 < n := by
    have hb := (hbounds last hlastbound).2
    have hne := hneq last m hlastbound hm (by omega)
    rw [hmvalue] at hne
    omega
  have hprefix (index : ℕ) (hi : index ≤ last) : Tall p index := by
    by_cases heq : index = last
    · simpa [heq] using hlastspec.2
    · by_contra hshortindex
      have hindexbound : index < p.length := by omega
      have hlow := hshort index later hindexbound hlaterbound (by omega) hshortindex
      exact hquad index last m later hindexbound hlastbound hm hlaterbound
        (by omega) hlastspec.1 hmlater hlow hlatervalue (by rwa [hmvalue])
  have hlowzero : p.getD later 0 < p.getD 0 0 := by
    by_cases hlastzero : last = 0
    · simpa [hlastzero] using hlatervalue
    · have hzero : 0 < p.length := by omega
      have hzeroLast := tall_ltrMax p hnodup h321 last hlastbound hlastspec.2 0 (by omega)
      have hne := hneq later 0 hlaterbound hzero (by omega)
      by_contra hnot
      have hzeroLater : p.getD 0 0 < p.getD later 0 := by omega
      exact hquad 0 last m later hzero hlastbound hm hlaterbound
        (by omega) hlastspec.1 hmlater hzeroLater hlatervalue (by rwa [hmvalue])
  refine ⟨last + 1, m, later, by omega, by omega, hm, hmvalue, hmlater,
    hlaterbound, hlowzero, ?_⟩
  intro index hi
  constructor
  · intro htall
    by_cases him : index < m
    · by_contra hnot
      exact hlast index (by omega) him htall
    · by_cases heq : index = m
      · exact Or.inr heq
      · exact False.elim (hafter index hi (by omega) htall)
  · rintro (hbefore | rfl)
    · exact hprefix index (by omega)
    · exact hmtall

theorem classification (p : List ℕ) (k : ℕ)
    (hp : p ∈ FranklinInversionDefs.avoiders k) :
    p = star k ∨ ∃ r t d h, 1 ≤ r ∧ 1 ≤ t ∧ 1 ≤ d ∧ d ≤ t ∧
      p = fiveBlock r t d h ∧ r * t + d + h = k := by
  classical
  have hstarMembership (k : ℕ) : star k ∈ FranklinInversionDefs.avoiders k := by
    have hget (index : ℕ) (hi : index < k + 1) :
        (star k).getD index 0 = if index = 0 then k + 1 else index := by
      cases index with
      | zero => simp [star]
      | succ index =>
        have hi' : index < k := by omega
        simp [star, hi', Nat.add_comm]
    have hinv : inv (star k) = k := by
      have hrow (index : ℕ) (hi : index ∈ List.range (k + 1)) :
          ((List.range (k + 1)).filter fun next => decide
            (index < next ∧ (star k).getD next 0 < (star k).getD index 0)).length =
            if index = 0 then k else 0 := by
        have hi' : index < k + 1 := List.mem_range.mp hi
        by_cases hz : index = 0
        · subst index
          have hfilter :
              (List.range (k + 1)).filter (fun next => decide
                  (0 < next ∧ (star k).getD next 0 < (star k).getD 0 0)) =
                (List.range (k + 1)).filter (fun next => decide (0 < next)) := by
            apply List.filter_congr
            intro next hn
            rw [hget next (List.mem_range.mp hn), hget 0 (by omega)]
            simp only [ite_true]
            by_cases hnext : next = 0 <;> simp [hnext, List.mem_range.mp hn]
          rw [hfilter, List.range_succ_eq_map]
          simp [List.filter_map, Function.comp_def]
        · have hfilter :
              (List.range (k + 1)).filter (fun next => decide
                (index < next ∧ (star k).getD next 0 < (star k).getD index 0)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro next hn
            rw [hget next (List.mem_range.mp hn), hget index hi']
            simp only [hz, ite_false]
            by_cases hnext : next = 0
            · simp [hnext]
            · simp only [hnext, ite_false, decide_eq_true_eq]
              omega
          rw [hfilter]
          simp [hz]
      unfold inv
      have hlength : (star k).length = k + 1 := by simp [star]
      simp only [hlength]
      have hmap := List.map_congr_left hrow
      rw [hmap, List.range_succ_eq_map]
      simp [List.map_map, Function.comp_def]
    refine ⟨k + 1, by omega, ?_, ?_, hinv, ?_, ?_⟩
    · rw [List.range'_concat]
      simpa [star, Nat.add_comm] using
        (List.perm_middle (a := k + 1) (l₁ := List.range' 1 k) (l₂ := [])).symm
    · intro cut hcut hproper hperm
      have hbound : cut ≤ k := by simpa [star] using hproper
      have hmem : k + 1 ∈ (star k).take cut := by
        obtain ⟨cut, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cut ≠ 0)
        simp [star]
      have := hperm.mem_iff.mp hmem
      simp only [List.mem_range', Nat.one_mul] at this
      omega
    · rintro ⟨values, hincreasing, _, hsublist, _⟩
      have h12 : values 1 < values 2 := hincreasing 1 (by omega) (by decide)
      have htail : [values 2, values 1].Sublist (List.range' 1 k) := by
        simpa [star] using hsublist.tail
      have hordered := (List.pairwise_lt_range' (s := 1) (n := k)).sublist htail
      have h21 : values 2 < values 1 :=
        (List.pairwise_cons.mp hordered).1 _ (by simp)
      omega
    · rintro ⟨values, hincreasing, _, hsublist, _⟩
      have h23 : values 2 < values 3 := hincreasing 2 (by omega) (by decide)
      have htail : [values 3, values 4, values 2].Sublist (List.range' 1 k) := by
        simpa [star] using hsublist.tail
      have hordered := (List.pairwise_lt_range' (s := 1) (n := k)).sublist htail
      have h32 : values 3 < values 2 :=
        (List.pairwise_cons.mp hordered).1 _ (by simp)
      omega
  obtain ⟨n, hn, hperm, hindecomp, hinv, h321, h1342⟩ := hp
  have hlength : p.length = n := by simpa using hperm.length_eq
  have hnodup : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hzero : 0 < p.length := by omega
  have hbounds (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hmem := hperm.mem_iff.mp (List.getElem_mem hi)
    rw [List.getD_eq_getElem _ _ hi]
    simp only [List.mem_range', Nat.one_mul] at hmem
    obtain ⟨offset, hoff, heq⟩ := hmem
    omega
  have hneq (left right : ℕ) (hl : left < p.length) (hr : right < p.length)
      (hne : left ≠ right) : p.getD left 0 ≠ p.getD right 0 := by
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hr]
    intro heq
    exact hne (hnodup.getElem_inj_iff.mp heq)
  have hshort (left right : ℕ) (hl : left < p.length) (hr : right < p.length)
      (hlr : left < right) (hleft : ¬ Tall p left) :
      p.getD left 0 < p.getD right 0 := by
    have hne := hneq left right hl hr (by omega)
    have hnot : ¬ p.getD right 0 < p.getD left 0 := by
      intro hlt
      exact hleft ⟨right, hlr, hr, hlt⟩
    omega
  by_cases hfirst : p.getD 0 0 = n
  · have hshorts (index : ℕ) (hi : index < p.length) (hpositive : 0 < index) :
        ¬ Tall p index := by
      intro htall
      have := tall_ltrMax p hnodup h321 index hi htall 0 hpositive
      rw [hfirst] at this
      have := (hbounds index hi).2
      omega
    have hsorted : List.Pairwise (· < ·) (p.drop 1) := by
      apply List.pairwise_iff_getElem.mpr
      intro left right hl hr hlr
      simp only [List.getElem_drop]
      have hl' : 1 + left < p.length := by simp only [List.length_drop] at hl; omega
      have hr' : 1 + right < p.length := by simp only [List.length_drop] at hr; omega
      simpa only [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hr'] using
        hshort (1 + left) (1 + right) hl' hr' (by omega)
          (hshorts _ hl' (by omega))
    have hdecomp : p = n :: p.drop 1 := by
      have := List.drop_eq_getElem_cons (i := 0) hzero
      have hgetzero := hfirst
      rw [List.getD_eq_getElem _ _ hzero] at hgetzero
      simpa only [List.drop_zero, Nat.zero_add, hgetzero] using this
    obtain ⟨starLength, _, hstarPerm, _, hstarInv, _, _⟩ := hstarMembership (n - 1)
    have hstarLength : starLength = n := by
      have := hstarPerm.length_eq
      simp only [star, List.length_cons, List.length_range'] at this
      omega
    rw [hstarLength] at hstarPerm
    have htailPerm : (p.drop 1).Perm (List.range' 1 (n - 1)) := by
      have := hperm.trans hstarPerm.symm
      rw [hdecomp] at this
      unfold star at this
      rw [show n - 1 + 1 = n by omega] at this
      exact this.cons_inv
    have htailEq := htailPerm.eq_of_pairwise' hsorted List.pairwise_lt_range'
    have hstarEq : p = star (n - 1) := by
      rw [hdecomp, htailEq]
      simp only [star, show n - 1 + 1 = n by omega]
    rw [hstarEq, hstarInv] at hinv
    exact Or.inl (by simpa [hinv] using hstarEq)
  · obtain ⟨r, m, later, hr, hrm, hm, hmvalue, hml, hlater, hlow, htall⟩ :=
      tall_block_structure p n hperm hindecomp h321 h1342 hn hfirst
    let a := p.getD 0 0
    let b := p.getD (r - 1) 0
    let s := m - r
    have hlast : r - 1 < p.length := by omega
    have hlasttall : Tall p (r - 1) := (htall _ hlast).mpr (Or.inl (by omega))
    have hzerotall : Tall p 0 := (htall _ hzero).mpr (Or.inl (by omega))
    have hab : a ≤ b := by
      by_cases heq : r - 1 = 0
      · simp [a, b, heq]
      · exact (tall_ltrMax p hnodup h321 _ hlast hlasttall 0 (by omega)).le
    have hbn : b < n := by
      have hb := (hbounds (r - 1) hlast).2
      have hne := hneq (r - 1) m hlast hm (by omega)
      rw [hmvalue] at hne
      omega
    have ha : 2 ≤ a := by
      obtain ⟨smaller, _, hsmaller, hlt⟩ := hzerotall
      have := (hbounds smaller hsmaller).1
      dsimp [a]
      omega
    have hmiddle (index : ℕ) (hri : r ≤ index) (him : index < m) :
        p.getD index 0 < p.getD later 0 := by
      have hi : index < p.length := by omega
      have hs : ¬ Tall p index := by rw [htall _ hi]; omega
      exact hshort index later hi hlater (by omega) hs
    have hquad (fourth : ℕ) (hf : fourth < p.length) (hmf : m < fourth)
        (hav : a < p.getD fourth 0) (hvb : p.getD fourth 0 < b) : False := by
      have hrbig : 0 < r - 1 := by
        by_contra hnot
        have : r - 1 = 0 := by omega
        dsimp [a, b] at *
        rw [this] at hvb
        omega
      apply h1342
      let values : ℕ → ℕ := fun rank =>
        if rank = 1 then a else if rank = 2 then p.getD fourth 0 else
          if rank = 3 then b else n
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hpositive hbound
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
          simp [Nonnesting.NonnestingDefs.letters] at hbound
          omega
        rcases this with rfl | rfl | rfl
        · simpa [values] using hav
        · simpa [values] using hvb
        · simpa [values] using hbn
      · intro rank hpositive hbound
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          simp [Nonnesting.NonnestingDefs.letters] at hbound
          omega
        rcases this with rfl | rfl | rfl | rfl
        · change p.getD 0 0 ∈ p
          rw [List.getD_eq_getElem _ _ hzero]
          exact List.getElem_mem hzero
        · change p.getD fourth 0 ∈ p
          rw [List.getD_eq_getElem _ _ hf]
          exact List.getElem_mem hf
        · change p.getD (r - 1) 0 ∈ p
          rw [List.getD_eq_getElem _ _ hlast]
          exact List.getElem_mem hlast
        · change n ∈ p
          rw [← hmvalue, List.getD_eq_getElem _ _ hm]
          exact List.getElem_mem hm
      · change [a, b, n, p.getD fourth 0].Sublist p
        let embedding : Fin 4 ↪o Fin p.length := OrderEmbedding.ofMapLEIff
          (fun rank => if rank.val = 0 then ⟨0, hzero⟩ else
            if rank.val = 1 then ⟨r - 1, hlast⟩ else
              if rank.val = 2 then ⟨m, hm⟩ else ⟨fourth, hf⟩)
          (by intro left right; fin_cases left <;> fin_cases right <;> simp <;> omega)
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨embedding, ?_⟩
        intro rank
        fin_cases rank <;> simp [embedding, a, b, ← hmvalue, hzero, hlast, hm, hf]
    have hhighSorted : List.Pairwise (· < ·) (p.take r) := by
      apply List.pairwise_iff_getElem.mpr
      intro left right hl hr' hlr
      have hl' : left < p.length := by simp only [List.length_take] at hl; omega
      have hr'' : right < p.length := by simp only [List.length_take] at hr'; omega
      have hrightTall : Tall p right :=
        (htall right hr'').mpr (Or.inl (by simp only [List.length_take] at hr'; omega))
      simpa only [List.getElem_take, List.getD_eq_getElem _ _ hl',
        List.getD_eq_getElem _ _ hr''] using
        tall_ltrMax p hnodup h321 right hr'' hrightTall left hlr
    have hhighBounds (index : ℕ) (hi : index < r) :
        a ≤ p.getD index 0 ∧ p.getD index 0 ≤ b := by
      have hibound : index < p.length := by omega
      constructor
      · by_cases heq : index = 0
        · simp [a, heq]
        · exact (tall_ltrMax p hnodup h321 index hibound
            ((htall index hibound).mpr (Or.inl hi)) 0 (by omega)).le
      · by_cases heq : index = r - 1
        · simp [b, heq]
        · exact (tall_ltrMax p hnodup h321 _ hlast hlasttall index (by omega)).le
    have hhighEq : p.take r = List.range' a (b + 1 - a) := by
      apply hhighSorted.eq_of_mem_iff List.pairwise_lt_range'
      intro value
      constructor
      · intro hmem
        obtain ⟨index, hi, hvalue⟩ := List.mem_take_iff_getElem.mp hmem
        have hibound : index < p.length := by omega
        have hb := hhighBounds index (by omega)
        rw [List.getD_eq_getElem _ _ hibound, hvalue] at hb
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨value - a, by omega, by omega⟩
      · intro hmem
        have hinterval : a ≤ value ∧ value ≤ b := by
          simp only [List.mem_range', Nat.one_mul] at hmem
          obtain ⟨offset, hoff, heq⟩ := hmem
          omega
        have hfull : value ∈ p := by
          apply hperm.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨value - 1, by omega, by omega⟩
        obtain ⟨index, hi, hvalue⟩ := List.mem_iff_getElem.mp hfull
        have hgetValue : p.getD index 0 = value := by
          rwa [List.getD_eq_getElem _ _ hi]
        have hir : index < r := by
          by_contra hnot
          by_cases him : index < m
          · have := hmiddle index (by omega) him
            rw [hgetValue] at this
            omega
          · by_cases heq : index = m
            · rw [heq, hmvalue] at hgetValue
              omega
            · have hmindex : m < index := by omega
              have hnea := hneq index 0 hi hzero (by omega)
              have hneb := hneq index (r - 1) hi hlast (by omega)
              rw [hgetValue] at hnea hneb
              exact hquad index hi hmindex (by omega) (by omega)
        exact List.mem_take_iff_getElem.mpr ⟨index, by omega, hvalue⟩
    have hwidth : b + 1 - a = r := by
      have := congrArg List.length hhighEq
      simp only [List.length_take, List.length_range'] at this
      omega
    let consumed := (p.drop r).take s
    let suffix := p.drop (m + 1)
    have hconsumedLength : consumed.length = s := by
      simp [consumed, s]
      omega
    have hconsumedIndex (index : ℕ) (hi : index < consumed.length) :
        r + index < m ∧ consumed[index] = p.getD (r + index) 0 := by
      have hibound : r + index < p.length := by omega
      constructor
      · rw [hconsumedLength] at hi
        dsimp [s] at hi
        omega
      · simp only [consumed, List.getElem_take, List.getElem_drop,
          List.getD_eq_getElem _ _ hibound]
    have hconsumedSubset : consumed ⊆ List.range' 1 (p.getD later 0 - 1) := by
      intro value hmem
      obtain ⟨index, hi, hvalue⟩ := List.mem_iff_getElem.mp hmem
      obtain ⟨him, hget⟩ := hconsumedIndex index hi
      have hb := (hbounds (r + index) (by omega)).1
      have hlt := hmiddle (r + index) (by omega) him
      rw [← hget, hvalue] at hb hlt
      simp only [List.mem_range', Nat.one_mul]
      exact ⟨value - 1, by omega, by omega⟩
    have hslt : s < a - 1 := by
      have hcnodup : consumed.Nodup :=
        hnodup.sublist ((List.take_sublist s (p.drop r)).trans (List.drop_sublist r p))
      have := (List.subperm_of_subset hcnodup hconsumedSubset).length_le
      rw [hconsumedLength, List.length_range'] at this
      dsimp [a]
      omega
    let t := a - 1
    let d := t - s
    let h := n - (r + t + 1)
    have ht : 1 ≤ t := by dsimp [t]; omega
    have hd : 1 ≤ d := by dsimp [d, t]; omega
    have hdt : d ≤ t := by dsimp [d]; omega
    have htd : t - d = s := by dsimp [d, t]; omega
    have hbtr : b = t + r := by dsimp [t]; omega
    have hnform : r + t + h + 1 = n := by dsimp [h]; omega
    have hhighForm : p.take r = List.range' (t + 1) r := by
      rw [hhighEq, hwidth]
      congr 1
      dsimp [t]
      omega
    have hdecomp : p = p.take r ++ consumed ++ n :: suffix := by
      have htake : p.take m = p.take r ++ consumed := by
        rw [show m = r + s by dsimp [s]; omega, List.take_add]
      have hdrop : p.drop m = n :: suffix := by
        rw [List.drop_eq_getElem_cons hm]
        have hgetmax := hmvalue
        rw [List.getD_eq_getElem _ _ hm] at hgetmax
        simp only [suffix, hgetmax]
      calc
        p = p.take m ++ p.drop m := (List.take_append_drop m p).symm
        _ = p.take r ++ consumed ++ n :: suffix := by rw [htake, hdrop]
    have hshortSorted : List.Pairwise (· < ·) (consumed ++ suffix) := by
      apply List.pairwise_iff_getElem.mpr
      intro left right hl hr' hlr
      have hindex (index : ℕ) (hi : index < (consumed ++ suffix).length) :
          ∃ position, position < p.length ∧ r ≤ position ∧ position ≠ m ∧
            (consumed ++ suffix)[index] = p.getD position 0 ∧
            position = if index < s then r + index else m + 1 + (index - s) := by
        by_cases his : index < s
        · refine ⟨r + index, by dsimp [s] at *; omega, by omega, ?_, ?_, by simp [his]⟩
          · dsimp [s] at *; omega
          · rw [List.getElem_append_left (by omega)]
            exact (hconsumedIndex index (by omega)).2
        · have hibound : m + 1 + (index - s) < p.length := by
            simp only [List.length_append, hconsumedLength, suffix, List.length_drop] at hi
            omega
          refine ⟨m + 1 + (index - s), hibound, by omega, by omega, ?_, by simp [his]⟩
          rw [List.getElem_append_right (by omega)]
          simp only [hconsumedLength, suffix, List.getElem_drop,
            List.getD_eq_getElem _ _ hibound]
      obtain ⟨leftPos, hlb, hlr', hlm, hleft, hleftPos⟩ := hindex left hl
      obtain ⟨rightPos, hrb, _, _, hright, hrightPos⟩ := hindex right hr'
      have hpositions : leftPos < rightPos := by
        rw [hleftPos, hrightPos]
        dsimp [s]
        split_ifs <;> omega
      rw [hleft, hright]
      apply hshort leftPos rightPos hlb hrb hpositions
      rw [htall leftPos hlb]
      omega
    obtain ⟨otherLength, _, hotherPerm, _, hotherInv, _, _⟩ :=
      fiveBlock_mem_avoiders r t d h hr ht hd hdt
    have hotherLength : otherLength = n := by
      have := hotherPerm.length_eq
      simp only [fiveBlock, List.length_append, List.length_range', List.length_cons] at this
      omega
    rw [hotherLength] at hotherPerm
    let low := List.range' 1 s
    let residual := List.range' (s + 1) d
    let finalHigh := List.range' (t + r + 1) h
    have hotherForm : fiveBlock r t d h =
        p.take r ++ low ++ n :: (residual ++ finalHigh) := by
      simp only [fiveBlock, hhighForm, low, residual, finalHigh, htd, hnform]
    have hmove : p.Perm (p.take r ++ n :: (consumed ++ suffix)) := by
      nth_rw 1 [hdecomp]
      simpa only [List.append_assoc] using
        (List.perm_middle (a := n) (l₁ := consumed) (l₂ := suffix)).append_left (p.take r)
    have hotherMove : (fiveBlock r t d h).Perm
        (p.take r ++ n :: (low ++ (residual ++ finalHigh))) := by
      rw [hotherForm]
      simpa only [List.append_assoc] using
        (List.perm_middle (a := n) (l₁ := low) (l₂ := residual ++ finalHigh)).append_left
          (p.take r)
    have hshortPerm : (consumed ++ suffix).Perm (low ++ (residual ++ finalHigh)) := by
      have := hmove.symm.trans ((hperm.trans hotherPerm.symm).trans hotherMove)
      exact ((List.perm_append_left_iff (p.take r)).mp this).cons_inv
    have hotherSorted : List.Pairwise (· < ·) (low ++ (residual ++ finalHigh)) := by
      have hlow : low ++ residual = List.range' 1 t := by
        dsimp [low, residual]
        have := List.range'_append (s := 1) (m := s) (n := d) (step := 1)
        simpa [show s + d = t by dsimp [d, t]; omega, Nat.add_comm] using this
      rw [← List.append_assoc, hlow]
      apply List.pairwise_append.mpr
      refine ⟨List.pairwise_lt_range', List.pairwise_lt_range', ?_⟩
      intro left hl right hr'
      simp only [List.mem_range', Nat.one_mul, finalHigh] at hl hr'
      obtain ⟨leftOffset, hlo, rfl⟩ := hl
      obtain ⟨rightOffset, hro, rfl⟩ := hr'
      omega
    have hshortEq := hshortPerm.eq_of_pairwise' hshortSorted hotherSorted
    have hconsumedEq : consumed = low := by
      have := congrArg (List.take s) hshortEq
      simpa [List.take_append, hconsumedLength, low] using this
    have hsuffixEq : suffix = residual ++ finalHigh := by
      have := congrArg (List.drop s) hshortEq
      simpa [List.drop_append, hconsumedLength, low] using this
    have hblockEq : p = fiveBlock r t d h := by
      rw [hotherForm, ← hconsumedEq, ← hsuffixEq]
      exact hdecomp
    rw [hblockEq, hotherInv] at hinv
    exact Or.inr ⟨r, t, d, h, hr, ht, hd, hdt, hblockEq, hinv⟩

end D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion
