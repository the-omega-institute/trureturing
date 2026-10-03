/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts
   mirror-E: none(waiver:indecomposable-component-boundary-count)
   anchors: []
   utility: none
   digest: Inversion witnesses identify and count the canonical component boundaries. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponentCuts

open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum FishburnBasicComponents

theorem component_boundary_count (parts : List (List ℕ))
    (hparts : ∀ block ∈ parts, block ≠ [] ∧
      block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) :
    let word := assemble parts
    (@Finset.filter ℕ (fun cut =>
      ∀ before ∈ word.take cut, ∀ later ∈ word.drop cut, before < later)
      (fun _ => Classical.propDecidable _) (Finset.range (word.length + 1))).card =
      parts.length + 1 := by
  classical
  let cuts (word : List ℕ) := @Finset.filter ℕ (fun cut =>
    ∀ before ∈ word.take cut, ∀ later ∈ word.drop cut, before < later)
    (fun _ => Classical.propDecidable _) (Finset.range (word.length + 1))
  change (cuts (assemble parts)).card = parts.length + 1
  have hvalues (block : List ℕ) (hp : block.Perm (List.range' 1 block.length))
      (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ block.length := by
    have hr := hp.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, ho, heq⟩ := hr
    omega
  have hpositive (blocks : List (List ℕ))
      (hp : ∀ block ∈ blocks, block.Perm (List.range' 1 block.length)) :
      ∀ value ∈ assemble blocks, 1 ≤ value := by
    induction blocks with
    | nil => simp [assemble]
    | cons first rest ih =>
      intro value hv
      rcases List.mem_append.mp hv with hfirst | hrest
      · exact (hvalues first (hp first (by simp)) value hfirst).1
      · obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hrest
        have := ih (fun block hb => hp block (by simp [hb])) small hs
        omega
  have htest (word : List ℕ) (cut : ℕ) : cut ∈ cuts word ↔ cut ≤ word.length ∧
      ∀ before later, before < cut → cut ≤ later → later < word.length →
        word.getD before 0 < word.getD later 0 := by
    simp only [cuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hb, hsep⟩
      refine ⟨hb, ?_⟩
      intro before later hbefore hlater hbound
      apply hsep
      · apply List.mem_take_iff_getElem.mpr
        exact ⟨before, by omega, (List.getD_eq_getElem word 0 (by omega)).symm⟩
      · apply List.mem_drop_iff_getElem.mpr
        refine ⟨later - cut, by omega, ?_⟩
        have heq : cut + (later - cut) = later := by omega
        simpa only [heq] using (List.getD_eq_getElem word 0 hbound).symm
    · rintro ⟨hb, hsep⟩
      refine ⟨hb, ?_⟩
      intro before hbefore later hlater
      obtain ⟨first, hf, heqFirst⟩ := List.mem_take_iff_getElem.mp hbefore
      obtain ⟨second, hs, heqSecond⟩ := List.mem_drop_iff_getElem.mp hlater
      have hless := hsep first (cut + second) (by omega) (by omega) (by omega)
      simpa only [List.getD_eq_getElem word 0 (by omega : first < word.length),
        List.getD_eq_getElem word 0 (by omega : cut + second < word.length),
        heqFirst, heqSecond] using hless
  revert hparts
  induction parts with
  | nil =>
    intro hparts
    simp [assemble, cuts]
  | cons first rest ih =>
    intro hparts
    have hf := hparts first (by simp)
    have hr := fun block hb => hparts block (List.mem_cons_of_mem first hb)
    have hrestCount := ih hr
    let tail := assemble rest
    let word := assemble (first :: rest)
    have hfirstPositive : 0 < first.length := List.length_pos_iff_ne_nil.mpr hf.1
    have hlength : word.length = first.length + tail.length := by
      simp [word, tail, assemble, directSum, shift]
    have htailPositive : ∀ value ∈ tail, 1 ≤ value :=
      hpositive rest (fun block hb => (hr block hb).2.1)
    have hbefore (index : ℕ) (hb : index < first.length) :
        word.getD index 0 = first.getD index 0 := by
      exact List.getD_append _ _ _ _ hb
    have hafter (index : ℕ) (hl : first.length ≤ index) (hb : index < word.length) :
        word.getD index 0 = tail.getD (index - first.length) 0 + first.length := by
      change (first ++ shift first.length tail).getD index 0 = _
      rw [List.getD_append_right _ _ _ _ hl]
      have hindex : index - first.length < tail.length := by omega
      rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hindex),
        List.getD_eq_getElem tail 0 hindex]
      simp [shift]
    have hshifted (cut : ℕ) (hb : cut ≤ tail.length) :
        first.length + cut ∈ cuts word ↔ cut ∈ cuts tail := by
      rw [htest, htest]
      constructor
      · rintro ⟨_, hsep⟩
        refine ⟨hb, ?_⟩
        intro before later hbeforeCut hlaterCut hbound
        have hless := hsep (first.length + before) (first.length + later)
          (by omega) (by omega) (by omega)
        rw [hafter _ (by omega) (by omega), hafter _ (by omega) (by omega),
          Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hless
        omega
      · rintro ⟨_, hsep⟩
        refine ⟨by omega, ?_⟩
        intro before later hbeforeCut hlaterCut hbound
        rw [hafter later (by omega) hbound]
        by_cases hlocal : before < first.length
        · rw [hbefore before hlocal]
          have hsmall : first.getD before 0 ≤ first.length := by
            apply (hvalues first hf.2.1 _ _).2
            rw [List.getD_eq_getElem first 0 hlocal]
            exact List.getElem_mem hlocal
          have hlarge : 1 ≤ tail.getD (later - first.length) 0 := by
            apply htailPositive
            rw [List.getD_eq_getElem tail 0 (by omega)]
            exact List.getElem_mem (by omega)
          omega
        · rw [hafter before (by omega) (by omega)]
          have hless := hsep (before - first.length) (later - first.length)
            (by omega) (by omega) (by omega)
          omega
    have hinternal (cut : ℕ) (hp : 0 < cut) (hb : cut < first.length) :
        cut ∉ cuts word := by
      intro hc
      have hsep := (htest word cut).mp hc |>.2
      obtain ⟨before, later, hbad⟩ := hf.2.2 ⟨cut, hb⟩ hp
      have hbeforeBound : before.val < cut := by
        have := before.is_lt
        simp only [List.length_take] at this
        omega
      have hlaterBound : cut + later.val < first.length := by
        have := later.is_lt
        simp only [List.length_drop] at this
        omega
      have hless := hsep before.val (cut + later.val) hbeforeBound (by omega) (by omega)
      rw [hbefore _ (by omega), hbefore _ hlaterBound,
        List.getD_eq_getElem first 0 (by omega),
        List.getD_eq_getElem first 0 hlaterBound] at hless
      have hbad' : first[cut + later.val] ≤ first[before.val] := by
        simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hbad
      omega
    have hzero : 0 ∈ cuts word := by
      apply (htest word 0).mpr
      exact ⟨Nat.zero_le _, by intros; omega⟩
    have hdecomp : cuts word = {0} ∪ (cuts tail).image (first.length + ·) := by
      ext cut
      constructor
      · intro hc
        have hb := ((htest word cut).mp hc).1
        by_cases hz : cut = 0
        · simp [hz]
        have hnoninternal : first.length ≤ cut := by
          by_contra hnot
          exact hinternal cut (by omega) (by omega) hc
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨cut - first.length, ?_, by omega⟩
        apply (hshifted (cut - first.length) (by omega)).mp
        simpa only [Nat.add_sub_cancel' hnoninternal] using hc
      · intro hc
        rcases Finset.mem_union.mp hc with hz | him
        · simpa only [Finset.mem_singleton.mp hz] using hzero
        · obtain ⟨suffixCut, hs, rfl⟩ := Finset.mem_image.mp him
          exact (hshifted suffixCut ((htest tail suffixCut).mp hs).1).mpr hs
    have hdisjoint : Disjoint ({0} : Finset ℕ)
        ((cuts tail).image (first.length + ·)) := by
      apply Finset.disjoint_left.mpr
      intro cut hzero him
      obtain ⟨suffixCut, _, heq⟩ := Finset.mem_image.mp him
      simp only [Finset.mem_singleton] at hzero
      omega
    have himage : ((cuts tail).image (first.length + ·)).card = (cuts tail).card :=
      Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_left_cancel heq)
    change (cuts word).card = (first :: rest).length + 1
    rw [hdecomp, Finset.card_union_of_disjoint hdisjoint, Finset.card_singleton, himage]
    change 1 + (cuts (assemble rest)).card = rest.length + 1 + 1
    omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponentCuts
