/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts
   mirror-E: none(waiver:indecomposable-component-boundary-count)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Component boundaries and reversible marked lists give weighted series identities. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents
import Mathlib.RingTheory.PowerSeries.Basic

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

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenComponentSeries

open D5.S3.Combinatorics Nonnesting NonnestingBasicSum FishburnDefs
open FishburnBasicComponents PowerSeries Finset

theorem weighted_component_series (patterns : List (List ℕ))
    (hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
      (∀ value ∈ pattern, 1 ≤ value) ∧
      ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern) :
    let components (size : ℕ) := {parts : List (List ℕ) |
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      assemble parts ∈ avoiders size patterns}
    let indecs : PowerSeries (Polynomial ℚ) := mk fun size =>
      if size = 0 then 0 else
        ({word : List ℕ | word ∈ avoiders size patterns ∧ sumIndecomposable word}.ncard :
          Polynomial ℚ)
    let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
      ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
    (∀ size, ∃ serialization : components size ≃ avoiders size patterns,
      ∀ parts, (serialization parts).val = assemble parts.val) ∧
    (1 - C Polynomial.X * indecs) * sequences = 1 ∧
    ∀ weight : ℕ → List ℕ → Polynomial ℚ,
      let marked : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ block : {word : List ℕ |
          word ∈ avoiders size patterns ∧ sumIndecomposable word}, weight size block.val
      let heads : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ parts : components size,
          (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
            weight (parts.val.headD []).length (parts.val.headD [])
      let lasts : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ parts : components size,
          (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
            weight (parts.val.reverse.headD []).length (parts.val.reverse.headD [])
      let tails : PowerSeries (Polynomial ℚ) := mk fun size =>
        if size = 0 then 0 else ∑ᶠ parts : components size,
          (Polynomial.X : Polynomial ℚ) ^
            (if parts.val.tail = [] then 1 else parts.val.tail.length) *
              weight (parts.val.headD []).length (parts.val.headD [])
      heads = marked * sequences ∧ lasts = heads ∧
        tails = C Polynomial.X * marked + marked * (sequences - 1) := by
  classical
  let components (size : ℕ) := {parts : List (List ℕ) |
    (∀ block ∈ parts, block ≠ [] ∧
      block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
    assemble parts ∈ avoiders size patterns}
  let indecs : PowerSeries (Polynomial ℚ) := mk fun size =>
    if size = 0 then 0 else
      ({word : List ℕ | word ∈ avoiders size patterns ∧ sumIndecomposable word}.ncard :
        Polynomial ℚ)
  let sequences : PowerSeries (Polynomial ℚ) := mk fun size =>
    ∑ᶠ parts : components size, (Polynomial.X : Polynomial ℚ) ^ parts.val.length
  change (∀ size, ∃ serialization : components size ≃ avoiders size patterns,
    ∀ parts, (serialization parts).val = assemble parts.val) ∧
    (1 - C Polynomial.X * indecs) * sequences = 1 ∧ _
  have hbase := unique_sum_components 0 [] (by simp) patterns hpatterns
  have hclosure := hbase.2.1
  have hlength (parts : List (List ℕ)) :
      (assemble parts).length = (parts.map List.length).sum := by
    induction parts with
    | nil => rfl
    | cons first rest ih =>
      simp only [assemble, directSum, shift, List.length_append, List.length_map,
        List.map_cons, List.sum_cons, ih]
  have hsize (size : ℕ) (parts : components size) :
      (assemble parts.val).length = size := by
    simpa using parts.property.2.1.length_eq
  have hblock (size : ℕ) (parts : components size) :
      ∀ block ∈ parts.val, block ∈ avoiders block.length patterns :=
    (hclosure parts.val parts.property.1).mp (by
      simpa only [hsize size parts] using parts.property.2)
  have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
    apply (List.finite_toSet (List.range' 1 size).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  let serialize (size : ℕ) (parts : components size) : avoiders size patterns :=
    ⟨assemble parts.val, parts.property.2⟩
  have hinjective (size : ℕ) : Function.Injective (serialize size) := by
    intro left right heq
    have hv : assemble left.val = assemble right.val := congrArg Subtype.val heq
    obtain ⟨canonical, _, hu⟩ :=
      (unique_sum_components size (assemble left.val) left.property.2.1 patterns
        hpatterns).1
    have hl : left.val = canonical := hu _ ⟨rfl, left.property.1, by
      simpa only [hsize size left] using hclosure left.val left.property.1⟩
    have hr : right.val = canonical := hu _ ⟨hv.symm, right.property.1, by
      have hh := hclosure right.val right.property.1
      rw [hsize size right, ← hv] at hh
      exact hh⟩
    exact Subtype.ext (hl.trans hr.symm)
  have hsurjective (size : ℕ) : Function.Surjective (serialize size) := by
    intro word
    obtain ⟨parts, hp, _⟩ :=
      (unique_sum_components size word.val word.property.1 patterns hpatterns).1
    exact ⟨⟨parts, hp.2.1, by simpa only [hp.1] using word.property⟩,
      Subtype.ext hp.1⟩
  let serialization (size : ℕ) :=
    Equiv.ofBijective (serialize size) ⟨hinjective size, hsurjective size⟩
  let (size : ℕ) : Finite (avoiders size patterns) := (hfinite size).to_subtype
  let (size : ℕ) : Finite (components size) :=
    Finite.of_injective (serialize size) (hinjective size)
  let (size : ℕ) : Fintype (components size) := Fintype.ofFinite _
  let blocks (size : ℕ) := {word : List ℕ |
    word ∈ avoiders size patterns ∧ sumIndecomposable word}
  let (size : ℕ) : Finite (blocks size) :=
    ((hfinite size).subset (fun _ hw => hw.1)).to_subtype
  let (size : ℕ) : Fintype (blocks size) := Fintype.ofFinite _
  have hempty : ∀ parts : components 0, parts.val = [] := by
    intro parts
    cases heq : parts.val with
    | nil => rfl
    | cons first rest =>
      have hf := parts.property.1 first (by simp [heq])
      have hpos := List.length_pos_iff_ne_nil.mpr hf.1
      have hs := hsize 0 parts
      simp only [heq, assemble, directSum, shift, List.length_append,
        List.length_map] at hs
      omega
  have hnil : [] ∈ components 0 := by
    refine ⟨by simp, ?_⟩
    exact (hclosure [] (by simp)).mpr (by simp)
  have hzero : coeff 0 sequences = 1 := by
    have hsingleton : components 0 = {[]} := by
      ext parts
      exact ⟨fun hp => hempty ⟨parts, hp⟩,
        fun hp => by simpa only [Set.mem_singleton_iff.mp hp] using hnil⟩
    simp only [sequences, coeff_mk]
    have hterm : ∀ parts : components 0,
        (Polynomial.X : Polynomial ℚ) ^ parts.val.length = 1 := by
      intro parts
      simp [hempty parts]
    rw [finsum_congr hterm, finsum_eq_sum_of_fintype]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsingleton, Set.ncard_singleton]
    rfl
  have hcons (size : ℕ) : ∃ decomposition :
      (Σ cut : Fin (size + 1), blocks (cut.val + 1) × components (size - cut.val)) ≃
        components (size + 1),
      ∀ entry, (decomposition entry).val = entry.2.1.val :: entry.2.2.val := by
    let source := Σ cut : Fin (size + 1),
      blocks (cut.val + 1) × components (size - cut.val)
    have hjoin (entry : source) :
        entry.2.1.val :: entry.2.2.val ∈ components (size + 1) := by
      have hfirst := entry.2.1.property
      have hfLen : entry.2.1.val.length = entry.1.val + 1 := by
        simpa using hfirst.1.1.length_eq
      have hv : ∀ block ∈ entry.2.1.val :: entry.2.2.val, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
        intro block hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨List.length_pos_iff_ne_nil.mp (by omega),
            by simpa only [hfLen] using hfirst.1.1, hfirst.2⟩
        · exact entry.2.2.property.1 block hb
      have hc := (hclosure _ hv).mpr (by
        intro block hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simpa only [hfLen] using hfirst.1
        · exact hblock _ entry.2.2 block hb)
      have hl : (assemble (entry.2.1.val :: entry.2.2.val)).length = size + 1 := by
        simp only [assemble, directSum, shift, List.length_append, List.length_map,
          hfLen, hsize _ entry.2.2]
        omega
      exact ⟨hv, by simpa only [hl] using hc⟩
    let build (entry : source) : components (size + 1) :=
      ⟨entry.2.1.val :: entry.2.2.val, hjoin entry⟩
    have hi : Function.Injective build := by
      intro left right heq
      have hc := List.cons.inj (congrArg Subtype.val heq)
      have hl : left.2.1.val.length = left.1.val + 1 := by
        simpa using left.2.1.property.1.1.length_eq
      have hr : right.2.1.val.length = right.1.val + 1 := by
        simpa using right.2.1.property.1.1.length_eq
      have hindex : left.1 = right.1 := Fin.ext (by
        have he := congrArg List.length hc.1
        omega)
      rcases left with ⟨leftCut, leftBlock, leftTail⟩
      rcases right with ⟨rightCut, rightBlock, rightTail⟩
      dsimp at hindex hc
      subst rightCut
      exact congrArg (Sigma.mk leftCut)
        (Prod.ext (Subtype.ext hc.1) (Subtype.ext hc.2))
    have hs : Function.Surjective build := by
      intro parts
      cases heq : parts.val with
      | nil =>
        have hl := hsize _ parts
        simp only [heq, assemble, List.length_nil] at hl
        omega
      | cons first rest =>
        have hf := parts.property.1 first (by simp [heq])
        have hpositive := List.length_pos_iff_ne_nil.mpr hf.1
        have hl := hsize _ parts
        simp only [heq, assemble, directSum, shift, List.length_append,
          List.length_map] at hl
        let cut : Fin (size + 1) := ⟨first.length - 1, by omega⟩
        have hcut : cut.val + 1 = first.length := by dsimp [cut]; omega
        have hv : ∀ block ∈ rest, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block :=
          fun block hb => parts.property.1 block (by simp [heq, hb])
        have hc := (hclosure rest hv).mpr (fun block hb =>
          hblock _ parts block (by simp [heq, hb]))
        have ht : (assemble rest).length = size - cut.val := by dsimp [cut]; omega
        let left : blocks (cut.val + 1) := ⟨first, by
          exact ⟨by simpa only [hcut] using hblock _ parts first (by simp [heq]),
            hf.2.2⟩⟩
        let right : components (size - cut.val) := ⟨rest, hv,
          by simpa only [ht] using hc⟩
        exact ⟨⟨cut, left, right⟩, Subtype.ext heq.symm⟩
    exact ⟨Equiv.ofBijective build ⟨hi, hs⟩, fun _ => rfl⟩
  have hsum (size : ℕ) (weight : List (List ℕ) → Polynomial ℚ) :
      (∑ᶠ parts : components (size + 1), weight parts.val) =
        ∑ cut : Fin (size + 1), ∑ᶠ block : blocks (cut.val + 1),
          ∑ᶠ rest : components (size - cut.val), weight (block.val :: rest.val) := by
    obtain ⟨decomposition, heq⟩ := hcons size
    rw [← finsum_comp_equiv decomposition]
    simp only [finsum_eq_sum_of_fintype, Fintype.sum_sigma, Fintype.sum_prod_type, heq]
  have hrecurrence : sequences = 1 + C Polynomial.X * indecs * sequences := by
    apply PowerSeries.ext
    intro degree
    cases degree with
    | zero => simp [hzero, indecs, coeff_zero_eq_constantCoeff_apply]
    | succ degree =>
      rw [map_add, coeff_one, if_neg (by omega), zero_add, mul_assoc, coeff_C_mul,
        coeff_mul, Finset.Nat.sum_antidiagonal_succ]
      simp only [indecs, coeff_mk, ↓reduceIte, zero_mul, zero_add]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show coeff (degree + 1) sequences =
        ∑ᶠ parts : components (degree + 1),
          (Polynomial.X : Polynomial ℚ) ^ parts.val.length by
            simp only [sequences, coeff_mk]]
      rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^ parts.length)]
      rw [← Fin.sum_univ_eq_sum_range]
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro cut _
      simp only [List.length_cons, pow_succ, finsum_eq_sum_of_fintype]
      rw [sum_comm]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (blocks (cut.val + 1)) : Polynomial ℚ) =
          ({word : List ℕ | word ∈ avoiders (cut.val + 1) patterns ∧
            sumIndecomposable word}.ncard : Polynomial ℚ) := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simp only [hcard, sequences, coeff_mk, finsum_eq_sum_of_fintype]
      conv_rhs => rw [mul_left_comm Polynomial.X, mul_sum, mul_sum]
      apply Finset.sum_congr rfl
      intro rest _
      ring
  refine ⟨fun size => ⟨serialization size, fun _ => rfl⟩, ?_, ?_⟩
  · linear_combination hrecurrence
  intro weight
  let marked : PowerSeries (Polynomial ℚ) := mk fun size =>
    if size = 0 then 0 else ∑ᶠ block : blocks size, weight size block.val
  let heads : PowerSeries (Polynomial ℚ) := mk fun size =>
    if size = 0 then 0 else ∑ᶠ parts : components size,
      (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
        weight (parts.val.headD []).length (parts.val.headD [])
  let lasts : PowerSeries (Polynomial ℚ) := mk fun size =>
    if size = 0 then 0 else ∑ᶠ parts : components size,
      (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1) *
        weight (parts.val.reverse.headD []).length (parts.val.reverse.headD [])
  let tails : PowerSeries (Polynomial ℚ) := mk fun size =>
    if size = 0 then 0 else ∑ᶠ parts : components size,
      (Polynomial.X : Polynomial ℚ) ^
        (if parts.val.tail = [] then 1 else parts.val.tail.length) *
          weight (parts.val.headD []).length (parts.val.headD [])
  change heads = marked * sequences ∧ lasts = heads ∧
    tails = C Polynomial.X * marked + marked * (sequences - 1)
  have hheads : heads = marked * sequences := by
    apply PowerSeries.ext
    intro degree
    cases degree with
    | zero => simp [heads, marked, coeff_zero_eq_constantCoeff_apply]
    | succ degree =>
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
      simp only [marked, coeff_mk, ↓reduceIte, zero_mul, zero_add]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [heads, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
      rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
        (parts.length - 1) * weight (parts.headD []).length (parts.headD [])),
        ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro cut _
      have hl (block : blocks (cut.val + 1)) : block.val.length = cut.val + 1 := by
        simpa using block.property.1.1.length_eq
      simp only [List.length_cons, Nat.add_sub_cancel, List.headD_cons, hl,
        finsum_eq_sum_of_fintype, sequences, coeff_mk]
      rw [sum_mul]
      apply Finset.sum_congr rfl
      intro block _
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro rest _
      exact mul_comm _ _
  refine ⟨hheads, ?_, ?_⟩
  · have hreverse (size : ℕ) (parts : components size) :
        parts.val.reverse ∈ components size := by
      have hv : ∀ block ∈ parts.val.reverse, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
        intro block hb
        exact parts.property.1 block (List.mem_reverse.mp hb)
      have hc := (hclosure _ hv).mpr (fun block hb =>
        hblock _ parts block (List.mem_reverse.mp hb))
      have hl : (assemble parts.val.reverse).length = size := by
        rw [hlength, List.map_reverse, List.sum_reverse, ← hlength, hsize]
      exact ⟨hv, by simpa only [hl] using hc⟩
    let reversal (size : ℕ) : components size ≃ components size :=
      { toFun := fun parts => ⟨parts.val.reverse, hreverse size parts⟩
        invFun := fun parts => ⟨parts.val.reverse, hreverse size parts⟩
        left_inv := fun parts => Subtype.ext (List.reverse_reverse parts.val)
        right_inv := fun parts => Subtype.ext (List.reverse_reverse parts.val) }
    apply PowerSeries.ext
    intro degree
    by_cases hz : degree = 0
    · simp [lasts, heads, hz]
    simp only [lasts, heads, coeff_mk, if_neg hz]
    rw [← finsum_comp_equiv (reversal degree)]
    apply finsum_congr
    intro parts
    simp [reversal]
  · have htailDifference : tails - heads = (C Polynomial.X - 1) * marked := by
      apply PowerSeries.ext
      intro degree
      cases degree with
      | zero => simp [tails, heads, marked, coeff_zero_eq_constantCoeff_apply]
      | succ degree =>
        rw [map_sub, sub_mul, one_mul, map_sub, coeff_C_mul]
        simp only [tails, heads, marked, coeff_mk, Nat.add_one_ne_zero, ↓reduceIte]
        rw [hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
          (if parts.tail = [] then 1 else parts.tail.length) *
            weight (parts.headD []).length (parts.headD [])),
          hsum degree (fun parts => (Polynomial.X : Polynomial ℚ) ^
            (parts.length - 1) * weight (parts.headD []).length (parts.headD []))]
        simp only [List.headD_cons, List.length_cons, Nat.add_sub_cancel,
          finsum_eq_sum_of_fintype]
        change (∑ cut : Fin (degree + 1), ∑ block : blocks (cut.val + 1),
          ∑ rest : components (degree - cut.val),
            Polynomial.X ^ (if rest.val = [] then 1 else rest.val.length) *
              weight block.val.length block.val) -
          (∑ cut : Fin (degree + 1), ∑ block : blocks (cut.val + 1),
            ∑ rest : components (degree - cut.val),
              Polynomial.X ^ rest.val.length * weight block.val.length block.val) = _
        rw [← sum_sub_distrib]
        let lastCut : Fin (degree + 1) := ⟨degree, by omega⟩
        rw [Finset.sum_eq_single lastCut]
        · dsimp +instances only [lastCut]
          have he (parts : components (degree - degree)) : parts.val = [] :=
            hempty ⟨parts.val, by simpa only [Nat.sub_self] using parts.property⟩
          let : Unique (components (degree - degree)) :=
            { default := ⟨[], by simpa only [Nat.sub_self] using hnil⟩
              uniq := fun parts => Subtype.ext (he parts) }
          have hl (block : blocks (degree + 1)) : block.val.length = degree + 1 := by
            simpa using block.property.1.1.length_eq
          simp only [he, ↓reduceIte, List.length_nil, pow_zero, pow_one, one_mul, hl,
            sum_const, card_univ, Fintype.card_unique, one_smul, ← mul_sum]
        · intro cut _ hne
          have hindex : cut.val ≠ degree := by
            intro heq
            exact hne (Fin.ext heq)
          have hpositive : 0 < degree - cut.val := by omega
          have hl (rest : components (degree - cut.val)) : rest.val ≠ [] := by
            intro heq
            have hs := hsize _ rest
            simp only [heq, assemble, List.length_nil] at hs
            omega
          simp only [hl, ↓reduceIte, sub_self]
        · simp
    linear_combination htailDifference + hheads

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenComponentSeries
