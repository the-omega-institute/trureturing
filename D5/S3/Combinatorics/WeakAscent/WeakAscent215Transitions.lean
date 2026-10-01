/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Transitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Transitions
   mirror-E: none(waiver:four-left-site-transitions)
   anchors: []
   utility: none
   digest: Constructs the four exact transitions of numerical lower active sites. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215WordHistory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Transitions

open WeakAscentDefs WeakAscentQuadrupleDefs WeakAscent215Left WeakAscent215Sites
open WeakAscent215WordHistory

theorem left_transitions (word : List ℕ) (hne : word ≠ [])
    (hword : word ∈ avoiders word.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) :
    let maximum := word.foldr max 0
    let budget := 1 + wasc word - maximum
    let mode := decide (word.getLast?.getD 0 = maximum)
    ∃ replayEquiv : (Fin budget ⊕ Fin (activeValues word).length) ≃
        {letter : ℕ // word ++ [letter] ∈
          avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]},
      (∀ gap, let letter := (replayEquiv (.inl gap)).val
        letter = maximum + gap.val + 1 ∧
        activeMarks (word ++ [letter]) =
          activeMarks word ++ List.replicate gap.val false ++ [true] ∧
        1 + wasc (word ++ [letter]) - (word ++ [letter]).foldr max 0 = budget - gap.val ∧
        decide ((word ++ [letter]).getLast?.getD 0 = (word ++ [letter]).foldr max 0) = true) ∧
      (∀ site, let letter := (replayEquiv (.inr site)).val
        letter = (activeValues word).get site ∧
        if (activeMarks word).getD site.val true = false then
          activeMarks (word ++ [letter]) = (activeMarks word).take site.val ∧
          1 + wasc (word ++ [letter]) - (word ++ [letter]).foldr max 0 = budget ∧
          decide ((word ++ [letter]).getLast?.getD 0 = (word ++ [letter]).foldr max 0) = false
        else if mode && (site.val + 1 == (activeValues word).length) then
          activeMarks (word ++ [letter]) = [true] ∧
          1 + wasc (word ++ [letter]) - (word ++ [letter]).foldr max 0 = budget + 1 ∧
          decide ((word ++ [letter]).getLast?.getD 0 = (word ++ [letter]).foldr max 0) = true
        else activeMarks (word ++ [letter]) = [] ∧
          1 + wasc (word ++ [letter]) - (word ++ [letter]).foldr max 0 = budget ∧
          decide ((word ++ [letter]).getLast?.getD 0 =
            (word ++ [letter]).foldr max 0) = false) := by
  have numeric_transitions (word : List ℕ) (hne : word ≠ [])
      (hword : word ∈ avoiders word.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
      (letter : ℕ)
      (hchild : word ++ [letter] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) :
      let maximum := word.foldr max 0
      let child := word ++ [letter]
      let oldSites : Set ℕ := {value | value ≤ maximum ∧ word ++ [value] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]}
      let newSites : Set ℕ := {value | value ≤ child.foldr max 0 ∧ child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]}
      (maximum < letter → child.foldr max 0 = letter ∧ wasc child = wasc word + 1 ∧
          newSites = oldSites ∪ Set.Icc (maximum + 1) letter) ∧
      (letter ≤ maximum → letter ∉ word →
        child.foldr max 0 = maximum ∧ wasc child = wasc word ∧
          newSites = oldSites ∩ Set.Iio letter) ∧
      (letter < maximum → letter ∈ word →
        child.foldr max 0 = maximum ∧ wasc child = wasc word ∧ newSites = ∅) ∧
      (letter = maximum → child.foldr max 0 = maximum ∧ wasc child = wasc word + 1 ∧
          newSites = {maximum}) := by
    classical
    dsimp only
    let maximum := word.foldr max 0
    let child := word ++ [letter]
    let bad (values : List ℕ) (value : ℕ) : Prop :=
      ∃ first second, first < second ∧ second < values.length ∧
        values.getD second 0 < values.getD first 0 ∧
        values.getD second 0 ≤ value ∧ value ≤ values.getD first 0
    have hlength : 0 < word.length := List.length_pos_iff.mpr hne
    have child_ne : child ≠ [] := by simp [child]
    have hchild' : child ∈
        avoiders child.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] := by
      simpa [child] using hchild
    have hlegal := (left_append_iff word hne hword letter).mp hchild
    have hstructure := left_active_structure word hne hword
    have hheight : maximum < 1 + wasc word := hstructure.1
    have read_bound (index : ℕ) (hindex : index < word.length) :
        word.getD index 0 ≤ maximum := by
      rw [List.getD_eq_getElem _ _ hindex]
      exact List.le_max_of_le (List.getElem_mem hindex) (Nat.le_refl _)
    have maximum_mem : maximum ∈ word := by
      have heq : maximum = word.max hne := by
        apply Nat.le_antisymm
        · exact List.max_le_of_forall_le word _ fun value hvalue => List.le_max_of_mem hvalue
        · exact List.le_max_of_le (List.max_mem hne) (Nat.le_refl _)
      rw [heq]
      exact List.max_mem hne
    obtain ⟨maximumIndex, hmaximumIndex, hmaximumValue⟩ := List.mem_iff_getElem.mp maximum_mem
    have maximum_read : word.getD maximumIndex 0 = maximum := by
      rw [List.getD_eq_getElem _ _ hmaximumIndex]
      exact hmaximumValue
    have last_read : word.getD (word.length - 1) 0 = word.getLast?.getD 0 := by
      rw [List.getLast?_eq_some_getLast hne, Option.getD_some,
        List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    have hlast : word.getLast?.getD 0 ≤ maximum := by
      rw [← last_read]
      exact read_bound _ (by omega)
    have old_read (index : ℕ) (hindex : index < word.length) :
        child.getD index 0 = word.getD index 0 := List.getD_append _ _ _ _ hindex
    have new_read : child.getD word.length 0 = letter := by
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      simp
    have maximum_update : child.foldr max 0 = max maximum letter := by
      have append_max (values : List ℕ) :
          (values ++ [letter]).foldr max 0 = max (values.foldr max 0) letter := by
        induction values with
        | nil => simp
        | cons first rest ih => simp [ih, max_assoc]
      exact append_max word
    have wasc_update : wasc child = wasc word +
        if word.getLast?.getD 0 ≤ letter then 1 else 0 := by
      have append_ascents (parent : List ℕ) :
          wasc (parent ++ [letter]) = wasc parent +
            if parent = [] then 0 else if parent.getLast?.getD 0 ≤ letter then 1 else 0 := by
        induction parent with
        | nil => simp [wasc]
        | cons first rest ih =>
          cases rest with
          | nil => by_cases hpair : first ≤ letter <;> simp [wasc, hpair]
          | cons second tail =>
            simp only [List.cons_append, wasc, List.tail_cons, List.zip_cons_cons,
              List.filter_cons] at ih ⊢
            by_cases hpair : first ≤ second
            · simp [hpair, List.getLast?_cons_cons, List.cons_ne_nil] at ih ⊢
              omega
            · simp only [decide_eq_true_eq, hpair, reduceCtorEq, ↓reduceIte,
                List.getLast?_cons_cons] at ih ⊢
              exact ih
      simpa [hne] using append_ascents word
    have threshold_test (values : List ℕ) (bound : ℕ) :
        repeatedThreshold values ≤ bound ↔
          ∀ first second, first < second → second < values.length →
            values.getD first 0 = values.getD second 0 → values.getD second 0 ≤ bound := by
      unfold repeatedThreshold
      constructor
      · intro h first second hfs hs heq
        have hsup := Finset.le_sup (f := fun second => if ∃ first, first < second ∧
            values.getD first 0 = values.getD second 0 then values.getD second 0 else 0)
          (Finset.mem_range.mpr hs)
        rw [if_pos ⟨first, hfs, heq⟩] at hsup
        exact hsup.trans h
      · intro h
        apply Finset.sup_le_iff.mpr
        intro second hs
        split
        · rename_i hrepeat
          obtain ⟨first, hfs, heq⟩ := hrepeat
          exact h first second hfs (Finset.mem_range.mp hs) heq
        · exact Nat.zero_le _
    have threshold_update : repeatedThreshold child =
        if letter ∈ word then max (repeatedThreshold word) letter
          else repeatedThreshold word := by
      by_cases hmem : letter ∈ word
      · rw [if_pos hmem]
        apply Nat.le_antisymm
        · apply (threshold_test child _).mpr
          intro first second hfs hs heq
          have hs' : second < word.length + 1 := by simpa [child] using hs
          by_cases hold : second < word.length
          · rw [old_read first (by omega), old_read second hold] at heq
            rw [old_read second hold]
            exact ((threshold_test word _).mp (Nat.le_refl _) first second hfs hold heq).trans
              (Nat.le_max_left _ _)
          · have heqlast : second = word.length := by omega
            subst second
            rw [new_read]
            exact Nat.le_max_right _ _
        · apply max_le
          · apply (threshold_test word _).mpr
            intro first second hfs hs heq
            have hle := (threshold_test child _).mp (Nat.le_refl _)
              first second hfs (by simpa [child] using (by omega : second < word.length + 1))
              (by rwa [old_read first (by omega), old_read second hs])
            rwa [old_read second hs] at hle
          · obtain ⟨first, hfirst, hvalue⟩ := List.mem_iff_getElem.mp hmem
            have hfirstread : word.getD first 0 = letter := by rwa [List.getD_eq_getElem _ _ hfirst]
            have hle := (threshold_test child _).mp (Nat.le_refl _)
              first word.length hfirst (by simp [child])
              (by rw [old_read first hfirst, new_read, hfirstread])
            rwa [new_read] at hle
      · rw [if_neg hmem]
        apply Nat.le_antisymm
        · apply (threshold_test child _).mpr
          intro first second hfs hs heq
          have hs' : second < word.length + 1 := by simpa [child] using hs
          by_cases hold : second < word.length
          · rw [old_read first (by omega), old_read second hold] at heq
            rw [old_read second hold]
            exact (threshold_test word _).mp (Nat.le_refl _) first second hfs hold heq
          · have heqlast : second = word.length := by omega
            subst second
            rw [old_read first hfs, new_read, List.getD_eq_getElem _ _ hfs] at heq
            exact False.elim (hmem (heq ▸ List.getElem_mem hfs))
        · apply (threshold_test word _).mpr
          intro first second hfs hs heq
          have hle := (threshold_test child _).mp (Nat.le_refl _)
            first second hfs (by simpa [child] using (by omega : second < word.length + 1))
            (by rwa [old_read first (by omega), old_read second hs])
          rwa [old_read second hs] at hle
    have bad_update (value : ℕ) : bad child value ↔
        bad word value ∨ (letter < maximum ∧ letter ≤ value ∧ value ≤ maximum) := by
      constructor
      · rintro ⟨first, second, hfs, hs, hinv, hlow, hhigh⟩
        have hs' : second < word.length + 1 := by simpa [child] using hs
        by_cases hold : second < word.length
        · simp only [old_read first (by omega), old_read second hold] at hinv hlow hhigh
          exact Or.inl ⟨first, second, hfs, hold, hinv, hlow, hhigh⟩
        · have heq : second = word.length := by omega
          subst second
          simp only [old_read first hfs, new_read] at hinv hlow hhigh
          have hfirst := read_bound first hfs
          exact Or.inr ⟨by omega, hlow, by omega⟩
      · rintro (⟨first, second, hfs, hs, hinv, hlow, hhigh⟩ | ⟨hlt, hlow, hhigh⟩)
        · refine ⟨first, second, hfs, by simpa [child] using
            (by omega : second < word.length + 1), ?_⟩
          rw [old_read first (by omega), old_read second hs]
          exact ⟨hinv, hlow, hhigh⟩
        · refine ⟨maximumIndex, word.length, hmaximumIndex, by simp [child], ?_⟩
          rw [old_read maximumIndex hmaximumIndex, new_read, maximum_read]
          exact ⟨hlt, hlow, hhigh⟩
    have old_choice (value : ℕ) : word ++ [value] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
        repeatedThreshold word ≤ value ∧ value ≤ 1 + wasc word ∧ ¬ bad word value :=
      left_append_iff word hne hword value
    have new_choice (value : ℕ) : child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
        repeatedThreshold child ≤ value ∧ value ≤ 1 + wasc child ∧ ¬ bad child value :=
      left_append_iff child child_ne hchild' value
    have threshold_bound : repeatedThreshold word ≤ maximum := by
      apply (threshold_test word _).mpr
      intro first second hfs hs heq
      exact read_bound second hs
    have high_not_bad (value : ℕ) (hvalue : maximum < value) : ¬ bad word value := by
      rintro ⟨first, second, hfs, hs, hinv, hlow, hhigh⟩
      have hfirst := read_bound first (by omega)
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hrecord
      have hfresh : letter ∉ word := by
        intro hmem
        have hb : letter ≤ maximum := List.le_max_of_le hmem (Nat.le_refl _)
        omega
      have hmaxchild : child.foldr max 0 = letter := by rw [maximum_update, max_eq_right]; omega
      have hascent : word.getLast?.getD 0 ≤ letter := by omega
      have hwaschild : wasc child = wasc word + 1 := by rw [wasc_update, if_pos hascent]
      have hthreshold : repeatedThreshold child = repeatedThreshold word := by
        rw [threshold_update, if_neg hfresh]
      refine ⟨hmaxchild, hwaschild, ?_⟩
      ext value
      change (value ≤ child.foldr max 0 ∧ child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ↔ _
      rw [hmaxchild, new_choice, hthreshold, hwaschild, bad_update]
      change _ ↔ (value ≤ maximum ∧ word ++ [value] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ∨
        (maximum + 1 ≤ value ∧ value ≤ letter)
      rw [old_choice]
      constructor
      · rintro ⟨hv, hr, hb, hbad⟩
        by_cases hlow : value ≤ maximum
        · exact Or.inl ⟨hlow, hr, by omega, fun h => hbad (Or.inl h)⟩
        · exact Or.inr ⟨by omega, hv⟩
      · rintro (⟨hv, hr, hb, hbad⟩ | ⟨hv, hb⟩)
        · exact ⟨by omega, hr, by omega, by
            rintro (h | h)
            · exact hbad h
            · omega⟩
        · exact ⟨hb, by omega, by omega, by
            rintro (h | h)
            · exact high_not_bad value (by omega) h
            · omega⟩
    · intro hlow hfresh
      have hlt : letter < maximum := by
        by_contra hnot
        have heq : letter = maximum := by omega
        exact hfresh (heq ▸ maximum_mem)
      have hdesc : letter < word.getLast?.getD 0 := hstructure.2.2.2 letter hlow hchild (by omega)
      have hmaxchild : child.foldr max 0 = maximum := by rw [maximum_update, max_eq_left hlow]
      have hwaschild : wasc child = wasc word := by
        rw [wasc_update, if_neg (by omega), Nat.add_zero]
      have hthreshold : repeatedThreshold child = repeatedThreshold word := by
        rw [threshold_update, if_neg hfresh]
      refine ⟨hmaxchild, hwaschild, ?_⟩
      ext value
      change (value ≤ child.foldr max 0 ∧ child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ↔ _
      rw [hmaxchild, new_choice, hthreshold, hwaschild, bad_update]
      change _ ↔ (value ≤ maximum ∧ word ++ [value] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ∧
        value < letter
      rw [old_choice]
      constructor
      · rintro ⟨hv, hr, hb, hbad⟩
        exact ⟨⟨hv, hr, hb, fun h => hbad (Or.inl h)⟩, by
          by_contra hnot; exact hbad (Or.inr ⟨hlt, by omega, hv⟩)⟩
      · rintro ⟨⟨hv, hr, hb, hbad⟩, hbefore⟩
        exact ⟨hv, hr, hb, by
          rintro (h | h)
          · exact hbad h
          · omega⟩
    · intro hlt hold
      have hlow : letter ≤ maximum := by omega
      have hdesc : letter < word.getLast?.getD 0 := hstructure.2.2.2 letter hlow hchild (by omega)
      have hmaxchild : child.foldr max 0 = maximum := by rw [maximum_update, max_eq_left hlow]
      have hwaschild : wasc child = wasc word := by
        rw [wasc_update, if_neg (by omega), Nat.add_zero]
      have hthreshold : repeatedThreshold child = letter := by
        rw [threshold_update, if_pos hold, max_eq_right hlegal.1]
      refine ⟨hmaxchild, hwaschild, ?_⟩
      ext value
      change (value ≤ child.foldr max 0 ∧ child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ↔ False
      rw [hmaxchild, new_choice, hthreshold, bad_update]
      constructor
      · rintro ⟨hv, hr, hb, hbad⟩
        exact hbad (Or.inr ⟨hlt, hr, hv⟩)
      · exact False.elim
    · intro heq
      have hold : letter ∈ word := heq ▸ maximum_mem
      have hlastmax : word.getLast?.getD 0 = maximum := hstructure.2.2.1.mp (by
        simpa only [heq] using hchild)
      have hascent : word.getLast?.getD 0 ≤ letter := by omega
      have hmaxchild : child.foldr max 0 = maximum := by rw [maximum_update, heq, max_self]
      have hwaschild : wasc child = wasc word + 1 := by rw [wasc_update, if_pos hascent]
      have hthreshold : repeatedThreshold child = maximum := by
        rw [threshold_update, if_pos hold, heq, max_eq_right threshold_bound]
      refine ⟨hmaxchild, hwaschild, ?_⟩
      ext value
      change (value ≤ child.foldr max 0 ∧ child ++ [value] ∈
        avoiders (child.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ↔
        value = maximum
      rw [hmaxchild, new_choice, hthreshold, hwaschild, bad_update]
      constructor
      · rintro ⟨hv, hr, hb, hbad⟩
        omega
      · intro hv
        subst value
        exact ⟨Nat.le_refl _, Nat.le_refl _, by omega, by
          rintro (h | h)
          · exact hlegal.2.2 (by simpa only [heq] using h)
          · omega⟩
  classical
  dsimp only
  let maximum := word.foldr max 0
  let budget := 1 + wasc word - maximum
  let values := activeValues word
  let marks := activeMarks word
  let Children := {letter : ℕ // word ++ [letter] ∈
    avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]}
  let numericalSites (parent : List ℕ) : Set ℕ := {value | value ≤ parent.foldr max 0 ∧
    parent ++ [value] ∈ avoiders (parent.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]}
  have mem_values (parent : List ℕ) (value : ℕ) : value ∈ activeValues parent ↔
      value ≤ parent.foldr max 0 ∧ parent ++ [value] ∈
        avoiders (parent.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] := by
    simp [activeValues]
  have sorted_values (parent : List ℕ) : (activeValues parent).Pairwise (· < ·) := by
    exact (Finset.sortedLT_sort _).pairwise
  have hstructure := left_active_structure word hne hword
  have hheight : maximum < 1 + wasc word := hstructure.1
  have hbudget : 0 < budget := by omega
  have site_mem (site : Fin values.length) : values.get site ∈ values :=
    List.getElem_mem site.isLt
  have site_bound (site : Fin values.length) : values.get site ≤ maximum :=
    ((mem_values word _).mp (site_mem site)).1
  let decode : Fin budget ⊕ Fin values.length → Children := fun choice =>
    match choice with
    | .inl gap => ⟨maximum + gap.val + 1,
        (hstructure.2.1 _ (by omega) (by have := gap.isLt; omega)).1⟩
    | .inr site => ⟨values.get site, ((mem_values word _).mp (site_mem site)).2⟩
  have decode_injective : Function.Injective decode := by
    intro first second heq
    cases first with
    | inl first =>
      cases second with
      | inl second =>
        have hval := congrArg Subtype.val heq
        apply congrArg Sum.inl
        apply Fin.ext
        change maximum + first.val + 1 = maximum + second.val + 1 at hval
        omega
      | inr second =>
        have hval := congrArg Subtype.val heq
        have hbound := site_bound second
        change maximum + first.val + 1 = values.get second at hval
        omega
    | inr first =>
      cases second with
      | inl second =>
        have hval := congrArg Subtype.val heq
        have hbound := site_bound first
        change values.get first = maximum + second.val + 1 at hval
        have hrecord : maximum < maximum + second.val + 1 :=
          Nat.lt_succ_of_le (Nat.le_add_right _ _)
        exact False.elim (Nat.not_lt_of_ge hbound (hval.symm ▸ hrecord))
      | inr second =>
        have hval := congrArg Subtype.val heq
        apply congrArg Sum.inr
        have hnodup : values.Nodup := (sorted_values word).nodup
        exact hnodup.get_inj_iff.mp hval
  have decode_surjective : Function.Surjective decode := by
    intro child
    by_cases hrecord : maximum < child.val
    · have hbound := (WeakAscent215Left.left_append_iff word hne hword child.val).mp child.property
      let gap : Fin budget := ⟨child.val - maximum - 1, by dsimp [budget]; omega⟩
      refine ⟨.inl gap, Subtype.ext ?_⟩
      change maximum + gap.val + 1 = child.val
      dsimp [gap]
      omega
    · have hmem : child.val ∈ values := (mem_values word _).mpr ⟨by omega, child.property⟩
      obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
      exact ⟨.inr ⟨index, hindex⟩, Subtype.ext hvalue⟩
  let replayEquiv := Equiv.ofBijective decode ⟨decode_injective, decode_surjective⟩
  have maximum_mem : maximum ∈ word := by
    have heq : maximum = word.max hne := by
      apply Nat.le_antisymm
      · exact List.max_le_of_forall_le word _ fun value hvalue => List.le_max_of_mem hvalue
      · exact List.le_max_of_le (List.max_mem hne) (Nat.le_refl _)
    rw [heq]
    exact List.max_mem hne
  have mark_read (site : Fin values.length) : marks.getD site.val true =
      decide (values.get site ∈ word) := by
    rw [List.getD_eq_getElem _ _ (by simp [marks, activeMarks, values, site.isLt])]
    simp [marks, activeMarks, values]
  refine ⟨replayEquiv, ?_, ?_⟩
  · intro gap
    change maximum + gap.val + 1 = maximum + gap.val + 1 ∧ _
    let letter := maximum + gap.val + 1
    let child := word ++ [letter]
    have hchild := (decode (.inl gap)).property
    have hrecord : maximum < letter := by omega
    have htransition := (numeric_transitions word hne hword letter hchild).1 hrecord
    have hsites : numericalSites child = numericalSites word ∪
        Set.Icc (maximum + 1) letter := htransition.2.2
    have hvalues : activeValues child =
        values ++ List.range' (maximum + 1) gap.val ++ [letter] := by
      apply (sorted_values child).eq_of_mem_iff
      · apply List.pairwise_append.mpr
        refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
        · apply List.pairwise_append.mpr
          refine ⟨sorted_values word, ?_, ?_⟩
          · exact (List.sortedLT_range' _ _ (by decide)).pairwise
          · intro old hold fresh hfresh
            have hbound := ((mem_values word old).mp hold).1
            have := List.mem_range'.mp hfresh
            omega
        · intro value hvalue last hlast
          simp only [List.mem_singleton] at hlast
          subst last
          rcases List.mem_append.mp hvalue with hold | hfresh
          · have hbound := ((mem_values word value).mp hold).1
            omega
          · have := List.mem_range'.mp hfresh
            omega
      · intro value
        rw [mem_values]
        change value ∈ numericalSites child ↔ _
        rw [hsites]
        simp only [Set.mem_union, numericalSites, Set.mem_ofPred_eq, Set.mem_Icc, List.mem_append,
          List.mem_range', List.mem_singleton]
        rw [mem_values]
        have hrange : (∃ index < gap.val, value = maximum + 1 + 1 * index) ↔
            maximum + 1 ≤ value ∧ value < maximum + 1 + gap.val := by
          constructor
          · rintro ⟨index, hindex, hvalue⟩
            omega
          · rintro ⟨hlow, hhigh⟩
            exact ⟨value - (maximum + 1), by omega, by omega⟩
        rw [hrange]
        dsimp [letter, maximum]
        by_cases hsite : value ≤ word.foldr max 0 ∧ word ++ [value] ∈
            avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
        · simp only [hsite, true_and, true_or]
        · simp only [hsite, false_or]
          omega
    have hmarks : activeMarks child = marks ++ List.replicate gap.val false ++ [true] := by
      rw [activeMarks, hvalues, List.map_append, List.map_append]
      have old_marks : values.map (fun value => decide (value ∈ child)) = marks := by
        apply List.map_congr_left
        intro value hvalue
        have hbound := ((mem_values word value).mp hvalue).1
        have hneq : value ≠ letter := by omega
        simp [child, hneq]
      have fresh_marks : (List.range' (maximum + 1) gap.val).map
          (fun value => decide (value ∈ child)) = List.replicate gap.val false := by
        have hconstant : ∀ value ∈ List.range' (maximum + 1) gap.val,
            decide (value ∈ child) = false := by
          intro value hvalue
          have hinterval := List.mem_range'.mp hvalue
          have hnot : value ∉ word := by
            intro hmem
            have := List.le_max_of_le hmem (Nat.le_refl value)
            change value ≤ maximum at this
            omega
          have hneq : value ≠ letter := by dsimp [letter]; omega
          simp [child, hnot, hneq]
        simpa using List.map_eq_replicate_iff.mpr hconstant
      rw [old_marks, fresh_marks]
      simp [child]
    refine ⟨rfl, hmarks, ?_, ?_⟩
    · change 1 + wasc child - child.foldr max 0 = budget - gap.val
      rw [htransition.1, htransition.2.1]
      dsimp [budget, letter]
      have := gap.isLt
      omega
    · change decide (child.getLast?.getD 0 = child.foldr max 0) = true
      rw [htransition.1]
      simp [child]
  · intro site
    change values.get site = values.get site ∧ _
    let letter := values.get site
    let child := word ++ [letter]
    have hchild := (decode (.inr site)).property
    have hle : letter ≤ maximum := site_bound site
    have htransition := numeric_transitions word hne hword letter hchild
    have child_last : child.getLast?.getD 0 = letter := by simp [child]
    have selected_read : marks.getD site.val true = decide (letter ∈ word) := mark_read site
    refine ⟨rfl, ?_⟩
    split
    · rename_i hfresh
      have hnot : letter ∉ word := by
        rw [selected_read] at hfresh
        exact of_decide_eq_false hfresh
      have hneq : letter ≠ maximum := by intro heq; exact hnot (heq ▸ maximum_mem)
      have hupdate := htransition.2.1 hle hnot
      have hsites : numericalSites child = numericalSites word ∩ Set.Iio letter := hupdate.2.2
      have hvalues : activeValues child = values.take site.val := by
        apply (sorted_values child).eq_of_mem_iff (sorted_values word).take
        intro value
        rw [mem_values]
        change value ∈ numericalSites child ↔ _
        rw [hsites]
        simp only [Set.mem_inter_iff, numericalSites, Set.mem_ofPred_eq, Set.mem_Iio]
        rw [← mem_values]
        constructor
        · rintro ⟨hmem, hlt⟩
          obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
          change values[index] = value at hvalue
          have hbefore : index < site.val := by
            by_contra hnotbefore
            have hafter : site.val ≤ index := by omega
            rcases Nat.eq_or_lt_of_le hafter with heq | hafter
            · have hsame : value = letter := by
                change value = values[site.val]
                simpa only [← heq] using hvalue.symm
              omega
            · have hordered := (sorted_values word).rel_get_of_lt
                (a := site) (b := ⟨index, hindex⟩) hafter
              change letter < values[index] at hordered
              omega
          apply List.mem_iff_getElem.mpr
          exact ⟨index, by simp; omega, by simpa using hvalue⟩
        · intro hmem
          obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
          have hbefore : index < site.val := by simp only [List.length_take] at hindex; omega
          have hindex' : index < values.length := by
            have hsiteLength : site.val < values.length := site.isLt
            omega
          have hordered := (sorted_values word).rel_get_of_lt
            (a := ⟨index, hindex'⟩) (b := site) hbefore
          have hread : values[index] = value := by simpa using hvalue
          refine ⟨?_, ?_⟩
          · rw [← hread]
            exact List.getElem_mem hindex'
          · change values[index] < letter at hordered
            omega
      have hmarks : activeMarks child = marks.take site.val := by
        change (activeValues child).map (fun value => decide (value ∈ child)) =
          (values.map (fun value => decide (value ∈ word))).take site.val
        rw [hvalues, ← List.map_take]
        apply List.map_congr_left
        intro value hvalue
        have hmem : value ∈ values := List.mem_of_mem_take hvalue
        have hneq : value ≠ letter := by
          intro heq
          have hnodup := (sorted_values word).nodup
          have hindex : values.idxOf letter = site.val := by
            exact List.Nodup.idxOf_getElem hnodup site.val site.isLt
          have hlt := (List.mem_take_iff_idxOf_lt hmem).mp hvalue
          rw [heq, hindex] at hlt
          omega
        simp [child, hneq]
      refine ⟨hmarks, ?_, ?_⟩
      · change 1 + wasc child - child.foldr max 0 = budget
        rw [hupdate.1, hupdate.2.1]
      · change decide (child.getLast?.getD 0 = child.foldr max 0) = false
        rw [child_last, hupdate.1]
        change decide (letter = maximum) = false
        simp [hneq]
    · rename_i hold
      have hmem : letter ∈ word := by
        rw [selected_read] at hold
        exact of_decide_eq_true (Bool.eq_true_of_not_eq_false hold)
      have top_iff :
          (decide (word.getLast?.getD 0 = maximum) &&
            (site.val + 1 == (activeValues word).length)) = true ↔ letter = maximum := by
        constructor
        · intro htop
          obtain ⟨hmode, hlast⟩ : decide (word.getLast?.getD 0 = maximum) = true ∧
              (site.val + 1 == (activeValues word).length) = true := by
            simpa only [Bool.and_eq_true] using htop
          have hmaximum_active := hstructure.2.2.1.mpr (of_decide_eq_true hmode)
          have hmaxmem : maximum ∈ values := (mem_values word _).mpr ⟨le_rfl, hmaximum_active⟩
          obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
          have htopindex : site.val + 1 = values.length := by exact of_decide_eq_true hlast
          have hsame : index = site.val := by
            by_contra hnot
            have hbefore : index < site.val := by omega
            have hordered := (sorted_values word).rel_get_of_lt
              (a := ⟨index, hindex⟩) (b := site) hbefore
            change values[index] < letter at hordered
            omega
          change values[site.val] = maximum
          simpa only [hsame] using hvalue
        · intro heq
          have hchildmax : word ++ [maximum] ∈ avoiders (word.length + 1)
                [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] := by
            simpa only [← heq] using hchild
          have hmode := hstructure.2.2.1.mp hchildmax
          have htopindex : site.val + 1 = values.length := by
            by_contra hnot
            have hsiteLength : site.val < values.length := site.isLt
            have hnext : site.val + 1 < values.length := by omega
            have hordered := (sorted_values word).rel_get_of_lt
              (a := site) (b := ⟨site.val + 1, hnext⟩)
              (by change site.val < site.val + 1; omega)
            have hbound := site_bound ⟨site.val + 1, hnext⟩
            change values[site.val + 1] ≤ maximum at hbound
            change letter < values[site.val + 1] at hordered
            omega
          simp [hmode, htopindex, maximum, values]
      split
      · rename_i htop
        have heq := top_iff.mp htop
        have hupdate := htransition.2.2.2 heq
        have hsites : numericalSites child = {maximum} := hupdate.2.2
        have hvalues : activeValues child = [maximum] := by
          apply (sorted_values child).eq_of_mem_iff (List.pairwise_singleton _ _)
          intro value
          rw [mem_values]
          change value ∈ numericalSites child ↔ _
          rw [hsites]
          simp
        refine ⟨?_, ?_, ?_⟩
        · change activeMarks child = [true]
          simp [activeMarks, hvalues, child, maximum_mem]
        · change 1 + wasc child - child.foldr max 0 = budget + 1
          rw [hupdate.1, hupdate.2.1]
          dsimp [budget]
          omega
        · change decide (child.getLast?.getD 0 = child.foldr max 0) = true
          rw [child_last, hupdate.1]
          change decide (letter = maximum) = true
          simp [heq]
      · rename_i htop
        have hneq : letter ≠ maximum := by intro heq; exact htop (top_iff.mpr heq)
        have hlt : letter < maximum := by omega
        have hupdate := htransition.2.2.1 hlt hmem
        have hsites : numericalSites child = ∅ := hupdate.2.2
        have hvalues : activeValues child = [] := by
          apply (sorted_values child).eq_of_mem_iff (by simp)
          intro value
          rw [mem_values]
          change value ∈ numericalSites child ↔ _
          rw [hsites]
          simp
        refine ⟨?_, ?_, ?_⟩
        · change activeMarks child = []
          simp [activeMarks, hvalues]
        · change 1 + wasc child - child.foldr max 0 = budget
          rw [hupdate.1, hupdate.2.1]
        · change decide (child.getLast?.getD 0 = child.foldr max 0) = false
          rw [child_last, hupdate.1]
          change decide (letter = maximum) = false
          simp [hneq]
end D5.S3.Combinatorics.WeakAscent.WeakAscent215Transitions
