/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable
   mirror-E: none(waiver:inductive-first-component-site-obstruction)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Maximum-deletion induction determines the weighted B component construction. -/
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBUpdates
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBSums
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSumInsertion
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.GeomSum
open D5.S3.Combinatorics.Fishburn
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable
open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicParents FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns
open FishburnBasicComponents FishburnBasicComponentCuts FishburnBasicSumInsertion
open FishburnTenThirteenBUpdates FishburnTenThirteenBSums NonnestingBasicSum
set_option maxHeartbeats 4000000 in
theorem inductive_counting (n : ℕ) (hn : 0 < n) :
    let active (size : ℕ) (word : List ℕ) := @Finset.filter ℕ
      (fun gap => word.insertIdx gap (size + 1) ∈
        avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
      (fun _ => Classical.propDecidable _) (Finset.range (word.length + 1))
    let components := {parts : List (List ℕ) | (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      assemble parts ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]]}
    let targets := {word : List ℕ |
      word ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧ sumIndecomposable word}
    (∑ᶠ child : targets,
      (Polynomial.X : Polynomial ℚ) ^ ((active (n + 1) child.val).card - 2)) =
        (∑ᶠ parts : components, (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1)) +
        ∑ᶠ parts : components, (Polynomial.X : Polynomial ℚ) ^
            (if parts.val.tail = [] then 1 else parts.val.tail.length) *
          ∑ exponent ∈ Finset.range
            ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ exponent := by
  classical
  dsimp only; let patterns := [[2, 4, 3, 1], [3, 2, 4, 1]]
  let active (size : ℕ) (word : List ℕ) := (Finset.range (word.length + 1)).filter
    fun gap => word.insertIdx gap (size + 1) ∈ avoiders (size + 1) patterns
  have indecSites (n : ℕ) (p : List ℕ) (hparent : p ∈ avoiders n patterns)
      (hindec : sumIndecomposable p) (site : ℕ) (hpositive : 0 < site)
      (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns) :
      n ∈ p.take site ∧ (site < p.length →
          let cuts := active n p; let child := p.insertIdx site (n + 1)
          let childCuts := active (n + 1) child
          childCuts.card = cuts.card + 1 - (cuts.filter fun gap => gap < site).card) := by
    have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
        (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ size := by
      have hm := hp.mem_iff.mp hv; simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm; omega
    have hpatterns : ∀ pattern ∈ patterns,
        pattern ≠ [] ∧ sumIndecomposable pattern ∧ (∀ value ∈ pattern, 1 ≤ value) ∧
        ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern := by
      intro pattern hp; simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl; all_goals
        refine ⟨by decide, by unfold sumIndecomposable; decide, by simp [patterns], ?_⟩
        intro rank hr hbound; norm_num [NonnestingDefs.letters] at hbound
        simp only [List.mem_cons, List.not_mem_nil]; omega
    have htailpositive (parts : List (List ℕ))
        (hparts : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
        ∀ value ∈ assemble parts, 1 ≤ value := by
      induction parts with
      | nil => simp [assemble]
      | cons first rest ih =>
        intro value hv; rcases List.mem_append.mp hv with hfirst | hrest
        · exact (hvalues first.length first (hparts first (by simp [patterns])) value hfirst).1
        · obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hrest
          have := ih (fun block hb => hparts block (by simp [hb])) small hs; omega
    have hpositions : ∀ size parent, parent ∈ avoiders size patterns →
        sumIndecomposable parent → ∀ gap, 0 < gap → gap ≤ parent.length →
        parent.insertIdx gap (size + 1) ∈
          avoiders (size + 1) patterns → size ∈ parent.take gap := by
      intro size
      induction size using Nat.strong_induction_on with
      | h size ih =>
        intro child hc hindec gap hgapPositive hgapBound hgapActive; cases size with
        | zero =>
          have hlength : child.length = 0 := (by simpa using hc.1.length_eq); omega
        | succ size =>
          obtain ⟨entry, heq⟩ := (maximum_insertion_bijection size patterns).2 ⟨child, hc⟩
          let parent := entry.val.1; let insertion := entry.val.2
          have hp : parent ∈ avoiders size patterns := entry.property.1
          have hinsBound : insertion ≤ parent.length := entry.property.2.1
          have hinsActive : parent.insertIdx insertion (size + 1) ∈
              avoiders (size + 1) patterns := entry.property.2.2
          have hword : parent.insertIdx insertion (size + 1) = child := congrArg Subtype.val heq
          have hparentLength : parent.length = size := (by simpa using hp.1.length_eq)
          have hchildLength : child.length = parent.length + 1 := by
            rw [← hword]; exact List.length_insertIdx_of_le_length hinsBound _
          by_cases hafter : insertion < gap
          · apply List.mem_take_iff_getElem.mpr; refine ⟨insertion, by omega, ?_⟩
            have hat : (parent.insertIdx insertion (size + 1)).getD insertion 0 = size + 1 := by
              rw [List.getD_eq_getElem _ 0 (by
                rw [List.length_insertIdx_of_le_length hinsBound]
                omega)]
              exact List.getElem_insertIdx_self _
            rw [hword] at hat; exact (List.getD_eq_getElem child 0 (by omega)).symm.trans hat
          have hbefore : gap ≤ insertion := by omega
          have hsizePositive : 0 < size := by omega
          have hupdates := (crossing_site_updates size parent hsizePositive hp insertion
            hinsBound hinsActive).1 gap hbefore
          have hgapChild : (parent.insertIdx insertion (size + 1)).insertIdx gap (size + 2) ∈
              avoiders (size + 2) patterns := by
            simpa only [hword, Nat.succ_eq_add_one, Nat.add_assoc] using hgapActive
          obtain ⟨hgapParent, hseparation⟩ := hupdates.mp hgapChild
          have hcuts := (indecomposable_maximum_insertion size parent hp.1 insertion
            hinsBound).mp (by rwa [hword])
          obtain ⟨parts, hparts, _⟩ :=
            (unique_sum_components size parent hp.1 patterns hpatterns).1
          cases parts with
          | nil =>
            have hempty : parent = [] := (by simpa [assemble] using hparts.1.symm)
            simp only [hempty, List.length_nil] at hinsBound; omega
          | cons first rest =>
            have hf := hparts.2.1 first (by simp [patterns])
            have hfClass : first ∈ avoiders first.length patterns :=
              (hparts.2.2.mp hp) first (by simp [patterns])
            have hdecomp : parent = first ++ shift first.length (assemble rest) := hparts.1.symm
            have hlength : parent.length = first.length + (assemble rest).length := by
              simp [hdecomp, shift]
            have hfirstPositive : 0 < first.length := List.length_pos_iff_ne_nil.mpr hf.1
            have hrightPositive : ∀ value ∈ assemble rest, 1 ≤ value :=
              htailpositive rest (fun block hb => (hparts.2.1 block (by simp [hb])).2.1)
            have hlocalBefore (index : ℕ) (hi : index < first.length) :
                parent.getD index 0 = first.getD index 0 := by
              rw [hdecomp]; exact List.getD_append _ _ _ _ hi
            have hsmall (index : ℕ) (hi : index < first.length) :
                parent.getD index 0 ≤ first.length := by
              rw [hlocalBefore index hi]; apply (hvalues first.length first hf.2.1 _ _).2
              rw [List.getD_eq_getElem first 0 hi]; exact List.getElem_mem hi
            have hinternal : insertion < first.length := by
              by_contra hnot; obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
                hcuts first.length hfirstPositive (by omega)
              have hsmallValue := hsmall before hb
              have hlater : parent.getD later 0 ∈ shift first.length (assemble rest) := by
                rw [hdecomp, List.getD_append_right _ _ _ _ hl,
                  List.getD_eq_getElem _ 0 (by simp only [shift, List.length_map]; omega)]
                exact List.getElem_mem (by simp only [shift, List.length_map]; omega)
              obtain ⟨value, hv, hequal⟩ := List.mem_map.mp hlater
              have := hrightPositive value hv
              omega
            have htailClass : assemble rest ∈ avoiders (assemble rest).length patterns := by
              apply ((unique_sum_components 0 [] (by simp [patterns]) patterns hpatterns).2.1 rest
                (fun block hb => hparts.2.1 block (by simp [hb]))).mpr
              intro block hb; exact (hparts.2.2.mp hp) block (by simp [hb])
            have hsum : directSum first.length first (assemble rest) ∈
                avoiders (first.length + (assemble rest).length) patterns := by
              simpa only [directSum, ← hdecomp, ← hlength, hparentLength] using hp
            have hfirstActive := (crossing_sum_sites first.length (assemble rest).length
              first (assemble rest) hfClass htailClass hsum).1 gap (by omega) |>.mp
                (by
                  simpa only [directSum, ← hdecomp, ← hlength, hparentLength] using hgapParent)
            have hfirstSmall : first.length < size + 1 := (by omega)
            have hfirstMax := ih first.length hfirstSmall first hfClass hf.2.2 gap
              hgapPositive (by omega) hfirstActive
            obtain ⟨maxIndex, hmaxIndex, hmaxValue⟩ := List.mem_take_iff_getElem.mp hfirstMax
            have hmaxD : parent.getD maxIndex 0 = first.length := by
              rw [hlocalBefore maxIndex (by omega), List.getD_eq_getElem first 0 (by omega)]
              exact hmaxValue
            have hcontra := hseparation maxIndex insertion (by omega) le_rfl (by omega)
            have := hsmall insertion hinternal; omega
    refine ⟨hpositions n p hparent hindec site hpositive hsite hactive, ?_⟩; intro hproper
    dsimp only; let cuts := active n p; let child := p.insertIdx site (n + 1)
    let childCuts := active (n + 1) child; let laterCuts := cuts.filter fun gap => site < gap
    change childCuts.card = cuts.card + 1 - (cuts.filter fun gap => gap < site).card
    have hn : 0 < n := by
      have := hparent.1.length_eq; simp only [List.length_range'] at this; omega
    have hlength : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite _
    have hcuts (gap : ℕ) : gap ∈ cuts ↔ gap ≤ p.length ∧
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) patterns := by
      simp only [cuts, active, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    have hchildren (gap : ℕ) : gap ∈ childCuts ↔ gap ≤ child.length ∧
        child.insertIdx gap (n + 2) ∈ avoiders (n + 2) patterns := by
      simp only [childCuts, active, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    have hupdates := crossing_site_updates n p hn hparent site hsite hactive
    have hmaximum : n ∈ p.take site :=
      hpositions n p hparent hindec site hpositive hsite hactive
    have hmiddle : site + 1 ∈ childCuts :=
      (hchildren _).mpr ⟨by omega, hupdates.2.2.1.mpr hmaximum⟩
    have hfront : child.insertIdx 0 (n + 2) ∈ avoiders (n + 2) patterns := by
      have hbound : ∀ value ∈ child, value < n + 2 := by
        intro value hv; have := hvalues (n + 1) child hactive.1 value hv; omega
      have hperm : (child.insertIdx 0 (n + 2)).Perm (List.range' 1 (n + 2)) := by
        apply (List.perm_insertIdx (n + 2) child (Nat.zero_le _)).trans
        apply (hactive.1.cons (n + 2)).trans
        have hconcat : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
          simpa only [Nat.add_assoc, Nat.one_add, Nat.one_mul] using
            (List.range'_concat (s := 1) (n := n + 1) (step := 1))
        rw [hconcat]
        exact (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
      refine ⟨hperm, ?_, ?_⟩
      · apply (isFishburn_insertIdx_max_iff child (n + 2) 0 (Nat.zero_le _) hbound).mpr
        exact ⟨hactive.2.1, by intros; omega⟩
      · intro pattern hp hbad
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · have htest :=
            (maximum_crossing_pattern_tests (n + 1) child hactive.1 0 (Nat.zero_le _)).2
          rcases htest.mp (by simpa only [Nat.add_assoc] using hbad) with hold | hnew
          · exact hactive.2.2 _ (by simp [patterns]) hold
          · obtain ⟨first, second, third, hb, _⟩ := hnew; omega
        · have htest := (maximum_four_pattern_tests (n + 1) child hactive.1 0 (Nat.zero_le _)).2.2
          rcases htest.mp (by simpa only [Nat.add_assoc] using hbad) with hold | hnew
          · exact hactive.2.2 _ (by simp [patterns]) hold
          · obtain ⟨first, second, third, _, hb, _⟩ := hnew; omega
    have hchildZero : 0 ∈ childCuts := (hchildren 0).mpr ⟨Nat.zero_le _, hfront⟩
    have hnoBefore (gap : ℕ) (hg : 0 < gap) (hb : gap ≤ site) : gap ∉ childCuts := by
      intro hgap
      obtain ⟨hgapActive, hsep⟩ := (hupdates.1 gap hb).mp ((hchildren gap).mp hgap).2
      have hmaxGap := hpositions n p hparent hindec gap hg (by omega) hgapActive
      obtain ⟨maxIndex, hm, hvalue⟩ := List.mem_take_iff_getElem.mp hmaxGap
      have hmaxD : p.getD maxIndex 0 = n := by
        rw [List.getD_eq_getElem p 0 (by omega)]; exact hvalue
      have hlater : p.getD site 0 ≤ n := by
        apply (hvalues n p hparent.1 _ _).2; rw [List.getD_eq_getElem p 0 hproper]
        exact List.getElem_mem hproper
      have hless := hsep maxIndex site (by omega) le_rfl hproper; rw [hmaxD] at hless; omega
    have hsurvive (gap : ℕ) (hg : site < gap) (hb : gap ≤ p.length)
        (ha : p.insertIdx gap (n + 1) ∈ avoiders (n + 1) patterns) :
        child.insertIdx (gap + 1) (n + 2) ∈ avoiders (n + 2) patterns := by
      apply (hupdates.2.1 gap hg hb).mpr; refine ⟨ha, ?_⟩
      obtain ⟨maxIndex, hm, hvalue⟩ := List.mem_take_iff_getElem.mp hmaximum
      have hmaxD : p.getD maxIndex 0 = n := by
        rw [List.getD_eq_getElem p 0 (by omega)]; exact hvalue
      have hempty : ([] : List ℕ) ∈ avoiders 0 patterns := by
        refine ⟨by simp [patterns], ?_, ?_⟩
        · intro first second horder hbound; simp at hbound
        · intro pattern hp hocc; obtain ⟨values, _, hmem, _⟩ := hocc
          simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
          have hletters : 1 ≤ NonnestingDefs.letters pattern := by
            rcases hp with rfl | rfl <;> norm_num [NonnestingDefs.letters]
          have := hmem 1 le_rfl hletters; simp at this
      have hsum := (crossing_sum_sites 0 n [] p hempty hparent
        (by simpa [directSum, shift] using hparent)).2.2
      have hseparation := hsum maxIndex gap (by simpa [directSum, shift] using hmaxD)
        (by omega) (by simpa [directSum, shift] using hb)
        (by simpa [directSum, shift] using ha)
      intro middle later hmiddle hmiddleGap hlater hbound
      simpa [directSum, shift] using hseparation middle later (by omega)
        hmiddleGap hlater (by simpa [directSum, shift] using hbound)
    have himage (gap : ℕ) : gap ∈ laterCuts.image (· + 1) ↔
        ∃ old, old ∈ cuts ∧ site < old ∧ old + 1 = gap := by
      simp only [Finset.mem_image, laterCuts, Finset.mem_filter]; aesop
    have hdecomp : childCuts = {0, site + 1} ∪ laterCuts.image (· + 1) := by
      ext gap
      constructor
      · intro hg; obtain ⟨hb, ha⟩ := (hchildren gap).mp hg
        by_cases hgap : gap = 0 ∨ gap = site + 1
        · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hgap
        have hafter : site + 1 < gap := by
          by_contra hnot; exact hnoBefore gap (by omega) (by omega) hg
        have hprevBound : gap - 1 ≤ p.length := (by omega)
        have hprevActive := (hupdates.2.1 (gap - 1) (by omega) hprevBound).mp
          (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using ha) |>.1
        apply Finset.mem_union_right; exact (himage gap).mpr ⟨gap - 1,
          (hcuts _).mpr ⟨hprevBound, hprevActive⟩, by omega, by omega⟩
      · intro hg; rcases Finset.mem_union.mp hg with hspecial | him
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hspecial
          rcases hspecial with rfl | rfl
          · exact hchildZero
          · exact hmiddle
        · obtain ⟨old, hold, hafter, rfl⟩ := (himage gap).mp him
          obtain ⟨hb, ha⟩ := (hcuts old).mp hold
          exact (hchildren _).mpr ⟨by omega, hsurvive old hafter hb ha⟩
    have hdisjoint : Disjoint ({0, site + 1} : Finset ℕ) (laterCuts.image (· + 1)) := by
      apply Finset.disjoint_left.mpr; intro gap hgap him
      obtain ⟨old, _, hafter, heq⟩ := (himage gap).mp him
      simp only [Finset.mem_insert, Finset.mem_singleton] at hgap; omega
    have himageCard : (laterCuts.image (· + 1)).card = laterCuts.card :=
      Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
    have hpartition : laterCuts.card + (cuts.filter fun gap => gap < site).card + 1 =
        cuts.card := by
      have hsiteCut := (hcuts site).mpr ⟨hsite, hactive⟩
      have hlow : (cuts.filter fun gap => ¬ site < gap) =
          insert site (cuts.filter fun gap => gap < site) := by
        ext gap
        simp only [Finset.mem_filter, Finset.mem_insert]; constructor
        · rintro ⟨hg, hb⟩; by_cases heq : gap = site
          · exact Or.inl heq
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hb⟩)
          · exact ⟨hsiteCut, by omega⟩
          · exact ⟨hg, by omega⟩
      have hsplit := Finset.card_filter_add_card_filter_not (s := cuts) (site < ·)
      rw [hlow, Finset.card_insert_of_notMem (by simp [patterns])] at hsplit; exact hsplit
    rw [hdecomp, Finset.card_union_of_disjoint hdisjoint, himageCard,
      Finset.card_pair (by omega : 0 ≠ site + 1)]
    omega
  have internalCount (m n : ℕ) (left right : List ℕ) (hleft : left ∈ avoiders m patterns)
      (hright : right ∈ avoiders n patterns)
      (hparent : directSum m left right ∈ avoiders (m + n) patterns)
      (hindec : sumIndecomposable left) (hn : 0 < n)
      (site : ℕ) (hpositive : 0 < site) (hproper : site < left.length)
      (hactive : left.insertIdx site (m + 1) ∈ avoiders (m + 1) patterns)
      (parts : List (List ℕ)) (hparts : ∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block)
      (hassemble : assemble parts = right) :
      let word := directSum m left right; let child := word.insertIdx site (m + n + 1)
      let cuts := active m left; let childCuts := active (m + n + 1) child
      childCuts.card + (cuts.filter fun gap => gap < site).card = cuts.card + parts.length := by
    dsimp only; let word := directSum m left right; let child := word.insertIdx site (m + n + 1)
    let cuts := active m left; let childCuts := active (m + n + 1) child
    let laterCuts := cuts.filter fun gap => site < gap
    let boundaries := (Finset.range (right.length + 1)).filter fun gap =>
      ∀ before ∈ right.take gap, ∀ later ∈ right.drop gap, before < later
    have hleftLen : left.length = m := (by simpa using hleft.1.length_eq)
    have hrightLen : right.length = n := (by simpa using hright.1.length_eq)
    have hlength : word.length = left.length + right.length := by
      simp [word, directSum, shift]
    have hsite : site ≤ word.length := (by omega)
    have hchildLen : child.length = word.length + 1 :=
      List.length_insertIdx_of_le_length hsite _
    have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
        (index : ℕ) (hb : index < block.length) :
        1 ≤ block.getD index 0 ∧ block.getD index 0 ≤ size := by
      have hm := hp.mem_iff.mp (show block.getD index 0 ∈ block from by
        rw [List.getD_eq_getElem block 0 hb]; exact List.getElem_mem hb)
      simp only [List.mem_range', Nat.one_mul] at hm; obtain ⟨offset, ho, heq⟩ := hm; omega
    have hbefore (index : ℕ) (hb : index < left.length) : word.getD index 0 = left.getD index 0 :=
      List.getD_append _ _ _ _ hb
    have hafter (index : ℕ) (hl : left.length ≤ index) (hb : index < word.length) :
        word.getD index 0 = right.getD (index - left.length) 0 + m := by
      change (left ++ shift m right).getD index 0 = _; rw [List.getD_append_right _ _ _ _ hl]
      have hi : index - left.length < right.length := (by omega)
      rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hi), List.getD_eq_getElem right 0 hi]
      simp [shift]
    have hsmall (index : ℕ) (hb : index < left.length) : word.getD index 0 ≤ m := by
      rw [hbefore index hb]; exact (hvalues m left hleft.1 index hb).2
    have hlarge (index : ℕ) (hl : left.length ≤ index) (hb : index < word.length) :
        m < word.getD index 0 := by
      have := (hvalues n right hright.1 (index - left.length) (by omega)).1; rw [hafter index hl hb]
      omega
    have hsums := crossing_sum_sites m n left right hleft hright hparent
    have hchild : child ∈ avoiders (m + n + 1) patterns := (hsums.1 site (by omega)).mpr hactive
    change childCuts.card + (cuts.filter fun gap => gap < site).card = cuts.card + parts.length
    have hcuts (gap : ℕ) : gap ∈ cuts ↔ gap ≤ left.length ∧
        left.insertIdx gap (m + 1) ∈ avoiders (m + 1) patterns := by
      simp only [cuts, active, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    have hchildren (gap : ℕ) : gap ∈ childCuts ↔ gap ≤ child.length ∧
        child.insertIdx gap (m + n + 2) ∈ avoiders (m + n + 2) patterns := by
      simp only [childCuts, active, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    have hboundary (gap : ℕ) : gap ∈ boundaries ↔ gap ≤ right.length ∧
        ∀ before later, before < gap → gap ≤ later → later < right.length →
          right.getD before 0 < right.getD later 0 := by
      simp only [boundaries, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]; constructor
      · rintro ⟨hb, hsep⟩; refine ⟨hb, ?_⟩; intro before later hbef hlat hbound; apply hsep
        · apply List.mem_take_iff_getElem.mpr
          exact ⟨before, by omega, (List.getD_eq_getElem right 0 (by omega)).symm⟩
        · apply List.mem_drop_iff_getElem.mpr; refine ⟨later - gap, by omega, ?_⟩
          simpa only [Nat.add_sub_cancel' hlat] using (List.getD_eq_getElem right 0 hbound).symm
      · rintro ⟨hb, hsep⟩; refine ⟨hb, ?_⟩; intro before hbef later hlat
        obtain ⟨first, hf, heq⟩ := List.mem_take_iff_getElem.mp hbef
        obtain ⟨second, hs, hseq⟩ := List.mem_drop_iff_getElem.mp hlat
        have hless := hsep first (gap + second) (by omega) (by omega) (by omega)
        rw [List.getD_eq_getElem right 0 (by omega),
          List.getD_eq_getElem right 0 (by omega), heq, hseq] at hless
        exact hless
    have hseparatedActive (size : ℕ) (block : List ℕ) (hp : block ∈ avoiders size patterns)
        (gap : ℕ) (hg : gap ≤ block.length)
        (hsep : ∀ before later, before < gap → gap ≤ later → later < block.length →
          block.getD before 0 < block.getD later 0) :
        block.insertIdx gap (size + 1) ∈ avoiders (size + 1) patterns := by
      have hmax : ∀ value ∈ block, value < size + 1 := by
        intro value hv; have hm := hp.1.mem_iff.mp hv
        simp only [List.mem_range', Nat.one_mul] at hm; obtain ⟨offset, ho, heq⟩ := hm; omega
      have hperm : (block.insertIdx gap (size + 1)).Perm (List.range' 1 (size + 1)) := by
        apply (List.perm_insertIdx (size + 1) block hg).trans; apply (hp.1.cons (size + 1)).trans
        rw [List.range'_concat]; simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      refine ⟨hperm, ?_, ?_⟩
      · apply (isFishburn_insertIdx_max_iff block (size + 1) gap hg hmax).mpr
        refine ⟨hp.2.1, ?_⟩
        intro before later hb hl hbound heq; have := hsep before later (by omega) hl hbound; omega
      · intro pattern hpattern hbad
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl
        · rcases (maximum_crossing_pattern_tests size block hp.1 gap hg).2.mp hbad with
            hold | ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
          · exact hp.2.2 _ (by simp [patterns]) hold
          · have := hsep first third hf (by omega) ht; omega
        · rcases (maximum_four_pattern_tests size block hp.1 gap hg).2.2.mp hbad with
            hold | ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
          · exact hp.2.2 _ (by simp [patterns]) hold
          · have := hsep second third hs hst ht; omega
    have hupdates := crossing_site_updates (m + n) word (by omega) hparent site hsite hchild
    have hzero : 0 ∈ childCuts := by
      apply (hchildren 0).mpr; exact ⟨Nat.zero_le _, hseparatedActive (m + n + 1) child hchild 0
        (Nat.zero_le _) (by intros; omega)⟩
    have hnoNew : site + 1 ∉ childCuts := by
      intro hg; have hmax := hupdates.2.2.1.mp ((hchildren _).mp hg).2
      obtain ⟨index, hi, heq⟩ := List.mem_take_iff_getElem.mp hmax
      have hsmallMax := hsmall index (by omega)
      rw [List.getD_eq_getElem word 0 (by omega), heq] at hsmallMax; omega
    have hnoBefore (gap : ℕ) (hg : 0 < gap) (hb : gap ≤ site) : gap ∉ childCuts := by
      intro hc; obtain ⟨hactiveGap, hsep⟩ := (hupdates.1 gap hb).mp ((hchildren gap).mp hc).2
      have hlocal := (hsums.1 gap (by omega)).mp hactiveGap
      have hmax := (indecSites m left hleft hindec gap hg (by omega) hlocal).1
      obtain ⟨index, hi, heq⟩ := List.mem_take_iff_getElem.mp hmax
      have hcontra := hsep index site (by omega) le_rfl (by omega)
      have hsmallSite := hsmall site hproper
      rw [hbefore index (by omega), List.getD_eq_getElem left 0 (by omega), heq] at hcontra; omega
    have hmaximum := (indecSites m left hleft hindec site hpositive (by omega) hactive).1
    obtain ⟨maximum, hmaximumBound, hmaximumValue⟩ := List.mem_take_iff_getElem.mp hmaximum
    have hmaximumD : left.getD maximum 0 = m := by
      rw [List.getD_eq_getElem left 0 (by omega)]; exact hmaximumValue
    have hempty : ([] : List ℕ) ∈ avoiders 0 patterns := by
      refine ⟨by simp [patterns], ?_, ?_⟩
      · intro first second horder hbound; simp at hbound
      · intro pattern hp hocc; obtain ⟨values, _, hmem, _⟩ := hocc
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
        have hletters : 1 ≤ NonnestingDefs.letters pattern := by
          rcases hp with rfl | rfl <;> norm_num [NonnestingDefs.letters]
        have := hmem 1 le_rfl hletters; simp at this
    have hlocalSurvives (gap : ℕ) (hafterSite : site < gap) (hb : gap ≤ left.length) :
        gap + 1 ∈ childCuts ↔ gap ∈ cuts := by
      constructor
      · intro hg; have hold := ((hupdates.2.1 gap hafterSite (by omega)).mp
          ((hchildren _).mp hg).2).1
        exact (hcuts gap).mpr ⟨hb, (hsums.1 gap hb).mp hold⟩
      · intro hg; have ha := ((hcuts gap).mp hg).2
        have htail := (crossing_sum_sites 0 m [] left hempty hleft
          (by simpa [directSum, shift] using hleft)).2.2 maximum gap
          (by simpa [directSum, shift] using hmaximumD) (by omega)
          (by simpa [directSum, shift] using hb) (by simpa [directSum, shift] using ha)
        apply (hchildren _).mpr; refine ⟨by omega, (hupdates.2.1 gap hafterSite (by omega)).mpr
          ⟨(hsums.1 gap hb).mpr ha, ?_⟩⟩
        intro middle later hm hmg hgl hl; by_cases hleftLater : later < left.length
        · have hless := htail middle later (by omega) hmg hgl
            (by simpa [directSum, shift] using hleftLater)
          rw [hbefore middle (by omega), hbefore later hleftLater]
          simpa [directSum, shift] using hless
        · have := hsmall middle (by omega); have := hlarge later (by omega) hl; omega
    have htailSurvives (gap : ℕ) (hpositiveGap : 0 < gap) (hb : gap ≤ right.length) :
        left.length + gap + 1 ∈ childCuts ↔ gap ∈ boundaries := by
      constructor
      · intro hg; have hsep := ((hupdates.2.1 (left.length + gap) (by omega) (by omega)).mp
          ((hchildren _).mp hg).2).2
        apply (hboundary gap).mpr; refine ⟨hb, ?_⟩; intro before later hbef hlat hbound
        have hless := hsep (left.length + before) (left.length + later)
          (by omega) (by omega) (by omega) (by omega)
        rw [hafter _ (by omega) (by omega), hafter _ (by omega) (by omega),
          Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hless
        omega
      · intro hg; have hsep := ((hboundary gap).mp hg).2
        have hrightActive := hseparatedActive n right hright gap hb hsep; apply (hchildren _).mpr
        refine ⟨by omega, (hupdates.2.1 (left.length + gap) (by omega) (by omega)).mpr
          ⟨(hsums.2.1 gap hb).mpr hrightActive, ?_⟩⟩
        intro middle later hm hmg hgl hl; by_cases hleftMiddle : middle < left.length
        · have := hsmall middle hleftMiddle; have := hlarge later (by omega) hl; omega
        · have hless := hsep (middle - left.length) (later - left.length)
            (by omega) (by omega) (by omega)
          rw [hafter middle (by omega) (by omega), hafter later (by omega) hl]; omega
    have hdecomp : childCuts = {0} ∪ laterCuts.image (· + 1) ∪
        (boundaries.erase 0).image (fun gap => left.length + gap + 1) := by
      ext gap
      constructor
      · intro hg; have hb := ((hchildren gap).mp hg).1; by_cases hz : gap = 0
        · simp [hz]
        have hafterSite : site + 1 < gap := by
          by_contra hnot; by_cases hnew : gap = site + 1
          · exact hnoNew (by simpa only [hnew] using hg)
          · exact hnoBefore gap (by omega) (by omega) hg
        by_cases hlocal : gap - 1 ≤ left.length
        · apply Finset.mem_union_left; apply Finset.mem_union_right; apply Finset.mem_image.mpr
          refine ⟨gap - 1, ?_, by omega⟩; apply Finset.mem_filter.mpr
          refine ⟨(hlocalSurvives (gap - 1) (by omega) hlocal).mp
            (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using hg), by omega⟩
        · apply Finset.mem_union_right; apply Finset.mem_image.mpr
          refine ⟨gap - 1 - left.length, ?_, by omega⟩; apply Finset.mem_erase.mpr
          refine ⟨by omega, (htailSurvives _ (by omega) (by omega)).mp ?_⟩
          simpa only [Nat.add_sub_cancel' (by omega : left.length ≤ gap - 1),
            Nat.sub_add_cancel (by omega : 1 ≤ gap)] using hg
      · intro hg; rcases Finset.mem_union.mp hg with hfirst | htail
        · rcases Finset.mem_union.mp hfirst with hz | hlocal
          · simpa only [Finset.mem_singleton.mp hz] using hzero
          · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hlocal
            obtain ⟨ha, hs⟩ := Finset.mem_filter.mp hold
            exact (hlocalSurvives old hs ((hcuts old).mp ha).1).mpr ha
        · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp htail
          obtain ⟨hnotZero, ha⟩ := Finset.mem_erase.mp hold
          exact (htailSurvives old (by omega) ((hboundary old).mp ha).1).mpr ha
    have hdisjointLocal : Disjoint ({0} : Finset ℕ) (laterCuts.image (· + 1)) := by
      apply Finset.disjoint_left.mpr; intro gap hz him
      obtain ⟨old, _, heq⟩ := Finset.mem_image.mp him
      simp only [Finset.mem_singleton] at hz; omega
    have hdisjointTail : Disjoint ({0} ∪ laterCuts.image (· + 1))
        ((boundaries.erase 0).image (fun gap => left.length + gap + 1)) := by
      apply Finset.disjoint_left.mpr; intro gap hlocal htail
      obtain ⟨tailGap, ht, heq⟩ := Finset.mem_image.mp htail
      have htPositive : 0 < tailGap := by
        have := (Finset.mem_erase.mp ht).1; omega
      rcases Finset.mem_union.mp hlocal with hz | him
      · simp only [Finset.mem_singleton] at hz; omega
      · obtain ⟨old, ho, hequal⟩ := Finset.mem_image.mp him
        have := ((hcuts old).mp (Finset.mem_filter.mp ho).1).1; omega
    have hlocalCard : (laterCuts.image (· + 1)).card = laterCuts.card :=
      Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
    have htailCard : ((boundaries.erase 0).image
        (fun gap => left.length + gap + 1)).card = (boundaries.erase 0).card := by
      apply Finset.card_image_of_injective; intro first second heq; dsimp only at heq; omega
    have hboundaryZero : 0 ∈ boundaries := (by simp [boundaries])
    have hboundaryCard : boundaries.card = parts.length + 1 := by
      simpa only [hassemble] using component_boundary_count parts hparts
    have htailCount := Finset.card_erase_add_one hboundaryZero
    have hsiteCut : site ∈ cuts := (hcuts site).mpr ⟨by omega, hactive⟩
    have hlow : cuts.filter (fun gap => ¬ site < gap) =
        insert site (cuts.filter fun gap => gap < site) := by
      ext gap
      simp only [Finset.mem_filter, Finset.mem_insert]; constructor
      · rintro ⟨hg, hs⟩; by_cases heq : gap = site
        · exact Or.inl heq
        · exact Or.inr ⟨hg, by omega⟩
      · rintro (rfl | ⟨hg, hs⟩)
        · exact ⟨hsiteCut, by omega⟩
        · exact ⟨hg, by omega⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := cuts) (site < ·)
    rw [hlow, Finset.card_insert_of_notMem (by simp [patterns])] at hsplit
    rw [hdecomp, Finset.card_union_of_disjoint hdisjointTail,
      Finset.card_union_of_disjoint hdisjointLocal, Finset.card_singleton,
      hlocalCard, htailCard]
    change laterCuts.card + _ = _ at hsplit; omega
  have hfront (n : ℕ) (p : List ℕ) (hp : p ∈ avoiders n patterns) :
      p.insertIdx 0 (n + 1) ∈ avoiders (n + 1) patterns := by
    have hmax : ∀ value ∈ p, value < n + 1 := by
      intro value hv; have hm := hp.1.mem_iff.mp hv; simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm; omega
    have hperm : (p.insertIdx 0 (n + 1)).Perm (List.range' 1 (n + 1)) := by
      apply (List.perm_insertIdx (n + 1) p (Nat.zero_le _)).trans; apply (hp.1.cons (n + 1)).trans
      rw [List.range'_concat]; simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
    refine ⟨hperm, ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (Nat.zero_le _) hmax).mpr
      exact ⟨hp.2.1, by intros; omega⟩
    · intro pattern hpattern hbad
      simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · rcases (maximum_crossing_pattern_tests n p hp.1 0 (Nat.zero_le _)).2.mp hbad
          with hold | ⟨first, second, third, hf, _⟩
        · exact hp.2.2 _ (by simp [patterns]) hold
        · omega
      · rcases (maximum_four_pattern_tests n p hp.1 0 (Nat.zero_le _)).2.2.mp hbad
          with hold | ⟨first, second, third, hf, hs, _⟩
        · exact hp.2.2 _ (by simp [patterns]) hold
        · omega
  have hstructure (n : ℕ) :
    Set.BijOn (fun entry : List ℕ × ℕ => entry.1.insertIdx entry.2 (n + 1))
      {entry | entry.1 ∈ avoiders n patterns ∧
        (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
          (∀ block ∈ first :: rest, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
          entry.2 < first.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns)}
      {p | p ∈ avoiders (n + 1) patterns ∧ sumIndecomposable p} ∧
    (∀ parts : List (List ℕ), (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      assemble parts ∈ avoiders n patterns → 0 < n →
      let child := (assemble parts).insertIdx 0 (n + 1)
      (active (n + 1) child).card = parts.length + 1) ∧
    (∀ first rest, (∀ block ∈ first :: rest, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      first ∈ avoiders first.length patterns →
      assemble rest ∈ avoiders (assemble rest).length patterns →
      assemble (first :: rest) ∈ avoiders n patterns →
      ∀ site, 0 < site → site < first.length → first.insertIdx site (first.length + 1) ∈
          avoiders (first.length + 1) patterns →
      let cuts := active first.length first
      let child := (assemble (first :: rest)).insertIdx site (n + 1)
      let childCuts := active (n + 1) child
      childCuts.card + (cuts.filter fun gap => gap < site).card =
        cuts.card + if rest = [] then 1 else rest.length) ∧
    (∀ p, p ∈ avoiders n patterns → 0 < n →
      let cuts := active n p
      ∃ selection : Fin (cuts.card - 2) ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length},
        ∀ index, (cuts.filter fun gap => gap < (selection index).val).card = index.val + 1) := by
    have hfront := hfront n
    refine ⟨?constructors, ?frontCounts, ?internalCounts, ?rankedChoices⟩
    case rankedChoices =>
      intro p hp hn; have hlast : p.insertIdx p.length (n + 1) ∈ avoiders (n + 1) patterns := by
        have hmax : ∀ value ∈ p, value < n + 1 := by
          intro value hv; have hm := hp.1.mem_iff.mp hv
          simp only [List.mem_range', Nat.one_mul] at hm; obtain ⟨offset, ho, heq⟩ := hm; omega
        have hperm : (p.insertIdx p.length (n + 1)).Perm (List.range' 1 (n + 1)) := by
          apply (List.perm_insertIdx (n + 1) p le_rfl).trans; apply (hp.1.cons (n + 1)).trans
          rw [List.range'_concat]; simpa [Nat.add_comm] using
            (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
        refine ⟨hperm, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff p (n + 1) p.length le_rfl hmax).mpr
          refine ⟨hp.2.1, ?_⟩; intro before later hb hl hbound; omega
        · intro pattern hpattern hbad
          simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
          rcases hpattern with rfl | rfl
          · rcases (maximum_crossing_pattern_tests n p hp.1 p.length le_rfl).2.mp hbad
              with hold | ⟨first, second, third, hf, hs, hst, ht, _⟩
            · exact hp.2.2 _ (by simp [patterns]) hold
            · omega
          · rcases (maximum_four_pattern_tests n p hp.1 p.length le_rfl).2.2.mp hbad
              with hold | ⟨first, second, third, hf, hs, hst, ht, _⟩
            · exact hp.2.2 _ (by simp [patterns]) hold
            · omega
      dsimp only; let cuts := active n p; let internal := (cuts.erase 0).erase p.length
      have hlen : p.length = n := (by simpa using hp.1.length_eq); have hzero : 0 ∈ cuts :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hfront p hp⟩
      have hfinal : p.length ∈ cuts :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlast⟩
      have hfinalErase : p.length ∈ cuts.erase 0 := Finset.mem_erase.mpr ⟨by omega, hfinal⟩
      have hcard : internal.card = cuts.card - 2 := by
        have hfirst := Finset.card_erase_add_one hzero
        have hsecond := Finset.card_erase_add_one hfinalErase; dsimp only [internal]; omega
      have htest (gap : ℕ) :
          gap ∈ internal ↔ gap ∈ cuts ∧ 0 < gap ∧ gap < p.length := by
        simp only [internal, Finset.mem_erase]; constructor
        · rintro ⟨hl, hz, hg⟩; have hb : gap ≤ p.length := by
            have := (Finset.mem_filter.mp hg).1; simp only [Finset.mem_range] at this; omega
          exact ⟨hg, by omega, by omega⟩
        · rintro ⟨hg, hz, hl⟩; exact ⟨by omega, by omega, hg⟩
      let ordering := internal.orderIsoOfFin hcard; let correspondence : internal ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length} :=
        Equiv.subtypeEquivRight htest
      let selection := ordering.toEquiv.trans correspondence
      refine ⟨selection, ?_⟩; intro index
      have hindexBound : index.val < cuts.card - 2 := index.is_lt; let site := (ordering index).val
      have hsite : site ∈ internal := (ordering index).property
      have hsitePositive := ((htest site).mp hsite).2.1
      have hsiteBound := ((htest site).mp hsite).2.2
      have hsplit : cuts.filter (fun gap => gap < site) =
          insert 0 (internal.filter fun gap => gap < site) := by
        ext gap
        simp only [Finset.mem_filter, Finset.mem_insert]; constructor
        · rintro ⟨hg, hb⟩; by_cases hz : gap = 0
          · exact Or.inl hz
          · exact Or.inr ⟨(htest gap).mpr ⟨hg, by omega, by omega⟩, hb⟩
        · rintro (rfl | ⟨hg, hb⟩)
          · exact ⟨hzero, hsitePositive⟩
          · exact ⟨((htest gap).mp hg).1, hb⟩
      have hinternalRank : (internal.filter fun gap => gap < site).card = index.val := by
        have hsmall (rank : ℕ) (hr : rank ∈ Finset.range index.val) : rank < cuts.card - 2 := by
          have := Finset.mem_range.mp hr; omega
        have hbijection : (Finset.range index.val).card =
            (internal.filter fun gap => gap < site).card := by
          apply Finset.card_bij (fun rank hr => (ordering ⟨rank, hsmall rank hr⟩).val)
          · intro rank hr; apply Finset.mem_filter.mpr
            refine ⟨(ordering ⟨rank, hsmall rank hr⟩).property, ?_⟩
            have hless : (⟨rank, hsmall rank hr⟩ : Fin (cuts.card - 2)) < index :=
              Finset.mem_range.mp hr
            exact ordering.strictMono hless
          · intro first hf second hs heq; have hequal := ordering.injective (Subtype.ext heq)
            exact congrArg Fin.val hequal
          · intro gap hg; obtain ⟨hi, hless⟩ := Finset.mem_filter.mp hg
            let rank := ordering.symm ⟨gap, hi⟩; have hsmallRank : rank < index := by
              apply ordering.lt_iff_lt.mp
              change ordering (ordering.symm ⟨gap, hi⟩) < ordering index
              rw [ordering.apply_symm_apply]; exact hless
            refine ⟨rank.val, Finset.mem_range.mpr hsmallRank, ?_⟩
            have heq : (⟨rank.val, hsmall rank.val (Finset.mem_range.mpr hsmallRank)⟩ :
                Fin (cuts.card - 2)) = rank := rfl
            rw [heq]; exact congrArg Subtype.val (ordering.apply_symm_apply ⟨gap, hi⟩)
        simpa only [Finset.card_range] using hbijection.symm
      change (cuts.filter fun gap => gap < site).card = index.val + 1
      rw [hsplit, Finset.card_insert_of_notMem (by simp [internal]), hinternalRank]
    case frontCounts =>
      intro parts hparts hp hn
      exact (FishburnTenThirteenBUpdates.crossing_site_updates n (assemble parts) hn hp 0
        (Nat.zero_le _) (hfront (assemble parts) hp)).2.2.2 rfl parts hparts rfl
    case internalCounts =>
      intro first rest hparts hf hr hp site hpositive hproper hactive
      have hindec := (hparts first (by simp [patterns])).2.2
      have hsize : n = first.length + (assemble rest).length := by
        have := hp.1.length_eq; simpa [assemble, directSum, shift] using this.symm
      by_cases hempty : rest = []
      · subst rest; have hsizeFirst : n = first.length := (by simpa [assemble] using hsize)
        rw [hsizeFirst]; dsimp only
        simp only [assemble, directSum, shift, List.map_nil, List.append_nil, ↓reduceIte]
        let cuts := active first.length first; have hcount := (indecSites
          first.length first hf hindec site hpositive (by omega) hactive).2 hproper
        dsimp only at hcount; have hbound := Finset.card_filter_le cuts (fun gap => gap < site)
        change _ + (cuts.filter fun gap => gap < site).card = cuts.card + 1
        change _ = cuts.card + 1 - (cuts.filter fun gap => gap < site).card at hcount; omega
      · have htailPositive : 0 < (assemble rest).length := by
          cases rest with
          | nil => exact (hempty rfl).elim
          | cons next tail =>
            have hnext := (hparts next (by simp [patterns])).1
            have hnextLen := List.length_pos_iff.mpr hnext
            simp only [assemble, directSum, List.length_append, shift, List.length_map]; omega
        have hcount := (internalCount
          first.length (assemble rest).length first (assemble rest) hf hr
          (by simpa only [assemble, hsize] using hp) hindec htailPositive site hpositive
          hproper hactive rest (fun block hb => hparts block (by simp [hb])) rfl)
        simpa only [assemble, hsize, if_neg hempty] using hcount
    have hvalues (block : List ℕ) (hp : block.Perm (List.range' 1 block.length))
        (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ block.length := by
      have hm := hp.mem_iff.mp hv; simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm; omega
    have htailPositive (parts : List (List ℕ))
        (hp : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
        ∀ value ∈ assemble parts, 1 ≤ value := by
      induction parts with
      | nil => simp [assemble]
      | cons first rest ih =>
        intro value hv; rcases List.mem_append.mp hv with hfirst | hrest
        · exact (hvalues first (hp first (by simp [patterns])) value hfirst).1
        · obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hrest
          have := ih (fun block hb => hp block (by simp [hb])) small hs; omega
    have hfirstTest (p : List ℕ) (hp : p ∈ avoiders n patterns)
        (first : List ℕ) (rest : List (List ℕ)) (heq : assemble (first :: rest) = p)
        (hparts : ∀ block ∈ first :: rest, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block)
        (site : ℕ) (hs : site ≤ p.length) :
        sumIndecomposable (p.insertIdx site (n + 1)) ↔ site < first.length := by
      have hf := hparts first (by simp [patterns])
      have hfirstPositive : 0 < first.length := List.length_pos_iff.mpr hf.1
      have hdecomp : p = first ++ shift first.length (assemble rest) := heq.symm
      have hlength : p.length = first.length + (assemble rest).length := by
        simp [hdecomp, shift]
      have hbefore (index : ℕ) (hb : index < first.length) :
          p.getD index 0 = first.getD index 0 := by
        rw [hdecomp]; exact List.getD_append _ _ _ _ hb
      have hsmall (index : ℕ) (hb : index < first.length) : p.getD index 0 ≤ first.length := by
        rw [hbefore index hb]; apply (hvalues first hf.2.1 _ _).2
        rw [List.getD_eq_getElem first 0 hb]; exact List.getElem_mem hb
      have hlarge (index : ℕ) (hl : first.length ≤ index) (hb : index < p.length) :
          first.length < p.getD index 0 := by
        have hm : p.getD index 0 ∈ shift first.length (assemble rest) := by
          rw [hdecomp, List.getD_append_right _ _ _ _ hl,
            List.getD_eq_getElem _ 0 (by simp only [shift, List.length_map]; omega)]
          exact List.getElem_mem (by simp only [shift, List.length_map]; omega)
        obtain ⟨value, hv, hequal⟩ := List.mem_map.mp hm
        have := htailPositive rest (fun block hb => (hparts block (by simp [hb])).2.1) value hv
        omega
      rw [indecomposable_maximum_insertion n p hp.1 site hs]; constructor
      · intro hcuts; by_contra hnot; obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
          hcuts first.length hfirstPositive (by omega)
        have := hsmall before hb; have := hlarge later hl hbound; omega
      · intro hproper boundary hb hs
        obtain ⟨before, later, hbad⟩ := hf.2.2 ⟨boundary, by omega⟩ hb
        have hbef : before.val < boundary := by
          have := before.is_lt; simp only [List.length_take] at this; omega
        have hlat : boundary + later.val < first.length := by
          have := later.is_lt; simp only [List.length_drop] at this; omega
        refine ⟨before.val, boundary + later.val, hbef, by omega, by omega, ?_⟩
        rw [hbefore before.val (by omega), hbefore (boundary + later.val) hlat,
          List.getD_eq_getElem first 0 (by omega : before.val < first.length),
          List.getD_eq_getElem first 0 hlat]
        simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hbad
    have hsource (entry : List ℕ × ℕ) (he : entry.1 ∈ avoiders n patterns ∧
          (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
            (∀ block ∈ first :: rest, block ≠ [] ∧
              block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
            entry.2 < first.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
              avoiders (n + 1) patterns)) :
        entry.2 ≤ entry.1.length ∧
        entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns ∧
            sumIndecomposable (entry.1.insertIdx entry.2 (n + 1)) := by
      rcases he.2 with hz | ⟨first, rest, heq, hparts, hb, ha⟩
      · refine ⟨by omega, by simpa only [hz] using hfront entry.1 he.1, ?_⟩
        apply (indecomposable_maximum_insertion n entry.1 he.1.1 entry.2 (by omega)).mpr
        intros
        omega
      · have hlength : entry.1.length = first.length + (assemble rest).length := by
          rw [← heq]; simp [assemble, directSum, shift]
        exact ⟨by omega, ha, (hfirstTest entry.1 he.1 first rest heq hparts entry.2
          (by omega)).mpr hb⟩
    have hbij := maximum_insertion_bijection n patterns; refine ⟨?_, ?_, ?_⟩
    · intro entry he; exact (hsource entry he).2
    · intro first hf second hs heq; have hfirst := hsource first hf
      have hsecond := hsource second hs; let firstRaw : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n patterns ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) patterns} := ⟨first, hf.1, hfirst.1, hfirst.2.1⟩
      let secondRaw : {entry : List ℕ × ℕ // entry.1 ∈ avoiders n patterns ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) patterns} := ⟨second, hs.1, hsecond.1, hsecond.2.1⟩
      have hraw := hbij.1 (a₁ := firstRaw) (a₂ := secondRaw) (Subtype.ext heq)
      exact congrArg Subtype.val hraw
    · intro p hp; obtain ⟨entry, heq⟩ := hbij.2 ⟨p, hp.1⟩
      have hword : entry.val.1.insertIdx entry.val.2 (n + 1) = p := congrArg Subtype.val heq
      refine ⟨entry.val, ⟨entry.property.1, ?_⟩, hword⟩; by_cases hz : entry.val.2 = 0
      · exact Or.inl hz
      have hpatterns : ∀ pattern ∈ patterns,
          pattern ≠ [] ∧ sumIndecomposable pattern ∧ (∀ value ∈ pattern, 1 ≤ value) ∧
          ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern →
            rank ∈ pattern := by
        intro pattern hpattern
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl; all_goals
          refine ⟨by decide, by unfold sumIndecomposable; decide, by simp [patterns], ?_⟩
          intro rank hr hbound; norm_num [NonnestingDefs.letters] at hbound
          simp only [List.mem_cons, List.not_mem_nil]; omega
      obtain ⟨parts, hparts, _⟩ := (unique_sum_components n entry.val.1 entry.property.1.1
        patterns hpatterns).1
      cases parts with
      | nil =>
        have hempty : entry.val.1 = [] := (by simpa [assemble] using hparts.1.symm)
        have := entry.property.2.1; simp only [hempty, List.length_nil] at this; omega
      | cons first rest =>
        have hproper := (hfirstTest entry.val.1 entry.property.1 first rest hparts.1
          hparts.2.1 entry.val.2 entry.property.2.1).mp (by rw [hword]; exact hp.2)
        exact Or.inr ⟨first, rest, hparts.1, hparts.2.1, hproper, entry.property.2.2⟩
  have hstructureGlobal := hstructure; have hstructure := hstructure n
  let components : Set (List (List ℕ)) := {parts | (∀ block ∈ parts, block ≠ [] ∧
      block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
    assemble parts ∈ avoiders n patterns}
  let choices := Σ parts : components,
    Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)
  have hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
      (∀ value ∈ pattern, 1 ≤ value) ∧
      ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern := by
    intro pattern hp; simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl; all_goals
      refine ⟨by decide, by unfold sumIndecomposable; decide, by simp [patterns], ?_⟩
      intro rank hr hb; norm_num [NonnestingDefs.letters] at hb
      simp only [List.mem_cons, List.not_mem_nil]; omega
  have hclosure := (unique_sum_components 0 [] (by simp [patterns]) patterns hpatterns).2.1
  have hinfo (parts : components) : parts.val.headD [] ≠ [] ∧
      parts.val.headD [] ∈ avoiders (parts.val.headD []).length patterns ∧
      assemble parts.val.tail ∈ avoiders (assemble parts.val.tail).length patterns ∧
      parts.val = parts.val.headD [] :: parts.val.tail ∧
      n = (parts.val.headD []).length + (assemble parts.val.tail).length := by
    have hv := parts.property.1; have hp := parts.property.2; cases heq : parts.val with
    | nil =>
      rw [heq] at hp; have hlen := hp.1.length_eq
      simp only [assemble, List.length_nil, List.length_range'] at hlen; omega
    | cons first rest =>
      rw [heq] at hv hp; change first ≠ [] ∧ first ∈ avoiders first.length patterns ∧
        assemble rest ∈ avoiders (assemble rest).length patterns ∧
        first :: rest = first :: rest ∧ n = first.length + (assemble rest).length
      have hlen : (assemble (first :: rest)).length = n := (by simpa using hp.1.length_eq)
      have hblocks := (hclosure (first :: rest) hv).mp (by simpa only [hlen] using hp)
      refine ⟨(hv first (by simp [patterns])).1,
        hblocks first (by simp [patterns]), ?_, rfl, ?_⟩
      · apply (hclosure rest (fun block hb => hv block (by simp [hb]))).mpr
        exact fun block hb => hblocks block (by simp [hb])
      · simpa only [assemble, directSum, shift, List.length_append, List.length_map]
          using hlen.symm
  let serialize (parts : components) : avoiders n patterns :=
    ⟨assemble parts.val, parts.property.2⟩
  have hserialize : Function.Injective serialize := by
    intro left right heq
    have hequal : assemble left.val = assemble right.val := congrArg Subtype.val heq
    obtain ⟨canonical, _, hu⟩ :=
      (unique_sum_components n (assemble left.val) left.property.2.1 patterns hpatterns).1
    have hlen : (assemble left.val).length = n := (by simpa using left.property.2.1.length_eq)
    have hl : left.val = canonical := hu _ ⟨rfl, left.property.1, by
      simpa only [hlen] using hclosure left.val left.property.1⟩
    have hr : right.val = canonical := hu _ ⟨hequal.symm, right.property.1, by
      simpa only [← hequal, hlen] using hclosure right.val right.property.1⟩
    exact Subtype.ext (hl.trans hr.symm)
  have hserializeSurjective : Function.Surjective serialize := by
    intro word; obtain ⟨parts, hp, _⟩ :=
      (unique_sum_components n word.val word.property.1 patterns hpatterns).1
    exact ⟨⟨parts, hp.2.1, by rw [hp.1]; exact word.property⟩, Subtype.ext hp.1⟩
  have hsite (parts : components) (gap : ℕ) (hb : gap ≤ (parts.val.headD []).length) :
      (assemble parts.val).insertIdx gap (n + 1) ∈ avoiders (n + 1) patterns ↔
        (parts.val.headD []).insertIdx gap ((parts.val.headD []).length + 1) ∈
          avoiders ((parts.val.headD []).length + 1) patterns := by
    have hi := hinfo parts; have heq : assemble parts.val = directSum (parts.val.headD []).length
        (parts.val.headD []) (assemble parts.val.tail) := by
      conv_lhs => rw [hi.2.2.2.1]
      rfl
    have hs := FishburnTenThirteenBSums.crossing_sum_sites
      (parts.val.headD []).length (assemble parts.val.tail).length
      (parts.val.headD []) (assemble parts.val.tail) hi.2.1 hi.2.2.1
      (by simpa only [heq, hi.2.2.2.2] using parts.property.2)
    simpa only [← heq, ← hi.2.2.2.2] using hs.1 gap hb
  let pick (parts : components) :
      Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2) ≃
        {gap : ℕ // gap ∈ active (parts.val.headD []).length (parts.val.headD []) ∧
          0 < gap ∧ gap < (parts.val.headD []).length} :=
    Classical.choose ((hstructureGlobal (parts.val.headD []).length).2.2.2
      (parts.val.headD []) (hinfo parts).2.1
      (List.length_pos_iff_ne_nil.mpr (hinfo parts).1))
  have hpick (parts : components)
      (index : Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)) :
      ((active (parts.val.headD []).length (parts.val.headD [])).filter
        fun gap => gap < (pick parts index).val).card = index.val + 1 :=
    Classical.choose_spec ((hstructureGlobal (parts.val.headD []).length).2.2.2
      (parts.val.headD []) (hinfo parts).2.1
      (List.length_pos_iff_ne_nil.mpr (hinfo parts).1)) index
  let domain : Set (List ℕ × ℕ) := {entry | entry.1 ∈ avoiders n patterns ∧
    (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
      (∀ block ∈ first :: rest, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      entry.2 < first.length ∧
      entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns)}
  let raw : components ⊕ choices → domain
    | Sum.inl parts => ⟨(assemble parts.val, 0), parts.property.2, Or.inl rfl⟩
    | Sum.inr ⟨parts, index⟩ => ⟨(assemble parts.val, (pick parts index).val),
      parts.property.2, Or.inr ⟨parts.val.headD [], parts.val.tail,
        congrArg assemble (hinfo parts).2.2.2.1.symm,
        by simpa only [← (hinfo parts).2.2.2.1] using parts.property.1,
        (pick parts index).property.2.2,
        (hsite parts _ (Nat.le_of_lt (pick parts index).property.2.2)).mpr
          (Finset.mem_filter.mp (pick parts index).property.1).2⟩⟩
  have hrawInjective : Function.Injective raw := by
    intro left right heq; have hv := congrArg Subtype.val heq; cases left with
    | inl left =>
      cases right with
      | inl right =>
        exact congrArg Sum.inl (hserialize (Subtype.ext (congrArg Prod.fst hv)))
      | inr right =>
        have hs := congrArg Prod.snd hv; have hp := (pick right.1 right.2).property.2.1
        change 0 = (pick right.1 right.2).val at hs; omega
    | inr left =>
      cases right with
      | inl right =>
        have hs := congrArg Prod.snd hv; have hp := (pick left.1 left.2).property.2.1
        change (pick left.1 left.2).val = 0 at hs; omega
      | inr right =>
        have hparts : left.1 = right.1 := hserialize (Subtype.ext (congrArg Prod.fst hv))
        rcases left with ⟨lp, li⟩; rcases right with ⟨rp, ri⟩; dsimp at hparts; subst rp
        have hindex : li = ri := (pick lp).injective (Subtype.ext (congrArg Prod.snd hv)); subst ri
        rfl
  have hrawSurjective : Function.Surjective raw := by
    intro entry; by_cases hz : entry.val.2 = 0
    · let parts := (Equiv.ofBijective serialize ⟨hserialize, hserializeSurjective⟩).symm
        ⟨entry.val.1, entry.property.1⟩
      have heq : assemble parts.val = entry.val.1 := congrArg Subtype.val
        ((Equiv.ofBijective serialize ⟨hserialize, hserializeSurjective⟩).apply_symm_apply
          ⟨entry.val.1, entry.property.1⟩)
      exact ⟨Sum.inl parts, Subtype.ext (Prod.ext heq hz.symm)⟩
    · obtain ⟨first, rest, heq, hv, hb, ha⟩ := entry.property.2.resolve_left hz
      let parts : components := ⟨first :: rest, hv, by rw [heq]; exact entry.property.1⟩
      have hbound : entry.val.2 ≤ first.length := (by omega)
      have hlocal := (hsite parts entry.val.2 hbound).mp (by simpa only [parts, heq] using ha)
      let gap : {gap : ℕ // gap ∈ active (parts.val.headD []).length
          (parts.val.headD []) ∧ 0 < gap ∧ gap < (parts.val.headD []).length} :=
        ⟨entry.val.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          change entry.val.2 < first.length + 1
          omega), hlocal⟩, by omega, hb⟩
      refine ⟨Sum.inr ⟨parts, (pick parts).symm gap⟩, Subtype.ext ?_⟩
      change (assemble parts.val, (pick parts ((pick parts).symm gap)).val) = entry.val
      exact Prod.ext heq (congrArg Subtype.val ((pick parts).apply_symm_apply gap))
  let construction := (Equiv.ofBijective raw ⟨hrawInjective, hrawSurjective⟩).trans
    hstructure.1.equiv
  have hfrontLabels (parts : components) :
      (active (n + 1) (construction (Sum.inl parts)).val).card = parts.val.length + 1 := by
    exact hstructure.2.1 parts.val parts.property.1 parts.property.2 hn
  have hinternalLabels (parts : components)
      (index : Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)) :
      (active (n + 1) (construction (Sum.inr ⟨parts, index⟩)).val).card =
        (active (parts.val.headD []).length (parts.val.headD [])).card +
          (if parts.val.tail = [] then 1 else parts.val.tail.length) - index.val - 1 := by
    have hi := hinfo parts
    have hv : ∀ block ∈ parts.val.headD [] :: parts.val.tail, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
      simpa only [← hi.2.2.2.1] using parts.property.1
    have hp : assemble (parts.val.headD [] :: parts.val.tail) ∈ avoiders n patterns := by
      simpa only [← hi.2.2.2.1] using parts.property.2
    have hf := hstructure.2.2.1 (parts.val.headD []) parts.val.tail hv hi.2.1 hi.2.2.1 hp
      (pick parts index).val (pick parts index).property.2.1 (pick parts index).property.2.2
      (Finset.mem_filter.mp (pick parts index).property.1).2
    have hrank := hpick parts index; change (active (n + 1)
        ((assemble (parts.val.headD [] :: parts.val.tail)).insertIdx
          (pick parts index).val (n + 1))).card +
      ((active (parts.val.headD []).length (parts.val.headD [])).filter
        fun gap => gap < (pick parts index).val).card =
      (active (parts.val.headD []).length (parts.val.headD [])).card +
        if parts.val.tail = [] then 1 else parts.val.tail.length at hf
    rw [← hi.2.2.2.1, hrank] at hf; change (active (n + 1)
      ((assemble parts.val).insertIdx (pick parts index).val (n + 1))).card = _
    omega
  have hfinite : (avoiders n patterns).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset; intro word hw
    exact List.mem_permutations.mpr hw.1
  let : Finite (avoiders n patterns) := hfinite.to_subtype
  let : Finite components := Finite.of_injective serialize hserialize
  let : Fintype components := Fintype.ofFinite _; rw [← finsum_comp_equiv construction]
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_sum_type]; apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl; intro parts _; rw [hfrontLabels]; congr 1
  · rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl; intro parts _; have hsum : (∑ index : Fin
        ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
        (Polynomial.X : Polynomial ℚ) ^
          ((active (n + 1) (construction (Sum.inr ⟨parts, index⟩)).val).card - 2)) =
        ∑ index : Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
          (Polynomial.X : Polynomial ℚ) ^
            ((active (parts.val.headD []).length (parts.val.headD [])).card +
              (if parts.val.tail = [] then 1 else parts.val.tail.length) - index.val - 3) := by
      apply Finset.sum_congr rfl; intro index _; rw [hinternalLabels]; congr 1
    rw [hsum, Fin.sum_univ_eq_sum_range (fun index =>
      (Polynomial.X : Polynomial ℚ) ^
        ((active (parts.val.headD []).length (parts.val.headD [])).card +
          (if parts.val.tail = [] then 1 else parts.val.tail.length) - index - 3))]
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun index =>
      (Polynomial.X : Polynomial ℚ) ^
        (if parts.val.tail = [] then 1 else parts.val.tail.length) * Polynomial.X ^ index)]
    apply Finset.sum_congr rfl; intro index hi; rw [← pow_add]; have := Finset.mem_range.mp hi
    congr 1; dsimp only [active, patterns] at this ⊢; omega
end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable
