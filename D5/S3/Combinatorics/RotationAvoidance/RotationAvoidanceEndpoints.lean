/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints
   mirror-E: none(waiver:extreme-endpoint-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Extreme endpoints count unique-bad-cut words through the A and binary D classes. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGroups
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEndpoints

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular

theorem ascending_extreme_endpoint_count (width : ℕ) (hwidth : 2 ≤ width) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
      word.head? = some 1 ∧ word.getLast? = some (width + 2) ∧
      ∀ cut < width + 2, Occurs [1, 2, 3, 4] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard =
        2 ^ (width + 1) - 2 * width - 2 - (width + 1).choose 3 := by
  classical
  have build (pattern selected : List ℕ) (witness : ℕ → ℕ)
      (hpattern : pattern.Perm (List.range' 1 pattern.length))
      (hletters : letters pattern = pattern.length)
      (hincreasing : ∀ rank, 1 ≤ rank → rank < pattern.length →
        witness rank < witness (rank + 1))
      (hsub : (pattern.map witness).Sublist selected) : Occurs pattern selected := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa only [hletters] using hincreasing
    · intro rank hlow hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      rw [hletters] at hhigh
      simp only [List.mem_range'_1]
      exact ⟨hlow, by omega⟩
  have quadruple (first second third fourth : ℕ)
      (hfirst : first < second) (hsecond : second < third) (hthird : third < fourth)
      (selected : List ℕ) (hsub : [first, second, third, fourth].Sublist selected) :
      Occurs [1, 2, 3, 4] selected := by
    let witness := fun rank : ℕ =>
      if rank = 1 then first else if rank = 2 then second else
        if rank = 3 then third else fourth
    apply build [1, 2, 3, 4] selected witness (by rfl) (by rfl)
    · intro rank hlow hhigh
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
        simp only [List.length_cons, List.length_nil] at hhigh
        omega
      rcases this with rfl | rfl | rfl
      · exact hfirst
      · exact hsecond
      · exact hthird
    · simpa [witness] using hsub
  have triple (first second third : ℕ) (hfirst : first < second)
      (hsecond : second < third) (selected : List ℕ)
      (hsub : [first, second, third].Sublist selected) : Occurs [1, 2, 3] selected := by
    let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then second
      else third
    apply build [1, 2, 3] selected witness (by rfl) (by rfl)
    · intro rank hlow hhigh
      have : rank = 1 ∨ rank = 2 := by
        simp only [List.length_cons, List.length_nil] at hhigh
        omega
      rcases this with rfl | rfl
      · exact hfirst
      · exact hsecond
    · simpa [witness] using hsub
  have rangeEndpoints : List.range' 1 (width + 2) =
      1 :: List.range' 2 width ++ [width + 2] := by
    rw [show width + 2 = (width + 1) + 1 by omega, List.range'_concat,
      List.range'_succ]
    simp [Nat.add_comm]
  have criterion (interior : List ℕ) (hp : interior.Perm (List.range' 2 width)) :
      (∀ cut < width + 2,
        Occurs [1, 2, 3, 4] ((1 :: interior ++ [width + 2]).rotate cut) ↔ cut = 0) ↔
        ¬ Occurs [1, 2, 3] interior ∧ ¬ Occurs [3, 4, 1, 2] interior ∧
          ¬ interior.Pairwise (· > ·) := by
    let word := 1 :: interior ++ [width + 2]
    have wordPerm : word.Perm (List.range' 1 (width + 2)) := by
      rw [rangeEndpoints]
      exact (hp.append_right [width + 2]).cons 1
    have wordDrop : word.dropLast = 1 :: interior := by
      change ((1 :: interior) ++ [width + 2]).dropLast = 1 :: interior
      rw [List.dropLast_append_cons]
      simp
    have bounds : ∀ value ∈ interior, 1 < value ∧ value < width + 2 := by
      intro value hvalue
      have := List.mem_range'.mp (hp.mem_iff.mp hvalue)
      omega
    have hnodup : interior.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have contains_interior (pattern : List ℕ) : Occurs pattern interior →
        Occurs pattern word := by
      rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      exact ⟨witness, hincreasing, fun rank hlo hhi =>
        List.mem_cons_of_mem _ (List.mem_append_left _ (hmem rank hlo hhi)),
          (hsub.trans (List.sublist_append_left _ _)).cons 1, by simp⟩
    have nonendpoint_occurrence (first second third last : ℕ)
        (hpattern : ([first, second, third, last] : List ℕ).Perm [1, 2, 3, 4])
        (hfirst : 1 < first) (hlast : last < 4) :
        Occurs [first, second, third, last] word →
          Occurs [first, second, third, last] interior := by
      have hletters : letters [first, second, third, last] = 4 := by
        simpa [letters] using hpattern.foldr_eq (f := max) 0
      rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have hi : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1) := by
        simpa only [hletters] using hincreasing
      have hw1 : 1 ≤ witness 1 := by
        have := wordPerm.mem_iff.mp (hmem 1 (by omega) (by rw [hletters]; omega))
        have := List.mem_range'.mp this
        omega
      have hw4 : witness 4 ≤ width + 2 := by
        have := wordPerm.mem_iff.mp (hmem 4 (by omega)
          (by simpa only [hletters] using Nat.le_refl 4))
        have := List.mem_range'.mp this
        omega
      have hfirstBound : first ≤ 4 := by
        have := hpattern.mem_iff.mp (List.mem_cons_self :
          first ∈ [first, second, third, last])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      have hlastBound : 1 ≤ last := by
        have := hpattern.mem_iff.mp (show last ∈ [first, second, third, last] by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      have h12 := hi 1 (by omega) (by omega)
      have h23 := hi 2 (by omega) (by omega)
      have h34 := hi 3 (by omega) (by omega)
      norm_num only at h12 h23 h34
      have hfirstNe : witness first ≠ 1 := by
        have : first = 2 ∨ first = 3 ∨ first = 4 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      have hlastNe : witness last ≠ width + 2 := by
        have : last = 1 ∨ last = 2 ∨ last = 3 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      have hwithoutFirst : ([first, second, third, last].map witness).Sublist
          (interior ++ [width + 2]) := List.Sublist.of_cons_of_ne hfirstNe hsub
      have hreverse : [witness last, witness third, witness second, witness first].Sublist
          ((width + 2) :: interior.reverse) := by
        simpa using hwithoutFirst.reverse
      have hwithoutLast := List.Sublist.of_cons_of_ne hlastNe hreverse
      have hselected : ([first, second, third, last].map witness).Sublist interior := by
        simpa using hwithoutLast.reverse
      apply build [first, second, third, last] interior witness hpattern hletters
      · simpa only [List.length_cons, List.length_nil] using hi
      · exact hselected
    have triple_subpatterns :
        Occurs [2, 3, 4, 1] interior ∨ Occurs [4, 1, 2, 3] interior →
          Occurs [1, 2, 3] interior := by
      rintro (⟨witness, hi, _, hsub, _⟩ | ⟨witness, hi, _, hsub, _⟩)
      · apply triple (witness 2) (witness 3) (witness 4)
          (hi 2 (by omega) (by decide)) (hi 3 (by omega) (by decide))
        exact ((by decide : [2, 3, 4].Sublist [2, 3, 4, 1]).map witness).trans hsub
      · apply triple (witness 1) (witness 2) (witness 3)
          (hi 1 (by omega) (by decide)) (hi 2 (by omega) (by decide))
        exact ((by decide : [1, 2, 3].Sublist [4, 1, 2, 3]).map witness).trans hsub
    rw [unique_bad_cut_iff (width + 2) (by omega) [1, 2, 3, 4] word (by rfl) wordPerm]
    constructor
    · rintro ⟨hocc, hshifts, _, hdrop⟩
      have h123 : ¬ Occurs [1, 2, 3] interior := by
        rintro ⟨witness, hi, hmem, hsub, _⟩
        have hw1 := (bounds _ (hmem 1 (by omega) (by decide))).1
        have hfull := quadruple 1 (witness 1) (witness 2) (witness 3) hw1
          (hi 1 (by omega) (by decide)) (hi 2 (by omega) (by decide))
          (1 :: interior) (hsub.cons_cons 1)
        apply hdrop
        simpa only [wordDrop] using hfull
      have h3412 : ¬ Occurs [3, 4, 1, 2] interior := by
        intro hocc
        exact hshifts 2 (by omega) (by omega) (contains_interior _ hocc)
      refine ⟨h123, h3412, ?_⟩
      intro hdesc
      obtain ⟨witness, hi, _, hsub, _⟩ := hocc
      have hpair : [witness 2, witness 3].Sublist interior := by
        have hfirst := hsub.of_cons_cons
        have hreverse : [witness 4, witness 3, witness 2].Sublist
            ((width + 2) :: interior.reverse) := by simpa using hfirst.reverse
        simpa using hreverse.of_cons_cons.reverse
      have := List.pairwise_iff_forall_sublist.mp hdesc hpair
      have hlt : witness 2 < witness 3 := hi 2 (by omega) (by decide)
      omega
    · rintro ⟨h123, h3412, hdesc⟩
      obtain ⟨first, last, hpair, hnot⟩ :
          ∃ first last, [first, last].Sublist interior ∧ first ≤ last := by
        have := List.pairwise_iff_forall_sublist.not.mp hdesc
        push Not at this
        exact this
      have hne := List.pairwise_iff_forall_sublist.mp
        (List.nodup_iff_pairwise_ne.mp hnodup) hpair
      have hlo := (bounds first (hpair.subset (by simp))).1
      have hhi := (bounds last (hpair.subset (by simp))).2
      refine ⟨quadruple 1 first last (width + 2) hlo (by omega) hhi word
        ((hpair.append_right [width + 2]).cons_cons 1), ?_, ?_, ?_⟩
      · intro shift hpositive hshift hocc
        have : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact h123 (triple_subpatterns (Or.inl
            (nonendpoint_occurrence 2 3 4 1 (by decide) (by decide) (by decide) hocc)))
        · exact h3412 (nonendpoint_occurrence 3 4 1 2
            (by decide) (by decide) (by decide) hocc)
        · exact h123 (triple_subpatterns (Or.inr
            (nonendpoint_occurrence 4 1 2 3 (by decide) (by decide) (by decide) hocc)))
      · rintro ⟨witness, hi, _, hsub, _⟩
        have hselected : [witness 1, witness 2, witness 3].Sublist interior := by
          have hreverse : [witness 4, witness 3, witness 2, witness 1].Sublist
              ((width + 2) :: interior.reverse) := by simpa [word] using hsub.reverse
          simpa using hreverse.of_cons_cons.reverse
        exact h123 (triple _ _ _ (hi 1 (by omega) (by decide))
          (hi 2 (by omega) (by decide)) interior hselected)
      · rintro ⟨witness, hi, _, hsub, _⟩
        have hselected : [witness 2, witness 3, witness 4].Sublist interior := by
          have hsub' : [witness 1, witness 2, witness 3, witness 4].Sublist
              (1 :: interior) := by
            simpa only [wordDrop, List.map_cons, List.map_nil] using hsub
          exact hsub'.of_cons_cons
        exact h123 (triple _ _ _ (hi 2 (by omega) (by decide))
          (hi 3 (by omega) (by decide)) interior hselected)
  let parents := Fishburn.FishburnClassicalDefs.classicalAvoiders width
    [[1, 2, 3], [3, 4, 1, 2]]
  let decreasing := (List.range' 1 width).reverse
  let domain := parents \ {decreasing}
  let target := {word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
    word.head? = some 1 ∧ word.getLast? = some (width + 2) ∧
    ∀ cut < width + 2, Occurs [1, 2, 3, 4] (word.rotate cut) ↔ cut = 0}
  let emit := fun word : List ℕ => 1 :: word.map Nat.succ ++ [width + 2]
  have membership (word : List ℕ) : word ∈ domain ↔
      word.Perm (List.range' 1 width) ∧ ¬ Occurs [1, 2, 3] word ∧
        ¬ Occurs [3, 4, 1, 2] word ∧ ¬ word.Pairwise (· > ·) := by
    have descent (hp : word.Perm (List.range' 1 width)) :
        word = decreasing ↔ word.Pairwise (· > ·) := by
      have hd : decreasing.Pairwise (· > ·) :=
        List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
      exact ⟨fun heq => heq ▸ hd, fun hw =>
        (hp.trans (List.reverse_perm _).symm).eq_of_pairwise
          (by intro first last hfirst hlast; omega) hw hd⟩
    simp only [domain, parents, Set.mem_sdiff, Fishburn.FishburnClassicalDefs.classicalAvoiders,
      Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hp, h123, h3412⟩, hne⟩
      exact ⟨hp, h123, h3412, fun hd => hne ((descent hp).mpr hd)⟩
    · rintro ⟨hp, h123, h3412, hd⟩
      exact ⟨⟨hp, h123, h3412⟩, fun heq => hd ((descent hp).mp heq)⟩
  have shift (pattern word : List ℕ)
      (hpattern : pattern ∈ [[1, 2, 3], [3, 4, 1, 2]]) :
      Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
    have hl : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
      (by intro first last hlt; omega)
  have shiftedPerm (word : List ℕ) (hp : word.Perm (List.range' 1 width)) :
      (word.map Nat.succ).Perm (List.range' 2 width) := by
    have hr : (List.range' 1 width).map Nat.succ = List.range' 2 width := by
      simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
        funext value; omega, Nat.reduceAdd] using List.map_add_range' (a := 1) 1 width 1
    simpa only [hr] using hp.map Nat.succ
  have emitMember (word : List ℕ) (hword : word ∈ domain) : emit word ∈ target := by
    obtain ⟨hp, h123, h3412, hd⟩ := (membership word).mp hword
    have hinner := shiftedPerm word hp
    have htest := (criterion _ hinner).mpr ⟨fun hocc => h123 ((shift _ _ (by simp)).mp hocc),
      fun hocc => h3412 ((shift _ _ (by simp)).mp hocc), fun hdesc =>
        hd (List.pairwise_map.mp hdesc |>.imp (by intro first last hlt; omega))⟩
    refine ⟨?_, by simp [emit], ?_, htest⟩
    · rw [rangeEndpoints]
      exact (hinner.append_right [width + 2]).cons 1
    · change ((1 :: word.map Nat.succ) ++ [width + 2]).getLast? = some (width + 2)
      rw [List.getLast?_append_cons]
      rfl
  have emitInjective : Function.Injective emit := by
    intro first second heq
    exact List.map_injective_iff.mpr Nat.succ_injective
      (List.append_cancel_right (List.cons.inj heq).2)
  have emitSurjective (word : List ℕ) (hword : word ∈ target) :
      ∃ parent ∈ domain, emit parent = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hword.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = 1 :: interior ++ [width + 2] := by
      cases front with
      | nil =>
        have := hword.1.length_eq
        simp [hlast] at this
      | cons head interior =>
        have : head = 1 := by simpa [hlast] using hword.2.1
        exact ⟨interior, by simpa [this] using hlast⟩
    have hinner : interior.Perm (List.range' 2 width) := by
      have hp := hword.1
      rw [hsplit, rangeEndpoints] at hp
      exact (List.perm_append_right_iff _).mp (List.Perm.cons_inv hp)
    let parent := interior.map (· - 1)
    have restore : parent.map Nat.succ = interior := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hvalue
      have := List.mem_range'.mp (hinner.mem_iff.mp hvalue)
      dsimp; omega
    have hparent : parent.Perm (List.range' 1 width) := by
      have hr : (List.range' 2 width).map (fun value : ℕ => value - 1) =
          List.range' 1 width := List.map_sub_range' (by omega : 1 ≤ 2) width
      have hmap := hinner.map (fun value : ℕ => value - 1)
      rw [hr] at hmap
      exact hmap
    have htest := (criterion interior hinner).mp (hsplit ▸ hword.2.2.2)
    refine ⟨parent, (membership parent).mpr ⟨hparent, ?_, ?_, ?_⟩,
      by simpa only [emit, restore] using hsplit.symm⟩
    · intro hocc
      exact htest.1 (restore ▸ (shift _ _ (by simp)).mpr hocc)
    · intro hocc
      exact htest.2.1 (restore ▸ (shift _ _ (by simp)).mpr hocc)
    · intro hd
      exact htest.2.2 (restore ▸ List.pairwise_map.mpr
        (hd.imp (by intro first last hlt; omega)))
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun word _ => emit word)
    emitMember (fun first second _ _ heq => emitInjective heq) (by
      intro word hword
      obtain ⟨parent, hparent, heq⟩ := emitSurjective word hword
      exact ⟨parent, hparent, heq⟩)
  have hdecreasing : decreasing ∈ parents := by
    have hd : decreasing.Pairwise (· > ·) :=
      List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
    refine ⟨List.reverse_perm _, ?_⟩
    intro pattern hpattern
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl
    · rintro ⟨witness, hi, _, hsub, _⟩
      have hp := ((by decide : [1, 2].Sublist [1, 2, 3]).map witness).trans hsub
      have := List.pairwise_iff_forall_sublist.mp hd hp
      have hlt : witness 1 < witness 2 := hi 1 (by omega) (by decide)
      omega
    · rintro ⟨witness, hi, _, hsub, _⟩
      have hp := ((by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness).trans hsub
      have := List.pairwise_iff_forall_sublist.mp hd hp
      have hlt : witness 3 < witness 4 := hi 3 (by omega) (by decide)
      omega
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 width).permutations).subset
    intro word hword
    exact List.mem_permutations.mpr hword.1
  have hminus := Set.ncard_sdiff_singleton_add_one hdecreasing finiteParents
  have henumeration := RotationAvoidanceEnumeration.ascending_count width
  change target.ncard = _
  change domain.ncard + 1 = parents.ncard at hminus
  change parents.ncard = _ at henumeration
  omega

theorem fibonacci_extreme_endpoint_count (width : ℕ) (hwidth : 2 ≤ width) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
      word.head? = some 1 ∧ word.getLast? = some (width + 2) ∧
      ∀ cut < width + 2, Occurs [1, 3, 2, 4] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard = 2 ^ (width - 1) - 1 := by
  classical
  have build (pattern selected : List ℕ) (witness : ℕ → ℕ)
      (hpattern : pattern.Perm (List.range' 1 pattern.length))
      (hletters : letters pattern = pattern.length)
      (hincreasing : ∀ rank, 1 ≤ rank → rank < pattern.length →
        witness rank < witness (rank + 1))
      (hsub : (pattern.map witness).Sublist selected) : Occurs pattern selected := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa only [hletters] using hincreasing
    · intro rank hlow hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      rw [hletters] at hhigh
      simp only [List.mem_range'_1]
      exact ⟨hlow, by omega⟩
  have rangeEndpoints : List.range' 1 (width + 2) =
      1 :: List.range' 2 width ++ [width + 2] := by
    rw [show width + 2 = (width + 1) + 1 by omega, List.range'_concat,
      List.range'_succ]
    simp [Nat.add_comm]
  have criterion (interior : List ℕ) (hp : interior.Perm (List.range' 2 width)) :
      (∀ cut < width + 2,
        Occurs [1, 3, 2, 4] ((1 :: interior ++ [width + 2]).rotate cut) ↔ cut = 0) ↔
        ¬ Occurs [1, 3, 2] interior ∧ ¬ Occurs [2, 1, 3] interior ∧
          ¬ interior.Pairwise (· < ·) := by
    let word := 1 :: interior ++ [width + 2]
    have wordPerm : word.Perm (List.range' 1 (width + 2)) := by
      rw [rangeEndpoints]
      exact (hp.append_right [width + 2]).cons 1
    have wordDrop : word.dropLast = 1 :: interior := by
      change ((1 :: interior) ++ [width + 2]).dropLast = 1 :: interior
      rw [List.dropLast_append_cons]
      simp
    have bounds : ∀ value ∈ interior, 1 < value ∧ value < width + 2 := by
      intro value hvalue
      have := List.mem_range'.mp (hp.mem_iff.mp hvalue)
      omega
    have hnodup : interior.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have nonendpoint_occurrence (first second third last : ℕ)
        (hpattern : ([first, second, third, last] : List ℕ).Perm [1, 2, 3, 4])
        (hfirst : 1 < first) (hlast : last < 4) :
        Occurs [first, second, third, last] word →
          Occurs [first, second, third, last] interior := by
      have hletters : letters [first, second, third, last] = 4 := by
        simpa [letters] using hpattern.foldr_eq (f := max) 0
      rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have hi : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1) := by
        simpa only [hletters] using hincreasing
      have hw1 : 1 ≤ witness 1 := by
        have := wordPerm.mem_iff.mp (hmem 1 (by omega) (by rw [hletters]; omega))
        have := List.mem_range'.mp this
        omega
      have hw4 : witness 4 ≤ width + 2 := by
        have := wordPerm.mem_iff.mp (hmem 4 (by omega)
          (by simpa only [hletters] using Nat.le_refl 4))
        have := List.mem_range'.mp this
        omega
      have hfirstBound : first ≤ 4 := by
        have := hpattern.mem_iff.mp (List.mem_cons_self :
          first ∈ [first, second, third, last])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      have hlastBound : 1 ≤ last := by
        have := hpattern.mem_iff.mp (show last ∈ [first, second, third, last] by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      have h12 := hi 1 (by omega) (by omega)
      have h23 := hi 2 (by omega) (by omega)
      have h34 := hi 3 (by omega) (by omega)
      norm_num only at h12 h23 h34
      have hfirstNe : witness first ≠ 1 := by
        have : first = 2 ∨ first = 3 ∨ first = 4 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      have hlastNe : witness last ≠ width + 2 := by
        have : last = 1 ∨ last = 2 ∨ last = 3 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      have hwithoutFirst : ([first, second, third, last].map witness).Sublist
          (interior ++ [width + 2]) := List.Sublist.of_cons_of_ne hfirstNe hsub
      have hreverse : [witness last, witness third, witness second, witness first].Sublist
          ((width + 2) :: interior.reverse) := by simpa using hwithoutFirst.reverse
      have hselected : ([first, second, third, last].map witness).Sublist interior := by
        simpa using (List.Sublist.of_cons_of_ne hlastNe hreverse).reverse
      apply build [first, second, third, last] interior witness hpattern hletters
      · simpa only [List.length_cons, List.length_nil] using hi
      · exact hselected
    have subpattern (pattern : List ℕ)
        (hpattern : pattern ∈ [[3, 2, 4, 1], [2, 4, 1, 3], [4, 1, 3, 2]]) :
        Occurs pattern interior → Occurs [1, 3, 2] interior ∨
          Occurs [2, 1, 3] interior := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · rintro ⟨witness, hi, _, hsub, _⟩
        right
        apply build [2, 1, 3] interior (fun rank => witness (rank + 1)) (by decide) (by rfl)
        · intro rank hlo hhi
          have : rank = 1 ∨ rank = 2 := by simp at hhi; omega
          rcases this with rfl | rfl
          · exact hi 2 (by omega) (by decide)
          · exact hi 3 (by omega) (by decide)
        · exact ((by decide : [3, 2, 4].Sublist [3, 2, 4, 1]).map witness).trans hsub
      · rintro ⟨witness, hi, _, hsub, _⟩
        right
        apply build [2, 1, 3] interior witness (by decide) (by rfl)
        · intro rank hlo hhi
          exact hi rank hlo (by change rank < 4; simp at hhi; omega)
        · exact ((by decide : [2, 1, 3].Sublist [2, 4, 1, 3]).map witness).trans hsub
      · rintro ⟨witness, hi, _, hsub, _⟩
        left
        apply build [1, 3, 2] interior witness (by decide) (by rfl)
        · intro rank hlo hhi
          exact hi rank hlo (by change rank < 4; simp at hhi; omega)
        · exact ((by decide : [1, 3, 2].Sublist [4, 1, 3, 2]).map witness).trans hsub
    rw [unique_bad_cut_iff (width + 2) (by omega) [1, 3, 2, 4] word (by decide) wordPerm]
    constructor
    · rintro ⟨hocc, _, htail, hdrop⟩
      have h132 : ¬ Occurs [1, 3, 2] interior := by
        rintro ⟨witness, hi, hmem, hsub, _⟩
        let enlarged := fun rank : ℕ => if rank = 4 then width + 2 else witness rank
        apply htail
        apply build [1, 3, 2, 4] word.tail enlarged (by decide) (by rfl)
        · intro rank hlo hhi
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hhi; omega
          rcases this with rfl | rfl | rfl
          · simpa [enlarged] using hi 1 (by omega) (by decide)
          · simpa [enlarged] using hi 2 (by omega) (by decide)
          · simpa [enlarged] using (bounds _ (hmem 3 (by omega) (by decide))).2
        · simpa [word, enlarged] using hsub.append_right [width + 2]
      have h213 : ¬ Occurs [2, 1, 3] interior := by
        rintro ⟨witness, hi, hmem, hsub, _⟩
        let enlarged := fun rank : ℕ => if rank = 1 then 1 else witness (rank - 1)
        apply hdrop
        rw [wordDrop]
        apply build [1, 3, 2, 4] (1 :: interior) enlarged (by decide) (by rfl)
        · intro rank hlo hhi
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hhi; omega
          rcases this with rfl | rfl | rfl
          · simpa [enlarged] using (bounds _ (hmem 1 (by omega) (by decide))).1
          · simpa [enlarged] using hi 1 (by omega) (by decide)
          · simpa [enlarged] using hi 2 (by omega) (by decide)
        · simpa [enlarged] using hsub.cons_cons 1
      refine ⟨h132, h213, ?_⟩
      intro hinc
      obtain ⟨witness, hi, _, hsub, _⟩ := hocc
      have hreverse : [witness 4, witness 2, witness 3].Sublist
          ((width + 2) :: interior.reverse) := by simpa using hsub.of_cons_cons.reverse
      have hpair : [witness 3, witness 2].Sublist interior := by
        simpa using hreverse.of_cons_cons.reverse
      have := List.pairwise_iff_forall_sublist.mp hinc hpair
      have hlt : witness 2 < witness 3 := hi 2 (by omega) (by decide)
      omega
    · rintro ⟨h132, h213, hinc⟩
      obtain ⟨first, last, hpair, hnot⟩ :
          ∃ first last, [first, last].Sublist interior ∧ last ≤ first := by
        have := List.pairwise_iff_forall_sublist.not.mp hinc
        push Not at this
        exact this
      have hne := List.pairwise_iff_forall_sublist.mp
        (List.nodup_iff_pairwise_ne.mp hnodup) hpair
      let witness := fun rank : ℕ => if rank = 1 then 1 else
        if rank = 2 then last else if rank = 3 then first else width + 2
      have hocc : Occurs [1, 3, 2, 4] word := by
        apply build [1, 3, 2, 4] word witness (by decide) (by rfl)
        · intro rank hlo hhi
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp at hhi; omega
          rcases this with rfl | rfl | rfl
          · simpa [witness] using (bounds last (hpair.subset (by simp))).1
          · simp [witness]; omega
          · simpa [witness] using (bounds first (hpair.subset (by simp))).2
        · simpa [witness, word] using (hpair.append_right [width + 2]).cons_cons 1
      refine ⟨hocc, ?_, ?_, ?_⟩
      · intro shift hpositive hshift hocc
        have : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
        have heither : Occurs [1, 3, 2] interior ∨ Occurs [2, 1, 3] interior := by
          rcases this with rfl | rfl | rfl
          · exact subpattern [3, 2, 4, 1] (by simp)
              (nonendpoint_occurrence 3 2 4 1 (by decide) (by decide) (by decide) hocc)
          · exact subpattern [2, 4, 1, 3] (by simp)
              (nonendpoint_occurrence 2 4 1 3 (by decide) (by decide) (by decide) hocc)
          · exact subpattern [4, 1, 3, 2] (by simp)
              (nonendpoint_occurrence 4 1 3 2 (by decide) (by decide) (by decide) hocc)
        exact heither.elim h132 h213
      · rintro ⟨witness, hi, _, hsub, _⟩
        apply h132
        apply build [1, 3, 2] interior witness (by decide) (by rfl)
        · intro rank hlo hhi
          exact hi rank hlo (by change rank < 4; simp at hhi; omega)
        · have hr : [witness 4, witness 2, witness 3, witness 1].Sublist
              ((width + 2) :: interior.reverse) := by simpa [word] using hsub.reverse
          simpa using hr.of_cons_cons.reverse
      · rintro ⟨witness, hi, _, hsub, _⟩
        apply h213
        apply build [2, 1, 3] interior (fun rank => witness (rank + 1)) (by decide) (by rfl)
        · intro rank hlo hhi
          have : rank = 1 ∨ rank = 2 := by simp at hhi; omega
          rcases this with rfl | rfl
          · exact hi 2 (by omega) (by decide)
          · exact hi 3 (by omega) (by decide)
        · have hs : [witness 1, witness 3, witness 2, witness 4].Sublist (1 :: interior) := by
            simpa only [wordDrop, List.map_cons, List.map_nil] using hsub
          exact hs.of_cons_cons
  let parents := Fishburn.FishburnClassicalDefs.classicalAvoiders width
    [[1, 3, 2], [2, 1, 3]]
  let increasing := List.range' 1 width
  let domain := parents \ {increasing}
  let target := {word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
    word.head? = some 1 ∧ word.getLast? = some (width + 2) ∧
    ∀ cut < width + 2, Occurs [1, 3, 2, 4] (word.rotate cut) ↔ cut = 0}
  let emit := fun word : List ℕ => 1 :: word.map Nat.succ ++ [width + 2]
  have membership (word : List ℕ) : word ∈ domain ↔
      word.Perm (List.range' 1 width) ∧ ¬ Occurs [1, 3, 2] word ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ word.Pairwise (· < ·) := by
    have ordered (hp : word.Perm (List.range' 1 width)) :
        word = increasing ↔ word.Pairwise (· < ·) := by
      have hi : increasing.Pairwise (· < ·) := List.pairwise_lt_range' _ (by omega)
      exact ⟨fun heq => heq ▸ hi, fun hw => hp.eq_of_pairwise
        (by intro first last hfirst hlast; omega) hw hi⟩
    simp only [domain, parents, Set.mem_sdiff, Fishburn.FishburnClassicalDefs.classicalAvoiders,
      Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hp, h132, h213⟩, hne⟩
      exact ⟨hp, h132, h213, fun hi => hne ((ordered hp).mpr hi)⟩
    · rintro ⟨hp, h132, h213, hi⟩
      exact ⟨⟨hp, h132, h213⟩, fun heq => hi ((ordered hp).mp heq)⟩
  have shift (pattern word : List ℕ) (hpattern : pattern ∈ [[1, 3, 2], [2, 1, 3]]) :
      Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
    have hl : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
      (by intro first last hlt; omega)
  have emitMember (word : List ℕ) (hword : word ∈ domain) : emit word ∈ target := by
    obtain ⟨hp, h132, h213, hi⟩ := (membership word).mp hword
    have hr : (List.range' 1 width).map Nat.succ = List.range' 2 width := by
      simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
        funext value; omega, Nat.reduceAdd] using List.map_add_range' (a := 1) 1 width 1
    have hinner : (word.map Nat.succ).Perm (List.range' 2 width) := by
      simpa only [hr] using hp.map Nat.succ
    have htest := (criterion _ hinner).mpr ⟨fun hocc => h132 ((shift _ _ (by simp)).mp hocc),
      fun hocc => h213 ((shift _ _ (by simp)).mp hocc), fun hinc =>
        hi (List.pairwise_map.mp hinc |>.imp (by intro first last hlt; omega))⟩
    refine ⟨?_, by simp [emit], ?_, htest⟩
    · rw [rangeEndpoints]
      exact (hinner.append_right [width + 2]).cons 1
    · change ((1 :: word.map Nat.succ) ++ [width + 2]).getLast? = some (width + 2)
      rw [List.getLast?_append_cons]
      rfl
  have emitInjective : Function.Injective emit := by
    intro first second heq
    exact List.map_injective_iff.mpr Nat.succ_injective
      (List.append_cancel_right (List.cons.inj heq).2)
  have emitSurjective (word : List ℕ) (hword : word ∈ target) :
      ∃ parent ∈ domain, emit parent = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hword.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = 1 :: interior ++ [width + 2] := by
      cases front with
      | nil => have := hword.1.length_eq; simp [hlast] at this
      | cons head interior =>
        have : head = 1 := by simpa [hlast] using hword.2.1
        exact ⟨interior, by simpa [this] using hlast⟩
    have hinner : interior.Perm (List.range' 2 width) := by
      have hp := hword.1
      rw [hsplit, rangeEndpoints] at hp
      exact (List.perm_append_right_iff _).mp (List.Perm.cons_inv hp)
    let parent := interior.map (· - 1)
    have restore : parent.map Nat.succ = interior := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hvalue
      have := List.mem_range'.mp (hinner.mem_iff.mp hvalue)
      dsimp; omega
    have hparent : parent.Perm (List.range' 1 width) := by
      have hr : (List.range' 2 width).map (fun value : ℕ => value - 1) =
          List.range' 1 width := List.map_sub_range' (by omega : 1 ≤ 2) width
      have hmap := hinner.map (fun value : ℕ => value - 1)
      rw [hr] at hmap
      exact hmap
    have htest := (criterion interior hinner).mp (hsplit ▸ hword.2.2.2)
    refine ⟨parent, (membership parent).mpr ⟨hparent, ?_, ?_, ?_⟩,
      by simpa only [emit, restore] using hsplit.symm⟩
    · intro hocc
      exact htest.1 (restore ▸ (shift _ _ (by simp)).mpr hocc)
    · intro hocc
      exact htest.2.1 (restore ▸ (shift _ _ (by simp)).mpr hocc)
    · intro hi
      exact htest.2.2 (restore ▸ List.pairwise_map.mpr
        (hi.imp (by intro first last hlt; omega)))
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun word _ => emit word)
    emitMember (fun first second _ _ heq => emitInjective heq) (by
      intro word hword
      obtain ⟨parent, hparent, heq⟩ := emitSurjective word hword
      exact ⟨parent, hparent, heq⟩)
  have hincreasing : increasing ∈ parents := by
    have hi : increasing.Pairwise (· < ·) := List.pairwise_lt_range' _ (by omega)
    refine ⟨List.Perm.refl _, ?_⟩
    intro pattern hpattern
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl
    · rintro ⟨witness, hg, _, hsub, _⟩
      have hp := ((by decide : [3, 2].Sublist [1, 3, 2]).map witness).trans hsub
      have := List.pairwise_iff_forall_sublist.mp hi hp
      have hlt : witness 2 < witness 3 := hg 2 (by omega) (by decide)
      omega
    · rintro ⟨witness, hg, _, hsub, _⟩
      have hp := ((by decide : [2, 1].Sublist [2, 1, 3]).map witness).trans hsub
      have := List.pairwise_iff_forall_sublist.mp hi hp
      have hlt : witness 1 < witness 2 := hg 1 (by omega) (by decide)
      omega
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 width).permutations).subset
    intro word hword
    exact List.mem_permutations.mpr hword.1
  have hminus := Set.ncard_sdiff_singleton_add_one hincreasing finiteParents
  have henumeration := RotationAvoidanceFibonacci.skew_block_binary_count width (by omega)
  change target.ncard = _
  change domain.ncard + 1 = parents.ncard at hminus
  change parents.ncard = _ at henumeration
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEndpoints
