/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction
   mirror-E: none(waiver:binary-contraction-slices)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Consecutive endpoint contraction enumerates binary parents with an upper ascent. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLinear
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceBinaryContraction

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular

set_option maxHeartbeats 1200000 in
-- The circular witness relocation is elaborated uniformly for both pattern classes.
set_option maxRecDepth 4096 in
theorem consecutive_endpoint_contraction (size first : ℕ) (interior pattern : List ℕ)
    (hsize : 4 ≤ size)
    (hpattern : pattern = [2, 4, 1, 3] ∨ pattern = [1, 3, 4, 2])
    (hperm : (first :: interior ++ [first + 1]).Perm (List.range' 1 size)) :
    (∀ cut < size,
      Occurs pattern ((first :: interior ++ [first + 1]).rotate cut) ↔ cut = 0) ↔
      (∀ shift < 4, ¬ Occurs (pattern.rotate shift) (interior ++ [first + 1])) ∧
        Occurs pattern (first :: interior ++ [first + 1]) := by
  classical
  let word := first :: interior ++ [first + 1]
  let parent := interior ++ [first + 1]
  have hp : pattern.Perm [1, 2, 3, 4] := by
    rcases hpattern with rfl | rfl <;> decide
  have plen : pattern.length = 4 := by simpa using hp.length_eq
  have rotatedPerm (shift : ℕ) : (pattern.rotate shift).Perm [1, 2, 3, 4] :=
    (List.rotate_perm _ _).trans hp
  have lettersFour (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) : letters r = 4 := by
    simpa [letters] using hr.foldr_eq (f := max) 0
  have build (r container : List ℕ) (chosen : ℕ → ℕ)
      (hr : r.Perm [1, 2, 3, 4])
      (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1))
      (hs : (r.map chosen).Sublist container) : Occurs r container := by
    refine ⟨chosen, ?_, ?_, hs, by simp⟩
    · simpa only [lettersFour r hr] using hi
    · intro rank hlo hhi
      rw [lettersFour r hr] at hhi
      apply hs.subset
      apply List.mem_map_of_mem
      apply hr.mem_iff.mpr
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hh with rfl | rfl | rfl | rfl <;> simp
  have mono (r small large : List ℕ) (hs : small.Sublist large) :
      Occurs r small → Occurs r large := by
    rintro ⟨chosen, hi, hm, ht, _⟩
    exact ⟨chosen, hi, fun rank hlo hhi => hs.subset (hm rank hlo hhi),
      ht.trans hs, by simp⟩
  have wordNodup := hperm.nodup_iff.mpr List.nodup_range'
  have notFirst : first ∉ interior := fun hv =>
    (List.nodup_cons.mp wordNodup).1 (List.mem_append_left _ hv)
  have notLast : first + 1 ∉ first :: interior := by
    have hh := (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
    simp only [List.mem_cons]
    rintro (he | hv)
    · omega
    · exact hh (first + 1) hv (first + 1) (by simp) rfl
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [first + 1]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have relocate (r : List ℕ) (hr : r.Perm [1, 2, 3, 4])
      (ho : Occurs r (first :: interior)) :
      Occurs r parent ∨ Occurs (r.rotate 1) parent := by
    obtain ⟨chosen, hi, hm, hs, _⟩ := ho
    have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
      simpa only [lettersFour r hr] using hi
    have avoidLast (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ 4) :
        chosen rank ≠ first + 1 := fun he =>
      notLast (he ▸ hm rank hlo (by simpa only [lettersFour r hr] using hhi))
    let replace := fun value : ℕ => if value = first then first + 1 else value
    have replaceInterior : interior.map replace = interior := by
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hv
      simp only [replace, show value ≠ first from fun he => notFirst (he ▸ hv),
        if_false, id_eq]
    let lifted := fun rank : ℕ => replace (chosen rank)
    have liftedIncreasing : ∀ rank, 1 ≤ rank → rank < 4 →
        lifted rank < lifted (rank + 1) := by
      intro rank hlo hhi
      have hlt := hi' rank hlo hhi
      have hn := avoidLast (rank + 1) (by omega) (by omega)
      dsimp [lifted, replace]
      split_ifs <;> omega
    have hs' : (r.map lifted).Sublist ((first + 1) :: interior) := by
      have hh := hs.map replace
      simpa only [List.map_cons, replace, if_true, replaceInterior, List.map_map,
        Function.comp_def, lifted] using hh
    cases r with
    | nil => simp at hr
    | cons rank rest =>
      by_cases he : lifted rank = first + 1
      · have tailSub : (rest.map lifted).Sublist interior := by
          apply List.cons_sublist_cons.mp
          simpa only [List.map_cons, he] using hs'
        right
        apply build _ parent lifted ((List.rotate_perm _ _).trans hr) liftedIncreasing
        have rot : (rank :: rest).rotate 1 = rest ++ [rank] := by
          simpa using List.rotate_cons_succ rank rest 0
        rw [rot, List.map_append, List.map_singleton, he]
        exact tailSub.append (List.Sublist.refl [first + 1])
      · left
        apply build _ parent lifted hr liftedIncreasing
        exact (List.Sublist.of_cons_of_ne he hs').trans
          (List.sublist_append_left interior [first + 1])
  have criterion := unique_bad_cut_iff size hsize pattern word hp hperm
  constructor
  · intro hcuts
    have hc := criterion.mp hcuts
    refine ⟨?_, hc.1⟩
    intro shift hshift
    by_cases hz : shift = 0
    · subst shift
      simpa only [List.rotate_zero, word, List.cons_append, List.tail_cons] using hc.2.2.1
    · exact fun ho => hc.2.1 shift (by omega) hshift
        (mono _ _ word (List.sublist_cons_self first parent) ho)
  · rintro ⟨hparent, htarget⟩
    have parentNo (r : List ℕ) (shift : ℕ) (he : pattern.rotate shift = r) :
        ¬ Occurs r parent := by
      have hh : pattern.rotate (shift % 4) = pattern.rotate shift := by
        simpa only [plen] using (List.rotate_mod pattern shift)
      exact he ▸ hh ▸ hparent (shift % 4) (by omega)
    have dropNo (shift : ℕ) : ¬ Occurs (pattern.rotate shift) (first :: interior) := by
      intro ho
      rcases relocate _ (rotatedPerm shift) ho with hh | hh
      · exact parentNo _ shift rfl hh
      · rw [List.rotate_rotate] at hh
        exact parentNo _ (shift + 1) rfl hh
    have noOther (shift : ℕ) (hs : 0 < shift) (hb : shift < 4) :
        ¬ Occurs (pattern.rotate shift) word := by
      intro ho
      obtain ⟨chosen, hi, hm, selected, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa only [lettersFour _ (rotatedPerm shift)] using hi
      have h12 : chosen 1 < chosen 2 := by simpa using hi' 1 (by omega) (by omega)
      have h23 : chosen 2 < chosen 3 := by simpa using hi' 2 (by omega) (by omega)
      have h34 : chosen 3 < chosen 4 := by simpa using hi' 3 (by omega) (by omega)
      have firstUsed (head : ℕ) (tail : List ℕ)
          (he : (pattern.rotate shift).map chosen = head :: tail) : head = first := by
        by_contra hn
        have hh : (head :: tail).Sublist (first :: parent) := by
          simpa only [word, parent, List.cons_append, ← he] using selected
        exact parentNo _ shift rfl
          (build _ parent chosen (rotatedPerm shift) hi'
            (by simpa only [he] using List.Sublist.of_cons_of_ne hn hh))
      have lastUsed (last : ℕ) (initial : List ℕ)
          (he : (pattern.rotate shift).map chosen = initial ++ [last]) :
          last = first + 1 := by
        by_contra hn
        have hh : (last :: initial.reverse).Sublist
            ((first + 1) :: (first :: interior).reverse) := by
          simpa [he, word] using selected.reverse
        have hh := (List.Sublist.of_cons_of_ne hn hh).reverse
        apply dropNo shift
        apply build _ (first :: interior) chosen (rotatedPerm shift) hi'
        simpa [List.reverse_reverse, ← he] using hh
      rcases hpattern with rfl | rfl <;> interval_cases shift
      · have hf := firstUsed (chosen 4) [chosen 1, chosen 3, chosen 2] rfl
        have hl := lastUsed (chosen 2) [chosen 4, chosen 1, chosen 3] rfl
        omega
      · have hf := firstUsed (chosen 1) [chosen 3, chosen 2, chosen 4] rfl
        have hl := lastUsed (chosen 4) [chosen 1, chosen 3, chosen 2] rfl
        omega
      · have hf := firstUsed (chosen 3) [chosen 2, chosen 4, chosen 1] rfl
        have hl := lastUsed (chosen 1) [chosen 3, chosen 2, chosen 4] rfl
        omega
      · have hf := firstUsed (chosen 3) [chosen 4, chosen 2, chosen 1] rfl
        have hl := lastUsed (chosen 1) [chosen 3, chosen 4, chosen 2] rfl
        omega
      · have hf := firstUsed (chosen 4) [chosen 2, chosen 1, chosen 3] rfl
        have hl := lastUsed (chosen 3) [chosen 4, chosen 2, chosen 1] rfl
        omega
      · have hf := firstUsed (chosen 2) [chosen 1, chosen 3, chosen 4] rfl
        have hl := lastUsed (chosen 4) [chosen 2, chosen 1, chosen 3] rfl
        omega
    apply criterion.mpr
    refine ⟨htarget, noOther, ?_, ?_⟩
    · simpa only [word, parent, List.cons_append, List.tail_cons] using parentNo pattern 0 (by simp)
    · rw [dropWord]
      simpa only [List.rotate_zero] using dropNo 0


set_option maxHeartbeats 1800000 in
-- The endpoint bijection and its inverse are kept in this single counting proof.
set_option maxRecDepth 4096 in
theorem binary_least_consecutive_endpoint_count (width : ℕ) (hwidth : 3 ≤ width) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
      word.head? = some 1 ∧ word.getLast? = some 2 ∧
      ∀ cut < width + 2, Occurs [1, 3, 4, 2] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = 2 ^ width - width - 1 := by
  classical
  let patterns := [[2, 3, 1], [2, 1, 3, 4], [4, 2, 1, 3]]
  let parents := Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns
  let decreasing := (List.range' 1 width).reverse
  let domain := parents \ {decreasing}
  let target := {word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
    word.head? = some 1 ∧ word.getLast? = some 2 ∧
    ∀ cut < width + 2, Occurs [1, 3, 4, 2] (word.rotate cut) ↔ cut = 0}
  let emit := fun parent : List ℕ => 1 :: parent.map (fun value : ℕ => 2 + value) ++ [2]
  have membership (parent : List ℕ) : parent ∈ domain ↔
      parent.Perm (List.range' 1 width) ∧
        (∀ r ∈ patterns, ¬ Occurs r parent) ∧ ¬ parent.Pairwise (· > ·) := by
    have decreasingIff (hp : parent.Perm (List.range' 1 width)) :
        parent = decreasing ↔ parent.Pairwise (· > ·) := by
      have hd : decreasing.Pairwise (· > ·) :=
        List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
      exact ⟨fun he => he ▸ hd, fun hh =>
        (hp.trans (List.reverse_perm _).symm).eq_of_pairwise
          (by intro a b hab hba; omega) hh hd⟩
    simp only [domain, parents, Set.mem_sdiff, Set.mem_singleton_iff,
      Fishburn.FishburnClassicalDefs.classicalAvoiders, Set.mem_ofPred_eq]
    exact ⟨fun hh => ⟨hh.1.1, hh.1.2, fun hd => hh.2 ((decreasingIff hh.1.1).mpr hd)⟩,
      fun hh => ⟨⟨hh.1, hh.2.1⟩, fun he => hh.2.2 ((decreasingIff hh.1).mp he)⟩⟩
  have shift (r parent : List ℕ) (hl : letters r = r.length) (amount : ℕ) :
      Occurs r (parent.map (amount + ·)) ↔ Occurs r parent := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff r parent (amount + ·)
      (by intro a b hh; dsimp; omega)
  have upperPerm (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (parent.map (fun value : ℕ => 2 + value)).Perm (List.range' 3 width) := by
    simpa only [List.map_add_range', Nat.reduceAdd] using hp.map (fun value : ℕ => 2 + value)
  have rangeEndpoints : List.range' 1 (width + 2) = 1 :: 2 :: List.range' 3 width := by
    rw [show width + 2 = (width + 1) + 1 by omega, List.range'_succ,
      List.range'_succ]
  have emitPerm (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (emit parent).Perm (List.range' 1 (width + 2)) := by
    rw [rangeEndpoints]
    have hh := (upperPerm parent hp).append_right [2]
    have moved : (List.range' 3 width ++ [2]).Perm (2 :: List.range' 3 width) := by
      simpa using (List.perm_middle (a := 2) (l₁ := List.range' 3 width) (l₂ := []))
    exact (hh.trans moved).cons 1
  have parentCycles (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (∀ r ∈ patterns, ¬ Occurs r parent) ↔
        ∀ shift < 4,
          ¬ Occurs (([1, 3, 4, 2] : List ℕ).rotate shift)
            (parent.map (fun value : ℕ => 2 + value) ++ [2]) := by
    let tail := parent.map (fun value : ℕ => 1 + value)
    let circle := 1 :: tail
    have tailPerm : tail.Perm (List.range' 2 width) := by
      simpa only [List.map_add_range', Nat.reduceAdd] using hp.map (fun value : ℕ => 1 + value)
    have circlePerm : circle.Perm (List.range' 1 (width + 1)) := by
      rw [List.range'_succ]
      exact tailPerm.cons 1
    have shifted : (circle.rotate 1).map (fun value : ℕ => 1 + value) =
        parent.map (fun value : ℕ => 2 + value) ++ [2] := by
      simp only [circle, List.rotate_cons_succ, List.rotate_zero, List.map_append,
        List.map_singleton, tail, List.map_map]
      congr 2
      funext value
      simp only [Function.comp_def]; omega
    have goodRotation (p : List ℕ)
        (hg : p ∈ rotationAvoiders (width + 1) (width + 1) [1, 3, 4, 2]) (start : ℕ) :
        p.rotate start ∈ rotationAvoiders (width + 1) (width + 1) [1, 3, 4, 2] := by
      refine ⟨(List.rotate_perm _ _).trans hg.1, ?_⟩
      intro cut hcut ho
      rw [List.rotate_rotate, ← List.rotate_mod,
        show p.length = width + 1 by simpa using hg.1.length_eq] at ho
      exact hg.2 _ (Nat.mod_lt _ (by omega)) ho
    have reduction := (RotationAvoidanceCounts.minimum_rooted_reductions width tail
      circlePerm).2.1
    have shiftedPatterns : (∀ r ∈ patterns, ¬ Occurs r tail) ↔
        ∀ r ∈ patterns, ¬ Occurs r parent := by
      have hl (r : List ℕ) (hr : r ∈ patterns) : letters r = r.length := by
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> rfl
      simp only [tail]
      constructor <;> intro hh r hr
      · exact fun ho => hh r hr ((shift r parent (hl r hr) 1).mpr ho)
      · exact fun ho => hh r hr ((shift r parent (hl r hr) 1).mp ho)
    have reduction' : circle ∈ circularAvoiders (width + 1) [1, 3, 4, 2] ↔
        ∀ r ∈ patterns, ¬ Occurs r parent := by
      have hh : (¬ Occurs [2, 3, 1] tail ∧ ¬ Occurs [2, 1, 3, 4] tail ∧
          ¬ Occurs [4, 2, 1, 3] tail) ↔ ∀ r ∈ patterns, ¬ Occurs r tail := by
        simp [patterns]
      exact reduction.trans (hh.trans shiftedPatterns)
    have rotatedCriterion := all_cuts_iff_cycle_avoidance (width + 1) (by omega)
      [1, 3, 4, 2] (circle.rotate 1) (by decide)
      ((List.rotate_perm _ _).trans circlePerm)
    have hl (start : ℕ) : letters (([1, 3, 4, 2] : List ℕ).rotate start) =
        (([1, 3, 4, 2] : List ℕ).rotate start).length := by
      have hp := (List.rotate_perm ([1, 3, 4, 2] : List ℕ) start).trans
        (by decide : ([1, 3, 4, 2] : List ℕ).Perm [1, 2, 3, 4])
      have hh : letters (([1, 3, 4, 2] : List ℕ).rotate start) = 4 := by
        simpa [letters] using hp.foldr_eq (f := max) 0
      simpa using hh
    constructor
    · intro hh
      have hg := goodRotation circle ((reduction').mpr hh).1 1
      intro start hs ho
      have forbidden := rotatedCriterion.mp hg start hs
      rw [← shifted] at ho
      exact forbidden ((shift _ _ (hl start) 1).mp ho)
    · intro hh
      have hg := rotatedCriterion.mpr (by
        intro start hs ho
        apply hh start hs
        rw [← shifted]
        exact (shift _ _ (hl start) 1).mpr ho)
      have back := goodRotation (circle.rotate 1) hg width
      have hc : (circle.rotate 1).rotate width = circle := by
        rw [List.rotate_rotate, show 1 + width = circle.length by
          have hh : parent.length = width := by simpa using hp.length_eq
          simp [circle, tail, hh, Nat.add_comm], List.rotate_length]
      rw [hc] at back
      exact reduction'.mp ⟨back, by simp [circle]⟩
  have witness (interior : List ℕ) (low high : ℕ)
      (hs : [low, high].Sublist interior) (hlo : 2 < low) (hlt : low < high) :
      Occurs [1, 3, 4, 2] (1 :: interior ++ [2]) := by
    let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then 2
      else if rank = 3 then low else high
    refine ⟨chosen, ?_, ?_, ?_, by simp⟩
    · intro rank hlo' hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
        change rank < 4 at hhi; omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · intro rank hlo' hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        change rank ≤ 4 at hhi; omega
      have hlow := hs.subset (by simp : low ∈ [low, high])
      have hhigh := hs.subset (by simp : high ∈ [low, high])
      rcases hh with rfl | rfl | rfl | rfl <;> simp [chosen, hlow, hhigh]
    · simpa [chosen] using (hs.append (List.Sublist.refl [2])).cons_cons 1
  have emitMember (parent : List ℕ) (hparent : parent ∈ domain) : emit parent ∈ target := by
    obtain ⟨hp, ha, hd⟩ := (membership parent).mp hparent
    have hn := hp.nodup_iff.mpr List.nodup_range'
    obtain ⟨low, high, hpair, hnot⟩ : ∃ low high, [low, high].Sublist parent ∧ ¬ low > high := by
      simpa only [List.pairwise_iff_forall_sublist, not_forall, Classical.not_imp,
        exists_prop] using hd
    have hne : low ≠ high := by
      simpa using (List.nodup_cons.mp (hn.sublist hpair)).1
    have hb := List.mem_range'_1.mp (hp.mem_iff.mp (hpair.subset (by simp : low ∈ _)))
    have ht := witness (parent.map (fun value : ℕ => 2 + value)) (2 + low) (2 + high)
      (by simpa using hpair.map (fun value : ℕ => 2 + value)) (by omega) (by omega)
    have hc := (consecutive_endpoint_contraction (width + 2) 1
      (parent.map (fun value : ℕ => 2 + value))
      [1, 3, 4, 2] (by omega) (Or.inr rfl) (emitPerm parent hp)).mpr
        ⟨(parentCycles parent hp).mp ha, ht⟩
    refine ⟨emitPerm parent hp, by simp [emit], ?_, hc⟩
    change ((1 :: parent.map (fun value : ℕ => 2 + value)) ++ [2]).getLast? = some 2
    rw [List.getLast?_append_cons]; rfl
  have emitInjective : Function.Injective emit := by
    intro left right he
    have hh := congrArg
      (fun word : List ℕ => word.tail.dropLast.map (fun value : ℕ => value - 2)) he
    simpa [emit, List.cons_append, List.tail_cons, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil, List.map_map,
      Function.comp_def, Nat.add_sub_cancel_left] using hh
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ parent ∈ domain, emit parent = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = 1 :: interior ++ [2] := by
      cases front with
      | nil => have hh := hw.1.length_eq; simp [hlast] at hh
      | cons head interior =>
        have hh : head = 1 := by simpa [hlast] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    have interiorPerm : interior.Perm (List.range' 3 width) := by
      have hh := hsplit ▸ hw.1
      have moved : (2 :: List.range' 3 width).Perm (List.range' 3 width ++ [2]) := by
        simpa using (List.perm_middle (a := 2) (l₁ := List.range' 3 width) (l₂ := [])).symm
      rw [rangeEndpoints] at hh
      exact (List.perm_append_right_iff _).mp ((List.Perm.cons_inv hh).trans moved)
    let parent := interior.map (fun value : ℕ => value - 2)
    have parentPerm : parent.Perm (List.range' 1 width) := by
      simpa only [parent, List.map_sub_range' (by omega : 2 ≤ 3), Nat.reduceSub]
        using interiorPerm.map (fun value : ℕ => value - 2)
    have restore : parent.map (fun value : ℕ => 2 + value) = interior := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range'_1.mp (interiorPerm.mem_iff.mp hv)
      dsimp; omega
    have hc := (consecutive_endpoint_contraction (width + 2) 1 interior [1, 3, 4, 2]
      (by omega) (Or.inr rfl) (hsplit ▸ hw.1)).mp (hsplit ▸ hw.2.2.2)
    have ha := (parentCycles parent parentPerm).mpr (restore.symm ▸ hc.1)
    have notDecreasing : ¬ parent.Pairwise (· > ·) := by
      intro hd
      have hi : interior.Pairwise (· > ·) := by
        rw [← restore, List.pairwise_map]
        exact hd.imp (by intro a b hh; omega)
      obtain ⟨chosen, hinc, _, hs, _⟩ := hc.2
      have h34 : chosen 3 < chosen 4 := by simpa using hinc 3 (by omega) (by decide)
      have pair : [chosen 3, chosen 4].Sublist interior := by
        have hs' : [chosen 3, chosen 4, chosen 2].Sublist (interior ++ [2]) :=
          hs.of_cons_cons
        have hs' : [chosen 2, chosen 4, chosen 3].Sublist (2 :: interior.reverse) := by
          simpa using hs'.reverse
        have pair' := hs'.of_cons_cons
        simpa using pair'.reverse
      have hh := List.pairwise_iff_forall_sublist.mp hi pair
      omega
    exact ⟨parent, (membership parent).mpr ⟨parentPerm, ha, notDecreasing⟩,
      by simpa only [emit, restore] using hsplit.symm⟩
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun parent _ => emit parent)
    emitMember (fun a b _ _ he => emitInjective he) (by
      intro word hw
      obtain ⟨parent, hp, he⟩ := emitSurjective word hw
      exact ⟨parent, hp, he⟩)
  have decreasingMember : decreasing ∈ parents := by
    have hd : decreasing.Pairwise (· > ·) :=
      List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
    refine ⟨List.reverse_perm _, ?_⟩
    intro r hr
    simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rintro ⟨chosen, hi, _, hs, _⟩
      have pair := ((by decide : ([2, 3] : List ℕ).Sublist [2, 3, 1]).map chosen).trans hs
      have hh := List.pairwise_iff_forall_sublist.mp hd pair
      have ht : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
      omega
    · rintro ⟨chosen, hi, _, hs, _⟩
      have pair := ((by decide : ([1, 3] : List ℕ).Sublist [2, 1, 3, 4]).map chosen).trans hs
      have hh := List.pairwise_iff_forall_sublist.mp hd pair
      have h12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
      omega
    · rintro ⟨chosen, hi, _, hs, _⟩
      have pair := ((by decide : ([1, 3] : List ℕ).Sublist [4, 2, 1, 3]).map chosen).trans hs
      have hh := List.pairwise_iff_forall_sublist.mp hd pair
      have h12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
      omega
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 width).permutations).subset
    intro parent hp
    exact List.mem_permutations.mpr hp.1
  have rejected := Set.ncard_sdiff_singleton_add_one decreasingMember finiteParents
  have count := RotationAvoidanceLinear.binary_separator_count width
  change domain.ncard + 1 = parents.ncard at rejected
  change parents.ncard = _ at count
  change target.ncard = _
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceBinaryContraction
