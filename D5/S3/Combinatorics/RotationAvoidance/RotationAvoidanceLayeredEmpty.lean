/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty
   mirror-E: none(waiver:layered-zero-lower-endpoint-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Splitting the decreasing middle around an upper parent counts zero-lower 1423 slices. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayered
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredEmpty

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 4096 in
theorem layered_empty_lower_endpoint_count (size last : ℕ)
    (hgap : 2 < last) (hlast : last < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some 1 ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = (last - 2) * Nat.fib (2 * (size - last) - 1) := by
  classical
  have construction (split : ℕ) (upper : List ℕ) (hsplit : split < last - 2)
      (hupper : upper.Perm (List.range' (last + 1) (size - last)))
      (hupper312 : ¬ Occurs [3, 1, 2] upper)
      (hupper2314 : ¬ Occurs [2, 3, 1, 4] upper) :
      let before := (List.range' (last - split) split).reverse
      let after := (List.range' 2 (last - 2 - split)).reverse
      let word := 1 :: before ++ upper ++ after ++ [last]
      word.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0 := by
    let before := (List.range' (last - split) split).reverse
    let after := (List.range' 2 (last - 2 - split)).reverse
    let word := 1 :: before ++ upper ++ after ++ [last]
    let bucket := fun value : ℕ => if value ≤ 1 then 0 else if value < last - split then 1
      else if value < last then 2 else if value = last then 3 else 4
    have bucketBound (value : ℕ) : bucket value < 5 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 5)
    let slot : Fin 5 → ℕ := fun shade => if shade = 0 then 0 else if shade = 1 then 3
      else if shade = 2 then 1 else if shade = 3 then 4 else 2
    let position := fun value : ℕ => slot (color value)
    have beforeBounds (value : ℕ) (hv : value ∈ before) :
        last - split ≤ value ∧ value < last := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
    have afterBounds (value : ℕ) (hv : value ∈ after) :
        1 < value ∧ value < last - split := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
    have upperBounds (value : ℕ) (hv : value ∈ upper) : last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hupper.mem_iff.mp hv); omega
    have firstColor : color 1 = 0 := by simp [color, bucket]
    have lastColor : color last = 3 := by
      simp [color, bucket, show ¬ last ≤ 1 by omega,
        show ¬ last < last - split by omega]
    have beforeColor (value : ℕ) (hv : value ∈ before) : color value = 2 := by
      have hh := beforeBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega,
        show ¬ value < last - split by omega, hh.2]
    have afterColor (value : ℕ) (hv : value ∈ after) : color value = 1 := by
      have hh := afterBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega, hh.2]
    have upperColor (value : ℕ) (hv : value ∈ upper) : color value = 4 := by
      have hh := upperBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega,
        show ¬ value < last - split by omega, show ¬ value < last by omega,
        show value ≠ last by omega]
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have wordNodup : word.Nodup := by
      have hbu : (before ++ upper).Nodup := List.nodup_append.mpr
        ⟨List.nodup_reverse.mpr List.nodup_range', hupper.nodup_iff.mpr List.nodup_range', by
          intro left hl right hr he
          have := beforeBounds left hl; have := upperBounds right hr; omega⟩
      have hba : (before ++ upper ++ after).Nodup := List.nodup_append.mpr
        ⟨hbu, List.nodup_reverse.mpr List.nodup_range', by
          intro left hl right hr he
          have := afterBounds right hr
          rcases List.mem_append.mp hl with hl | hl
          · have := beforeBounds left hl; omega
          · have := upperBounds left hl; omega⟩
      have hbal : (before ++ upper ++ after ++ [last]).Nodup := List.nodup_append.mpr
        ⟨hba, by simp, by
          intro left hl right hr he
          have hr : right = last := by simpa using hr
          rcases List.mem_append.mp hl with hl | hl
          · rcases List.mem_append.mp hl with hl | hl
            · have := beforeBounds left hl; omega
            · have := upperBounds left hl; omega
          · have := afterBounds left hl; omega⟩
      apply List.nodup_cons.mpr ⟨?_, hbal⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro (((hv | hv) | hv) | he)
      · have := beforeBounds 1 hv; omega
      · have := upperBounds 1 hv; omega
      · have := afterBounds 1 hv; omega
      · omega
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      simp only [word, before, after, List.cons_append, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, hupper.mem_iff, List.mem_reverse, List.mem_range'_1]
      omega
    have orderedWord : word.Pairwise (fun left right => position left ≤ position right) := by
      have beforeOrdered : before.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, beforeColor left hl, beforeColor right hr])
      have afterOrdered : after.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, afterColor left hl, afterColor right hr])
      have upperOrdered : upper.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, upperColor left hl, upperColor right hr])
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact beforeOrdered
        | exact afterOrdered
        | exact upperOrdered
        | (intros; simp [position, firstColor, lastColor, beforeColor, afterColor,
            upperColor, slot, *])
    have firstEndpoint (value : ℕ) (hv : value ∈ word) (hc : color value = 0) : value = 1 := by
      have he := congrArg Fin.val hc
      have hb := List.mem_range'_1.mp (wordPerm.mem_iff.mp hv)
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 3) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have filtered (shade : Fin 5) :
        word.filter (fun value => decide (color value = shade)) =
          (if shade = 0 then [1] else []) ++ (if shade = 2 then before else []) ++
          (if shade = 4 then upper else []) ++ (if shade = 1 then after else []) ++
          (if shade = 3 then [last] else []) := by
      have block (values : List ℕ) (paint : Fin 5)
          (hc : ∀ value ∈ values, color value = paint) :
          values.filter (fun value => decide (color value = shade)) =
            if shade = paint then values else [] := by
        split_ifs with he
        · exact List.filter_eq_self.mpr (by intro value hv; simp [hc value hv, he])
        · exact List.filter_eq_nil_iff.mpr (by intro value hv; simp [hc value hv, Ne.symm he])
      simp only [word, List.cons_append, List.filter_append, List.filter_cons,
        List.filter_singleton, firstColor, lastColor]
      rw [block before 2 beforeColor, block upper 4 upperColor, block after 1 afterColor]
      fin_cases shade <;> simp
    have finiteProfiles : ∀ low second third high : Fin 5,
        low ≤ second → second ≤ third → third ≤ high →
        (low = second → low ≠ 0 ∧ low ≠ 3) →
        (second = third → second ≠ 0 ∧ second ≠ 3) →
        (third = high → third ≠ 0 ∧ third ≠ 3) →
        ((slot low ≤ slot high ∧ slot high ≤ slot second ∧ slot second ≤ slot third ∧
            ¬ (second = third ∧ (second = 1 ∨ second = 2))) →
          (second = 4 ∧ third = 4 ∧ high = 4) ∨ (low = 0 ∧ third = 3)) ∧
        ((slot high ≤ slot second ∧ slot second ≤ slot third ∧ slot third ≤ slot low ∧
            ¬ (second = third ∧ (second = 1 ∨ second = 2))) →
          (second = 4 ∧ third = 4 ∧ high = 4)) ∧
        ((slot second ≤ slot third ∧ slot third ≤ slot low ∧ slot low ≤ slot high ∧
            ¬ (second = third ∧ (second = 1 ∨ second = 2))) →
          (low = 4 ∧ second = 4 ∧ third = 4 ∧ high = 4)) ∧
        ((slot third ≤ slot low ∧ slot low ≤ slot high ∧ slot high ≤ slot second ∧
            ¬ (low = high ∧ (low = 1 ∨ low = 2))) →
          (low = 4 ∧ second = 4 ∧ third = 4 ∧ high = 4)) := by decide
    have build (pattern container : List ℕ) (width : ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
        (hi : ∀ rank, 1 ≤ rank → rank < width → chosen rank < chosen (rank + 1))
        (hs : (pattern.map chosen).Sublist container) : Occurs pattern container := by
      refine ⟨chosen, ?_, ?_, hs, by simp⟩
      · simpa only [hl] using hi
      · intro rank hlo hhi
        rw [hl] at hhi
        exact hs.subset (List.mem_map_of_mem
          (hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))))
    have profile (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (hp : pattern.Perm [1, 2, 3, 4])
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) := by
      have inWord (rank : ℕ) (hr : rank ∈ pattern) : chosen rank ∈ word :=
        (hs.trans hcontainer).subset (List.mem_map_of_mem hr)
      have singleton (left right : ℕ) (hl : left ∈ pattern) (hr : right ∈ pattern)
          (hh : chosen left < chosen right) :
          color (chosen left) = color (chosen right) →
            color (chosen left) ≠ 0 ∧ color (chosen left) ≠ 3 := by
        intro he
        constructor
        · intro hc
          have := firstEndpoint _ (inWord _ hl) hc
          have := firstEndpoint _ (inWord _ hr) (he.symm.trans hc)
          omega
        · intro hc
          have := lastEndpoint _ hc
          have := lastEndpoint _ (he.symm.trans hc)
          omega
      exact finiteProfiles (color (chosen 1)) (color (chosen 2))
        (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
        (singleton 1 2 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 1 (by omega) (by omega)))
        (singleton 2 3 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 2 (by omega) (by omega)))
        (singleton 3 4 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 3 (by omega) (by omega)))
    have edge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) :
        position (chosen left) ≤ position (chosen right) :=
      List.pairwise_iff_forall_sublist.mp orderedWord
        ((hr.map chosen).trans (hs.trans hcontainer))
    have project (pattern container ranks block : List ℕ) (chosen : ℕ → ℕ) (shade : Fin 5)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (hr : ranks.Sublist pattern) (hc : ∀ rank ∈ ranks, color (chosen rank) = shade)
        (hf : word.filter (fun value => decide (color value = shade)) = block) :
        (ranks.map chosen).Sublist block := by
      have hh := ((hr.map chosen).trans (hs.trans hcontainer)).filter
        (fun value => decide (color value = shade))
      have he : (ranks.map chosen).filter (fun value => decide (color value = shade)) =
          ranks.map chosen := List.filter_eq_self.mpr (by
        intro value hv
        obtain ⟨rank, hr, rfl⟩ := List.mem_map.mp hv
        simp [hc rank hr])
      rwa [he, hf] at hh
    have noMiddleAscent (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) (hh : chosen left < chosen right) :
        ¬ (color (chosen left) = color (chosen right) ∧
          (color (chosen left) = 1 ∨ color (chosen left) = 2)) := by
      rintro ⟨he, hc | hc⟩
      · have ht := project _ _ [left, right] after chosen 1 hcontainer hs hr
          (by intro rank hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl; exact hc; exact he.symm.trans hc)
          (by simpa using filtered 1)
        have hd := List.pairwise_iff_forall_sublist.mp
          (by simpa only [after, List.pairwise_reverse] using
            (List.pairwise_lt_range' (s := 2) (n := last - 2 - split)) :
            after.Pairwise (· > ·)) ht
        omega
      · have ht := project _ _ [left, right] before chosen 2 hcontainer hs hr
          (by intro rank hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl; exact hc; exact he.symm.trans hc)
          (by simpa using filtered 2)
        have hd := List.pairwise_iff_forall_sublist.mp
          (by simpa only [before, List.pairwise_reverse] using
            (List.pairwise_lt_range' (s := last - split) (n := split)) :
            before.Pairwise (· > ·)) ht
        omega
    have triple (block pattern : List ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm [1, 2, 3]) (hi : chosen 1 < chosen 2 ∧ chosen 2 < chosen 3)
        (hs : (pattern.map chosen).Sublist block) : Occurs pattern block := by
      have hl : letters pattern = 3 := by
        simpa [letters] using hp.foldr_eq (f := max) 0
      apply build _ _ 3 chosen hp hl _ hs
      intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 := by omega
      rcases hh with rfl | rfl
      · exact hi.1
      · exact hi.2
    have forcedEndpoints (container : List ℕ) (hcontainer : container.Sublist word)
        (ho : Occurs [1, 4, 2, 3] container) : 1 ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := hi
      have shapes := (profile _ _ chosen hcontainer hs (by decide) hi').1
        ⟨edge _ _ _ hcontainer hs 1 4 (by decide), edge _ _ _ hcontainer hs 4 2 (by decide),
          edge _ _ _ hcontainer hs 2 3 (by decide),
          noMiddleAscent _ _ _ hcontainer hs 2 3 (by decide)
            (hi' 2 (by omega) (by omega))⟩
      rcases shapes with hu | he
      · exfalso
        apply hupper312
        apply triple upper [3, 1, 2] (fun rank => chosen (rank + 1)) (by decide)
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
        simpa using project _ _ [4, 2, 3] upper chosen 4 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> tauto) (by simpa using filtered 4)
      · constructor
        · rw [← firstEndpoint _ ((hs.trans hcontainer).subset (by simp)) he.1]
          exact hs.subset (by simp)
        · rw [← lastEndpoint _ he.2]; exact hs.subset (by simp)
    have noRotated (rotation : ℕ) (hpositive : 0 < rotation) (hrotation : rotation < 4) :
        ¬ Occurs ([1, 4, 2, 3].rotate rotation) word := by
      rintro ⟨chosen, hi, _, hs, _⟩
      have hp : ([1, 4, 2, 3] : List ℕ).rotate rotation |>.Perm [1, 2, 3, 4] :=
        (List.rotate_perm _ _).trans (by decide)
      have hl : letters (([1, 4, 2, 3] : List ℕ).rotate rotation) = 4 := by
        simpa [letters] using hp.foldr_eq (f := max) 0
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa only [hl] using hi
      have shapes := (profile _ _ chosen (List.Sublist.refl word) hs hp hi').2
      have ascending := noMiddleAscent _ _ chosen (List.Sublist.refl word) hs 2 3
      have ascendingValue := hi' 2 (by omega) (by omega)
      interval_cases rotation
      · have hu := shapes.1 ⟨edge _ _ _ (List.Sublist.refl word) hs 4 2 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 2 3 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          ascending (by decide) ascendingValue⟩
        apply hupper312
        apply triple upper [3, 1, 2] (fun rank => chosen (rank + 1)) (by decide)
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
        simpa using project _ _ [4, 2, 3] upper chosen 4 (List.Sublist.refl word) hs
          (by decide) (by
            intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> tauto) (by simpa using filtered 4)
      · have hu := shapes.2.1 ⟨edge _ _ _ (List.Sublist.refl word) hs 2 3 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 1 4 (by decide),
          ascending (by decide) ascendingValue⟩
        apply hupper2314
        exact build _ upper 4 chosen (by decide) rfl hi'
          (project _ _ [2, 3, 1, 4] upper chosen 4 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl | rfl <;> tauto) (by simpa using filtered 4))
      · have hu := shapes.2.2 ⟨edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 1 4 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 4 2 (by decide),
          noMiddleAscent _ _ _ (List.Sublist.refl word) hs 1 4 (by decide) (by
            have h12 := hi' 1 (by omega) (by omega)
            have h23 := hi' 2 (by omega) (by omega)
            have h34 := hi' 3 (by omega) (by omega)
            simp only [Nat.reduceAdd] at h12 h23 h34; omega)⟩
        apply hupper312
        apply triple upper [3, 1, 2] chosen (by decide)
          ⟨hi' 1 (by omega) (by omega), hi' 2 (by omega) (by omega)⟩
        exact project _ _ [3, 1, 2] upper chosen 4 (List.Sublist.refl word) hs
          (by decide) (by
            intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> tauto) (by simpa using filtered 4)
    have targetOccurrence : Occurs [1, 4, 2, 3] word := by
      have highMem : last + 1 ∈ upper := hupper.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega))
      have lowMem : 2 ∈ after := List.mem_reverse.mpr (List.mem_range'_1.mpr (by omega))
      let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then 2
        else if rank = 3 then last else last + 1
      apply build _ word 4 chosen (by decide) rfl
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · have hs : [last + 1, 2].Sublist (before ++ upper ++ after) :=
          (((List.singleton_sublist.mpr highMem).trans
            (List.sublist_append_right before upper)).append
              (List.singleton_sublist.mpr lowMem))
        simpa [word, chosen] using (hs.append_right [last]).cons_cons 1
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [1, 4, 2, 3] word
      (by decide) wordPerm).mpr ⟨targetOccurrence, noRotated, ?_, ?_⟩⟩
    · intro ho
      exact (List.nodup_cons.mp wordNodup).1
        (forcedEndpoints word.tail (List.tail_sublist word) ho).1
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist word) ho).2
      have he : word.dropLast = 1 :: (before ++ upper ++ after) := by
        change ((1 :: (before ++ upper ++ after)) ++ [last]).dropLast = _
        rw [List.dropLast_append_cons]; simp
      rw [he] at hh
      simp only [List.mem_cons, List.mem_append] at hh
      rcases hh with he | ((hv | hv) | hv)
      · omega
      · have := beforeBounds last hv; omega
      · have := upperBounds last hv; omega
      · have := afterBounds last hv; omega
  let parents := Fishburn.FishburnClassicalDefs.classicalAvoiders (size - last)
    [[3, 1, 2], [2, 3, 1, 4]]
  let splits : Set ℕ := ↑(Finset.range (last - 2))
  let domain := splits ×ˢ parents
  let target := {word : List ℕ | word.Perm (List.range' 1 size) ∧
    word.head? = some 1 ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0}
  let emit := fun pair : ℕ × List ℕ => 1 ::
    (List.range' (last - pair.1) pair.1).reverse ++ pair.2.map (last + ·) ++
      (List.range' 2 (last - 2 - pair.1)).reverse ++ [last]
  let extract := fun word : List ℕ =>
    ((word.takeWhile (fun value => decide (value < last))).length - 1,
      (word.filter (fun value => decide (last < value))).map (fun value => value - last))
  have membership (word : List ℕ) : word ∈ parents ↔
      word.Perm (List.range' 1 (size - last)) ∧
        ¬ Occurs [3, 1, 2] word ∧ ¬ Occurs [2, 3, 1, 4] word := by
    simp [parents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have shift (pattern word : List ℕ) (hl : letters pattern = pattern.length) :
      Occurs pattern (word.map (last + ·)) ↔ Occurs pattern word := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (last + ·)
      (by intro low high hh; dsimp; omega)
  have recover (before upper after : List ℕ)
      (hb : ∀ value ∈ before, value < last)
      (hu : ∀ value ∈ upper, last < value)
      (ha : ∀ value ∈ after, value < last) (hne : upper ≠ []) :
      extract (1 :: before ++ upper ++ after ++ [last]) =
        (before.length, upper.map (fun value => value - last)) := by
    have takePrefix (left : List ℕ) (hl : ∀ value ∈ left, value < last) :
        (left ++ upper ++ after ++ [last]).takeWhile (fun value => decide (value < last)) =
          left := by
      induction left with
      | nil =>
        cases upper with
        | nil => exact (hne rfl).elim
        | cons head tail =>
          have hh := hu head (by simp)
          simp [show ¬ head < last by omega]
      | cons head tail ih =>
        have hh := hl head (by simp)
        have ht := ih (by intro value hv; exact hl value (by simp [hv]))
        simpa [hh] using congrArg (head :: ·) ht
    have hbFilter : before.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv; have := hb value hv; simp only [decide_eq_true_eq]; omega)
    have haFilter : after.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv; have := ha value hv; simp only [decide_eq_true_eq]; omega)
    have huFilter : upper.filter (fun value => decide (last < value)) = upper :=
      List.filter_eq_self.mpr (by intro value hv; simp [hu value hv])
    have ht := takePrefix (1 :: before) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · omega
      · exact hb value hv)
    have ht' : (1 :: before ++ upper ++ after ++ [last]).takeWhile
        (fun value => decide (value < last)) = 1 :: before := by
      simpa only [List.cons_append, List.append_assoc] using ht
    apply Prod.ext
    · change _ - 1 = before.length
      rw [ht']; simp
    · simp [extract, List.filter_append, hbFilter, haFilter, huFilter,
        show ¬ last < 1 by omega]
  have emitMember (pair : ℕ × List ℕ) (hp : pair ∈ domain) : emit pair ∈ target := by
    have hs : pair.1 < last - 2 := by simpa [splits] using hp.1
    have pu := (membership _).mp hp.2
    have upperPerm : (pair.2.map (last + ·)).Perm
        (List.range' (last + 1) (size - last)) := by
      simpa only [List.map_add_range', Nat.add_comm] using pu.1.map (last + ·)
    have hc := construction pair.1 (pair.2.map (last + ·)) hs upperPerm
      (by intro ho; exact pu.2.1 ((shift _ _ rfl).mp ho))
      (by intro ho; exact pu.2.2 ((shift _ _ rfl).mp ho))
    refine ⟨hc.1, ?_, ?_, hc.2⟩
    · simp [emit]
    · dsimp only [emit]
      rw [List.getLast?_append_cons]; rfl
  have decode (pair : ℕ × List ℕ) (hp : pair ∈ domain) : extract (emit pair) = pair := by
    have hs : pair.1 < last - 2 := by simpa [splits] using hp.1
    have pu := (membership _).mp hp.2
    have upperBounds (value : ℕ) (hv : value ∈ pair.2.map (last + ·)) : last < value := by
      obtain ⟨parent, hm, rfl⟩ := List.mem_map.mp hv
      have hh := List.mem_range'_1.mp (pu.1.mem_iff.mp hm); omega
    have hn : pair.2.map (last + ·) ≠ [] := by
      intro he
      have hl := congrArg List.length he
      have hp := pu.1.length_eq
      simp only [List.length_map, List.length_nil, List.length_range'] at hl hp
      omega
    have restore : (pair.2.map (last + ·)).map (fun value => value - last) = pair.2 := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id pair.2]
      apply List.map_congr_left
      intro value hv
      dsimp; omega
    have hh := recover (List.range' (last - pair.1) pair.1).reverse
      (pair.2.map (last + ·)) (List.range' 2 (last - 2 - pair.1)).reverse
      (by intro value hv; have := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega)
      upperBounds
      (by intro value hv; have := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega) hn
    simpa [emit, restore] using hh
  have surjective (word : List ℕ) (hw : word ∈ target) :
      ∃ pair ∈ domain, emit pair = word := by
    obtain ⟨interior, hword⟩ : ∃ interior, word = 1 :: interior ++ [last] := by
      cases word with
      | nil => simp [target] at hw
      | cons head tail =>
        have he : head = 1 := by simpa using hw.2.1
        subst head
        have hlen : (1 :: tail).length = size := by simpa using hw.1.length_eq
        have htail : tail ≠ [] := by intro he; simp [he] at hlen; omega
        have ht : tail.getLast? = some last := by
          cases tail with
          | nil => exact (htail rfl).elim
          | cons head rest => simpa only [List.getLast?_cons_cons] using hw.2.2.1
        have hh : tail = tail.dropLast ++ [last] :=
          (List.dropLast_append_getLast? last (by simp [ht])).symm
        exact ⟨tail.dropLast, by simpa only [List.cons_append] using congrArg (1 :: ·) hh⟩
    obtain ⟨_, _, before, upper, lower, after, he, upperPerm, lowerPerm, middlePerm,
        beforeSorted, afterSorted, above, afterNotNil, _, hu312, hu2314, _, _⟩ :=
      RotationAvoidanceLayered.layered_endpoint_normal_form size 1 last interior
        (by omega) (by omega) (by omega) (hword ▸ hw.1)
        (by simpa only [← hword] using hw.2.2.2)
    have lowerEmpty : lower = [] := List.Perm.eq_nil (by simpa using lowerPerm)
    have middleSorted : (before ++ after).Pairwise (· > ·) :=
      List.pairwise_append.mpr ⟨beforeSorted, afterSorted, above⟩
    have middleEq : before ++ after = (List.range' 2 (last - 2)).reverse :=
      (middlePerm.trans (List.reverse_perm _).symm).eq_of_pairwise
        (by intro left right hl hr; omega) middleSorted
        (by simpa only [List.pairwise_reverse] using
          (List.pairwise_lt_range' (s := 2) (n := last - 2)))
    let split := before.length
    have hs : split < last - 2 := by
      have hh := middlePerm.length_eq
      have ha : 0 < after.length := List.length_pos_iff.mpr afterNotNil
      simp only [List.length_append, List.length_range'] at hh
      dsimp [split]; omega
    have totalEq : (List.range' 2 (last - 2)).reverse =
        (List.range' (last - split) split).reverse ++
          (List.range' 2 (last - 2 - split)).reverse := by
      have hh := List.range'_append_1 (s := 2) (m := last - 2 - split) (n := split)
      have hsum : last - 2 - split + split = last - 2 := by omega
      have hstart : 2 + (last - 2 - split) = last - split := by omega
      rw [hsum, hstart] at hh
      simpa only [List.reverse_append] using (congrArg List.reverse hh).symm
    have beforeEq : before = (List.range' (last - split) split).reverse := by
      have hh := congrArg (List.take split) (middleEq.trans totalEq)
      have ht : List.take split ((List.range' (last - split) split).reverse ++
          (List.range' 2 (last - 2 - split)).reverse) =
            (List.range' (last - split) split).reverse := by
        simpa only [List.length_reverse, List.length_range'] using
          (List.take_left (l₁ := (List.range' (last - split) split).reverse)
            (l₂ := (List.range' 2 (last - 2 - split)).reverse))
      simpa only [split, List.take_left] using (hh.trans ht)
    have afterEq : after = (List.range' 2 (last - 2 - split)).reverse := by
      have hh := congrArg (List.drop split) (middleEq.trans totalEq)
      have ht : List.drop split ((List.range' (last - split) split).reverse ++
          (List.range' 2 (last - 2 - split)).reverse) =
            (List.range' 2 (last - 2 - split)).reverse := by
        simpa only [List.length_reverse, List.length_range'] using
          (List.drop_left (l₁ := (List.range' (last - split) split).reverse)
            (l₂ := (List.range' 2 (last - 2 - split)).reverse))
      simpa only [split, List.drop_left] using (hh.trans ht)
    let parent := upper.map (fun value => value - last)
    have restore : parent.map (last + ·) = upper := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id upper]
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range'_1.mp (upperPerm.mem_iff.mp hv)
      dsimp; omega
    have parentPerm : parent.Perm (List.range' 1 (size - last)) := by
      have hh := upperPerm.map (fun value => value - last)
      simpa only [parent, List.map_sub_range' (by omega : last ≤ last + 1) (size - last),
        show last + 1 - last = 1 by omega] using hh
    refine ⟨(split, parent), ⟨by simpa [splits] using hs, ?_⟩, ?_⟩
    · refine (membership _).mpr ⟨parentPerm, ?_, ?_⟩
      · intro ho; exact hu312 (restore ▸ (shift _ _ rfl).mpr ho)
      · intro ho; exact hu2314 (restore ▸ (shift _ _ rfl).mpr ho)
    · have hnormal : interior = (List.range' (last - split) split).reverse ++ upper ++
          (List.range' 2 (last - 2 - split)).reverse := by
        simpa only [lowerEmpty, List.append_nil, beforeEq, afterEq] using he
      simpa only [emit, restore, List.cons_append, List.append_assoc] using
        (hword.trans (congrArg (fun tail => 1 :: tail ++ [last]) hnormal)).symm
  have sliceCard := Set.ncard_congr (s := domain) (t := target) (fun pair _ => emit pair)
    emitMember (fun left right hl hr he => by
      have hh := congrArg extract he
      rwa [decode left hl, decode right hr] at hh) (by
      intro word hw
      obtain ⟨pair, hp, he⟩ := surjective word hw
      exact ⟨pair, hp, he⟩)
  have parentCard : parents.ncard = Nat.fib (2 * (size - last) - 1) := by
    let standard := Fishburn.FishburnClassicalDefs.classicalAvoiders (size - last)
      [[2, 1, 3], [4, 1, 3, 2]]
    have reverseOccurrence (pattern word : List ℕ)
        (hl : letters pattern.reverse = letters pattern) :
        Occurs pattern word → Occurs pattern.reverse word.reverse := by
      rintro ⟨chosen, hi, hm, hs, ht⟩
      refine ⟨chosen, by simpa only [hl] using hi,
        by intro rank hlo hhi; exact List.mem_reverse.mpr (hm rank hlo (hl ▸ hhi)),
        ?_, by simp⟩
      simpa only [List.map_reverse] using hs.reverse
    have forward (word : List ℕ) (hw : word ∈ parents) : word.reverse ∈ standard := by
      refine ⟨(List.reverse_perm word).trans hw.1, ?_⟩
      intro pattern ht ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · have hh := reverseOccurrence [2, 1, 3] word.reverse rfl ho
        rw [List.reverse_reverse] at hh
        exact hw.2 [3, 1, 2] (by simp) hh
      · have hh := reverseOccurrence [4, 1, 3, 2] word.reverse rfl ho
        rw [List.reverse_reverse] at hh
        exact hw.2 [2, 3, 1, 4] (by simp) hh
    have backward (word : List ℕ) (hw : word ∈ standard) : word.reverse ∈ parents := by
      refine ⟨(List.reverse_perm word).trans hw.1, ?_⟩
      intro pattern ht ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · have hh := reverseOccurrence [3, 1, 2] word.reverse rfl ho
        rw [List.reverse_reverse] at hh
        exact hw.2 [2, 1, 3] (by simp) hh
      · have hh := reverseOccurrence [2, 3, 1, 4] word.reverse rfl ho
        rw [List.reverse_reverse] at hh
        exact hw.2 [4, 1, 3, 2] (by simp) hh
    have hc := Set.ncard_congr (s := parents) (t := standard)
      (fun word _ => word.reverse) forward
      (by intro left right _ _ he; simpa using congrArg List.reverse he)
      (by intro word hw; exact ⟨word.reverse, backward word hw, List.reverse_reverse word⟩)
    exact hc.trans (RotationAvoidanceFibonacci.fibonacci_count (size - last) (by omega))
  change target.ncard = _
  rw [← sliceCard]
  have splitsCard : splits.ncard = last - 2 := by
    change (↑(Finset.range (last - 2)) : Set ℕ).ncard = last - 2
    rw [Set.ncard_coe_finset, Finset.card_range]
  exact (Set.ncard_prod (s := splits) (t := parents)).trans
    (by rw [splitsCard, parentCard])

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredEmpty
