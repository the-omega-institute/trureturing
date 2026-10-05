/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount
   mirror-E: none(waiver:layered-positive-lower-endpoint-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Layered block constructions and their inverses count positive-lower 1423 slices. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayered
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredCount

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 4096 in
theorem layered_nonempty_lower_endpoint_count (size first last : ℕ)
    (hfirst : 2 ≤ first) (hgap : first + 1 < last) (hlast : last < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some first ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = Nat.fib (2 * (size - last) - 1) *
          Nat.fib (2 * (first - 1) - 1) := by
  have construction (size first last : ℕ)
      (upper lower : List ℕ) (hfirst : 2 ≤ first) (hgap : first + 1 < last)
      (hlast : last < size)
      (hupper : upper.Perm (List.range' (last + 1) (size - last)))
      (hlower : lower.Perm (List.range' 1 (first - 1)))
      (hupper312 : ¬ Occurs [3, 1, 2] upper)
      (hupper2314 : ¬ Occurs [2, 3, 1, 4] upper)
      (hlower231 : ¬ Occurs [2, 3, 1] lower)
      (hlower1423 : ¬ Occurs [1, 4, 2, 3] lower) :
      let word := first :: upper ++ lower ++
        (List.range' (first + 1) (last - first - 1)).reverse ++ [last]
      word.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0 := by
    let middle := (List.range' (first + 1) (last - first - 1)).reverse
    let word := first :: upper ++ lower ++ middle ++ [last]
    let bucket := fun value : ℕ => if value < first then 0 else if value = first then 1
      else if value < last then 2 else if value = last then 3 else 4
    have bucketBound (value : ℕ) : bucket value < 5 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 5)
    let slot : Fin 5 → ℕ := fun shade => if shade = 0 then 2 else if shade = 1 then 0
      else if shade = 2 then 3 else if shade = 3 then 4 else 1
    let position := fun value : ℕ => slot (color value)
    have upperBounds (value : ℕ) (hv : value ∈ upper) : last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hupper.mem_iff.mp hv)
      omega
    have lowerBounds (value : ℕ) (hv : value ∈ lower) : 1 ≤ value ∧ value < first := by
      have hh := List.mem_range'_1.mp (hlower.mem_iff.mp hv)
      omega
    have middleBounds (value : ℕ) (hv : value ∈ middle) : first < value ∧ value < last := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv)
      omega
    have firstColor : color first = 1 := by simp [color, bucket]
    have lastColor : color last = 3 := by
      simp [color, bucket, show ¬ last < first by omega, show last ≠ first by omega]
    have upperColor (value : ℕ) (hv : value ∈ upper) : color value = 4 := by
      have hh := upperBounds value hv
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        show ¬ value < last by omega, show value ≠ last by omega]
    have lowerColor (value : ℕ) (hv : value ∈ lower) : color value = 0 := by
      simp [color, bucket, (lowerBounds value hv).2]
    have middleColor (value : ℕ) (hv : value ∈ middle) : color value = 2 := by
      have hh := middleBounds value hv
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega, hh.2]
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have wordNodup : word.Nodup := by
      have hu := hupper.nodup_iff.mpr List.nodup_range'
      have hl := hlower.nodup_iff.mpr List.nodup_range'
      have hum : (upper ++ lower).Nodup := List.nodup_append.mpr
        ⟨hu, hl, by
          intro left hh right ht he
          have := upperBounds left hh
          have := lowerBounds right ht
          omega⟩
      have huml : (upper ++ lower ++ middle).Nodup := List.nodup_append.mpr
        ⟨hum, List.nodup_reverse.mpr List.nodup_range', by
          intro left hh right ht he
          have := middleBounds right ht
          rcases List.mem_append.mp hh with hh | hh
          · have := upperBounds left hh; omega
          · have := lowerBounds left hh; omega⟩
      have humle : (upper ++ lower ++ middle ++ [last]).Nodup := List.nodup_append.mpr
        ⟨huml, List.nodup_singleton _, by
          intro left hh right ht he
          simp only [List.mem_singleton] at ht
          simp only [List.mem_append] at hh
          rcases hh with (hh | hh) | hh
          · have := upperBounds left hh; omega
          · have := lowerBounds left hh; omega
          · have := middleBounds left hh; omega⟩
      apply List.nodup_cons.mpr
      refine ⟨?_, humle⟩
      intro hh
      change first ∈ upper ++ lower ++ middle ++ [last] at hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with ((hh | hh) | hh) | hh
      · have := upperBounds first hh; omega
      · have := lowerBounds first hh; omega
      · have := middleBounds first hh; omega
      · omega
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      simp only [word, middle, List.cons_append, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, hupper.mem_iff, hlower.mem_iff,
        List.mem_reverse, List.mem_range'_1]
      omega
    have orderedWord : word.Pairwise (fun left right => position left ≤ position right) := by
      have upperOrdered : upper.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, upperColor left hl, upperColor right hr])
      have middleOrdered : middle.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, middleColor left hl, middleColor right hr])
      have lowerOrdered : lower.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr; simp [position, lowerColor left hl, lowerColor right hr])
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact upperOrdered
        | exact middleOrdered
        | exact lowerOrdered
        | (intros; simp [position, firstColor, lastColor, upperColor, middleColor,
            lowerColor, slot, *])
    have firstEndpoint (value : ℕ) (hc : color value = 1) : value = first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 3) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have filtered (shade : Fin 5) :
        word.filter (fun value => decide (color value = shade)) =
          (if shade = 1 then [first] else []) ++
          (if shade = 4 then upper else []) ++
          (if shade = 0 then lower else []) ++
          (if shade = 2 then middle else []) ++ (if shade = 3 then [last] else []) := by
      have block (values : List ℕ) (paint : Fin 5)
          (hc : ∀ value ∈ values, color value = paint) :
          values.filter (fun value => decide (color value = shade)) =
            if shade = paint then values else [] := by
        split_ifs with he
        · exact List.filter_eq_self.mpr (by intro value hv; simp [hc value hv, he])
        · exact List.filter_eq_nil_iff.mpr (by
            intro value hv; simp [hc value hv, Ne.symm he])
      simp only [word, List.cons_append, List.filter_cons, List.filter_append,
        block upper 4 upperColor, block middle 2 middleColor, block lower 0 lowerColor,
        firstColor, lastColor, List.filter_singleton]
      fin_cases shade <;> simp
    have finiteProfiles : ∀ low second third high : Fin 5,
        low ≤ second → second ≤ third → third ≤ high →
        (low = second → low ≠ 1 ∧ low ≠ 3) →
        (second = third → second ≠ 1 ∧ second ≠ 3) →
        (third = high → third ≠ 1 ∧ third ≠ 3) →
        ((slot low ≤ slot high ∧ slot high ≤ slot second ∧ slot second ≤ slot third ∧
            ¬ (second = 2 ∧ third = 2)) →
          (low = 0 ∧ second = 0 ∧ third = 0 ∧ high = 0) ∨
          (second = 4 ∧ third = 4 ∧ high = 4) ∨
          (low = 1 ∧ third = 3)) ∧
        ((slot high ≤ slot second ∧ slot second ≤ slot third ∧ slot third ≤ slot low ∧
            ¬ (second = 2 ∧ third = 2)) →
          (low = 0 ∧ second = 0 ∧ third = 0) ∨
          (second = 4 ∧ third = 4 ∧ high = 4)) ∧
        ((slot second ≤ slot third ∧ slot third ≤ slot low ∧ slot low ≤ slot high ∧
            ¬ (second = 2 ∧ third = 2)) →
          (low = 0 ∧ second = 0 ∧ third = 0) ∨
          (low = 4 ∧ second = 4 ∧ third = 4 ∧ high = 4)) ∧
        ((slot third ≤ slot low ∧ slot low ≤ slot high ∧ slot high ≤ slot second ∧
            ¬ (low = 2 ∧ high = 2)) →
          (second = 0 ∧ third = 0 ∧ high = 0) ∨
          (low = 4 ∧ second = 4 ∧ third = 4)) := by decide
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
      have singleton (left right : ℕ) (hh : chosen left < chosen right) :
          color (chosen left) = color (chosen right) →
            color (chosen left) ≠ 1 ∧ color (chosen left) ≠ 3 := by
        intro he
        constructor
        · intro hc
          have := firstEndpoint _ hc
          have := firstEndpoint _ (he.symm.trans hc)
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
        (singleton 1 2 (hi 1 (by omega) (by omega)))
        (singleton 2 3 (hi 2 (by omega) (by omega)))
        (singleton 3 4 (hi 3 (by omega) (by omega)))
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
        ¬ (color (chosen left) = 2 ∧ color (chosen right) = 2) := by
      rintro ⟨hl, ht⟩
      have hp := project _ _ [left, right] middle chosen 2 hcontainer hs hr
        (by intro rank hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl <;> assumption) (by simpa using filtered 2)
      have hi := List.pairwise_iff_forall_sublist.mp
        (by
          simpa only [middle, List.pairwise_reverse] using
            (List.pairwise_lt_range' (s := first + 1) (n := last - first - 1)) :
          middle.Pairwise (· > ·)) hp
      omega
    have triple (block : List ℕ) (pattern : List ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm [1, 2, 3])
        (hi : chosen 1 < chosen 2 ∧ chosen 2 < chosen 3)
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
        (ho : Occurs [1, 4, 2, 3] container) : first ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := hi
      have shapes := (profile _ _ chosen hcontainer hs (by decide) hi').1
        ⟨edge _ _ _ hcontainer hs 1 4 (by decide), edge _ _ _ hcontainer hs 4 2 (by decide),
          edge _ _ _ hcontainer hs 2 3 (by decide),
          noMiddleAscent _ _ _ hcontainer hs 2 3 (by decide)
            (hi' 2 (by omega) (by omega))⟩
      rcases shapes with hl | hu | he
      · exfalso
        apply hlower1423
        exact build _ lower 4 chosen (by decide) rfl hi'
          (project _ _ [1, 4, 2, 3] lower chosen 0 hcontainer hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 0))
      · exfalso
        apply hupper312
        apply triple upper [3, 1, 2] (fun rank => chosen (rank + 1)) (by decide)
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
        simpa using project _ _ [4, 2, 3] upper chosen 4 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> tauto)
          (by simpa using filtered 4)
      · constructor
        · rw [← firstEndpoint _ he.1]; exact hs.subset (by simp)
        · rw [← lastEndpoint _ he.2]; exact hs.subset (by simp)
    have noRotated (rotation : ℕ) (hpositive : 0 < rotation) (hrotation : rotation < 4) :
        ¬ Occurs ([1, 4, 2, 3].rotate rotation) word := by
      intro ho
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
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
      · have shape := shapes.1 ⟨edge _ _ _ (List.Sublist.refl word) hs 4 2 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 2 3 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          ascending (by decide) ascendingValue⟩
        rcases shape with hl | hu
        · apply hlower231
          apply triple lower [2, 3, 1] chosen (by decide)
            ⟨hi' 1 (by omega) (by omega), hi' 2 (by omega) (by omega)⟩
          exact project _ _ [2, 3, 1] lower chosen 0 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 0)
        · apply hupper312
          apply triple upper [3, 1, 2] (fun rank => chosen (rank + 1)) (by decide)
            ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
          simpa using project _ _ [4, 2, 3] upper chosen 4 (List.Sublist.refl word) hs
            (by decide) (by
              intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 4)
      · have shape := shapes.2.1 ⟨edge _ _ _ (List.Sublist.refl word) hs 2 3 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 1 4 (by decide),
          ascending (by decide) ascendingValue⟩
        rcases shape with hl | hu
        · apply hlower231
          apply triple lower [2, 3, 1] chosen (by decide)
            ⟨hi' 1 (by omega) (by omega), hi' 2 (by omega) (by omega)⟩
          exact project _ _ [2, 3, 1] lower chosen 0 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 0)
        · apply hupper2314
          exact build _ upper 4 chosen (by decide) rfl hi'
            (project _ _ [2, 3, 1, 4] upper chosen 4 (List.Sublist.refl word) hs (by decide)
              (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl | rfl | rfl <;> tauto)
              (by simpa using filtered 4))
      · have shape := shapes.2.2 ⟨edge _ _ _ (List.Sublist.refl word) hs 3 1 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 1 4 (by decide),
          edge _ _ _ (List.Sublist.refl word) hs 4 2 (by decide),
          noMiddleAscent _ _ _ (List.Sublist.refl word) hs 1 4 (by decide) (by
            have h12 := hi' 1 (by omega) (by omega)
            have h23 := hi' 2 (by omega) (by omega)
            have h34 := hi' 3 (by omega) (by omega)
            simp only [Nat.reduceAdd] at h12 h23 h34
            omega)⟩
        rcases shape with hl | hu
        · apply hlower231
          apply triple lower [2, 3, 1] (fun rank => chosen (rank + 1)) (by decide)
            ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
          simpa using project _ _ [3, 4, 2] lower chosen 0 (List.Sublist.refl word) hs
            (by decide) (by
              intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 0)
        · apply hupper312
          apply triple upper [3, 1, 2] chosen (by decide)
            ⟨hi' 1 (by omega) (by omega), hi' 2 (by omega) (by omega)⟩
          exact project _ _ [3, 1, 2] upper chosen 4 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl <;> tauto)
            (by simpa using filtered 4)
    have targetOccurrence : Occurs [1, 4, 2, 3] word := by
      obtain ⟨high, hh⟩ : ∃ high, high ∈ upper := by
        exact ⟨last + 1, hupper.mem_iff.mpr (List.mem_range'_1.mpr (by omega))⟩
      obtain ⟨low, ht⟩ : ∃ low, low ∈ middle := by
        exact ⟨first + 1, List.mem_reverse.mpr (List.mem_range'_1.mpr (by omega))⟩
      let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then low
        else if rank = 3 then last else high
      apply build _ word 4 chosen (by decide) rfl
      · intro rank hlo hhi
        have hu := upperBounds high hh
        have hl := middleBounds low ht
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hc with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · have hs : [high, low].Sublist (upper ++ lower ++ middle) :=
          (((List.singleton_sublist.mpr hh).trans (List.sublist_append_left _ _)).append
            (List.singleton_sublist.mpr ht))
        simpa [word, chosen] using (hs.append_right [last]).cons_cons first
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [1, 4, 2, 3] word
      (by decide) wordPerm).mpr ⟨targetOccurrence, noRotated, ?_, ?_⟩⟩
    · intro ho
      have hh := (forcedEndpoints word.tail (List.tail_sublist word) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hh
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist word) ho).2
      have hp : last ∉ word.dropLast := by
        have hn := List.nodup_append.mp
          (List.nodup_cons.mp wordNodup).2
        have he : word.dropLast = first :: (upper ++ lower ++ middle) := by
          change ((first :: (upper ++ lower ++ middle)) ++ [last]).dropLast = _
          rw [List.dropLast_append_cons]; simp
        rw [he]
        simp only [List.mem_cons]
        rintro (hh | hh)
        · omega
        · exact hn.2.2 last hh last (by simp) rfl
      exact hp hh
  classical
  let upperParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (size - last)
    [[3, 1, 2], [2, 3, 1, 4]]
  let lowerParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (first - 1)
    [[2, 3, 1], [1, 4, 2, 3]]
  let domain := upperParents ×ˢ lowerParents
  let middle := (List.range' (first + 1) (last - first - 1)).reverse
  let target := {word : List ℕ | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 4, 2, 3] (word.rotate cut) ↔ cut = 0}
  let emit := fun pair : List ℕ × List ℕ => first ::
    pair.1.map (fun value => last + value) ++ pair.2 ++ middle ++ [last]
  let extract := fun word : List ℕ =>
    ((word.filter (fun value => decide (last < value))).map (fun value => value - last),
      word.filter (fun value => decide (value < first)))
  have upperMembership (word : List ℕ) : word ∈ upperParents ↔
      word.Perm (List.range' 1 (size - last)) ∧
        ¬ Occurs [3, 1, 2] word ∧ ¬ Occurs [2, 3, 1, 4] word := by
    simp [upperParents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have lowerMembership (word : List ℕ) : word ∈ lowerParents ↔
      word.Perm (List.range' 1 (first - 1)) ∧
        ¬ Occurs [2, 3, 1] word ∧ ¬ Occurs [1, 4, 2, 3] word := by
    simp [lowerParents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have shift (pattern word : List ℕ) (hl : letters pattern = pattern.length) :
      Occurs pattern (word.map (fun value => last + value)) ↔ Occurs pattern word := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (last + ·)
      (by intro left right hh; dsimp; omega)
  have emitMember (pair : List ℕ × List ℕ) (hp : pair ∈ domain) : emit pair ∈ target := by
    obtain ⟨huPerm, hu312, hu2314⟩ := (upperMembership pair.1).mp hp.1
    obtain ⟨hlPerm, hl231, hl1423⟩ := (lowerMembership pair.2).mp hp.2
    have hu : (pair.1.map (fun value => last + value)).Perm
        (List.range' (last + 1) (size - last)) := by
      simpa only [List.map_add_range'] using huPerm.map (fun value => last + value)
    have hc := construction size first last
      (pair.1.map (fun value => last + value)) pair.2 hfirst hgap hlast hu hlPerm
      (fun ho => hu312 ((shift _ _ rfl).mp ho))
      (fun ho => hu2314 ((shift _ _ rfl).mp ho)) hl231 hl1423
    refine ⟨hc.1, ?_, ?_, hc.2⟩
    · simp [emit]
    · change ((first :: pair.1.map (fun value => last + value) ++ pair.2 ++ middle) ++
        [last]).getLast? = some last
      rw [List.getLast?_append_cons]
      rfl
  have decode (pair : List ℕ × List ℕ) (hp : pair ∈ domain) :
      extract (emit pair) = pair := by
    have upperBounds (value : ℕ) (hv : value ∈ pair.1.map (last + ·)) :
        last < value ∧ value ≤ size := by
      obtain ⟨parent, hm, rfl⟩ := List.mem_map.mp hv
      have hh := List.mem_range'_1.mp (hp.1.1.mem_iff.mp hm)
      omega
    have lowerBounds (value : ℕ) (hv : value ∈ pair.2) : 1 ≤ value ∧ value < first := by
      have hh := List.mem_range'_1.mp (hp.2.1.mem_iff.mp hv)
      omega
    have middleBounds (value : ℕ) (hv : value ∈ middle) : first < value ∧ value < last := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv)
      omega
    have upperKeep : (pair.1.map (last + ·)).filter (fun value => decide (last < value)) =
        pair.1.map (last + ·) := List.filter_eq_self.mpr (by
      intro value hv; simp [(upperBounds value hv).1])
    have upperDrop : (pair.1.map (last + ·)).filter (fun value => decide (value < first)) =
        [] := List.filter_eq_nil_iff.mpr (by
      intro value hv; have := upperBounds value hv; simp only [decide_eq_true_eq]; omega)
    have lowerKeep : pair.2.filter (fun value => decide (value < first)) = pair.2 :=
      List.filter_eq_self.mpr (by intro value hv; simp [(lowerBounds value hv).2])
    have lowerDrop : pair.2.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv; have := lowerBounds value hv; simp only [decide_eq_true_eq]; omega)
    have middleDropUpper : middle.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv; have := middleBounds value hv; simp only [decide_eq_true_eq]; omega)
    have middleDropLower : middle.filter (fun value => decide (value < first)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv; have := middleBounds value hv; simp only [decide_eq_true_eq]; omega)
    have restore : (pair.1.map (last + ·)).map (fun value => value - last) = pair.1 := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id pair.1]
      apply List.map_congr_left
      intro value hv
      dsimp; omega
    simp [extract, emit, List.filter_append, upperKeep, upperDrop, lowerKeep, lowerDrop,
      middleDropUpper, middleDropLower, show ¬ last < first by omega,
      show ¬ first > last by omega, restore]
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ pair ∈ domain, emit pair = word := by
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases word with
      | nil => simp [target] at hw
      | cons head tail =>
        have he : head = first := by simpa using hw.2.1
        subst head
        have hlen : (first :: tail).length = size := by
          simpa using hw.1.length_eq
        have htail : tail ≠ [] := by intro he; simp [he] at hlen; omega
        have htailLast : tail.getLast? = some last := by
          cases tail with
          | nil => exact (htail rfl).elim
          | cons head rest => simpa only [List.getLast?_cons_cons] using hw.2.2.1
        have hh : tail = tail.dropLast ++ [last] :=
          (List.dropLast_append_getLast? last (by simp [htailLast])).symm
        exact ⟨tail.dropLast, by simpa only [List.cons_append] using congrArg (first :: ·) hh⟩
    obtain ⟨_, _, before, upper, lower, after, he, upperPerm, lowerPerm, middlePerm,
        _, afterSorted, _, _, beforeEmpty, hu312, hu2314, hl231, hl1423⟩ :=
      RotationAvoidanceLayered.layered_endpoint_normal_form size first last interior
        (by omega) (by omega) (by omega) (hsplit ▸ hw.1)
        (by simpa only [← hsplit] using hw.2.2.2)
    have hbefore := beforeEmpty hfirst
    subst before
    have afterPerm : after.Perm (List.range' (first + 1) (last - first - 1)) := by
      simpa using middlePerm
    have afterEq : after = middle :=
      (afterPerm.trans (List.reverse_perm _).symm).eq_of_pairwise
        (by intro left right hl hr; omega) afterSorted
        (by simpa only [middle, List.pairwise_reverse] using
          (List.pairwise_lt_range' (s := first + 1) (n := last - first - 1)))
    have hnormal : interior = upper ++ lower ++ middle := by
      simpa only [List.nil_append, afterEq] using he
    let parent := upper.map (fun value => value - last)
    have restore : parent.map (fun value => last + value) = upper := by
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
    refine ⟨(parent, lower), ?_, ?_⟩
    · refine ⟨(upperMembership _).mpr ⟨parentPerm, ?_, ?_⟩,
        (lowerMembership _).mpr ⟨lowerPerm, hl231, hl1423⟩⟩
      · intro ho; exact hu312 (restore ▸ (shift _ _ rfl).mpr ho)
      · intro ho; exact hu2314 (restore ▸ (shift _ _ rfl).mpr ho)
    · simpa only [emit, restore, List.cons_append, List.append_assoc] using
        (hsplit.trans (congrArg (fun tail => first :: tail ++ [last]) hnormal)).symm
  have sliceCard := Set.ncard_congr (s := domain) (t := target) (fun pair _ => emit pair)
    emitMember (fun left right hl hr he => by
      have hh := congrArg extract he
      rwa [decode left hl, decode right hr] at hh) (by
      intro word hw
      obtain ⟨pair, hp, he⟩ := emitSurjective word hw
      exact ⟨pair, hp, he⟩)
  let reflectedParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (first - 1)
    [[2, 1, 3], [4, 1, 3, 2]]
  let reflect := fun word : List ℕ => word.map (fun value => first - value)
  have reflectPerm (word : List ℕ) (hp : word.Perm (List.range' 1 (first - 1))) :
      (reflect word).Perm (List.range' 1 (first - 1)) := by
    have hr : (List.range' 1 (first - 1)).map (fun value => first - value) =
        (List.range' 1 (first - 1)).reverse := by
      rw [List.reverse_range', List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro value hv
      dsimp; omega
    exact ((hp.map (first - ·)).trans (List.Perm.of_eq hr)).trans (List.reverse_perm _)
  have reflectTwice (word : List ℕ) (hp : word.Perm (List.range' 1 (first - 1))) :
      reflect (reflect word) = word := by
    simp only [reflect, List.map_map]
    conv_rhs => rw [← List.map_id word]
    apply List.map_congr_left
    intro value hv
    have hh := List.mem_range'_1.mp (hp.mem_iff.mp hv)
    dsimp; omega
  have reflectOccurrence (width : ℕ) (pattern word : List ℕ)
      (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
      (hr : letters (pattern.map (fun rank => width + 1 - rank)) = width)
      (hw : word.Perm (List.range' 1 (first - 1))) :
      Occurs pattern word →
        Occurs (pattern.map (fun rank => width + 1 - rank)) (reflect word) := by
    rintro ⟨witness, hi, hm, hs, _⟩
    let chosen := fun rank : ℕ => first - witness (width + 1 - rank)
    have witnessBounds (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ width) :
        1 ≤ witness rank ∧ witness rank < first := by
      have hh := List.mem_range'_1.mp (hw.mem_iff.mp (hm rank hlo (by rwa [hl])))
      omega
    refine ⟨chosen, ?_, ?_, ?_, by simp⟩
    · intro rank hlo hhi
      rw [hr] at hhi
      have hh := hi (width - rank) (by omega) (by rw [hl]; omega)
      have hb := witnessBounds (width + 1 - rank) (by omega) (by omega)
      have he : width - rank + 1 = width + 1 - rank := by omega
      rw [he] at hh
      dsimp [chosen]
      have he' : width + 1 - (rank + 1) = width - rank := by omega
      rw [he']; omega
    · intro rank hlo hhi
      rw [hr] at hhi
      exact List.mem_map.mpr ⟨witness (width + 1 - rank),
        hm _ (by omega) (by rw [hl]; omega), rfl⟩
    · have ht := hs.map (fun value => first - value)
      convert ht using 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro rank hk
      have hb := List.mem_range'_1.mp (hp.mem_iff.mp hk)
      dsimp [chosen]
      congr 2
      omega
  have reflectMember (word : List ℕ) (hw : word ∈ lowerParents) :
      reflect word ∈ reflectedParents := by
    obtain ⟨hp, h132, h3241⟩ := (lowerMembership word).mp hw
    refine ⟨reflectPerm word hp, ?_⟩
    intro pattern ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · intro ho
      have hh := reflectOccurrence 3 [2, 1, 3] (reflect word) (by decide) rfl rfl
        (reflectPerm word hp) ho
      rw [reflectTwice word hp] at hh
      exact h132 hh
    · intro ho
      have hh := reflectOccurrence 4 [4, 1, 3, 2] (reflect word) (by decide) rfl rfl
        (reflectPerm word hp) ho
      rw [reflectTwice word hp] at hh
      exact h3241 hh
  have reflectBack (word : List ℕ) (hw : word ∈ reflectedParents) :
      reflect word ∈ lowerParents := by
    refine (lowerMembership _).mpr ⟨reflectPerm word hw.1, ?_, ?_⟩
    · intro ho
      have hh := reflectOccurrence 3 [2, 3, 1] (reflect word) (by decide) rfl rfl
        (reflectPerm word hw.1) ho
      rw [reflectTwice word hw.1] at hh
      exact hw.2 [2, 1, 3] (by simp) hh
    · intro ho
      have hh := reflectOccurrence 4 [1, 4, 2, 3] (reflect word) (by decide) rfl rfl
        (reflectPerm word hw.1) ho
      rw [reflectTwice word hw.1] at hh
      exact hw.2 [4, 1, 3, 2] (by simp) hh
  have lowerCard : lowerParents.ncard = Nat.fib (2 * (first - 1) - 1) := by
    have hc := Set.ncard_congr (s := lowerParents) (t := reflectedParents)
      (fun word _ => reflect word) reflectMember (by
        intro left right hl hr he
        have hh := congrArg reflect he
        rwa [reflectTwice left hl.1, reflectTwice right hr.1] at hh) (by
        intro word hw
        exact ⟨reflect word, reflectBack word hw, reflectTwice word hw.1⟩)
    exact hc.trans (RotationAvoidanceFibonacci.fibonacci_count (first - 1) (by omega))
  have upperCard : upperParents.ncard = Nat.fib (2 * (size - last) - 1) := by
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
    have forward (word : List ℕ) (hw : word ∈ upperParents) : word.reverse ∈ standard := by
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
    have backward (word : List ℕ) (hw : word ∈ standard) : word.reverse ∈ upperParents := by
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
    have hc := Set.ncard_congr (s := upperParents) (t := standard)
      (fun word _ => word.reverse) forward
      (by intro left right _ _ he; simpa using congrArg List.reverse he)
      (by intro word hw; exact ⟨word.reverse, backward word hw, List.reverse_reverse word⟩)
    exact hc.trans (RotationAvoidanceFibonacci.fibonacci_count (size - last) (by omega))
  change target.ncard = _
  rw [← sliceCard]
  exact (Set.ncard_prod (s := upperParents) (t := lowerParents)).trans
    (by rw [upperCard, lowerCard])

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayeredCount
