/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices
   mirror-E: none(waiver:fibonacci-endpoint-slices)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Pattern witnesses characterize and count the extreme-endpoint 1324 slices. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSeparated
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEndpoints
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSlices

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 2048 in
theorem fibonacci_least_endpoint_count (size last : ℕ) (hlast : 4 ≤ last)
    (hbound : last ≤ size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some 1 ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 3, 2, 4] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = (if last = size then 1 else Nat.fib (2 * (size - last) - 1)) *
          (2 ^ (last - 3) - 1) := by
  have construction (size last : ℕ) (upper middle : List ℕ)
      (hlast : 4 ≤ last) (hbound : last ≤ size)
      (hupper : upper.Perm (List.range' (last + 1) (size - last)))
      (hmiddle : middle.Perm (List.range' 2 (last - 2)))
      (hupper213 : ¬ Occurs [2, 1, 3] upper)
      (hupper4132 : ¬ Occurs [4, 1, 3, 2] upper)
      (hmiddle132 : ¬ Occurs [1, 3, 2] middle)
      (hmiddle213 : ¬ Occurs [2, 1, 3] middle)
      (hdescent : ¬ middle.Pairwise (· < ·)) :
      (1 :: upper ++ middle ++ [last]).Perm (List.range' 1 size) ∧
        ∀ cut < size,
          Occurs [1, 3, 2, 4] ((1 :: upper ++ middle ++ [last]).rotate cut) ↔ cut = 0 := by
    let word := 1 :: upper ++ middle ++ [last]
    let bucket := fun value : ℕ => if value ≤ 1 then 0 else if value < last then 1
      else if value = last then 2 else 3
    have bucketBound (value : ℕ) : bucket value < 4 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 4)
    let slot : Fin 4 → ℕ := fun rank => if rank = 0 then 0 else if rank = 1 then 2
      else if rank = 2 then 3 else 1
    let position := fun value : ℕ => slot (color value)
    have upperBounds (value : ℕ) (hv : value ∈ upper) : last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hupper.mem_iff.mp hv)
      omega
    have middleBounds (value : ℕ) (hv : value ∈ middle) : 1 < value ∧ value < last := by
      have hh := List.mem_range'_1.mp (hmiddle.mem_iff.mp hv)
      omega
    have firstColor : color 1 = 0 := by simp [color, bucket]
    have lastColor : color last = 2 := by simp [color, bucket, show ¬ last ≤ 1 by omega]
    have upperColor (value : ℕ) (hv : value ∈ upper) : color value = 3 := by
      have hh := upperBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega, show ¬ value < last by omega,
        show value ≠ last by omega]
    have middleColor (value : ℕ) (hv : value ∈ middle) : color value = 1 := by
      have hh := middleBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega, hh.2]
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have wordNodup : word.Nodup := by
      have hu := hupper.nodup_iff.mpr List.nodup_range'
      have hm := hmiddle.nodup_iff.mpr List.nodup_range'
      have hum : (upper ++ middle).Nodup := List.nodup_append.mpr ⟨hu, hm, by
        intro left hl right hr heq
        have hh := upperBounds left hl
        have ht := middleBounds right hr
        omega⟩
      have huml : (upper ++ middle ++ [last]).Nodup := List.nodup_append.mpr
        ⟨hum, List.nodup_singleton _, by
          intro left hl right hr heq
          simp only [List.mem_singleton] at hr
          rcases List.mem_append.mp hl with hl | hl
          · have hh := upperBounds left hl; omega
          · have hh := middleBounds left hl; omega⟩
      change (1 :: (upper ++ middle ++ [last])).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_, huml⟩
      intro hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with (hh | hh) | hh
      · have ht := upperBounds 1 hh; omega
      · have ht := middleBounds 1 hh; omega
      · omega
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      simp only [word, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        hupper.mem_iff, hmiddle.mem_iff, List.mem_range'_1]
      omega
    have orderedWord : word.Pairwise (fun left right => position left ≤ position right) := by
      have upperOrdered : upper.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr
          simp [position, upperColor left hl, upperColor right hr])
      have middleOrdered : middle.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr
          simp [position, middleColor left hl, middleColor right hr])
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton,
        List.mem_append, List.mem_singleton, List.not_mem_nil, forall_false, or_imp,
        forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact upperOrdered
        | exact middleOrdered
        | (intros; simp [position, firstColor, lastColor, upperColor, middleColor, slot,
            *])
    have firstEndpoint (value : ℕ) (hv : value ∈ word) (hc : color value = 0) : value = 1 := by
      have hh := List.mem_range'_1.mp (wordPerm.mem_iff.mp hv)
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 2) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have upperFilter : word.filter (fun value => decide (color value = 3)) = upper := by
      have hu : upper.filter (fun value => decide (color value = 3)) = upper :=
        List.filter_eq_self.mpr (by intro value hv; simp [upperColor value hv])
      have hm : middle.filter (fun value => decide (color value = 3)) = [] :=
        List.filter_eq_nil_iff.mpr (by intro value hv; simp [middleColor value hv])
      simp [word, firstColor, lastColor, List.filter_append, hu, hm]
    have middleFilter : word.filter (fun value => decide (color value = 1)) = middle := by
      have hu : upper.filter (fun value => decide (color value = 1)) = [] :=
        List.filter_eq_nil_iff.mpr (by intro value hv; simp [upperColor value hv])
      have hm : middle.filter (fun value => decide (color value = 1)) = middle :=
        List.filter_eq_self.mpr (by intro value hv; simp [middleColor value hv])
      simp [word, firstColor, lastColor, List.filter_append, hu, hm]
    have finiteProfiles : ∀ lower second third greatest : Fin 4,
        lower ≤ second → second ≤ third → third ≤ greatest →
        (lower = second → lower ≠ 0 ∧ lower ≠ 2) →
        (second = third → second ≠ 0 ∧ second ≠ 2) →
        (third = greatest → third ≠ 0 ∧ third ≠ 2) →
        ((slot lower ≤ slot third ∧ slot third ≤ slot second ∧
            slot second ≤ slot greatest) →
          (second = 3 ∧ third = 3 ∧ greatest = 3) ∨
          (lower = 1 ∧ second = 1 ∧ third = 1) ∨
          (second = 1 ∧ third = 1 ∧ greatest = 1) ∨
          (lower = 0 ∧ greatest = 2)) ∧
        ((slot third ≤ slot second ∧ slot second ≤ slot greatest ∧
            slot greatest ≤ slot lower) →
          (second = 3 ∧ third = 3 ∧ greatest = 3) ∨
          (second = 1 ∧ third = 1 ∧ greatest = 1)) ∧
        ((slot second ≤ slot greatest ∧ slot greatest ≤ slot lower ∧
            slot lower ≤ slot third) →
          (lower = 3 ∧ second = 3 ∧ third = 3) ∨
          (lower = 1 ∧ second = 1 ∧ third = 1)) ∧
        ((slot greatest ≤ slot lower ∧ slot lower ≤ slot third ∧
            slot third ≤ slot second) →
          (lower = 3 ∧ second = 3 ∧ third = 3 ∧ greatest = 3) ∨
          (lower = 1 ∧ second = 1 ∧ third = 1)) := by decide
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
      have member (rank : ℕ) (hr : rank ∈ pattern) : chosen rank ∈ word :=
        hcontainer.subset (hs.subset (List.mem_map_of_mem hr))
      have singleton (left right : ℕ) (hleft : left ∈ pattern) (hright : right ∈ pattern)
          (hh : chosen left < chosen right) :
          color (chosen left) = color (chosen right) →
            color (chosen left) ≠ 0 ∧ color (chosen left) ≠ 2 := by
        intro he
        constructor
        · intro hc
          have hl := firstEndpoint _ (member left hleft) hc
          have hr := firstEndpoint _ (member right hright) (he.symm.trans hc)
          omega
        · intro hc
          have hl := lastEndpoint _ hc
          have hr := lastEndpoint _ (he.symm.trans hc)
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
    have project (pattern container ranks block : List ℕ) (chosen : ℕ → ℕ) (shade : Fin 4)
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
    have triple132 (block : List ℕ) (chosen : ℕ → ℕ)
        (hi : chosen 1 < chosen 2 ∧ chosen 2 < chosen 3)
        (hs : [chosen 1, chosen 3, chosen 2].Sublist block) : Occurs [1, 3, 2] block := by
      refine build _ _ 3 chosen (by decide) rfl ?_ (by simpa using hs)
      intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 := by omega
      rcases hh with rfl | rfl
      · exact hi.1
      · exact hi.2
    have triple213 (block : List ℕ) (chosen : ℕ → ℕ)
        (hi : chosen 1 < chosen 2 ∧ chosen 2 < chosen 3)
        (hs : [chosen 2, chosen 1, chosen 3].Sublist block) : Occurs [2, 1, 3] block := by
      refine build _ _ 3 chosen (by decide) rfl ?_ (by simpa using hs)
      intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 := by omega
      rcases hh with rfl | rfl
      · exact hi.1
      · exact hi.2
    have forcedEndpoints (container : List ℕ) (hcontainer : container.Sublist word)
        (ho : Occurs [1, 3, 2, 4] container) : 1 ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile _ _ chosen hcontainer hs (by decide) hi').1
        ⟨edge _ _ _ hcontainer hs 1 3 (by decide),
          edge _ _ _ hcontainer hs 3 2 (by decide),
          edge _ _ _ hcontainer hs 2 4 (by decide)⟩
      rcases hp with hu | hm | hm | he
      · apply False.elim
        apply hupper213
        apply triple213 upper (fun rank => chosen (rank + 1))
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
        exact project _ _ [3, 2, 4] upper chosen 3 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
              rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) upperFilter
      · apply False.elim
        apply hmiddle132
        apply triple132 middle chosen ⟨hi' 1 (by omega) (by omega),
          hi' 2 (by omega) (by omega)⟩
        exact project _ _ [1, 3, 2] middle chosen 1 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
              rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) middleFilter
      · apply False.elim
        apply hmiddle213
        apply triple213 middle (fun rank => chosen (rank + 1))
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
        exact project _ _ [3, 2, 4] middle chosen 1 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
              rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) middleFilter
      · have hf := firstEndpoint _
          (hcontainer.subset (hs.subset (by simp : chosen 1 ∈ _))) he.1
        have hl := lastEndpoint _ he.2
        constructor
        · rw [← hf]; exact hs.subset (by simp)
        · rw [← hl]; exact hs.subset (by simp)
    have noRotated (shift : ℕ) (hpositive : 0 < shift) (hshift : shift < 4) :
        ¬ Occurs ([1, 3, 2, 4].rotate shift) word := by
      intro ho
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hp : ([1, 3, 2, 4] : List ℕ).rotate shift |>.Perm [1, 2, 3, 4] :=
        (List.rotate_perm _ _).trans (by decide)
      have hl : letters (([1, 3, 2, 4] : List ℕ).rotate shift) = 4 := by
        simpa [letters] using hp.foldr_eq (f := max) 0
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa only [hl] using hi
      have shapes := (profile _ _ chosen (List.Sublist.refl word) hs hp hi').2
      have edge' := edge _ _ chosen (List.Sublist.refl word) hs
      interval_cases shift
      · have shape := shapes.1 ⟨edge' 3 2 (by decide), edge' 2 4 (by decide),
          edge' 4 1 (by decide)⟩
        rcases shape with hu | hm
        · apply hupper213
          apply triple213 upper (fun rank => chosen (rank + 1))
            ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
          exact project _ _ [3, 2, 4] upper chosen 3 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) upperFilter
        · apply hmiddle213
          apply triple213 middle (fun rank => chosen (rank + 1))
            ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
          exact project _ _ [3, 2, 4] middle chosen 1 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) middleFilter
      · have shape := shapes.2.1 ⟨edge' 2 4 (by decide), edge' 4 1 (by decide),
          edge' 1 3 (by decide)⟩
        rcases shape with hu | hm
        · apply hupper213
          apply triple213 upper chosen ⟨hi' 1 (by omega) (by omega),
            hi' 2 (by omega) (by omega)⟩
          exact project _ _ [2, 1, 3] upper chosen 3 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) upperFilter
        · apply hmiddle213
          apply triple213 middle chosen ⟨hi' 1 (by omega) (by omega),
            hi' 2 (by omega) (by omega)⟩
          exact project _ _ [2, 1, 3] middle chosen 1 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) middleFilter
      · have shape := shapes.2.2 ⟨edge' 4 1 (by decide), edge' 1 3 (by decide),
          edge' 3 2 (by decide)⟩
        rcases shape with hu | hm
        · apply hupper4132
          exact build _ upper 4 chosen (by decide) rfl hi'
            (project _ _ [4, 1, 3, 2] upper chosen 3 (List.Sublist.refl word) hs (by decide)
              (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                  rcases hr with rfl | rfl | rfl | rfl <;> simp_all only [and_true]) upperFilter)
        · apply hmiddle132
          apply triple132 middle chosen ⟨hi' 1 (by omega) (by omega),
            hi' 2 (by omega) (by omega)⟩
          exact project _ _ [1, 3, 2] middle chosen 1 (List.Sublist.refl word) hs (by decide)
            (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
                rcases hr with rfl | rfl | rfl <;> simp_all only [and_true]) middleFilter
    have targetOccurrence : Occurs [1, 3, 2, 4] word := by
      obtain ⟨left, right, hs, hn⟩ : ∃ left right,
          [left, right].Sublist middle ∧ right ≤ left := by
        have hh := List.pairwise_iff_forall_sublist.not.mp hdescent
        push Not at hh
        exact hh
      have hne := List.pairwise_iff_forall_sublist.mp
        (List.nodup_iff_pairwise_ne.mp (hmiddle.nodup_iff.mpr List.nodup_range')) hs
      have hbLeft := middleBounds left (hs.subset (by simp))
      have hbRight := middleBounds right (hs.subset (by simp))
      let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then right
        else if rank = 3 then left else last
      refine build _ word 4 chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [chosen, word] using
          ((hs.trans (List.sublist_append_right upper middle)).append_right [last]).cons_cons 1
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [1, 3, 2, 4] word
      (by decide) wordPerm).mpr ⟨targetOccurrence, noRotated, ?_, ?_⟩⟩
    · intro ho
      have hh := (forcedEndpoints word.tail (List.tail_sublist word) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hh
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist word) ho).2
      have hd : word.dropLast = 1 :: upper ++ middle := by
        change ((1 :: upper ++ middle) ++ [last]).dropLast = _
        rw [List.dropLast_append_cons]; simp
      rw [hd] at hh
      exact (List.nodup_append.mp wordNodup).2.2 last hh last (by simp) rfl

  classical
  by_cases heq : last = size
  · subst last
    have hc := RotationAvoidanceEndpoints.fibonacci_extreme_endpoint_count (size - 2)
      (by omega)
    simpa [show size - 2 + 2 = size by omega,
      show size - 2 - 1 = size - 3 by omega] using hc
  have hstrict : last < size := by omega
  simp only [if_neg heq]
  let upperParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (size - last)
    [[2, 1, 3], [4, 1, 3, 2]]
  let middleParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (last - 2)
    [[1, 3, 2], [2, 1, 3]]
  let increasing := List.range' 1 (last - 2)
  let middleDomain := middleParents \ {increasing}
  let domain := upperParents ×ˢ middleDomain
  let target := {word : List ℕ | word.Perm (List.range' 1 size) ∧
    word.head? = some 1 ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 3, 2, 4] (word.rotate cut) ↔ cut = 0}
  let emit := fun pair : List ℕ × List ℕ =>
    1 :: pair.1.map (fun value => last + value) ++ pair.2.map Nat.succ ++ [last]
  let extract := fun word : List ℕ =>
    ((word.filter (fun value => decide (last < value))).map (fun value => value - last),
      (word.filter (fun value => decide (1 < value ∧ value < last))).map (fun value =>
        value - 1))
  have upperMembership (word : List ℕ) : word ∈ upperParents ↔
      word.Perm (List.range' 1 (size - last)) ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ Occurs [4, 1, 3, 2] word := by
    simp [upperParents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have middleMembership (word : List ℕ) : word ∈ middleDomain ↔
      word.Perm (List.range' 1 (last - 2)) ∧ ¬ Occurs [1, 3, 2] word ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ word.Pairwise (· < ·) := by
    have canonical (hp : word.Perm (List.range' 1 (last - 2))) :
        word = increasing ↔ word.Pairwise (· < ·) := by
      have hi : increasing.Pairwise (· < ·) := List.pairwise_lt_range' _ (by omega)
      exact ⟨fun he => he ▸ hi, fun hw => hp.eq_of_pairwise
        (by intro left right hleft hright; omega) hw hi⟩
    simp only [middleDomain, middleParents, Fishburn.FishburnClassicalDefs.classicalAvoiders,
      Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨hp, h132, h213⟩, hn⟩
      exact ⟨hp, h132, h213, fun hi => hn ((canonical hp).mpr hi)⟩
    · rintro ⟨hp, h132, h213, hn⟩
      exact ⟨⟨hp, h132, h213⟩, fun he => hn ((canonical hp).mp he)⟩
  have shift (pattern word : List ℕ) (offset : ℕ)
      (hl : letters pattern = pattern.length) :
      Occurs pattern (word.map (fun value => offset + value)) ↔ Occurs pattern word := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (fun value => offset + value)
      (by intro left right hh; dsimp; omega)
  have succShift (pattern word : List ℕ) (hl : letters pattern = pattern.length) :
      Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
    simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
      funext value; omega] using shift pattern word 1 hl
  have emitMember (pair : List ℕ × List ℕ) (hp : pair ∈ domain) : emit pair ∈ target := by
    obtain ⟨huPerm, hu213, hu4132⟩ := (upperMembership pair.1).mp hp.1
    obtain ⟨hmPerm, hm132, hm213, hmDesc⟩ := (middleMembership pair.2).mp hp.2
    have hu : (pair.1.map (fun value => last + value)).Perm
        (List.range' (last + 1) (size - last)) := by
      simpa only [List.map_add_range'] using huPerm.map (fun value => last + value)
    have hm : (pair.2.map Nat.succ).Perm (List.range' 2 (last - 2)) := by
      simpa only [show Nat.succ = (fun value : ℕ => 1 + value) by funext value; omega,
        List.map_add_range', Nat.reduceAdd] using hmPerm.map Nat.succ
    have hc := construction size last _ _ hlast hbound hu hm
      (fun ho => hu213 ((shift _ _ last rfl).mp ho))
      (fun ho => hu4132 ((shift _ _ last rfl).mp ho))
      (fun ho => hm132 ((succShift _ _ rfl).mp ho))
      (fun ho => hm213 ((succShift _ _ rfl).mp ho))
      (fun hi => hmDesc ((List.pairwise_map.mp hi).imp (by intro left right hh; omega)))
    refine ⟨hc.1, by simp [emit], ?_, hc.2⟩
    · change ((1 :: pair.1.map (fun value => last + value) ++ pair.2.map Nat.succ) ++
        [last]).getLast? = some last
      rw [List.getLast?_append_cons]
      rfl
  have decode (pair : List ℕ × List ℕ) (hp : pair ∈ domain) :
      extract (emit pair) = pair := by
    have huPerm := ((upperMembership pair.1).mp hp.1).1
    have hmPerm := ((middleMembership pair.2).mp hp.2).1
    have huBounds (value : ℕ) (hv : value ∈ pair.1.map (fun value => last + value)) :
        last < value := by
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hv
      have hh := List.mem_range'_1.mp (huPerm.mem_iff.mp ho)
      omega
    have hmBounds (value : ℕ) (hv : value ∈ pair.2.map Nat.succ) :
        1 < value ∧ value < last := by
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hv
      have hh := List.mem_range'_1.mp (hmPerm.mem_iff.mp ho)
      omega
    have upperKeep : (pair.1.map (fun value => last + value)).filter
        (fun value => decide (last < value)) = pair.1.map (fun value => last + value) :=
      List.filter_eq_self.mpr (by intro value hv; simp [huBounds value hv])
    have middleDrop : (pair.2.map Nat.succ).filter
        (fun value => decide (last < value)) = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hh := hmBounds value hv
      simp only [decide_eq_true_eq]; omega)
    have upperDrop : (pair.1.map (fun value => last + value)).filter
        (fun value => decide (1 < value ∧ value < last)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := huBounds value hv
        simp only [decide_eq_true_eq]; omega)
    have middleKeep : (pair.2.map Nat.succ).filter
        (fun value => decide (1 < value ∧ value < last)) = pair.2.map Nat.succ :=
      List.filter_eq_self.mpr (by intro value hv; simp [hmBounds value hv])
    simp only [extract, emit, List.cons_append, List.filter_append, List.filter_cons,
      List.filter_nil, upperKeep, middleKeep, upperDrop, middleDrop,
      show ¬ last < 1 by omega, show ¬ 1 < 1 by omega, show ¬ last < last by omega,
      false_and, and_false, decide_false, Bool.false_eq_true, not_false_eq_true,
      cond_false, if_false, List.nil_append, List.append_nil, List.map_map,
      Function.comp_def, Nat.add_sub_cancel_left, Nat.add_one_sub_one, List.map_id']
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ pair ∈ domain, emit pair = word := by
    obtain ⟨front, hlastWord⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = 1 :: interior ++ [last] := by
      cases front with
      | nil =>
        have hh := hw.1.length_eq
        simp [hlastWord] at hh
        omega
      | cons head interior =>
        have hh : head = 1 := by simpa [hlastWord] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlastWord⟩
    obtain ⟨_, hnormal, huPerm, hmPerm, hu213, hu4132, hm132, hm213, hmDesc⟩ :=
      RotationAvoidanceSeparated.fibonacci_least_endpoint_normal_form size last interior
        (by omega) (hsplit ▸ hw.1) (by simpa only [← hsplit] using hw.2.2.2)
    let upper := interior.filter (fun value => decide (last < value))
    let middle := interior.filter (fun value => decide (value < last))
    let upperParent := upper.map (fun value => value - last)
    let middleParent := middle.map (fun value => value - 1)
    change upper.Perm _ at huPerm
    change middle.Perm _ at hmPerm
    change ¬ Occurs [2, 1, 3] upper at hu213
    change ¬ Occurs [4, 1, 3, 2] upper at hu4132
    change ¬ Occurs [1, 3, 2] middle at hm132
    change ¬ Occurs [2, 1, 3] middle at hm213
    change ¬ middle.Pairwise (· < ·) at hmDesc
    change interior = upper ++ middle at hnormal
    have restoreUpper : upperParent.map (fun value => last + value) = upper := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id upper]
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range'_1.mp (huPerm.mem_iff.mp hv)
      dsimp; omega
    have restoreMiddle : middleParent.map Nat.succ = middle := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id middle]
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range'_1.mp (hmPerm.mem_iff.mp hv)
      dsimp; omega
    have upperParentPerm : upperParent.Perm (List.range' 1 (size - last)) := by
      have hh := huPerm.map (fun value => value - last)
      simpa only [upperParent, List.map_sub_range' (by omega : last ≤ last + 1) (size - last),
        show last + 1 - last = 1 by omega] using hh
    have middleParentPerm : middleParent.Perm (List.range' 1 (last - 2)) := by
      have hr : (List.range' 2 (last - 2)).map (fun value => value - 1) =
          List.range' 1 (last - 2) := List.map_sub_range' (by omega : 1 ≤ 2) (last - 2)
      exact (hmPerm.map (fun value => value - 1)).trans (List.Perm.of_eq hr)
    refine ⟨(upperParent, middleParent), ?_, ?_⟩
    · refine ⟨(upperMembership _).mpr ⟨upperParentPerm, ?_, ?_⟩,
        (middleMembership _).mpr ⟨middleParentPerm, ?_, ?_, ?_⟩⟩
      · intro ho
        exact hu213 (restoreUpper ▸ (shift _ _ last rfl).mpr ho)
      · intro ho
        exact hu4132 (restoreUpper ▸ (shift _ _ last rfl).mpr ho)
      · intro ho
        exact hm132 (restoreMiddle ▸ (succShift _ _ rfl).mpr ho)
      · intro ho
        exact hm213 (restoreMiddle ▸ (succShift _ _ rfl).mpr ho)
      · intro hi
        exact hmDesc (restoreMiddle ▸ List.pairwise_map.mpr
          (hi.imp (by intro left right hh; omega)))
    · simpa only [emit, restoreUpper, restoreMiddle, List.cons_append, List.append_assoc] using
        (hsplit.trans (congrArg (fun tail => 1 :: tail ++ [last]) hnormal)).symm
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun pair _ => emit pair)
    emitMember (fun left right hl hr he => by
      have hh := congrArg extract he
      rwa [decode left hl, decode right hr] at hh) (by
      intro word hw
      obtain ⟨pair, hp, he⟩ := emitSurjective word hw
      exact ⟨pair, hp, he⟩)
  have increasingMember : increasing ∈ middleParents := by
    have hi : increasing.Pairwise (· < ·) := List.pairwise_lt_range' _ (by omega)
    refine ⟨List.Perm.refl _, ?_⟩
    intro pattern hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rintro ⟨chosen, hg, _, hs, _⟩
      have hh := List.pairwise_iff_forall_sublist.mp hi
        (((by decide : [3, 2].Sublist [1, 3, 2]).map chosen).trans hs)
      have ht : chosen 2 < chosen 3 := hg 2 (by omega) (by decide)
      omega
    · rintro ⟨chosen, hg, _, hs, _⟩
      have hh := List.pairwise_iff_forall_sublist.mp hi
        (((by decide : [2, 1].Sublist [2, 1, 3]).map chosen).trans hs)
      have ht : chosen 1 < chosen 2 := hg 1 (by omega) (by decide)
      omega
  have finiteMiddle : middleParents.Finite := by
    apply (List.finite_toSet (List.range' 1 (last - 2)).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  have middleCard : middleDomain.ncard = 2 ^ (last - 3) - 1 := by
    have hh := Set.ncard_sdiff_singleton_add_one increasingMember finiteMiddle
    have hb := RotationAvoidanceFibonacci.skew_block_binary_count (last - 2) (by omega)
    change middleDomain.ncard + 1 = middleParents.ncard at hh
    change middleParents.ncard = _ at hb
    rw [show last - 2 - 1 = last - 3 by omega] at hb
    omega
  have upperCard : upperParents.ncard = Nat.fib (2 * (size - last) - 1) :=
    RotationAvoidanceFibonacci.fibonacci_count (size - last) (by omega)
  change target.ncard = _
  rw [← hcard]
  exact (Set.ncard_prod (s := upperParents) (t := middleDomain)).trans
    (by rw [upperCard, middleCard])

theorem fibonacci_endpoint_extremality (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 3, 2, 4] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    first = 1 ∨ last = size := by
  classical
  let word := first :: interior ++ [last]
  have criterion := (unique_bad_cut_iff size hsize [1, 3, 2, 4] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have build (pattern container : List ℕ) (chosen : ℕ → ℕ)
      (hp : pattern.Perm [1, 2, 3, 4]) (hl : letters pattern = 4)
      (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1))
      (hs : (pattern.map chosen).Sublist container) : Occurs pattern container := by
    refine ⟨chosen, ?_, ?_, hs, by simp⟩
    · simpa only [hl] using hi
    · intro rank hlo hhi
      rw [hl] at hhi
      exact hs.subset (List.mem_map_of_mem (hp.mem_iff.mpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
  obtain ⟨chosen, hg, _, selectedWord, _⟩ := criterion.1
  have hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
    simpa [letters] using hg
  have firstChosen : chosen 1 = first := by
    by_contra hn
    exact criterion.2.2.1 (build _ word.tail chosen (by decide) rfl hi
      (List.Sublist.of_cons_of_ne hn selectedWord))
  have lastChosen : chosen 4 = last := by
    by_contra hn
    have hs : [chosen 4, chosen 2, chosen 3, chosen 1].Sublist
        (last :: interior.reverse ++ [first]) := by simpa [word] using selectedWord.reverse
    have hs := List.Sublist.of_cons_of_ne hn hs
    have ht : ([1, 3, 2, 4].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2 (build _ _ chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let left := chosen 3
  let right := chosen 2
  have rightBound : first < right := by
    simpa [right, firstChosen] using hi 1 (by omega) (by omega)
  have descending : right < left := hi 2 (by omega) (by omega)
  have leftBound : left < last := by
    simpa [left, lastChosen] using hi 3 (by omega) (by omega)
  have selected : [left, right].Sublist interior := by
    have hs : [left, right, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, left, right, firstChosen, lastChosen] using selectedWord
    have hr : (last :: [right, left]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    simpa using (List.cons_sublist_cons.mp hr).reverse
  by_contra hn
  push Not at hn
  have firstBound : 1 < first := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp (by simp [word] : first ∈ word))
    omega
  have lastBound : last < size := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp (by simp [word] : last ∈ word))
    omega
  have lowMember : 1 ∈ interior := by
    have hh := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega : 1 ≤ 1 ∧ 1 < 1 + size))
    simpa [show 1 ≠ first by omega, show 1 ≠ last by omega] using hh
  have highMember : size ∈ interior := by
    have hh := hperm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega : 1 ≤ size ∧ size < 1 + size))
    simpa [show size ≠ first by omega, show size ≠ last by omega] using hh
  have insertThird (container : List ℕ) (extra : ℕ) (hs : [left, right].Sublist container)
      (hm : extra ∈ container) (hneLeft : extra ≠ left) (hneRight : extra ≠ right) :
      [extra, left, right].Sublist container ∨ [left, extra, right].Sublist container ∨
        [left, right, extra].Sublist container := by
    have pairOrder (container : List ℕ) (one two : ℕ)
        (h1 : one ∈ container) (h2 : two ∈ container) (hne : one ≠ two) :
        [one, two].Sublist container ∨ [two, one].Sublist container := by
      induction container with
      | nil => simp at h1
      | cons head tail ih =>
        by_cases he : head = one
        · subst head
          exact Or.inl ((List.singleton_sublist.mpr
            ((List.mem_cons.mp h2).resolve_left (Ne.symm hne))).cons_cons one)
        · by_cases ht : head = two
          · subst head
            exact Or.inr ((List.singleton_sublist.mpr
              ((List.mem_cons.mp h1).resolve_left hne)).cons_cons two)
          · rcases ih ((List.mem_cons.mp h1).resolve_left (Ne.symm he))
              ((List.mem_cons.mp h2).resolve_left (Ne.symm ht)) with hh | hh
            · exact Or.inl (hh.cons head)
            · exact Or.inr (hh.cons head)
    induction container with
    | nil => simp at hs
    | cons head tail ih =>
      by_cases he : head = extra
      · subst head
        exact Or.inl ((List.Sublist.of_cons_of_ne (Ne.symm hneLeft) hs).cons_cons extra)
      · by_cases hl : head = left
        · subst head
          have hm := (List.mem_cons.mp hm).resolve_left hneLeft
          have hr := List.singleton_sublist.mp (List.cons_sublist_cons.mp hs)
          rcases pairOrder tail extra right hm hr hneRight with hh | hh
          · exact Or.inr (Or.inl (hh.cons_cons left))
          · exact Or.inr (Or.inr (hh.cons_cons left))
        · rcases ih (List.Sublist.of_cons_of_ne (Ne.symm hl) hs)
            ((List.mem_cons.mp hm).resolve_left (Ne.symm he)) with hh | hh | hh
          · exact Or.inl (hh.cons head)
          · exact Or.inr (Or.inl (hh.cons head))
          · exact Or.inr (Or.inr (hh.cons head))
  have highBefore : [size, left, right].Sublist interior := by
    rcases insertThird interior size selected highMember (by omega) (by omega) with hs | hs | hs
    · exact hs
    · apply False.elim
      apply criterion.2.1 2 (by omega) (by omega)
      change Occurs [2, 4, 1, 3] word
      let witness := fun rank : ℕ => if rank = 1 then right else if rank = 2 then left
        else if rank = 3 then last else size
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        interval_cases rank <;> simp [witness] <;> omega
      · simpa [witness, word] using (hs.append_right [last]).cons first
    · apply False.elim
      apply criterion.2.2.2
      rw [dropWord]
      let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then right
        else if rank = 3 then left else size
      refine build _ _ witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        interval_cases rank <;> simp [witness] <;> omega
      · simpa [witness] using hs.cons_cons first
  have lowAfter : [left, right, 1].Sublist interior := by
    rcases insertThird interior 1 selected lowMember (by omega) (by omega) with hs | hs | hs
    · apply False.elim
      apply criterion.2.2.1
      let witness := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then right
        else if rank = 3 then left else last
      refine build _ _ witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        interval_cases rank <;> simp [witness] <;> omega
      · simpa [witness, word] using hs.append_right [last]
    · apply False.elim
      apply criterion.2.1 2 (by omega) (by omega)
      change Occurs [2, 4, 1, 3] word
      let witness := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then first
        else if rank = 3 then right else left
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        interval_cases rank <;> simp [witness] <;> omega
      · simpa [witness, word] using
          (hs.trans (List.sublist_append_left interior [last])).cons_cons first
    · exact hs
  have chain (container : List ℕ) (one pivot two : ℕ) (hnd : container.Nodup)
      (hl : [one, pivot].Sublist container) (hr : [pivot, two].Sublist container) :
      [one, pivot, two].Sublist container := by
    induction container with
    | nil => simp at hl
    | cons head tail ih =>
      have ht := (List.nodup_cons.mp hnd).2
      by_cases hh : head = one
      · subst head
        have hne : pivot ≠ one := by
          have hh := hnd.sublist hl
          exact Ne.symm (by simpa using (List.nodup_cons.mp hh).1)
        exact (List.Sublist.of_cons_of_ne hne hr).cons_cons one
      · have hl := List.Sublist.of_cons_of_ne (Ne.symm hh) hl
        have hne : pivot ≠ head := by
          intro heq
          exact (List.nodup_cons.mp hnd).1 (heq ▸ hl.subset (by simp))
        exact (ih ht hl (List.Sublist.of_cons_of_ne hne hr)).cons head
  have interiorNodup : interior.Nodup :=
    ((List.nodup_cons.mp (hperm.nodup_iff.mpr List.nodup_range')).2).sublist
      (List.sublist_append_left _ _)
  have joined := chain interior size left 1 interiorNodup
    ((List.sublist_append_left [size, left] [right]).trans highBefore)
    (((List.sublist_cons_self right [1]).cons_cons left).trans lowAfter)
  have pair : [size, 1].Sublist interior :=
    ((List.sublist_cons_self left [1]).cons_cons size).trans joined
  let witness := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then first
    else if rank = 3 then last else size
  apply criterion.2.1 2 (by omega) (by omega)
  change Occurs [2, 4, 1, 3] word
  refine build _ word witness (by decide) rfl ?_ ?_
  · intro rank hlo hhi
    interval_cases rank <;> simp [witness] <;> omega
  · simpa [witness, word] using (pair.append_right [last]).cons_cons first

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSlices
