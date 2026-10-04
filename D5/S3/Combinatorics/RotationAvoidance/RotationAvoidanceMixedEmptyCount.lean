/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount
   mirror-E: none(waiver:zero-lower-mixed-endpoint-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A disjoint shuffle and skew-split construction enumerates zero-lower 1243 slices. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmpty
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmptyCount

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 4096 in
theorem mixed_empty_lower_endpoint_count (size last : ℕ)
    (hgap : 2 < last) (hlast : last < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some 1 ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 2, 4, 3] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = (size - 2).choose (last - 2) + (size - last) - 2 := by
  classical
  let middle := (List.range' 2 (last - 2)).reverse
  let upper := List.range' (last + 1) (size - last)
  let predicate := fun value : ℕ => decide (value < last)
  let shuffles : Set (List ℕ) := {interior | interior.Perm (middle ++ upper) ∧
    interior.filter predicate = middle ∧ interior.filter (fun value => !predicate value) = upper}
  let canonical := upper ++ middle
  let ordinary := shuffles \ {canonical}
  let target := {word : List ℕ | word.Perm (List.range' 1 size) ∧
    word.head? = some 1 ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 2, 4, 3] (word.rotate cut) ↔ cut = 0}
  let emit := fun interior : List ℕ => 1 :: interior ++ [last]
  let exceptional := fun split : ℕ => List.range' (size - split + 1) split ++
    middle ++ List.range' (last + 1) (size - last - split)
  have middleBounds (value : ℕ) (hv : value ∈ middle) : 1 < value ∧ value < last := by
    have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
  have upperBounds (value : ℕ) (hv : value ∈ upper) : last < value ∧ value ≤ size := by
    have hh := List.mem_range'_1.mp hv; omega
  have emitPerm (interior : List ℕ) (hp : interior.Perm (middle ++ upper)) :
      (emit interior).Perm (List.range' 1 size) := by
    have rangeSplit : List.range' 1 size =
        1 :: List.range' 2 (last - 2) ++ last :: upper := by
      rw [show size = (size - 1) + 1 by omega, List.range'_succ]
      simp only [Nat.reduceAdd, Nat.mul_one]
      rw [show size - 1 = (last - 2) + (size - last + 1) by omega,
        ← List.range'_append_1, show 2 + (last - 2) = last by omega, List.range'_succ]
      simp only [upper, List.cons_append]
    have hu : (middle ++ upper ++ [last]).Perm
        (List.range' 2 (last - 2) ++ last :: upper) := by
      have hh := (List.reverse_perm (List.range' 2 (last - 2))).append_right upper
      have move := List.perm_middle (a := last)
        (l₁ := List.range' 2 (last - 2) ++ upper) (l₂ := [])
      have move' := List.perm_middle (a := last) (l₁ := List.range' 2 (last - 2)) (l₂ := upper)
      have moved : (List.range' 2 (last - 2) ++ upper ++ [last]).Perm
          (last :: (List.range' 2 (last - 2) ++ upper)) := by simpa using move
      exact (hh.append_right [last]).trans (moved.trans move'.symm)
    rw [rangeSplit]
    exact ((hp.append_right [last]).trans hu).cons 1
  have interiorBounds (interior : List ℕ) (hp : interior.Perm (middle ++ upper))
      (value : ℕ) (hv : value ∈ interior) :
      (1 < value ∧ value < last) ∨ (last < value ∧ value ≤ size) := by
    rcases List.mem_append.mp (hp.mem_iff.mp hv) with hm | hu
    · exact Or.inl (middleBounds value hm)
    · exact Or.inr (upperBounds value hu)
  have filterUpper (interior : List ℕ) (hp : interior.Perm (middle ++ upper)) :
      interior.filter (fun value => decide (last < value)) =
        interior.filter (fun value => !predicate value) := by
    apply List.filter_congr
    intro value hv
    rcases interiorBounds interior hp value hv with hm | hu
    · simp [predicate, hm.2, show ¬ last < value by omega]
    · simp [predicate, hu.1, show ¬ value < last by omega]
  let bucket := fun threshold value : ℕ => if value ≤ 1 then 0 else if value < last then 1
    else if value = last then 2 else if value < threshold then 3 else 4
  have bucketBound (threshold value : ℕ) : bucket threshold value < 5 := by
    dsimp [bucket]; split_ifs <;> omega
  let color := fun threshold value : ℕ =>
    (⟨bucket threshold value, bucketBound threshold value⟩ : Fin 5)
  let slot := fun (mode : Bool) (shade : Fin 5) => if shade = 0 then 0 else
    if shade = 2 then 4 else if mode then (if shade = 4 then 1 else if shade = 1 then 2 else 3)
    else 2
  let allowed := fun (mode : Bool) (left right : Fin 5) (ascending : Bool) =>
    slot mode left ≤ slot mode right ∧ (left = right →
      (left = 1 ∧ ascending = false) ∨ ((left = 3 ∨ left = 4) ∧ ascending = true))
  let patternColors := fun (left second third right : Fin 5) (index : ℕ) =>
    if index = 1 then left else if index = 2 then second else if index = 3 then third else right
  let fits := fun (mode : Bool) (pattern : List ℕ) (left second third right : Fin 5) =>
    pattern.Pairwise (fun before after =>
      allowed mode (patternColors left second third right before)
        (patternColors left second third right after)
        (@decide (before < after) (Nat.decLt before after)))
  have profiles : ∀ mode : Bool, ∀ left second third right : Fin 5,
      left ≤ second → second ≤ third → third ≤ right →
      (mode = false → right ≠ 4) →
      (fits mode [1, 2, 4, 3] left second third right → left = 0 ∧ third = 2) ∧
      ¬ fits mode [2, 4, 3, 1] left second third right ∧
      ¬ fits mode [4, 3, 1, 2] left second third right ∧
      ¬ fits mode [3, 1, 2, 4] left second third right := by
    simp only [fits, List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
    dsimp only [allowed, patternColors, slot]
    decide
  have construction (interior : List ℕ) (threshold : ℕ) (mode : Bool)
      (hp : interior.Perm (middle ++ upper))
      (hthreshold : mode = false → threshold = size + 1)
      (hallowed : (emit interior).Pairwise (fun left right =>
        allowed mode (color threshold left) (color threshold right) (decide (left < right))))
      (htarget : ∃ low high, [low, high].Sublist interior ∧
        1 < low ∧ low < last ∧ last < high) : emit interior ∈ target := by
    let word := emit interior
    have wordPerm := emitPerm interior hp
    have wordNodup := wordPerm.nodup_iff.mpr List.nodup_range'
    have colorMono (left right : ℕ) (hh : left ≤ right) :
        color threshold left ≤ color threshold right := by
      change bucket threshold left ≤ bucket threshold right
      dsimp [bucket]; split_ifs <;> omega
    have firstEndpoint (value : ℕ) (hv : value ∈ word) (hc : color threshold value = 0) :
        value = 1 := by
      have he := congrArg Fin.val hc
      have hb := List.mem_range'_1.mp (wordPerm.mem_iff.mp hv)
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color threshold value = 2) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have matching (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hpp : pattern.Perm [1, 2, 3, 4]) (hc : container.Sublist word)
        (hs : (pattern.map chosen).Sublist container)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) :
        fits mode pattern (color threshold (chosen 1)) (color threshold (chosen 2))
          (color threshold (chosen 3)) (color threshold (chosen 4)) := by
      have h12 := hi 1 (by omega) (by omega)
      have h23 := hi 2 (by omega) (by omega)
      have h34 := hi 3 (by omega) (by omega)
      simp only [Nat.reduceAdd] at h12 h23 h34
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right ht
      have leftMem := hpp.mem_iff.mp (ht.subset (by simp : left ∈ _))
      have rightMem := hpp.mem_iff.mp (ht.subset (by simp : right ∈ _))
      have leftBound : 1 ≤ left ∧ left ≤ 4 := by simp at leftMem; omega
      have rightBound : 1 ≤ right ∧ right ≤ 4 := by simp at rightMem; omega
      have colorsAt (rank : ℕ) (hb : 1 ≤ rank ∧ rank ≤ 4) :
          patternColors (color threshold (chosen 1)) (color threshold (chosen 2))
            (color threshold (chosen 3)) (color threshold (chosen 4)) rank =
              color threshold (chosen rank) := by
        obtain ⟨hlo, hhi⟩ := hb
        interval_cases rank <;> simp [patternColors]
      have faithful : decide (chosen left < chosen right) = decide (left < right) := by
        obtain ⟨hll, hlh⟩ := leftBound
        obtain ⟨hrl, hrh⟩ := rightBound
        apply Bool.decide_congr
        interval_cases left <;> interval_cases right <;>
          simp only [Nat.reduceLT, iff_false, iff_true] <;> omega
      change allowed mode _ _ _
      rw [colorsAt left leftBound, colorsAt right rightBound, ← faithful]
      exact List.pairwise_iff_forall_sublist.mp hallowed ((ht.map chosen).trans (hs.trans hc))
    have profile (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm [1, 2, 3, 4]) (hc : container.Sublist word)
        (hs : (pattern.map chosen).Sublist container)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) := by
      have rightMem : chosen 4 ∈ word :=
        (hs.trans hc).subset (List.mem_map_of_mem (hp.mem_iff.mpr (by simp)))
      have restricted : mode = false → color threshold (chosen 4) ≠ 4 := by
        intro hm
        have he := hthreshold hm
        have hb := List.mem_range'_1.mp (wordPerm.mem_iff.mp rightMem)
        intro hn
        have hh := congrArg Fin.val hn
        dsimp [color, bucket] at hh
        split_ifs at hh <;> omega
      exact profiles mode (color threshold (chosen 1)) (color threshold (chosen 2))
        (color threshold (chosen 3)) (color threshold (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le) restricted
    have forcedEndpoints (container : List ℕ) (hc : container.Sublist word)
        (ho : Occurs [1, 2, 4, 3] container) : 1 ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hh := (profile _ _ _ (by decide) hc hs hi').1
        (matching _ _ _ (by decide) hc hs hi')
      exact ⟨firstEndpoint _ ((hs.trans hc).subset (by simp)) hh.1 ▸ hs.subset (by simp),
        lastEndpoint _ hh.2 ▸ hs.subset (by simp)⟩
    have targetOccurrence : Occurs [1, 2, 4, 3] word := by
      obtain ⟨low, high, hs, hlo, hlb, hhi⟩ := htarget
      let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then low
        else if rank = 3 then last else high
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hl hr
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp [letters] at hr; omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · intro rank hl hr
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          simp [letters] at hr; omega
        rcases hh with rfl | rfl | rfl | rfl <;>
          simp [word, emit, chosen, hs.subset (by simp : low ∈ _),
            hs.subset (by simp : high ∈ _)]
      · simpa [word, emit, chosen] using (hs.append (List.Sublist.refl [last])).cons_cons 1
    have cuts : ∀ cut < size, Occurs [1, 2, 4, 3] (word.rotate cut) ↔ cut = 0 := by
      apply (unique_bad_cut_iff size (by omega) [1, 2, 4, 3] word (by decide) wordPerm).mpr
      refine ⟨targetOccurrence, ?_, ?_, ?_⟩
      · intro rotation hp hr ho
        obtain ⟨chosen, hi, _, hs, _⟩ := ho
        have hpp : ([1, 2, 4, 3] : List ℕ).rotate rotation |>.Perm [1, 2, 3, 4] :=
          (List.rotate_perm _ _).trans (by decide)
        have hl : letters (([1, 2, 4, 3] : List ℕ).rotate rotation) = 4 := by
          simpa [letters] using hpp.foldr_eq (f := max) 0
        have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
          simpa only [hl] using hi
        have ht := matching _ _ chosen hpp (List.Sublist.refl word) hs hi'
        have hh := (profile _ _ chosen hpp (List.Sublist.refl word) hs hi').2
        interval_cases rotation
        · exact hh.1 ht
        · exact hh.2.1 ht
        · exact hh.2.2 ht
      · intro ho
        exact (List.nodup_cons.mp wordNodup).1
          (forcedEndpoints word.tail (List.tail_sublist word) ho).1
      · intro ho
        have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist word) ho).2
        have he : word.dropLast = 1 :: interior := by
          change ((1 :: interior) ++ [last]).dropLast = _
          rw [List.dropLast_append_cons]; simp
        rw [he] at hh
        rcases List.mem_cons.mp hh with he | hv
        · omega
        · exact (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
            last hv last (by simp) rfl
    exact ⟨wordPerm, by simp [word, emit], by
      change ((1 :: interior) ++ [last]).getLast? = some last
      rw [List.getLast?_append_cons]; rfl, cuts⟩
  have ordinaryMember (interior : List ℕ) (hp : interior ∈ ordinary) :
      emit interior ∈ target := by
    have hmiddle : middle.Pairwise (· > ·) := by
      simpa only [middle, List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := 2) (n := last - 2))
    have hupper : upper.Pairwise (· < ·) := List.pairwise_lt_range'
    have firstColor : color (size + 1) 1 = 0 := by simp [color, bucket]
    have lastColor : color (size + 1) last = 2 := by
      simp [color, bucket, show ¬ last ≤ 1 by omega]
    have paintMiddle (value : ℕ) (hm : 1 < value ∧ value < last) :
        color (size + 1) value = 1 := by simp [color, bucket, show ¬ value ≤ 1 by omega, hm.2]
    have paintUpper (value : ℕ) (hu : last < value ∧ value ≤ size) :
        color (size + 1) value = 3 := by
      simp [color, bucket, show ¬ value ≤ 1 by omega, show ¬ value < last by omega,
        show value ≠ last by omega, show value < size + 1 by omega]
    have insideAllowed : interior.Pairwise (fun left right =>
        allowed false (color (size + 1) left) (color (size + 1) right)
          (decide (left < right))) := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hs
      rcases interiorBounds interior hp.1.1 left (hs.subset (by simp)) with hl | hl <;>
        rcases interiorBounds interior hp.1.1 right (hs.subset (by simp)) with hr | hr
      · have ht : [left, right].Sublist middle := by
          simpa [predicate, hl.2, hr.2, hp.1.2.1] using hs.filter predicate
        have hd := List.pairwise_iff_forall_sublist.mp hmiddle ht
        simp [allowed, slot, paintMiddle left hl, paintMiddle right hr,
          show ¬ left < right by omega]
      · simp [allowed, slot, paintMiddle left hl, paintUpper right hr]
      · simp [allowed, slot, paintUpper left hl, paintMiddle right hr]
      · have ht : [left, right].Sublist upper := by
          simpa [predicate, show ¬ left < last by omega, show ¬ right < last by omega,
            hp.1.2.2] using hs.filter (fun value => !predicate value)
        have hi := List.pairwise_iff_forall_sublist.mp hupper ht
        simp [allowed, slot, paintUpper left hl, paintUpper right hr, hi]
    have allAllowed : (emit interior).Pairwise (fun left right =>
        allowed false (color (size + 1) left) (color (size + 1) right)
          (decide (left < right))) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_append.mpr ⟨insideAllowed, by simp, ?_⟩⟩
      · intro value hv
        rcases List.mem_append.mp hv with hv | hv
        · rcases interiorBounds interior hp.1.1 value hv with hm | hu
          · simp [allowed, slot, firstColor, paintMiddle value hm]
          · simp [allowed, slot, firstColor, paintUpper value hu]
        · have he : value = last := by simpa using hv
          subst value
          simp [allowed, slot, firstColor, lastColor]
      · intro value hv right hr
        have he : right = last := by simpa using hr
        subst right
        rcases interiorBounds interior hp.1.1 value hv with hm | hu
        · simp [allowed, slot, lastColor, paintMiddle value hm]
        · simp [allowed, slot, lastColor, paintUpper value hu]
    have pairExists : ∃ low high, [low, high].Sublist interior ∧
        1 < low ∧ low < last ∧ last < high := by
      by_contra hnone
      push Not at hnone
      have noCross (low high : ℕ) (hs : [low, high].Sublist interior) (hl : low < last) :
          high < last := by
        rcases interiorBounds interior hp.1.1 low (hs.subset (by simp)) with hb | hb
        · rcases interiorBounds interior hp.1.1 high (hs.subset (by simp)) with hh | hh
          · exact hh.2
          · exact False.elim ((not_lt_of_ge (hnone low high hs hb.1 hl)) hh.1)
        · omega
      have separated (selected : List ℕ)
          (hno : ∀ low high, [low, high].Sublist selected → low < last → high < last) :
          selected.filter (fun value => !predicate value) ++ selected.filter predicate =
            selected := by
        induction selected with
        | nil => simp
        | cons head tail ih =>
          have ht := ih (by intro low high hs hl; exact hno _ _ (hs.cons head) hl)
          by_cases hh : head < last
          · have hall : ∀ value ∈ tail, value < last := by
              intro value hv
              exact hno head value ((List.singleton_sublist.mpr hv).cons_cons head) hh
            have htKeep : tail.filter predicate = tail := List.filter_eq_self.mpr
              (by intro value hv; simp [predicate, hall value hv])
            have htDrop : tail.filter (fun value => !predicate value) = [] :=
              List.filter_eq_nil_iff.mpr (by intro value hv; simp [predicate, hall value hv])
            simp [predicate, hh, htKeep, htDrop]
          · simpa [predicate, hh] using congrArg (List.cons head) ht
      have he := separated interior noCross
      rw [hp.1.2.1, hp.1.2.2] at he
      exact hp.2 (Set.mem_singleton_iff.mpr he.symm)
    exact construction interior (size + 1) false hp.1.1 (by intro; rfl) allAllowed pairExists
  have exceptionalPerm (split : ℕ) (hs : 1 ≤ split ∧ split < size - last) :
      (exceptional split).Perm (middle ++ upper) := by
    have hr : List.range' (last + 1) (size - last - split) ++
        List.range' (size - split + 1) split = upper := by
      have hh := List.range'_append_1 (s := last + 1) (m := size - last - split) (n := split)
      have hsum : size - last - split + split = size - last := by omega
      have hstart : last + 1 + (size - last - split) = size - split + 1 := by omega
      simpa only [upper, hsum, hstart] using hh
    have hp : (exceptional split).Perm
        (middle ++ (List.range' (last + 1) (size - last - split) ++
          List.range' (size - split + 1) split)) := by
      simpa only [exceptional, List.append_assoc] using
        (List.perm_append_comm :
          (List.range' (size - split + 1) split ++
            (middle ++ List.range' (last + 1) (size - last - split))).Perm
              ((middle ++ List.range' (last + 1) (size - last - split)) ++
                List.range' (size - split + 1) split))
    simpa only [hr] using hp
  have exceptionalMember (split : ℕ) (hs : 1 ≤ split ∧ split < size - last) :
      emit (exceptional split) ∈ target := by
    let before := List.range' (size - split + 1) split
    let after := List.range' (last + 1) (size - last - split)
    let threshold := size - split + 1
    have beforeBounds (value : ℕ) (hv : value ∈ before) :
        threshold ≤ value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp hv; dsimp [threshold] at *; omega
    have afterBounds (value : ℕ) (hv : value ∈ after) : last < value ∧ value < threshold := by
      have hh := List.mem_range'_1.mp hv; dsimp [threshold] at *; omega
    have firstColor : color threshold 1 = 0 := by simp [color, bucket]
    have lastColor : color threshold last = 2 := by
      simp [color, bucket, show ¬ last ≤ 1 by omega]
    have beforeColor (value : ℕ) (hv : value ∈ before) : color threshold value = 4 := by
      have hh := beforeBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by dsimp [threshold] at hh; omega,
        show ¬ value < last by dsimp [threshold] at hh; omega,
        show value ≠ last by dsimp [threshold] at hh; omega, show ¬ value < threshold by omega]
    have afterColor (value : ℕ) (hv : value ∈ after) : color threshold value = 3 := by
      have hh := afterBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega, show ¬ value < last by omega,
        show value ≠ last by omega, hh.2]
    have middleColor (value : ℕ) (hv : value ∈ middle) : color threshold value = 1 := by
      have hh := middleBounds value hv
      simp [color, bucket, show ¬ value ≤ 1 by omega, hh.2]
    let relation := fun left right : ℕ =>
      allowed true (color threshold left) (color threshold right) (decide (left < right))
    have beforeAllowed : before.Pairwise relation := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hp
      have hh := List.pairwise_iff_forall_sublist.mp
        (List.pairwise_lt_range' (s := size - split + 1) (n := split)) hp
      simp [relation, allowed, slot, beforeColor left (hp.subset (by simp)),
        beforeColor right (hp.subset (by simp)), hh]
    have afterAllowed : after.Pairwise relation := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hp
      have hh := List.pairwise_iff_forall_sublist.mp
        (List.pairwise_lt_range' (s := last + 1) (n := size - last - split)) hp
      simp [relation, allowed, slot, afterColor left (hp.subset (by simp)),
        afterColor right (hp.subset (by simp)), hh]
    have middleAllowed : middle.Pairwise relation := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hp
      have hh := List.pairwise_iff_forall_sublist.mp
        (by simpa only [middle, List.pairwise_reverse] using
          (List.pairwise_lt_range' (s := 2) (n := last - 2)) : middle.Pairwise (· > ·)) hp
      simp [relation, allowed, slot, middleColor left (hp.subset (by simp)),
        middleColor right (hp.subset (by simp)), show ¬ left < right by omega,
        show right ≤ left by omega]
    have allAllowed : (emit (exceptional split)).Pairwise relation := by
      change (1 :: before ++ middle ++ after ++ [last]).Pairwise relation
      simp only [List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact beforeAllowed
        | exact afterAllowed
        | exact middleAllowed
        | (solve | simp [relation, allowed, slot, firstColor, lastColor])
        | (intros; simp [relation, allowed, slot, firstColor, lastColor,
            beforeColor, afterColor, middleColor, *])
    apply construction (exceptional split) threshold true (exceptionalPerm split hs)
      (by simp) allAllowed
    have hm : 2 ∈ middle := List.mem_reverse.mpr (List.mem_range'_1.mpr (by omega))
    have hu : last + 1 ∈ after := List.mem_range'_1.mpr (by omega)
    refine ⟨2, last + 1, ?_, by omega, by omega, by omega⟩
    exact ((List.singleton_sublist.mpr hm).append (List.singleton_sublist.mpr hu)).trans
      (by simpa only [exceptional, before, after, List.append_assoc] using
        List.sublist_append_right before (middle ++ after))
  have ordinaryFinite : ordinary.Finite := by
    apply (List.finite_toSet (middle ++ upper).permutations).subset
    intro interior hi
    exact List.mem_permutations.mpr hi.1.1
  let Domain := ordinary ⊕ Fin (size - last - 1)
  have : Finite ordinary := ordinaryFinite.to_subtype
  let assemble : Domain → target := fun datum => match datum with
    | Sum.inl interior => ⟨emit interior.val, ordinaryMember interior.val interior.property⟩
    | Sum.inr split => ⟨emit (exceptional (split.val + 1)),
        exceptionalMember (split.val + 1) (by have := split.isLt; omega)⟩
  have exceptionalPrefix (split : ℕ) (hs : 1 ≤ split ∧ split < size - last) :
      ((exceptional split).takeWhile (fun value => decide (last < value))).length = split := by
    let before := List.range' (size - split + 1) split
    let after := List.range' (last + 1) (size - last - split)
    have middleNotNil : middle ≠ [] := by
      have hh : 2 ∈ middle := List.mem_reverse.mpr (List.mem_range'_1.mpr (by omega))
      exact List.ne_nil_of_mem hh
    have takePrefix (selected : List ℕ) (hp : ∀ value ∈ selected, last < value) :
        (selected ++ middle ++ after).takeWhile (fun value => decide (last < value)) =
          selected := by
      induction selected with
      | nil =>
        cases hm : middle with
        | nil => exact (middleNotNil hm).elim
        | cons head tail =>
          have hh := middleBounds head (by simp [hm])
          simp [show ¬ last < head by omega]
      | cons head tail ih =>
        have hh := hp head (by simp)
        have ht := ih (by intro value hv; exact hp value (by simp [hv]))
        simpa [hh] using congrArg (head :: ·) ht
    have ht := takePrefix before (by
      intro value hv
      have hh := List.mem_range'_1.mp hv; omega)
    simpa only [exceptional, before, after, List.length_range'] using congrArg List.length ht
  have exceptionalDescent (split : ℕ) (hs : 1 ≤ split ∧ split < size - last) :
      ¬ ((exceptional split).filter (fun value => decide (last < value))).Pairwise (· < ·) := by
    intro hh
    have hp : [size, last + 1].Sublist (exceptional split) := by
      have hb : size ∈ List.range' (size - split + 1) split :=
        List.mem_range'_1.mpr (by omega)
      have ha : last + 1 ∈ List.range' (last + 1) (size - last - split) :=
        List.mem_range'_1.mpr (by omega)
      exact (((List.singleton_sublist.mpr hb).trans (List.sublist_append_left _ middle)).append
        (List.singleton_sublist.mpr ha))
    have hp' : [size, last + 1].Sublist
        ((exceptional split).filter (fun value => decide (last < value))) := by
      simpa [show last < size by omega, show last < last + 1 by omega] using
        hp.filter (fun value => decide (last < value))
    have hi := List.pairwise_iff_forall_sublist.mp hh hp'
    omega
  have emitInjective : Function.Injective emit := by
    intro left right he
    have hh := congrArg List.dropLast he
    change ((1 :: left) ++ [last]).dropLast = ((1 :: right) ++ [last]).dropLast at hh
    simpa only [List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil, List.cons.injEq, true_and] using hh
  have assembleInjective : Function.Injective assemble := by
    intro left right he
    have hv := congrArg Subtype.val he
    cases left with
    | inl left =>
      cases right with
      | inl right =>
        exact congrArg Sum.inl (Subtype.ext (emitInjective hv))
      | inr right =>
        have he := emitInjective hv
        have hsorted :
            (left.val.filter (fun value => decide (last < value))).Pairwise (· < ·) := by
          rw [filterUpper left.val left.property.1.1, left.property.1.2.2]
          exact List.pairwise_lt_range'
        rw [he] at hsorted
        exact False.elim (exceptionalDescent (right.val + 1)
          (by have := right.isLt; omega) hsorted)
    | inr left =>
      cases right with
      | inl right =>
        have he := emitInjective hv
        have hsorted :
            (right.val.filter (fun value => decide (last < value))).Pairwise (· < ·) := by
          rw [filterUpper right.val right.property.1.1, right.property.1.2.2]
          exact List.pairwise_lt_range'
        rw [← he] at hsorted
        exact False.elim (exceptionalDescent (left.val + 1)
          (by have := left.isLt; omega) hsorted)
      | inr right =>
        have he := emitInjective hv
        have hh := congrArg (fun interior =>
          (interior.takeWhile (fun value => decide (last < value))).length) he
        rw [exceptionalPrefix (left.val + 1) (by have := left.isLt; omega),
          exceptionalPrefix (right.val + 1) (by have := right.isLt; omega)] at hh
        exact congrArg Sum.inr (Fin.ext (by omega))
  have assembleSurjective : Function.Surjective assemble := by
    intro word
    have hw := word.property
    obtain ⟨interior, hword⟩ : ∃ interior, word.val = 1 :: interior ++ [last] := by
      cases hh : word.val with
      | nil => simp [target, hh] at hw
      | cons head tail =>
        have he : head = 1 := by simpa [hh] using hw.2.1
        subst head
        have hlen : (1 :: tail).length = size := by simpa [hh] using hw.1.length_eq
        have htail : tail ≠ [] := by intro he; simp [he] at hlen; omega
        have ht : tail.getLast? = some last := by
          cases tail with
          | nil => exact (htail rfl).elim
          | cons head rest => simpa [hh] using hw.2.2.1
        have he : tail = tail.dropLast ++ [last] :=
          (List.dropLast_append_getLast? last (by simp [ht])).symm
        exact ⟨tail.dropLast, by
          simpa only [List.cons_append] using congrArg (1 :: ·) he⟩
    obtain ⟨_, _, hmiddle, hcases⟩ :=
      RotationAvoidanceMixedEmpty.mixed_empty_lower_normal_form size last interior
        (by omega) (by omega) (hword ▸ hw.1)
        (by simpa only [← hword] using hw.2.2.2)
    rcases hcases with ⟨hupper, hne⟩ | ⟨split, hlo, hhi, he⟩
    · have hiPerm : interior.Perm (middle ++ upper) := by
        have hp := hword ▸ hw.1
        have hn := (List.nodup_cons.mp (hp.nodup_iff.mpr List.nodup_range')).2.sublist
          (List.sublist_append_left interior [last])
        have hb : (middle ++ upper).Nodup := List.nodup_append.mpr
          ⟨List.nodup_reverse.mpr List.nodup_range', List.nodup_range', by
            intro left hl right hr he
            have := middleBounds left hl; have := upperBounds right hr; omega⟩
        apply (List.perm_ext_iff_of_nodup hn hb).mpr
        intro value
        have hn1 : 1 ∉ interior := fun hv =>
          (List.nodup_cons.mp (hp.nodup_iff.mpr List.nodup_range')).1
            (List.mem_append_left _ hv)
        have hnb : last ∉ interior := fun hv =>
          (List.nodup_append.mp (List.nodup_cons.mp
            (hp.nodup_iff.mpr List.nodup_range')).2).2.2 last hv last (by simp) rfl
        simp only [middle, upper, List.mem_append, List.mem_reverse, List.mem_range'_1]
        constructor
        · intro hv
          have hh := List.mem_range'_1.mp (hp.mem_iff.mp
            (by simp [hv] : value ∈ 1 :: interior ++ [last]))
          have hne1 : value ≠ 1 := fun he => hn1 (he ▸ hv)
          have hneb : value ≠ last := fun he => hnb (he ▸ hv)
          omega
        · intro hv
          have hh : value ∈ 1 :: interior ++ [last] :=
            hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          simpa [show value ≠ 1 by omega, show value ≠ last by omega] using hh
      have ho : interior ∈ ordinary := by
        refine ⟨⟨hiPerm, hmiddle, ?_⟩, ?_⟩
        · rw [← filterUpper interior hiPerm]; exact hupper
        · exact fun hh => hne (Set.mem_singleton_iff.mp hh)
      refine ⟨Sum.inl ⟨interior, ho⟩, ?_⟩
      apply Subtype.ext
      exact hword.symm
    · let index : Fin (size - last - 1) := ⟨split - 1, by omega⟩
      refine ⟨Sum.inr index, ?_⟩
      apply Subtype.ext
      have hi : index.val + 1 = split := by dsimp [index]; omega
      have he' : exceptional split = interior := by
        simpa only [exceptional, middle] using he.symm
      change emit (exceptional (index.val + 1)) = word.val
      rw [hi, he']
      exact hword.symm
  have canonicalMember : canonical ∈ shuffles := by
    have hmKeep : middle.filter predicate = middle := List.filter_eq_self.mpr
      (by intro value hv; simp [predicate, (middleBounds value hv).2])
    have hmDrop : middle.filter (fun value => !predicate value) = [] :=
      List.filter_eq_nil_iff.mpr (by intro value hv; simp [predicate, (middleBounds value hv).2])
    have huDrop : upper.filter predicate = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv; have := upperBounds value hv; simp [predicate, show ¬ value < last by omega])
    have huKeep : upper.filter (fun value => !predicate value) = upper :=
      List.filter_eq_self.mpr (by
        intro value hv
        have := upperBounds value hv
        simp [predicate, show ¬ value < last by omega])
    exact ⟨List.perm_append_comm, by simp [canonical, List.filter_append, hmKeep, huDrop],
      by simp [canonical, List.filter_append, hmDrop, huKeep]⟩
  have shufflesFinite : shuffles.Finite := by
    apply (List.finite_toSet (middle ++ upper).permutations).subset
    intro interior hi
    exact List.mem_permutations.mpr hi.1
  have shufflesCard : shuffles.ncard = (size - 2).choose (last - 2) := by
    have hh := RotationAvoidanceAscending.shuffle_count predicate middle upper
      (by intro value hv; simp [predicate, (middleBounds value hv).2])
      (by intro value hv
          have := upperBounds value hv
          simp [predicate, show ¬ value < last by omega])
    simpa only [middle, upper, List.length_reverse, List.length_range',
      show last - 2 + (size - last) = size - 2 by omega] using hh
  have ordinaryCard : ordinary.ncard + 1 = (size - 2).choose (last - 2) := by
    exact (Set.ncard_sdiff_singleton_add_one canonicalMember shufflesFinite).trans shufflesCard
  have totalCard : target.ncard = ordinary.ncard + (size - last - 1) := by
    have hc := Nat.card_congr
      (Equiv.ofBijective assemble ⟨assembleInjective, assembleSurjective⟩)
    simpa only [Domain, Nat.card_sum, Nat.card_coe_set_eq, Nat.card_fin] using hc.symm
  change target.ncard = _
  rw [totalCard]
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmptyCount
