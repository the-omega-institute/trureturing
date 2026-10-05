/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive
   mirror-E: none(waiver:consecutive-endpoint-shuffle-bijection)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Endpoint slices count the increasing shuffles and five-block words for 2143. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMiddle
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceConsecutive

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceCircular RotationAvoidanceAscending RotationAvoidanceOneAscent
open RotationAvoidanceMiddle

theorem consecutive_shuffle_endpoint_count (lowerCount upperCount : ℕ)
    (hlower : 1 ≤ lowerCount) (hupper : 1 ≤ upperCount) :
    ({word : List ℕ | word.Perm (List.range' 1 (lowerCount + upperCount + 2)) ∧
      word.head? = some (lowerCount + 1) ∧ word.getLast? = some (lowerCount + 2) ∧
      ∀ cut < lowerCount + upperCount + 2,
        Occurs [2, 1, 4, 3] (word.rotate cut) ↔ cut = 0} : Set (List ℕ)).ncard =
      (lowerCount + upperCount).choose lowerCount - 1 := by
  classical
  let lower := List.range' 1 lowerCount
  let upper := List.range' (lowerCount + 3) upperCount
  let first := lowerCount + 1
  let last := lowerCount + 2
  let size := lowerCount + upperCount + 2
  let color := fun value : ℕ => decide (value < first)
  let shuffles : Set (List ℕ) := {interior | interior.Perm (lower ++ upper) ∧
    interior.filter color = lower ∧ interior.filter (fun value => !color value) = upper}
  let canonical := upper ++ lower
  let domain := shuffles \ {canonical}
  let emit := fun interior : List ℕ => first :: interior ++ [last]
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [2, 1, 4, 3] (word.rotate cut) ↔ cut = 0}
  have sizeBound : 4 ≤ size := by dsimp [size]; omega
  have lowerValues (value : ℕ) (hvalue : value ∈ lower) :
      1 ≤ value ∧ value < first := by
    have hh := List.mem_range'.mp hvalue
    dsimp [first]; omega
  have upperValues (value : ℕ) (hvalue : value ∈ upper) : last < value := by
    have hh := List.mem_range'.mp hvalue
    dsimp [last]; omega
  have rangeSplit : List.range' 1 size = lower ++ first :: last :: upper := by
    dsimp [size, lower, upper, first, last]
    rw [show lowerCount + upperCount + 2 = lowerCount + (upperCount + 2) by omega,
      ← List.range'_append (s := 1) (m := lowerCount) (n := upperCount + 2) (step := 1),
      show upperCount + 2 = (upperCount + 1) + 1 by omega,
      List.range'_succ, List.range'_succ]
    simp only [Nat.one_mul, Nat.add_comm 1 lowerCount, Nat.add_assoc, Nat.reduceAdd]
  have canonicalRange : (first :: (lower ++ upper) ++ [last]).Perm (List.range' 1 size) := by
    rw [rangeSplit]
    have hmove : (lower ++ first :: last :: upper).Perm (first :: last :: (lower ++ upper)) :=
      (List.perm_middle (a := first) (l₁ := lower) (l₂ := last :: upper)).trans
        ((List.perm_middle (a := last) (l₁ := lower) (l₂ := upper)).cons first)
    have hlast : (first :: (lower ++ upper) ++ [last]).Perm
        (first :: last :: (lower ++ upper)) := by
      simpa using (List.perm_middle (a := last) (l₁ := lower ++ upper) (l₂ := [])).cons first
    exact hlast.trans hmove.symm
  have emitPerm (interior : List ℕ) (hp : interior.Perm (lower ++ upper)) :
      (emit interior).Perm (List.range' 1 size) :=
    ((hp.append_right [last]).cons first).trans canonicalRange
  have interiorBounds (interior : List ℕ) (hp : interior.Perm (lower ++ upper)) :
      ∀ value ∈ interior, value < first ∨ last < value := by
    intro value hvalue
    rcases List.mem_append.mp (hp.mem_iff.mp hvalue) with hl | hh
    · exact Or.inl (lowerValues _ hl).2
    · exact Or.inr (upperValues _ hh)
  have filterHigh (interior : List ℕ) (hp : interior.Perm (lower ++ upper)) :
      interior.filter (fun value => decide (last < value)) =
        interior.filter (fun value => !color value) := by
    apply List.filter_congr
    intro value hvalue
    rcases interiorBounds interior hp value hvalue with hl | hh
    · have hn : ¬ last < value := by dsimp [first, last] at *; omega
      simp [color, hl, hn]
    · have hn : ¬ value < first := by dsimp [first, last] at *; omega
      simp [color, hh, hn]
  have filterPerm (interior : List ℕ) (hp : interior.Perm (lower ++ upper)) :
      (interior.filter color).Perm lower ∧
        (interior.filter (fun value => !color value)).Perm upper := by
    have hl : lower.filter color = lower := List.filter_eq_self.mpr (by
      intro value hvalue; simp [color, (lowerValues _ hvalue).2])
    have hh : upper.filter color = [] := List.filter_eq_nil_iff.mpr (by
      intro value hvalue
      have := upperValues _ hvalue
      have hn : ¬ value < first := by dsimp [first, last] at *; omega
      simp [color, hn])
    have hln : lower.filter (fun value => !color value) = [] := List.filter_eq_nil_iff.mpr (by
      intro value hvalue; simp [color, (lowerValues _ hvalue).2])
    have hhn : upper.filter (fun value => !color value) = upper := List.filter_eq_self.mpr (by
      intro value hvalue
      have := upperValues _ hvalue
      have hn : ¬ value < first := by dsimp [first, last] at *; omega
      simp [color, hn])
    exact ⟨by simpa [List.filter_append, hl, hh] using hp.filter color,
      by simpa [List.filter_append, hln, hhn] using hp.filter (fun value => !color value)⟩
  have pairExists (interior : List ℕ) (hinterior : interior ∈ domain) :
      ∃ low high, [low, high].Sublist interior ∧ low < first ∧ last < high := by
    by_contra hnone
    push Not at hnone
    have noCross (low high : ℕ) (hs : [low, high].Sublist interior) (hl : low < first) :
        high < first := by
      rcases interiorBounds interior hinterior.1.1 high (hs.subset (by simp)) with hh | hh
      · exact hh
      · have hn := hnone low high hs hl
        omega
    have separated (selected : List ℕ)
        (hno : ∀ low high, [low, high].Sublist selected → low < first → high < first) :
        selected.filter (fun value => !color value) ++ selected.filter color = selected := by
      induction selected with
      | nil => simp
      | cons head tail ih =>
        have htail := ih (by intro low high hs hl; exact hno _ _ (hs.cons head) hl)
        by_cases hhead : head < first
        · have hall : ∀ value ∈ tail, value < first := by
            intro value hvalue
            exact hno head value (List.cons_sublist_cons.mpr
              (List.singleton_sublist.mpr hvalue)) hhead
          have ht : tail.filter color = tail := List.filter_eq_self.mpr (by
            intro value hvalue; simp [color, hall _ hvalue])
          have hn : tail.filter (fun value => !color value) = [] :=
            List.filter_eq_nil_iff.mpr (by intro value hvalue; simp [color, hall _ hvalue])
          simp [color, hhead, ht, hn]
        · simpa [color, hhead] using congrArg (List.cons head) htail
    have heq := separated interior noCross
    rw [hinterior.1.2.1, hinterior.1.2.2] at heq
    exact hinterior.2 (Set.mem_singleton_iff.mpr heq.symm)
  have build (pattern selected : List ℕ) (length : ℕ) (witness : ℕ → ℕ)
      (hp : pattern.Perm (List.range' 1 length)) (hl : letters pattern = length)
      (hi : ∀ rank, 1 ≤ rank → rank < length → witness rank < witness (rank + 1))
      (hs : (pattern.map witness).Sublist selected) : Occurs pattern selected := by
    refine ⟨witness, ?_, ?_, hs, by simp⟩
    · simpa only [hl] using hi
    · intro rank hlo hhi
      rw [hl] at hhi
      exact hs.subset (List.mem_map_of_mem (hp.mem_iff.mpr (by
        simp only [List.mem_range'_1]; omega)))
  have criterion (interior : List ℕ) (hp : interior.Perm (lower ++ upper)) :
      (∀ cut < size, Occurs [2, 1, 4, 3] ((emit interior).rotate cut) ↔ cut = 0) ↔
        interior ∈ domain := by
    have wordPerm := emitPerm interior hp
    have bounds := interiorBounds interior hp
    have hnotFirst : first ∉ interior := by
      intro hh
      rcases bounds first hh with hh | hh <;> dsimp [first, last] at * <;> omega
    have hnotLast : last ∉ interior := by
      intro hh
      rcases bounds last hh with hh | hh <;> dsimp [first, last] at * <;> omega
    have hdrop : (emit interior).dropLast = first :: interior := by
      change ((first :: interior) ++ [last]).dropLast = _
      rw [List.dropLast_append_cons]; simp
    constructor
    · intro hcuts
      obtain ⟨_, hl, hh, low, high, hs, hlo, hhi⟩ :=
        paired_endpoint_color_order size first last interior sizeBound wordPerm hcuts
      have hf := filterPerm interior hp
      have lowerEq : interior.filter color = lower := hf.1.eq_of_pairwise
        (by intro low high hlo hhi; omega) hl (List.pairwise_lt_range' _ (by omega))
      have upperEq : interior.filter (fun value => !color value) = upper := by
        rw [filterHigh interior hp] at hh
        exact hf.2.eq_of_pairwise (by intro low high hlo hhi; omega) hh
          (List.pairwise_lt_range' _ (by omega))
      refine ⟨⟨hp, lowerEq, upperEq⟩, ?_⟩
      intro heq
      have hcanonical : canonical.Pairwise
          (fun left right => left < first → right < first) := by
        apply List.pairwise_append.mpr
        refine ⟨?_, ?_, ?_⟩
        · exact List.pairwise_of_forall_mem_list (by
            intro left hl right hr hlt
            have := upperValues left hl
            dsimp [first, last] at *; omega)
        · exact List.pairwise_of_forall_mem_list (by
            intro left hl right hr hlt; exact (lowerValues right hr).2)
        · intro left hl right hr hlt
          exact (lowerValues right hr).2
      have hh := List.pairwise_iff_forall_sublist.mp hcanonical
        (Set.mem_singleton_iff.mp heq ▸ hs) hlo
      dsimp [first, last] at *; omega
    · intro hinterior
      have lowSorted : (emit interior).filter (fun value => decide (value < first)) |>
          List.Pairwise (· < ·) := by
        have hn : ¬ last < first := by dsimp [first, last]; omega
        simpa [emit, hinterior.1.2.1, color, hn] using
          (List.pairwise_lt_range' 1 (by omega) : lower.Pairwise (· < ·))
      have highSorted : ((emit interior).filter (fun value => decide (last < value))).Pairwise
          (· < ·) := by
        have hn : ¬ last < first := by dsimp [first, last]; omega
        have heq : interior.filter (fun value => decide (last < value)) = upper := by
          rw [filterHigh interior hp, hinterior.1.2.2]
        simpa [emit, heq, hn] using
          (List.pairwise_lt_range' 1 (by omega) : upper.Pairwise (· < ·))
      have inversion (higher smaller : ℕ) (hs : [higher, smaller].Sublist (emit interior))
          (hlt : smaller < higher) : first ≤ higher ∧ smaller ≤ last := by
        constructor
        · by_contra hnot
          have hh := hs.filter (fun value => decide (value < first))
          have hs' : [higher, smaller].Sublist
              ((emit interior).filter (fun value => decide (value < first))) := by
            simpa [show higher < first by omega, show smaller < first by omega] using hh
          have := List.pairwise_iff_forall_sublist.mp lowSorted hs'
          omega
        · by_contra hnot
          have hh := hs.filter (fun value => decide (last < value))
          have hs' : [higher, smaller].Sublist
              ((emit interior).filter (fun value => decide (last < value))) := by
            simpa [show last < higher by omega, show last < smaller by omega] using hh
          have := List.pairwise_iff_forall_sublist.mp highSorted hs'
          omega
      have endpoints (witness : ℕ → ℕ)
          (hi : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1))
          (hs : ([2, 1, 4, 3].map witness).Sublist (emit interior)) :
          witness 2 = first ∧ witness 3 = last := by
        have h12 : witness 1 < witness 2 := hi 1 (by omega) (by omega)
        have h23 : witness 2 < witness 3 := hi 2 (by omega) (by omega)
        have h34 : witness 3 < witness 4 := hi 3 (by omega) (by omega)
        have hlo := inversion _ _
          (((by decide : [2, 1].Sublist [2, 1, 4, 3]).map witness).trans hs) h12
        have hhi := inversion _ _
          (((by decide : [4, 3].Sublist [2, 1, 4, 3]).map witness).trans hs) h34
        dsimp [first, last] at *; omega
      have noTriple (largest middle least : ℕ)
          (hs : [largest, middle, least].Sublist (emit interior))
          (hleft : middle < largest) (hright : least < middle) : False := by
        have hlo := inversion largest middle
          ((by simp : [largest, middle].Sublist [largest, middle, least]).trans hs) hleft
        have hhi := inversion middle least
          ((by simp : [middle, least].Sublist [largest, middle, least]).trans hs) hright
        have hfirstNe : largest ≠ first := by omega
        have hlastNe : least ≠ last := by omega
        have hwithoutFirst : [largest, middle, least].Sublist (interior ++ [last]) :=
          List.Sublist.of_cons_of_ne hfirstNe hs
        have hr : [least, middle, largest].Sublist (last :: interior.reverse) := by
          simpa using hwithoutFirst.reverse
        have hinside : [largest, middle, least].Sublist interior := by
          simpa using (List.Sublist.of_cons_of_ne hlastNe hr).reverse
        have hm := bounds middle (hinside.subset (by simp))
        omega
      apply (unique_bad_cut_iff size sizeBound [2, 1, 4, 3] (emit interior)
        (by decide) wordPerm).mpr
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨low, high, hs, hlo, hhi⟩ := pairExists interior hinterior
        let witness := fun rank : ℕ => if rank = 1 then low else if rank = 2 then first
          else if rank = 3 then last else high
        apply build [2, 1, 4, 3] (emit interior) 4 witness (by decide) rfl
        · intro rank hlow hhigh
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases this with rfl | rfl | rfl
          · simpa [witness] using hlo
          · simp [witness, first, last]
          · simpa [witness] using hhi
        · simpa [emit, witness] using (hs.append (List.Sublist.refl [last])).cons_cons first
      · intro shift hshift hshiftBound
        interval_cases shift
        · rintro ⟨witness, hi, _, hs, _⟩
          have h23 : witness 2 < witness 3 := hi 2 (by omega) (by decide)
          have h34 : witness 3 < witness 4 := hi 3 (by omega) (by decide)
          exact noTriple _ _ _
            (((by decide : [4, 3, 2].Sublist (([2, 1, 4, 3] : List ℕ).rotate 1))).map
              witness |>.trans hs) h34 h23
        · rintro ⟨witness, hi, _, hs, _⟩
          have h23 : witness 2 < witness 3 := hi 2 (by omega) (by decide)
          have h34 : witness 3 < witness 4 := hi 3 (by omega) (by decide)
          exact noTriple _ _ _
            (((by decide : [4, 3, 2].Sublist (([2, 1, 4, 3] : List ℕ).rotate 2))).map
              witness |>.trans hs) h34 h23
        · rintro ⟨witness, hi, _, hs, _⟩
          have h12 : witness 1 < witness 2 := hi 1 (by omega) (by decide)
          have h23 : witness 2 < witness 3 := hi 2 (by omega) (by decide)
          exact noTriple _ _ _
            (((by decide : [3, 2, 1].Sublist (([2, 1, 4, 3] : List ℕ).rotate 3))).map
              witness |>.trans hs) h23 h12
      · rintro ⟨witness, hi, hm, hs, _⟩
        have hwhole : ([2, 1, 4, 3].map witness).Sublist (emit interior) := hs.cons first
        have heq := (endpoints witness hi hwhole).1
        have hmem := hm 2 (by omega) (by decide)
        have hmem' : first ∈ interior ++ [last] := by simpa [emit, heq] using hmem
        rcases List.mem_append.mp hmem' with hh | hh
        · exact hnotFirst hh
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          dsimp [first, last] at hh; omega
      · rintro ⟨witness, hi, hm, hs, _⟩
        have hwhole := hs.trans (List.dropLast_sublist (emit interior))
        have heq := (endpoints witness hi hwhole).2
        have hmem := hm 3 (by omega) (by decide)
        rw [hdrop, heq] at hmem
        rcases List.mem_cons.mp hmem with hh | hh
        · dsimp [first, last] at hh; omega
        · exact hnotLast hh
  have canonicalMember : canonical ∈ shuffles := by
    refine ⟨List.perm_append_comm, ?_, ?_⟩
    · have hh : upper.filter color = [] := List.filter_eq_nil_iff.mpr (by
        intro value hvalue
        have := upperValues _ hvalue
        have hn : ¬ value < first := by dsimp [first, last] at *; omega
        simp [color, hn])
      have hl : lower.filter color = lower := List.filter_eq_self.mpr (by
        intro value hvalue; simp [color, (lowerValues _ hvalue).2])
      simp only [canonical, List.filter_append, hh, hl, List.nil_append]
    · have hl : lower.filter (fun value => !color value) = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro value hvalue; simp [color, (lowerValues _ hvalue).2])
      have hh : upper.filter (fun value => !color value) = upper :=
        List.filter_eq_self.mpr (by
          intro value hvalue
          have := upperValues _ hvalue
          have hn : ¬ value < first := by dsimp [first, last] at *; omega
          simp [color, hn])
      simp only [canonical, List.filter_append, hh, hl, List.append_nil]
  have finiteShuffles : shuffles.Finite := by
    apply (List.finite_toSet (lower ++ upper).permutations).subset
    intro interior hh
    exact List.mem_permutations.mpr hh.1
  have shuffleCount : shuffles.ncard = (lowerCount + upperCount).choose lowerCount := by
    simpa only [shuffles, lower, upper, List.length_range'] using
      shuffle_count color lower upper
        (by intro value hvalue; simp [color, (lowerValues _ hvalue).2])
        (by
          intro value hvalue
          have := upperValues _ hvalue
          have hn : ¬ value < first := by dsimp [first, last] at *; omega
          simp [color, hn])
  have domainCount : domain.ncard = (lowerCount + upperCount).choose lowerCount - 1 := by
    have hh := Set.ncard_sdiff_singleton_add_one canonicalMember finiteShuffles
    change domain.ncard + 1 = shuffles.ncard at hh
    rw [shuffleCount] at hh
    omega
  have emitMember (interior : List ℕ) (hh : interior ∈ domain) : emit interior ∈ target := by
    refine ⟨emitPerm interior hh.1.1, by simp [emit], ?_, (criterion interior hh.1.1).mpr hh⟩
    change ((first :: interior) ++ [last]).getLast? = some last
    rw [List.getLast?_append_cons]; rfl
  have emitInjective : Function.Injective emit := by
    intro left right heq
    exact List.append_cancel_right (List.cons.inj heq).2
  have emitSurjective (word : List ℕ) (hword : word ∈ target) :
      ∃ interior ∈ domain, emit interior = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hword.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases front with
      | nil =>
        have := hword.1.length_eq
        simp [hlast] at this
        omega
      | cons head interior =>
        have hh : head = first := by simpa [hlast] using hword.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    have hp : interior.Perm (lower ++ upper) := by
      have hh := (hsplit ▸ hword.1).trans canonicalRange.symm
      exact (List.perm_append_right_iff _).mp (List.Perm.cons_inv hh)
    refine ⟨interior, (criterion interior hp).mp ?_, hsplit.symm⟩
    simpa only [emit, ← hsplit] using hword.2.2.2
  have hh := Set.ncard_congr (s := domain) (t := target) (fun interior _ => emit interior)
    emitMember (fun left right _ _ heq => emitInjective heq) (by
      intro word hword
      obtain ⟨interior, hmem, heq⟩ := emitSurjective word hword
      exact ⟨interior, hmem, heq⟩)
  exact hh.symm.trans domainCount

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem positive_middle_endpoint_count (size first last : ℕ)
    (hfirst : 2 ≤ first) (hgap : first + 1 < last) (hlast : last < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧ word.head? = some first ∧
      word.getLast? = some last ∧
      ∀ cut < size, Occurs [2, 1, 4, 3] (word.rotate cut) ↔ cut = 0} : Set (List ℕ)).ncard =
        (first - 1) * (size - last) := by
  classical
  let form := fun lowerSplit upperSplit : ℕ =>
    first :: (List.range' (last + 1) upperSplit ++ List.range' 1 lowerSplit ++
      List.range' (first + 1) (last - first - 1) ++
      List.range' (last + upperSplit + 1) (size - last - upperSplit) ++
      List.range' (lowerSplit + 1) (first - 1 - lowerSplit)) ++ [last]
  let emit := fun pair : Fin (first - 1) × Fin (size - last) =>
    form (pair.1.val + 1) pair.2.val
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [2, 1, 4, 3] (word.rotate cut) ↔ cut = 0}
  let beforeMiddle := fun word : List ℕ =>
    word.takeWhile (fun value => decide (value ≠ first + 1))
  let extract := fun word : List ℕ =>
    (((beforeMiddle word).filter (fun value => decide (value < first))).length,
      ((beforeMiddle word).filter (fun value => decide (last < value))).length)
  have middleHead : List.range' (first + 1) (last - first - 1) =
      (first + 1) :: List.range' (first + 2) (last - first - 2) := by
    rw [show last - first - 1 = last - first - 2 + 1 by omega, List.range'_succ]
  have recover (lowerSplit upperSplit : ℕ) (hlower : lowerSplit < first) :
      beforeMiddle (form lowerSplit upperSplit) =
        first :: List.range' (last + 1) upperSplit ++ List.range' 1 lowerSplit := by
    dsimp only [beforeMiddle, form]
    simp only [List.cons_append, List.append_assoc]
    rw [List.takeWhile_cons_of_pos (by simp),
      List.takeWhile_append_of_pos (l₁ := List.range' (last + 1) upperSplit) (by
        intro value hv
        have hb := List.mem_range'_1.mp hv
        simp only [decide_eq_true_eq]; omega),
      List.takeWhile_append_of_pos (l₁ := List.range' 1 lowerSplit) (by
        intro value hv
        have hb := List.mem_range'_1.mp hv
        simp only [decide_eq_true_eq]; omega), middleHead]
    simp
  have decode (lowerSplit upperSplit : ℕ) (hlower : lowerSplit < first) :
      extract (form lowerSplit upperSplit) = (lowerSplit, upperSplit) := by
    have lowUpper : (List.range' (last + 1) upperSplit).filter
        (fun value => decide (value < first)) = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hb := List.mem_range'_1.mp hv
      simp only [decide_eq_true_eq]; omega)
    have lowLower : (List.range' 1 lowerSplit).filter
        (fun value => decide (value < first)) = List.range' 1 lowerSplit :=
      List.filter_eq_self.mpr (by
        intro value hv
        have hb := List.mem_range'_1.mp hv
        simp only [decide_eq_true_eq]; omega)
    have highUpper : (List.range' (last + 1) upperSplit).filter
        (fun value => decide (last < value)) = List.range' (last + 1) upperSplit :=
      List.filter_eq_self.mpr (by
        intro value hv
        have hb := List.mem_range'_1.mp hv
        simp only [decide_eq_true_eq]; omega)
    have highLower : (List.range' 1 lowerSplit).filter
        (fun value => decide (last < value)) = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hb := List.mem_range'_1.mp hv
      simp only [decide_eq_true_eq]; omega)
    simp only [extract, recover lowerSplit upperSplit hlower, List.filter_append,
      List.filter_cons, show ¬ first < first by omega, show ¬ last < first by omega,
      decide_false, Bool.false_eq_true, not_false_eq_true, List.length_range',
      lowUpper, lowLower, highUpper, highLower, List.nil_append, List.append_nil,
      cond_false, if_false]
  have construction (size first last lowerSplit upperSplit : ℕ)
      (hlower : 1 ≤ lowerSplit) (hfirst : lowerSplit < first)
      (hgap : first + 1 < last) (hupper : upperSplit < size - last) :
      let interior := List.range' (last + 1) upperSplit ++ List.range' 1 lowerSplit ++
        List.range' (first + 1) (last - first - 1) ++
        List.range' (last + upperSplit + 1) (size - last - upperSplit) ++
        List.range' (lowerSplit + 1) (first - 1 - lowerSplit)
      (first :: interior ++ [last]).Perm (List.range' 1 size) ∧
        ∀ cut < size,
          Occurs [2, 1, 4, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0 := by
    classical
    dsimp only
    let upperLeft := List.range' (last + 1) upperSplit
    let lowerLeft := List.range' 1 lowerSplit
    let middle := List.range' (first + 1) (last - first - 1)
    let upperRight := List.range' (last + upperSplit + 1) (size - last - upperSplit)
    let lowerRight := List.range' (lowerSplit + 1) (first - 1 - lowerSplit)
    let interior := upperLeft ++ lowerLeft ++ middle ++ upperRight ++ lowerRight
    let word := first :: interior ++ [last]
    let bucket := fun value : ℕ => if value ≤ lowerSplit then 0
      else if value < first then 1 else if value = first then 2
      else if value < last then 3 else if value = last then 4
      else if value ≤ last + upperSplit then 5 else 6
    have bucketBound (value : ℕ) : bucket value < 7 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 7)
    let slot := fun rank : Fin 7 => ([2, 5, 0, 3, 6, 1, 4] : List ℕ)[rank.val]
    let position := fun value : ℕ => slot (color value)
    let ordered := fun left right : ℕ => position left < position right ∨
      (position left = position right ∧ left < right)
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have keyFirst : position first = 0 := by
      simp [position, slot, color, bucket, show ¬ first ≤ lowerSplit by omega]
    have keyLast : position last = 6 := by
      simp [position, slot, color, bucket, show ¬ last ≤ lowerSplit by omega,
        show ¬ last < first by omega, show last ≠ first by omega]
    have keyUpperLeft (value : ℕ) (hv : value ∈ upperLeft) : position value = 1 := by
      have hb := List.mem_range'_1.mp hv
      simp only [position, slot, color, bucket]
      split_ifs <;> norm_num <;> omega
    have keyLowerLeft (value : ℕ) (hv : value ∈ lowerLeft) : position value = 2 := by
      have hb := List.mem_range'_1.mp hv
      simp only [position, slot, color, bucket]
      split_ifs <;> norm_num <;> omega
    have keyMiddle (value : ℕ) (hv : value ∈ middle) : position value = 3 := by
      have hb := List.mem_range'_1.mp hv
      simp only [position, slot, color, bucket]
      split_ifs <;> norm_num <;> omega
    have keyUpperRight (value : ℕ) (hv : value ∈ upperRight) : position value = 4 := by
      have hb := List.mem_range'_1.mp hv
      simp only [position, slot, color, bucket]
      split_ifs <;> norm_num <;> omega
    have keyLowerRight (value : ℕ) (hv : value ∈ lowerRight) : position value = 5 := by
      have hb := List.mem_range'_1.mp hv
      simp only [position, slot, color, bucket]
      split_ifs <;> norm_num <;> omega
    have rangeOrdered (start count rank : ℕ)
        (hk : ∀ value ∈ List.range' start count, position value = rank) :
        (List.range' start count).Pairwise ordered := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hs
      have hl := hk left (hs.subset (by simp))
      have hr := hk right (hs.subset (by simp))
      refine Or.inr ⟨by omega, ?_⟩
      exact List.pairwise_iff_forall_sublist.mp
        (List.pairwise_lt_range' (s := start) (n := count)) hs
    have orderedUpperLeft := rangeOrdered _ _ 1 keyUpperLeft
    have orderedLowerLeft := rangeOrdered _ _ 2 keyLowerLeft
    have orderedMiddle := rangeOrdered _ _ 3 keyMiddle
    have orderedUpperRight := rangeOrdered _ _ 4 keyUpperRight
    have orderedLowerRight := rangeOrdered _ _ 5 keyLowerRight
    have orderedWord : word.Pairwise ordered := by
      simp only [word, interior, List.cons_append, List.pairwise_cons,
        List.pairwise_append, List.pairwise_singleton, List.Pairwise.nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_singleton,
        or_false, forall_eq, forall_false, or_imp, forall_and, and_true]
      and_intros
      all_goals first
        | exact orderedUpperLeft
        | exact orderedLowerLeft
        | exact orderedMiddle
        | exact orderedUpperRight
        | exact orderedLowerRight
        | (intros; simp_all only [ordered, keyFirst, keyLast, keyUpperLeft,
            keyLowerLeft, keyMiddle, keyUpperRight, keyLowerRight] <;> omega)
    have wordNodup : word.Nodup := orderedWord.imp (by
      intro left right hh heq
      subst right
      rcases hh with hh | hh <;> omega)
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      simp only [word, interior, upperLeft, lowerLeft, middle, upperRight, lowerRight,
        List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, List.mem_range'_1]
      omega
    have finiteProfiles : ∀ lower firstRank lastRank upper : Fin 7,
        lower ≤ firstRank → firstRank ≤ lastRank → lastRank ≤ upper →
        ((slot firstRank < slot lower ∧ slot lower ≤ slot upper ∧
            slot upper < slot lastRank) →
          firstRank = 2 ∧ lastRank = 4) ∧
        ¬ ((slot lower ≤ slot upper ∧ slot upper < slot lastRank ∧
            slot lastRank < slot firstRank) ∨
          (slot upper < slot lastRank ∧ slot lastRank < slot firstRank ∧
            slot firstRank < slot lower) ∨
          (slot lastRank < slot firstRank ∧ slot firstRank < slot lower ∧
            slot lower ≤ slot upper)) := by decide
    have endpointColor (value : ℕ) :
        (color value = 2 → value = first) ∧ (color value = 4 → value = last) := by
      constructor <;> intro hh <;> have hv := congrArg Fin.val hh <;>
        dsimp [color, bucket] at hv <;> split_ifs at hv <;> omega
    have profile (witness : ℕ → ℕ)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1)) :=
      finiteProfiles (color (witness 1)) (color (witness 2))
        (color (witness 3)) (color (witness 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
    have edge (pattern container : List ℕ) (witness : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map witness).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) :
        position (witness left) ≤ position (witness right) ∧
          (witness right < witness left → position (witness left) < position (witness right)) := by
      have hh := List.pairwise_iff_forall_sublist.mp orderedWord
        ((hr.map witness).trans (hs.trans hcontainer))
      rcases hh with hh | hh
      · exact ⟨hh.le, fun _ => hh⟩
      · exact ⟨hh.1.le, fun hn => by omega⟩
    have forcedEndpoints (container : List ℕ) (hsub : container.Sublist word)
        (ho : Occurs [2, 1, 4, 3] container) : first ∈ container ∧ last ∈ container := by
      obtain ⟨witness, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1) := by
        simpa [letters] using hi
      have he21 := edge _ _ _ hsub hs 2 1 (by decide)
      have he14 := edge _ _ _ hsub hs 1 4 (by decide)
      have he43 := edge _ _ _ hsub hs 4 3 (by decide)
      have hp := (profile witness hi').1
        ⟨he21.2 (hi' 1 (by omega) (by omega)), he14.1,
          he43.2 (hi' 3 (by omega) (by omega))⟩
      have hfirstEndpoint := (endpointColor _).1 hp.1
      have hlastEndpoint := (endpointColor _).2 hp.2
      constructor
      · rw [← hfirstEndpoint]; exact hs.subset (by simp)
      · rw [← hlastEndpoint]; exact hs.subset (by simp)
    have noRotated (shift : ℕ) (hshift : 0 < shift) (hbound : shift < 4) :
        ¬ Occurs ([2, 1, 4, 3].rotate shift) word := by
      intro ho
      obtain ⟨witness, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1) := by
        have hp := (List.rotate_perm [2, 1, 4, 3] shift).trans
          (by decide : ([2, 1, 4, 3] : List ℕ).Perm [1, 2, 3, 4])
        have hl : letters (([2, 1, 4, 3] : List ℕ).rotate shift) = 4 := by
          simpa [letters] using hp.foldr_eq (f := max) 0
        simpa only [hl] using hi
      have forbidden := (profile witness hi').2
      have edge' := edge _ _ _ (List.Sublist.refl word) hs
      have h12 := hi' 1 (by omega) (by omega)
      have h23 := hi' 2 (by omega) (by omega)
      have h34 := hi' 3 (by omega) (by omega)
      interval_cases shift
      · apply forbidden; left
        exact ⟨(edge' 1 4 (by decide)).1, (edge' 4 3 (by decide)).2 h34,
          (edge' 3 2 (by decide)).2 h23⟩
      · apply forbidden; right; left
        exact ⟨(edge' 4 3 (by decide)).2 h34, (edge' 3 2 (by decide)).2 h23,
          (edge' 2 1 (by decide)).2 h12⟩
      · apply forbidden; right; right
        exact ⟨(edge' 3 2 (by decide)).2 h23, (edge' 2 1 (by decide)).2 h12,
          (edge' 1 4 (by decide)).1⟩
    have targetOccurrence : Occurs [2, 1, 4, 3] word := by
      let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then first
        else if rank = 3 then last else last + upperSplit + 1
      have lowMem : 1 ∈ lowerLeft := List.mem_range'_1.mpr (by omega)
      have highMem : last + upperSplit + 1 ∈ upperRight :=
        List.mem_range'_1.mpr (by omega)
      have hs : [1, last + upperSplit + 1].Sublist interior := by
        simpa only [interior, List.append_assoc, List.cons_append, List.nil_append] using
          ((List.singleton_sublist.mpr lowMem).append
          ((List.singleton_sublist.mpr highMem).trans
            (List.sublist_append_right middle upperRight))).trans
          ((List.sublist_append_right upperLeft _).trans
            (List.sublist_append_left _ lowerRight))
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp [letters] at hhi; omega
        rcases hr with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · intro rank hlo hhi
        have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          simp [letters] at hhi; omega
        rcases hr with rfl | rfl | rfl | rfl <;> simp [chosen, word, interior,
          List.mem_append, lowMem, highMem]
      · simpa [chosen, word] using (hs.append (List.Sublist.refl [last])).cons_cons first
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [2, 1, 4, 3] word
      (by decide) wordPerm).mpr ⟨targetOccurrence, noRotated, ?_, ?_⟩⟩
    · intro ho
      have hh := (forcedEndpoints word.tail (List.tail_sublist word) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hh
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist word) ho).2
      have hdrop : word.dropLast = first :: interior := by
        change ((first :: interior) ++ [last]).dropLast = _
        rw [List.dropLast_append_cons]; simp
      rw [hdrop] at hh
      exact (List.nodup_append.mp wordNodup).2.2 last hh last (by simp) rfl
  have emitMember (pair : Fin (first - 1) × Fin (size - last)) : emit pair ∈ target := by
    have hp := construction size first last
      (pair.1.val + 1) pair.2.val (by omega) (by have := pair.1.isLt; omega)
      hgap pair.2.isLt
    refine ⟨hp.1, ?_, ?_, hp.2⟩
    · simp [emit, form]
    · dsimp [emit, form]
      rw [← List.cons_append, List.getLast?_append_cons]
      rfl
  have emitInjective : Function.Injective emit := by
    intro left right heq
    have hh := congrArg extract heq
    change extract (form (left.1.val + 1) left.2.val) =
      extract (form (right.1.val + 1) right.2.val) at hh
    rw [decode _ _ (by have := left.1.isLt; omega),
      decode _ _ (by have := right.1.isLt; omega)] at hh
    have hl := congrArg Prod.fst hh
    have hr := congrArg Prod.snd hh
    exact Prod.ext (Fin.ext (by simpa using hl)) (Fin.ext hr)
  have emitSurjective (word : List ℕ) (hword : word ∈ target) :
      ∃ pair : Fin (first - 1) × Fin (size - last), emit pair = word := by
    obtain ⟨front, hlastWord⟩ := List.getLast?_eq_some_iff.mp hword.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases front with
      | nil =>
        have hh := hword.1.length_eq
        simp [hlastWord] at hh
        omega
      | cons head interior =>
        have hh : head = first := by simpa [hlastWord] using hword.2.1
        exact ⟨interior, by simpa [hh] using hlastWord⟩
    obtain ⟨lowerSplit, upperSplit, hlower, hlowerBound, hupper, hnormal⟩ :=
      paired_endpoint_middle_normal_form size first last interior (by omega) hgap
        (hsplit ▸ hword.1) (by simpa only [← hsplit] using hword.2.2.2)
    let pair : Fin (first - 1) × Fin (size - last) :=
      (⟨lowerSplit - 1, by omega⟩, ⟨upperSplit, hupper⟩)
    refine ⟨pair, ?_⟩
    dsimp only [emit, pair, form]
    rw [show lowerSplit - 1 + 1 = lowerSplit by omega, hsplit, hnormal]
  have hh := Set.ncard_congr (s := (Set.univ : Set (Fin (first - 1) × Fin (size - last))))
    (t := target) (fun pair _ => emit pair) (fun pair _ => emitMember pair)
    (fun left right _ _ heq => emitInjective heq) (by
      intro word hword
      obtain ⟨pair, heq⟩ := emitSurjective word hword
      exact ⟨pair, Set.mem_univ _, heq⟩)
  exact hh.symm.trans (by simp)

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceConsecutive
