/- GID: D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotPaths
   mirror-E: none(waiver:colored-excursion-bijections)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Unique signed primitive excursions reconstruct and reflect arbitrary balanced bridges. -/

import D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotDyck
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotPaths

open D5.S1.Words.Patterns

open D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotDyck
open D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotFibre
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs

theorem bridge_first_return (tail : List DyckStep)
    (balanced : (DyckStep.U :: tail).count DyckStep.U =
      (DyckStep.U :: tail).count DyckStep.D) :
    ∃! pieces : DyckWord × List DyckStep,
      pieces.2.count DyckStep.U = pieces.2.count DyckStep.D ∧
        DyckStep.U :: tail = pieces.1.nest.toList ++ pieces.2 := by
  let word := DyckStep.U :: tail
  have return_exists : ∃ index : ℕ, 0 < index ∧ index ≤ word.length ∧
      (word.take index).count DyckStep.U = (word.take index).count DyckStep.D :=
    ⟨word.length, by simp [word], le_rfl, by
      simpa only [List.take_length] using balanced⟩
  let cutoff := Nat.find return_exists
  have spec : 0 < cutoff ∧ cutoff ≤ word.length ∧
      (word.take cutoff).count DyckStep.U = (word.take cutoff).count DyckStep.D :=
    Nat.find_spec return_exists
  have no_return (index : ℕ) (positive : 0 < index) (small : index < cutoff) :
      (word.take index).count DyckStep.U ≠ (word.take index).count DyckStep.D := by
    intro equal
    exact Nat.find_min return_exists small ⟨positive, by omega, equal⟩
  have nonnegative : ∀ index : ℕ, index ≤ cutoff →
      (word.take index).count DyckStep.D ≤ (word.take index).count DyckStep.U := by
    intro index
    induction index with
    | zero => simp
    | succ index induction =>
      intro bounded
      by_cases final : index + 1 = cutoff
      · rw [final, spec.2.2]
      · have small : index + 1 < cutoff := by omega
        cases index with
        | zero => simp [word]
        | succ index =>
          have preceding := induction (by omega)
          have strict := no_return (index + 1) (by omega) (by omega)
          have location : index + 1 < word.length := by omega
          rw [List.take_succ_eq_append_getElem location, List.count_append,
            List.count_append]
          cases word[index + 1] <;> simp <;> omega
  let path : DyckWord :=
    ⟨word.take cutoff, spec.2.2, fun index => by
      rw [List.take_take]
      exact nonnegative (min index cutoff) (Nat.min_le_right _ _)⟩
  have nested : path.IsNested := by
    constructor
    · intro empty
      have length_eq := congrArg (fun value : DyckWord => value.toList.length) empty
      change (word.take cutoff).length = 0 at length_eq
      rw [List.length_take, Nat.min_eq_left spec.2.1] at length_eq
      omega
    · intro index positive bounded
      change index < (word.take cutoff).length at bounded
      rw [List.length_take, Nat.min_eq_left spec.2.1] at bounded
      change ((word.take cutoff).take index).count DyckStep.D <
        ((word.take cutoff).take index).count DyckStep.U
      rw [List.take_take, Nat.min_eq_left bounded.le]
      have weak := nonnegative index bounded.le
      have different := no_return index positive bounded
      omega
  have suffix_balanced : (word.drop cutoff).count DyckStep.U =
      (word.drop cutoff).count DyckStep.D := by
    have counts := balanced
    change word.count DyckStep.U = word.count DyckStep.D at counts
    rw [← List.take_append_drop cutoff word, List.count_append, List.count_append] at counts
    omega
  have split : word = (path.denest nested).nest.toList ++ word.drop cutoff := by
    rw [DyckWord.nest_denest]
    exact (List.take_append_drop cutoff word).symm
  refine ⟨⟨path.denest nested, word.drop cutoff⟩, ⟨suffix_balanced, split⟩, ?_⟩
  rintro ⟨candidate, suffix⟩ ⟨_, candidate_split⟩
  change word = candidate.nest.toList ++ suffix at candidate_split
  have prefix_length : candidate.nest.toList.length ≤ word.length := by
    rw [candidate_split, List.length_append]
    omega
  have positive_length : 0 < candidate.nest.toList.length := by
    exact List.length_pos_of_ne_nil (DyckWord.toList_ne_nil.mpr DyckWord.nest_ne_zero)
  have candidate_prefix : word.take candidate.nest.toList.length = candidate.nest.toList := by
    rw [candidate_split, List.take_left]
  have minimal : cutoff ≤ candidate.nest.toList.length := by
    apply Nat.find_min' return_exists
    refine ⟨positive_length, prefix_length, ?_⟩
    rw [candidate_prefix]
    exact candidate.nest.count_U_eq_count_D
  have length_equal : candidate.nest.toList.length = cutoff := by
    by_contra different
    have short : cutoff < candidate.nest.toList.length := by omega
    have strict := (DyckWord.IsNested.nest (p := candidate)).2 spec.1 short
    have initial : word.take cutoff = candidate.nest.toList.take cutoff := by
      rw [candidate_split, List.take_append_of_le_length short.le]
    rw [← initial] at strict
    omega
  have same_path : candidate.nest = path := by
    apply DyckWord.ext
    change candidate.nest.toList = word.take cutoff
    rw [← length_equal, candidate_prefix]
  have same_inside : candidate = path.denest nested := by
    have equal := congrArg DyckWord.insidePart same_path
    rw [DyckWord.insidePart_nest] at equal
    have recovered := congrArg DyckWord.insidePart (path.nest_denest nested)
    rw [DyckWord.insidePart_nest] at recovered
    exact equal.trans recovered.symm
  have same_suffix : suffix = word.drop cutoff := by
    rw [candidate_split, ← length_equal, List.drop_left]
  exact Prod.ext same_inside same_suffix

noncomputable def signed_bridge_equiv (size : ℕ) :
    {pieces : List (Bool × DyckWord) //
      (pieces.map (fun piece => piece.2.semilength + 1)).sum = size} ≃
      {word : List DyckStep // word.count DyckStep.U = size ∧
        word.count DyckStep.D = size} := by
  classical
  let flip := Equiv.swap DyckStep.U DyckStep.D
  have flip_twice (step : DyckStep) : flip (flip step) = step := by
    cases step <;> simp [flip]
  have map_twice (word : List DyckStep) : (word.map flip).map flip = word := by
    simp [List.map_map, Function.comp_def, flip_twice]
  have flip_up (word : List DyckStep) :
      (word.map flip).count DyckStep.U = word.count DyckStep.D := by
    simpa only [flip, Equiv.swap_apply_right] using
      List.count_map_of_injective word flip flip.injective DyckStep.D
  have flip_down (word : List DyckStep) :
      (word.map flip).count DyckStep.D = word.count DyckStep.U := by
    simpa only [flip, Equiv.swap_apply_left] using
      List.count_map_of_injective word flip flip.injective DyckStep.U
  let emit (piece : Bool × DyckWord) : List DyckStep :=
    if piece.1 then piece.2.nest.toList.map flip else piece.2.nest.toList
  have emit_length (piece : Bool × DyckWord) :
      (emit piece).length = piece.2.toList.length + 2 := by
    rcases piece with ⟨color, inside⟩
    cases color <;> simp [emit, DyckWord.nest]
  have emit_up (piece : Bool × DyckWord) :
      (emit piece).count DyckStep.U = piece.2.semilength + 1 := by
    rcases piece with ⟨color, inside⟩
    cases color
    · simp only [emit, Bool.false_eq_true, if_false]
      change inside.nest.semilength = inside.semilength + 1
      exact DyckWord.semilength_nest
    · simp only [emit, if_true, flip_up]
      rw [← DyckWord.semilength_eq_count_D, DyckWord.semilength_nest]
  have emit_down (piece : Bool × DyckWord) :
      (emit piece).count DyckStep.D = piece.2.semilength + 1 := by
    rcases piece with ⟨color, inside⟩
    cases color
    · simp only [emit, Bool.false_eq_true, if_false]
      rw [← DyckWord.semilength_eq_count_D, DyckWord.semilength_nest]
    · simp only [emit, if_true, flip_down]
      change inside.nest.semilength = inside.semilength + 1
      exact DyckWord.semilength_nest
  let bridges := {word : List DyckStep // word.count DyckStep.U = word.count DyckStep.D}
  let encode (pieces : List (Bool × DyckWord)) : bridges :=
    ⟨pieces.flatMap emit, by
      induction pieces with
      | nil => rfl
      | cons piece pieces induction =>
        simp only [List.flatMap_cons, List.count_append, emit_up, emit_down, induction]⟩
  have split (word : bridges) (nonempty : word.val ≠ []) :
      ∃! parts : (Bool × DyckWord) × bridges,
        word.val = emit parts.1 ++ parts.2.val := by
    rcases word with ⟨word, balanced⟩
    cases word with
    | nil => exact False.elim (nonempty rfl)
    | cons step tail =>
      cases step with
      | U =>
        obtain ⟨⟨inside, suffix⟩, ⟨suffix_balanced, decomposition⟩, unique⟩ :=
          bridge_first_return tail balanced
        refine ⟨⟨⟨false, inside⟩, ⟨suffix, suffix_balanced⟩⟩, ?_, ?_⟩
        · exact decomposition
        · rintro ⟨⟨color, candidate⟩, rest⟩ candidate_split
          cases color with
          | false =>
            have equal := unique ⟨candidate, rest.val⟩ ⟨rest.property, candidate_split⟩
            exact Prod.ext (Prod.ext rfl (congrArg Prod.fst equal))
              (Subtype.ext (congrArg Prod.snd equal))
          | true =>
            have impossible := congrArg List.head? candidate_split
            simp [emit, DyckWord.nest, flip] at impossible
      | D =>
        have normalized : (DyckStep.U :: tail.map flip).count DyckStep.U =
            (DyckStep.U :: tail.map flip).count DyckStep.D := by
          have equal : (DyckStep.D :: tail).map flip = DyckStep.U :: tail.map flip := by
            simp [flip]
          rw [← equal, flip_up, flip_down]
          exact balanced.symm
        obtain ⟨⟨inside, suffix⟩, ⟨suffix_balanced, decomposition⟩, unique⟩ :=
          bridge_first_return (tail.map flip) normalized
        have original : DyckStep.D :: tail =
            inside.nest.toList.map flip ++ suffix.map flip := by
          have equal := congrArg (List.map flip) decomposition
          simpa only [List.map_cons, flip, Equiv.swap_apply_left, List.map_append,
            map_twice] using equal
        refine ⟨⟨⟨true, inside⟩,
          ⟨suffix.map flip, by rw [flip_up, flip_down]; exact suffix_balanced.symm⟩⟩,
          original, ?_⟩
        rintro ⟨⟨color, candidate⟩, rest⟩ candidate_split
        cases color with
        | false =>
          have impossible := congrArg List.head? candidate_split
          simp [emit, DyckWord.nest] at impossible
        | true =>
          have normalized_split : DyckStep.U :: tail.map flip =
              candidate.nest.toList ++ rest.val.map flip := by
            have equal := congrArg (List.map flip) candidate_split
            simpa only [emit, if_true, List.map_cons, flip, Equiv.swap_apply_right,
              List.map_append, map_twice] using equal
          have equal := unique ⟨candidate, rest.val.map flip⟩
            ⟨by rw [flip_up, flip_down]; exact rest.property.symm, normalized_split⟩
          apply Prod.ext
          · exact Prod.ext rfl (congrArg Prod.fst equal)
          · apply Subtype.ext
            have suffix_equal := congrArg (List.map flip) (congrArg Prod.snd equal)
            simpa only [map_twice] using suffix_equal
  have encoded_nonempty (piece : Bool × DyckWord) (pieces : List (Bool × DyckWord)) :
      (encode (piece :: pieces)).val ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    change (emit piece ++ (encode pieces).val).length = 0 at lengths
    rw [List.length_append, emit_length] at lengths
    omega
  have injective : Function.Injective encode := by
    intro pieces
    induction pieces with
    | nil =>
      intro other equal
      cases other with
      | nil => rfl
      | cons piece pieces =>
        exact False.elim (encoded_nonempty piece pieces (congrArg Subtype.val equal.symm))
    | cons piece pieces induction =>
      intro other equal
      cases other with
      | nil => exact False.elim (encoded_nonempty piece pieces (congrArg Subtype.val equal))
      | cons other_piece other_pieces =>
        obtain ⟨chosen, _, unique⟩ :=
          split (encode (piece :: pieces)) (encoded_nonempty piece pieces)
        have parts_equal : (piece, encode pieces) = (other_piece, encode other_pieces) :=
          (unique (piece, encode pieces) rfl).trans
            (unique (other_piece, encode other_pieces) (congrArg Subtype.val equal)).symm
        exact congrArg₂ List.cons (congrArg Prod.fst parts_equal)
          (induction (congrArg Prod.snd parts_equal))
  have surjective : Function.Surjective encode := by
    suffices onto : ∀ length, ∀ word : bridges, word.val.length = length →
        ∃ pieces, encode pieces = word from fun word => onto word.val.length word rfl
    intro length
    induction length using Nat.strong_induction_on with
    | h length induction =>
      intro word length_eq
      by_cases empty : word.val = []
      · exact ⟨[], Subtype.ext empty.symm⟩
      · obtain ⟨parts, equation, _⟩ := split word empty
        have smaller : parts.2.val.length < length := by
          have lengths := congrArg List.length equation
          change word.val.length = (emit parts.1 ++ parts.2.val).length at lengths
          rw [List.length_append, emit_length] at lengths
          omega
        obtain ⟨pieces, previous⟩ := induction _ smaller parts.2 rfl
        refine ⟨parts.1 :: pieces, ?_⟩
        apply Subtype.ext
        change emit parts.1 ++ (encode pieces).val = word.val
        rw [previous]
        exact equation.symm
  let equivalence : List (Bool × DyckWord) ≃ bridges :=
    Equiv.ofBijective encode ⟨injective, surjective⟩
  have weight : ∀ pieces : List (Bool × DyckWord),
      (encode pieces).val.count DyckStep.U =
        (pieces.map (fun piece => piece.2.semilength + 1)).sum := by
    intro pieces
    induction pieces with
    | nil => rfl
    | cons piece pieces induction =>
      change (emit piece ++ (encode pieces).val).count DyckStep.U = _
      rw [List.count_append, emit_up, induction, List.map_cons, List.sum_cons]
  let restricted : {pieces : List (Bool × DyckWord) //
      (pieces.map (fun piece => piece.2.semilength + 1)).sum = size} ≃
        {word : bridges // word.val.count DyckStep.U = size} :=
    Equiv.subtypeEquiv equivalence (fun pieces => by
      change _ = size ↔ (encode pieces).val.count DyckStep.U = size
      rw [weight pieces])
  let flatten : {word : bridges // word.val.count DyckStep.U = size} ≃
      {word : List DyckStep // word.count DyckStep.U = size ∧
        word.count DyckStep.D = size} :=
    { toFun := fun word => ⟨word.val.val, word.property,
        word.val.property.symm.trans word.property⟩
      invFun := fun word => ⟨⟨word.val, word.property.1.trans word.property.2.symm⟩,
        word.property.1⟩
      left_inv := fun word => rfl
      right_inv := fun word => rfl }
  exact restricted.trans flatten

end D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotPaths
