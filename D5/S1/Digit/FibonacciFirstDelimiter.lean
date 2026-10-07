/- GID: D5/S1/Digit/FibonacciFirstDelimiter
   generality: I
   mirror-B: D5/B/S1/Digit/FibonacciFirstDelimiter
   mirror-E: none(waiver:exact-word-parsing)
   anchors: []
   utility: none
   digest: Positive canonical Fibonacci words have unique delimiter parses preserving suffixes. -/

import D5.S0.Automata.BinaryZeckendorfBlockSkeletonCore
import D5.S1.Digit.ZeckendorfResidueTransducer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.FibonacciFirstDelimiter

open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S1.Digit.ZeckendorfResidueTransducer

/-- Read return blocks until the first consecutive pair of ones, leaving the
remaining input untouched. An incomplete terminal pair fails. -/
def parseF : List (Fin 2) → Option (List ReturnBlock × List (Fin 2))
  | [] => none
  | digit :: rest =>
      if digit = 0 then
        (parseF rest).map fun result => (.zero :: result.1, result.2)
      else
        match rest with
        | [] => none
        | next :: tail =>
            if next = 0 then
              (parseF tail).map fun result => (.oneZero :: result.1, result.2)
            else
              some ([], tail)

/-- The canonical word of every positive natural number ends in its highest
occupied bit. Appending a terminal one lets the first-delimiter parser recover
its unique return blocks and preserve every following bit. -/
theorem positive_word_first_delimiter (n : Nat) (positive : 0 < n)
    (suffix : List (Fin 2)) :
    ∃! blocks : List ReturnBlock,
      zeckendorfLSDWord (wdigits n) = expand blocks .transient ∧
      parseF (zeckendorfLSDWord (wdigits n) ++ [1] ++ suffix) =
        some (blocks, suffix) := by
  let : Trans (fun a b : Nat => b + 2 ≤ a)
      (fun a b : Nat => b + 2 ≤ a) (fun a b : Nat => b + 2 ≤ a) :=
    ⟨fun _ _ => by omega⟩
  have canonical := (List.isChain_iff_pairwise.mp (wdigits_isCanonical n))
  have separated : ∀ i, i ∈ wdigits n → i + 1 ∉ wdigits n := by
    have all := List.Pairwise.forall_of_forall_of_flip
      (fun x (_ : x ∈ wdigits n) =>
        (Or.inl rfl : x = x ∨ x + 2 ≤ x ∨ x + 2 ≤ x))
      ((List.pairwise_append.mp canonical).1.imp
        (fun {_ _} h => Or.inr (Or.inl h)))
      ((List.pairwise_append.mp canonical).1.imp
        (fun {_ _} h => Or.inr (Or.inr h)))
    intro i hi hj
    have := all hi hj
    rcases this with h | h | h <;> omega
  have factor : ∀ count index : Nat, index + count ∈ wdigits n →
      ∃ blocks, denseBitsFrom (wdigits n) index (count + 1) =
        expand blocks .transient := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
      intro index endpoint
      cases count with
      | zero =>
          refine ⟨[], ?_⟩
          simpa [denseBitsFrom, expand] using endpoint
      | succ count =>
          by_cases occupied : index ∈ wdigits n
          · have nextEmpty := separated index occupied
            cases count with
            | zero =>
                exact False.elim (nextEmpty (by simpa using endpoint))
            | succ count =>
                obtain ⟨blocks, hb⟩ := ih count (by omega) (index + 2)
                  (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using endpoint)
                refine ⟨.oneZero :: blocks, ?_⟩
                simpa [denseBitsFrom, expand, occupied, nextEmpty,
                  Nat.add_assoc] using congrArg (fun w => (1 : Fin 2) :: 0 :: w) hb
          · obtain ⟨blocks, hb⟩ := ih count (by omega) (index + 1)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using endpoint)
            refine ⟨.zero :: blocks, ?_⟩
            simpa [denseBitsFrom, expand, occupied, Nat.add_assoc] using
              congrArg (fun w => (0 : Fin 2) :: w) hb
  have wordFactor : ∃ blocks,
      zeckendorfLSDWord (wdigits n) = expand blocks .transient := by
    cases hdigits : wdigits n with
    | nil =>
        have value := decode_wdigits n
        simp [hdigits] at value
        omega
    | cons largest rest =>
        have low : 2 ≤ largest := by
          exact (List.pairwise_append.mp canonical).2.2 largest
            (by simp [hdigits]) 0 (by simp)
        obtain ⟨blocks, hb⟩ := factor (largest - 2) 2 (by
          simp [Nat.add_sub_of_le low, hdigits])
        refine ⟨blocks, ?_⟩
        simpa [zeckendorfLSDWord, hdigits, show largest - 2 + 1 = largest - 1 by omega]
          using hb
  have scan : ∀ blocks : List ReturnBlock,
      parseF (expand blocks .transient ++ [1] ++ suffix) =
        some (blocks, suffix) := by
    intro blocks
    induction blocks with
    | nil => simp [expand, parseF]
    | cons block blocks ih =>
        have ih' : parseF (expand blocks .transient ++ 1 :: suffix) =
            some (blocks, suffix) := by
          simpa only [List.append_assoc, List.singleton_append] using ih
        cases block with
        | zero =>
            have mapped := congrArg
              (Option.map fun result : List ReturnBlock × List (Fin 2) =>
                (.zero :: result.1, result.2)) ih'
            cases hrest : expand blocks .transient ++ 1 :: suffix <;>
              simpa [expand, parseF, hrest] using mapped
        | oneZero =>
            have mapped := congrArg
              (Option.map fun result : List ReturnBlock × List (Fin 2) =>
                (.oneZero :: result.1, result.2)) ih'
            simpa [expand, parseF] using mapped
  obtain ⟨blocks, hb⟩ := wordFactor
  refine ⟨blocks, ⟨hb, ?_⟩, ?_⟩
  · rw [hb]
    exact scan blocks
  · intro other ho
    have codeEqual : (BlockCode.mk other .transient) =
        (BlockCode.mk blocks .transient) :=
      expandCode_injective (ho.1.symm.trans hb)
    exact congrArg BlockCode.blocks codeEqual

#print axioms parseF
#print axioms positive_word_first_delimiter

end D5.S1.Digit.FibonacciFirstDelimiter
