/- GID: D5/S0/Computability/DescriptionComplexity/TimeBoundedTwoPointPrice
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/TimeBoundedTwoPointPrice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite bounded search constructs incomparable fast-long and short-slow witnesses. -/

import Mathlib

/-!
Library-search and duplication audit (2026-09-05):
* Repository keyword, symbol-variant, digest, generalized-owner, and in-flight searches found
  `XorTransformationTightness` for an untimed incompressibility bound and `LogarithmicMargin`
  for the eventual contrapositive. Neither constructs one timed target family together with both
  endpoint witnesses. No exact or more general theorem was found.
* Pinned Mathlib supplies `Finset.card_image_le`, `Finset.card_eraseNone_le`,
  `Finset.sdiff_nonempty_of_card_lt_card`, and `Nat.find_min'`; they are used directly.
* The source's informal `K^T is computable` is made precise by a total bounded evaluator. The
  diagonal word is the least point outside the finite image of every binary code of length at
  most `length / 2`, so the construction itself is executable finite search.
* To avoid the totalized value `Nat.log 2 1 = 0`, the time budget uses
  `log_2 (timeBound length + 1)`. The source's `O(log length)` is represented by the explicit
  eventual quarter-margin field needed for the short-implies-slow conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.DescriptionComplexity.TimeBoundedTwoPointPrice

/-- A length-indexed binary word, represented by its lexicographic rank. -/
abbrev BitWord (length : Nat) := Fin (2 ^ length)

/-- Binary programs of length at most `cutoff`. -/
abbrev ShortCode (cutoff : Nat) := Sigma fun size : Fin (cutoff + 1) => Fin size.1 -> Fin 2

/-- Turn a bounded dependent binary vector into its ordinary list code. -/
def ShortCode.toList {cutoff : Nat} (code : ShortCode cutoff) : List (Fin 2) :=
  List.ofFn code.2

/-- Outputs reached by codes of length at most half the target length within the supplied
time budget. `eraseNone` removes failed bounded computations. -/
def shortOutputs
    (runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length))
    (wordBudget : Nat -> Nat) (length : Nat) : Finset (BitWord length) :=
  (Finset.univ.image fun code : ShortCode (length / 2) =>
    runWord length code.toList (wordBudget length)).eraseNone

private theorem short_code_card (cutoff : Nat) :
    Fintype.card (ShortCode cutoff) = 2 ^ (cutoff + 1) - 1 := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ]
    have hsum : (∑ i : Fin (cutoff + 1), 2 ^ (i : Nat)) = 2 ^ (cutoff + 1) - 1 := by
      simpa [Fintype.card_sigma] using ih
    rw [show (∑ i : Fin (cutoff + 1), 2 ^ ((i : Nat) + 1)) =
        (∑ i : Fin (cutoff + 1), 2 ^ (i : Nat)) * 2 by
      simp [pow_succ, Finset.sum_mul]]
    rw [hsum, pow_succ]
    have hpow : 0 < 2 ^ (cutoff + 1) := pow_pos (by decide) _
    omega

private theorem short_outputs_card_lt
    (runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length))
    (wordBudget : Nat -> Nat) (length : Nat) (hlength : 2 <= length) :
    (shortOutputs runWord wordBudget length).card < Fintype.card (BitWord length) := by
  have himage :
      ((Finset.univ.image fun code : ShortCode (length / 2) =>
        runWord length code.toList (wordBudget length))).card <=
        Fintype.card (ShortCode (length / 2)) := by
    simpa using (Finset.card_image_le :
      ((Finset.univ.image fun code : ShortCode (length / 2) =>
        runWord length code.toList (wordBudget length))).card <=
          (Finset.univ : Finset (ShortCode (length / 2))).card)
  have herase : (shortOutputs runWord wordBudget length).card <=
      ((Finset.univ.image fun code : ShortCode (length / 2) =>
        runWord length code.toList (wordBudget length))).card := by
    exact Finset.card_eraseNone_le _
  have hexponent : length / 2 + 1 <= length := by omega
  have hpower : 2 ^ (length / 2 + 1) <= 2 ^ length :=
    Nat.pow_le_pow_right (by decide) hexponent
  rw [Fintype.card_fin, short_code_card] at *
  have hpositive : 0 < 2 ^ (length / 2 + 1) := pow_pos (by decide) _
  omega

private theorem diagonal_candidates_nonempty
    (runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length))
    (wordBudget : Nat -> Nat) (length : Nat) (hlength : 2 <= length) :
    ((Finset.univ : Finset (BitWord length)) \ shortOutputs runWord wordBudget length).Nonempty :=
  Finset.sdiff_nonempty_of_card_lt_card
    (short_outputs_card_lt runWord wordBudget length hlength)

/-- The lexicographically first word missed by every half-length bounded computation. For the
two small lengths outside the theorem's range, the family is completed by the zero word. -/
def diagonalWord
    (runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length))
    (wordBudget : Nat -> Nat) (length : Nat) : BitWord length := by
  by_cases hlength : 2 <= length
  · exact (((Finset.univ : Finset (BitWord length)) \
      shortOutputs runWord wordBudget length).min'
        (diagonal_candidates_nonempty runWord wordBudget length hlength))
  · exact 0

private theorem diagonal_word_escapes_short_codes
    (runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length))
    (wordBudget : Nat -> Nat) (length : Nat) (hlength : 2 <= length)
    (code : List (Fin 2)) (hcode : code.length <= length / 2) :
    runWord length code (wordBudget length) ≠ some (diagonalWord runWord wordBudget length) := by
  intro hruns
  let packed : ShortCode (length / 2) :=
    ⟨⟨code.length, Nat.lt_succ_of_le hcode⟩, code.get⟩
  have houtput : diagonalWord runWord wordBudget length ∈
      shortOutputs runWord wordBudget length := by
    rw [shortOutputs, Finset.mem_eraseNone]
    apply Finset.mem_image.mpr
    refine ⟨packed, Finset.mem_univ _, ?_⟩
    simpa [packed, ShortCode.toList] using hruns
  have hcandidate : diagonalWord runWord wordBudget length ∈
      (Finset.univ : Finset (BitWord length)) \
        shortOutputs runWord wordBudget length := by
    simp only [diagonalWord, dif_pos hlength]
    exact Finset.min'_mem _ _
  exact (Finset.mem_sdiff.mp hcandidate).2 houtput

/-- A concrete interface for the source's time-priced witness machine. The bounded evaluators
are total functions. Endpoint codes are data, while `compileFast` is the fixed-overhead
interpreter that turns any description of a fast valid witness into a description of its target
word. -/
structure TimePricedMachine (Witness : Type*) [DecidableEq Witness] where
  timeBound : Nat -> Nat
  witnessBudgetConstant : Nat
  wordBudgetConstant : Nat
  overhead : Nat -> Nat
  marginIndex : Nat
  enumeratorCost : Nat
  runWord : (length : Nat) -> List (Fin 2) -> Nat -> Option (BitWord length)
  runWitness : Nat -> List (Fin 2) -> Nat -> Option Witness
  implements : (length : Nat) -> Witness -> BitWord length -> Prop
  runningTime : Nat -> Witness -> Nat
  encodeWitness : Witness -> List (Fin 2)
  encodeWitness_runs : forall length witness,
    runWitness length (encodeWitness witness) (witnessBudgetConstant * timeBound length) =
      some witness
  time_covers_length : forall length, length <= timeBound length
  compileFast : forall {length witness target witnessCode},
    runWitness length witnessCode (witnessBudgetConstant * timeBound length) = some witness ->
    implements length witness target -> runningTime length witness <= timeBound length ->
    exists wordCode,
      wordCode.length <= witnessCode.length + overhead length /\
      runWord length wordCode
        (wordBudgetConstant * timeBound length * Nat.log 2 (timeBound length + 1)) = some target
  quarter_margin : forall length, marginIndex <= length ->
    length / 4 + overhead length < length / 2
  tableWitness : Nat -> Witness
  tableCode : Nat -> List (Fin 2)
  tableCodeOverhead : Nat -> Nat
  tableCode_runs : forall length,
    runWitness length (tableCode length) (witnessBudgetConstant * timeBound length) =
      some (tableWitness length)
  tableCode_length : forall length, (tableCode length).length <= length + tableCodeOverhead length
  table_implements : forall length,
    implements length (tableWitness length)
      (diagonalWord runWord
        (fun n => wordBudgetConstant * timeBound n * Nat.log 2 (timeBound n + 1)) length)
  table_linear_time : forall length, runningTime length (tableWitness length) <= length
  enumeratorWitness : Nat -> Witness
  enumeratorCode : Nat -> List (Fin 2)
  enumeratorCode_runs : forall length,
    runWitness length (enumeratorCode length) (witnessBudgetConstant * timeBound length) =
      some (enumeratorWitness length)
  enumeratorCode_length : forall length, (enumeratorCode length).length <= enumeratorCost
  enumerator_implements : forall length,
    implements length (enumeratorWitness length)
      (diagonalWord runWord
        (fun n => wordBudgetConstant * timeBound n * Nat.log 2 (timeBound n + 1)) length)
  enumerator_slow : forall length,
    timeBound length < runningTime length (enumeratorWitness length)
  enumerator_quarter : forall length, marginIndex <= length -> enumeratorCost <= length / 4

namespace TimePricedMachine

/-- The source's `B(length) = c_0 * t(length)` witness-description budget. -/
def witnessBudget {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) : Nat :=
  machine.witnessBudgetConstant * machine.timeBound length

/-- The strengthened finite-search budget, with a positive totalized binary logarithm. -/
def wordBudget {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) : Nat :=
  machine.wordBudgetConstant * machine.timeBound length *
    Nat.log 2 (machine.timeBound length + 1)

private theorem witness_cost_exists {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) (witness : Witness) :
    exists cost, exists code : Fin cost -> Fin 2,
      machine.runWitness length (List.ofFn code) (machine.witnessBudget length) =
        some witness :=
  ⟨(machine.encodeWitness witness).length, (machine.encodeWitness witness).get, by
    simpa [witnessBudget] using machine.encodeWitness_runs length witness⟩

/-- The shortest description length of a witness within `B(length)` steps. -/
def boundedWitnessComplexity {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) (witness : Witness) : Nat :=
  Nat.find (witness_cost_exists machine length witness)

private theorem shortest_witness_code {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) (witness : Witness) :
    exists code,
      machine.runWitness length code (machine.witnessBudget length) = some witness /\
        code.length = machine.boundedWitnessComplexity length witness := by
  obtain ⟨code, hruns⟩ := Nat.find_spec (witness_cost_exists machine length witness)
  exact ⟨List.ofFn code, hruns, by simp [boundedWitnessComplexity]⟩

private theorem bounded_witness_complexity_le {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) (length : Nat) (witness : Witness)
    (code : List (Fin 2))
    (hruns : machine.runWitness length code (machine.witnessBudget length) = some witness) :
    machine.boundedWitnessComplexity length witness <= code.length := by
  unfold boundedWitnessComplexity
  apply Nat.find_min'
  exact ⟨code.get, by simpa using hruns⟩

/-- Finite bounded diagonalization gives a uniformly defined target family. Every fast witness
has a half-length price up to the explicit compiler overhead; every eventually quarter-short
witness is slow. The literal table and bounded-code enumerator are concrete witnesses, and at
large lengths their price-time pairs are strictly incomparable. -/
theorem time_bounded_two_point_price_frontier {Witness : Type*} [DecidableEq Witness]
    (machine : TimePricedMachine Witness) :
    (forall length, 2 <= length -> forall code,
      machine.runWord length code (machine.wordBudget length) =
          some (diagonalWord machine.runWord machine.wordBudget length) ->
        length / 2 < code.length) /\
    (forall length, 2 <= length -> forall witness,
      machine.implements length witness
          (diagonalWord machine.runWord machine.wordBudget length) ->
        machine.runningTime length witness <= machine.timeBound length ->
        length / 2 - machine.overhead length <=
          machine.boundedWitnessComplexity length witness) /\
    (forall length, max 2 machine.marginIndex <= length -> forall witness,
      machine.implements length witness
          (diagonalWord machine.runWord machine.wordBudget length) ->
        machine.boundedWitnessComplexity length witness <= length / 4 ->
        machine.timeBound length < machine.runningTime length witness) /\
    (forall length,
      machine.implements length (machine.tableWitness length)
          (diagonalWord machine.runWord machine.wordBudget length) /\
        machine.boundedWitnessComplexity length (machine.tableWitness length) <=
          length + machine.tableCodeOverhead length /\
        machine.runningTime length (machine.tableWitness length) <= length) /\
    (forall length,
      machine.implements length (machine.enumeratorWitness length)
          (diagonalWord machine.runWord machine.wordBudget length) /\
        machine.boundedWitnessComplexity length (machine.enumeratorWitness length) <=
          machine.enumeratorCost /\
        machine.timeBound length < machine.runningTime length (machine.enumeratorWitness length)) /\
    (forall length, max 2 machine.marginIndex <= length ->
      machine.boundedWitnessComplexity length (machine.enumeratorWitness length) <
          machine.boundedWitnessComplexity length (machine.tableWitness length) /\
        machine.runningTime length (machine.tableWitness length) <
          machine.runningTime length (machine.enumeratorWitness length)) := by
  have hescape : forall length, 2 <= length -> forall code,
      machine.runWord length code (machine.wordBudget length) =
          some (diagonalWord machine.runWord machine.wordBudget length) ->
        length / 2 < code.length := by
    intro length hlength code hruns
    by_contra hnot
    exact diagonal_word_escapes_short_codes machine.runWord machine.wordBudget length hlength
      code (Nat.le_of_not_gt hnot) hruns
  have hfastLong : forall length, 2 <= length -> forall witness,
      machine.implements length witness
          (diagonalWord machine.runWord machine.wordBudget length) ->
        machine.runningTime length witness <= machine.timeBound length ->
        length / 2 - machine.overhead length <=
          machine.boundedWitnessComplexity length witness := by
    intro length hlength witness himplements hfast
    obtain ⟨witnessCode, hwitnessRuns, hwitnessLength⟩ :=
      machine.shortest_witness_code length witness
    obtain ⟨wordCode, hwordLength, hwordRuns⟩ :=
      machine.compileFast hwitnessRuns himplements hfast
    have hwordLong := hescape length hlength wordCode hwordRuns
    omega
  have hshortSlow : forall length, max 2 machine.marginIndex <= length -> forall witness,
      machine.implements length witness
          (diagonalWord machine.runWord machine.wordBudget length) ->
        machine.boundedWitnessComplexity length witness <= length / 4 ->
        machine.timeBound length < machine.runningTime length witness := by
    intro length hlength witness himplements hshort
    have htwo : 2 <= length := le_trans (le_max_left _ _) hlength
    have hmarginIndex : machine.marginIndex <= length :=
      le_trans (le_max_right _ _) hlength
    by_contra hnotSlow
    have hfast : machine.runningTime length witness <= machine.timeBound length :=
      Nat.le_of_not_gt hnotSlow
    have hlong := hfastLong length htwo witness himplements hfast
    have hmargin := machine.quarter_margin length hmarginIndex
    omega
  have htable : forall length,
      machine.implements length (machine.tableWitness length)
          (diagonalWord machine.runWord machine.wordBudget length) /\
        machine.boundedWitnessComplexity length (machine.tableWitness length) <=
          length + machine.tableCodeOverhead length /\
        machine.runningTime length (machine.tableWitness length) <= length := by
    intro length
    exact ⟨machine.table_implements length,
      (machine.bounded_witness_complexity_le length (machine.tableWitness length)
        (machine.tableCode length) (machine.tableCode_runs length)).trans
          (machine.tableCode_length length),
      machine.table_linear_time length⟩
  have henumerator : forall length,
      machine.implements length (machine.enumeratorWitness length)
          (diagonalWord machine.runWord machine.wordBudget length) /\
        machine.boundedWitnessComplexity length (machine.enumeratorWitness length) <=
          machine.enumeratorCost /\
        machine.timeBound length <
          machine.runningTime length (machine.enumeratorWitness length) := by
    intro length
    exact ⟨machine.enumerator_implements length,
      (machine.bounded_witness_complexity_le length (machine.enumeratorWitness length)
        (machine.enumeratorCode length) (machine.enumeratorCode_runs length)).trans
          (machine.enumeratorCode_length length),
      machine.enumerator_slow length⟩
  refine ⟨hescape, hfastLong, hshortSlow, htable, henumerator, ?_⟩
  intro length hlength
  have htwo : 2 <= length := le_trans (le_max_left _ _) hlength
  have hmarginIndex : machine.marginIndex <= length :=
    le_trans (le_max_right _ _) hlength
  have htableFast : machine.runningTime length (machine.tableWitness length) <=
      machine.timeBound length :=
    (machine.table_linear_time length).trans (machine.time_covers_length length)
  have htableLong := hfastLong length htwo (machine.tableWitness length)
    (machine.table_implements length) htableFast
  have henumeratorShort := (henumerator length).2.1.trans
    (machine.enumerator_quarter length hmarginIndex)
  have hmargin := machine.quarter_margin length hmarginIndex
  refine ⟨?_, htableFast.trans_lt (henumerator length).2.2⟩
  omega

end TimePricedMachine

#print axioms TimePricedMachine.time_bounded_two_point_price_frontier

end D5.S0.Computability.DescriptionComplexity.TimeBoundedTwoPointPrice
