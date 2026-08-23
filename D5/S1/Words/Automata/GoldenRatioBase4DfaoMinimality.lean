/- GID: D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: D5/E/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.result--json
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: A 21-state DFAO matches the paper machine on every valid word. -/

import Mathlib

/- Provenance: literal transcription of the Walnut 5 and Walnut 8 `FD4`
   tables, followed by native finite checks and a structural word proof. -/

namespace D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality

/-- A total deterministic finite automaton with output and initial state zero. -/
structure DFAO (stateCount : Nat) where
  step : Fin stateCount -> Bool -> Fin stateCount
  output : Fin stateCount -> Fin 4

namespace DFAO

/-- Run a DFAO from an explicitly supplied state. -/
def runFrom {stateCount : Nat} (machine : DFAO stateCount) :
    Fin stateCount -> List Bool -> Fin stateCount
  | state, [] => state
  | state, bit :: rest => runFrom machine (machine.step state bit) rest

/-- Run a DFAO from its initial state zero and read its output. -/
def evaluate {stateCount : Nat} [NeZero stateCount]
    (machine : DFAO stateCount) (word : List Bool) : Fin 4 :=
  machine.output (machine.runFrom 0 word)

end DFAO

/-- A bit may follow the previous bit in a Zeckendorf word exactly when the
two bits are not both one. -/
def LegalNext (previous bit : Bool) : Prop :=
  Not (previous = true ∧ bit = true)

/-- Validity from a preceding bit; this is the no-adjacent-ones rule. -/
def ValidFrom : Bool -> List Bool -> Prop
  | _, [] => True
  | previous, bit :: rest => LegalNext previous bit ∧ ValidFrom bit rest

/-- The valid most-significant-digit-first Zeckendorf words, including words
with leading zeroes. -/
def ValidZeckendorf (word : List Bool) : Prop := ValidFrom false word

private def paperStepZero : Fin 22 -> Fin 22 :=
  ![0, 2, 4, 3, 6, 8, 9, 11, 12, 14, 15, 16, 18, 19, 9, 12, 6, 8, 16, 20, 11, 11]

private def paperStepOne : Fin 22 -> Fin 22 :=
  ![1, 3, 5, 3, 7, 3, 10, 3, 13, 1, 3, 17, 7, 3, 1, 5, 1, 3, 10, 13, 21, 3]

/-- The 22-state `FD4` DFAO emitted by Walnut 5. -/
def paperBase4DFAO : DFAO 22 where
  step state bit := if bit then paperStepOne state else paperStepZero state
  output := ![0, 2, 0, 0, 3, 1, 0, 2, 1, 3, 2, 0, 3, 1, 0, 1, 3, 2, 0, 1, 3, 3]

private def reducedStepZero : Fin 21 -> Fin 21 :=
  ![0, 2, 3, 5, 7, 8, 10, 11, 13, 14, 15, 17, 18, 8, 11, 5, 7, 15, 19, 10, 10]

private def reducedStepOne : Fin 21 -> Fin 21 :=
  ![1, 0, 4, 6, 0, 9, 0, 12, 1, 0, 16, 6, 0, 1, 4, 1, 0, 9, 12, 20, 0]

/-- The 21 live states emitted by modern Walnut, totalized by sending each
forbidden adjacent-one transition to state zero. -/
def reducedBase4DFAO : DFAO 21 where
  step state bit := if bit then reducedStepOne state else reducedStepZero state
  output := ![0, 2, 0, 3, 1, 0, 2, 1, 3, 2, 0, 3, 1, 0, 1, 3, 2, 0, 1, 3, 3]

/-- Embed the 21 live states into the old table by skipping dead state 3. -/
def liftState : Fin 21 -> Fin 22 :=
  ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

/-- The states reached immediately after reading a one on a valid word. -/
def EndsInOne : Fin 21 -> Bool :=
  ![false, true, false, false, true, false, true, false, false, true, false,
    false, true, false, false, false, true, false, false, false, true]

theorem output_compatibility_certificate :
    ∀ state : Fin 21,
      reducedBase4DFAO.output state = paperBase4DFAO.output (liftState state) := by
  intro state
  fin_cases state <;> decide

theorem transition_compatibility_certificate :
    ∀ (state : Fin 21) (previous bit : Bool),
      EndsInOne state = previous -> LegalNext previous bit ->
        liftState (reducedBase4DFAO.step state bit) =
          paperBase4DFAO.step (liftState state) bit := by
  intro state previous bit hstate hlegal
  fin_cases state <;> cases previous <;> cases bit <;>
    simp_all [EndsInOne, LegalNext, liftState, reducedBase4DFAO,
      paperBase4DFAO, reducedStepZero, reducedStepOne, paperStepZero,
      paperStepOne]

theorem terminal_bit_certificate :
    ∀ (state : Fin 21) (previous bit : Bool),
      EndsInOne state = previous -> LegalNext previous bit ->
        EndsInOne (reducedBase4DFAO.step state bit) = bit := by
  intro state previous bit hstate hlegal
  fin_cases state <;> cases previous <;> cases bit <;>
    simp_all [EndsInOne, LegalNext, reducedBase4DFAO, reducedStepZero,
      reducedStepOne]

theorem run_compatibility {state : Fin 21} {previous : Bool}
    (word : List Bool) (hstate : EndsInOne state = previous)
    (hvalid : ValidFrom previous word) :
    liftState (reducedBase4DFAO.runFrom state word) =
      paperBase4DFAO.runFrom (liftState state) word := by
  induction word generalizing state previous with
  | nil => rfl
  | cons bit rest ih =>
      rw [ValidFrom] at hvalid
      rw [DFAO.runFrom, DFAO.runFrom]
      rw [<- transition_compatibility_certificate state previous bit hstate hvalid.1]
      exact ih (terminal_bit_certificate state previous bit hstate hvalid.1) hvalid.2

theorem reduced_agrees_on_valid_words (word : List Bool)
    (hvalid : ValidZeckendorf word) :
    reducedBase4DFAO.evaluate word = paperBase4DFAO.evaluate word := by
  rw [DFAO.evaluate, DFAO.evaluate]
  rw [output_compatibility_certificate]
  have hrun := run_compatibility (state := (0 : Fin 21))
    (previous := false) word (by decide) hvalid
  simpa [liftState] using congrArg paperBase4DFAO.output hrun

theorem reduced_ignores_leading_zeroes (word : List Bool) :
    reducedBase4DFAO.evaluate (false :: word) =
      reducedBase4DFAO.evaluate word := by
  rfl

/-- The paper's 22-state machine is not minimal on valid Zeckendorf inputs:
the modern table supplies an equivalent 21-state total DFAO. -/
theorem paper_base4_golden_ratio_dfao_is_not_minimal :
    ∃ machine : DFAO 21,
      (∀ word : List Bool, ValidZeckendorf word ->
        machine.evaluate word = paperBase4DFAO.evaluate word) ∧
      (∀ word : List Bool,
        machine.evaluate (false :: word) = machine.evaluate word) := by
  exact ⟨reducedBase4DFAO, reduced_agrees_on_valid_words,
    reduced_ignores_leading_zeroes⟩

end D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality
