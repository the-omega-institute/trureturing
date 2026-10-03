/- GID: D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: D5/E/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.result--json
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: A rule-admissible 21-live-state partial DFAO refutes 22-state minimality. -/

import Mathlib

/- Provenance: literal transcription of the Walnut 5 and Walnut 8 `FD4`
   tables, followed by finite rule certificates and a structural word proof. -/

namespace D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality

/-- A total DFAO, used for the paper's 22-state Walnut table. -/
structure DFAO (stateCount : Nat) where
  step : Fin stateCount -> Bool -> Fin stateCount
  output : Fin stateCount -> Fin 4

namespace DFAO

def runFrom {stateCount : Nat} (machine : DFAO stateCount) :
    Fin stateCount -> List Bool -> Fin stateCount
  | state, [] => state
  | state, bit :: rest => runFrom machine (machine.step state bit) rest

def evaluate {stateCount : Nat} [NeZero stateCount]
    (machine : DFAO stateCount) (word : List Bool) : Fin 4 :=
  machine.output (machine.runFrom 0 word)

end DFAO

/-- A DFAO whose missing transitions enter the paper's implicit virtual dead
state. Only the live states are counted. -/
structure PartialDFAO (liveStateCount : Nat) where
  step : Fin liveStateCount -> Bool -> Option (Fin liveStateCount)
  output : Fin liveStateCount -> Fin 4

namespace PartialDFAO

def runFrom {liveStateCount : Nat} (machine : PartialDFAO liveStateCount) :
    Fin liveStateCount -> List Bool -> Option (Fin liveStateCount)
  | state, [] => some state
  | state, bit :: rest =>
      (machine.step state bit).bind fun next => machine.runFrom next rest

def evaluate {liveStateCount : Nat} [NeZero liveStateCount]
    (machine : PartialDFAO liveStateCount) (word : List Bool) : Option (Fin 4) :=
  (machine.runFrom 0 word).map machine.output

end PartialDFAO

/-- A bit may follow the previous bit exactly when the pair is not `11`. -/
def LegalNext (previous bit : Bool) : Prop :=
  Not (previous = true ∧ bit = true)

/-- Zeckendorf validity from a preceding bit. -/
def ValidFrom : Bool -> List Bool -> Prop
  | _, [] => True
  | previous, bit :: rest => LegalNext previous bit ∧ ValidFrom bit rest

/-- All admissible most-significant-digit-first Zeckendorf encodings, with
arbitrarily many leading zeroes. -/
def ValidZeckendorf (word : List Bool) : Prop := ValidFrom false word

/-- Equivalence is agreement on every admissible Zeckendorf encoding. The
partial machine must remain live throughout each such input. -/
def EquivalentOnAdmissibleEncodings {liveStateCount paperStateCount : Nat}
    [NeZero liveStateCount] [NeZero paperStateCount]
    (candidate : PartialDFAO liveStateCount) (paper : DFAO paperStateCount) : Prop :=
  forall word : List Bool, ValidZeckendorf word ->
    candidate.evaluate word = some (paper.evaluate word)

/-- The metallic-mean Ostrowski transition rules with the dead state virtual:
zero remains defined, no live state has a one-self-loop, and a second one is
undefined after every defined one-transition. -/
structure ObeysZeckendorfOstrowskiRules {liveStateCount : Nat}
    (machine : PartialDFAO liveStateCount) : Prop where
  zeroTransitionDefined : forall state, exists next,
    machine.step state false = some next
  noLiveOneSelfLoop : forall state next,
    machine.step state true = some next -> next != state
  consecutiveOneToVirtualDead : forall state next,
    machine.step state true = some next -> machine.step next true = none

/-- A candidate in the paper's original domain, including the convention that
leading zeroes cannot affect the result. -/
structure AdmissibleDFAO (liveStateCount : Nat) [NeZero liveStateCount] where
  machine : PartialDFAO liveStateCount
  ignoresLeadingZeroes : forall word : List Bool,
    machine.evaluate (false :: word) = machine.evaluate word
  ostrowski : ObeysZeckendorfOstrowskiRules machine

private def paperStepZero : Fin 22 -> Fin 22 :=
  ![0, 2, 4, 3, 6, 8, 9, 11, 12, 14, 15, 16, 18, 19, 9, 12, 6, 8, 16, 20, 11, 11]

private def paperStepOne : Fin 22 -> Fin 22 :=
  ![1, 3, 5, 3, 7, 3, 10, 3, 13, 1, 3, 17, 7, 3, 1, 5, 1, 3, 10, 13, 21, 3]

/-- The 22-state `FD4` table emitted by Walnut 5. -/
def paperBase4DFAO : DFAO 22 where
  step state bit := if bit then paperStepOne state else paperStepZero state
  output := ![0, 2, 0, 0, 3, 1, 0, 2, 1, 3, 2, 0, 3, 1, 0, 1, 3, 2, 0, 1, 3, 3]

private def reducedStepZero : Fin 21 -> Fin 21 :=
  ![0, 2, 3, 5, 7, 8, 10, 11, 13, 14, 15, 17, 18, 8, 11, 5, 7, 15, 19, 10, 10]

private def reducedStepOne : Fin 21 -> Option (Fin 21) :=
  ![some 1, none, some 4, some 6, none, some 9, none, some 12, some 1,
    none, some 16, some 6, none, some 1, some 4, some 1, none, some 9,
    some 12, some 20, none]

/-- The 21 live states emitted by modern Walnut. The seven forbidden
second-consecutive-one transitions are absent, not totalized. -/
def reducedBase4DFAO : PartialDFAO 21 where
  step state bit := if bit then reducedStepOne state else some (reducedStepZero state)
  output := ![0, 2, 0, 3, 1, 0, 2, 1, 3, 2, 0, 3, 1, 0, 1, 3, 2, 0, 1, 3, 3]

/-- Embed the 21 live states into the old table by skipping dead state 3. -/
def liftState : Fin 21 -> Fin 22 :=
  ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

/-- The states reached immediately after reading a one on a valid word. -/
def EndsInOne : Fin 21 -> Bool :=
  ![false, true, false, false, true, false, true, false, false, true, false,
    false, true, false, false, false, true, false, false, false, true]

theorem output_compatibility_certificate : forall state : Fin 21,
    reducedBase4DFAO.output state = paperBase4DFAO.output (liftState state) := by
  intro state
  fin_cases state <;> decide

/-- Every legal next bit has a defined reduced transition matching the paper
table and preserving the terminal-bit invariant. -/
theorem legal_transition_certificate :
    forall (state : Fin 21) (previous bit : Bool),
      EndsInOne state = previous -> LegalNext previous bit ->
        exists next : Fin 21,
          reducedBase4DFAO.step state bit = some next ∧
          liftState next = paperBase4DFAO.step (liftState state) bit ∧
          EndsInOne next = bit := by
  intro state previous bit hstate hlegal
  fin_cases state <;> cases previous <;> cases bit <;>
    simp_all [EndsInOne, LegalNext, liftState, reducedBase4DFAO,
      paperBase4DFAO, reducedStepZero, reducedStepOne, paperStepZero,
      paperStepOne]

theorem reduced_run_is_lift_compatible {state : Fin 21} {previous : Bool}
    (word : List Bool) (hstate : EndsInOne state = previous)
    (hvalid : ValidFrom previous word) :
    exists final : Fin 21,
      reducedBase4DFAO.runFrom state word = some final ∧
      liftState final = paperBase4DFAO.runFrom (liftState state) word := by
  induction word generalizing state previous with
  | nil => exact ⟨state, rfl, rfl⟩
  | cons bit rest ih =>
      rw [ValidFrom] at hvalid
      obtain ⟨next, hstep, hlift, hterminal⟩ :=
        legal_transition_certificate state previous bit hstate hvalid.1
      obtain ⟨final, hrun, hfinal⟩ := ih hterminal hvalid.2
      refine ⟨final, ?_, ?_⟩
      · simp only [PartialDFAO.runFrom, hstep, Option.bind_some, hrun]
      · rw [DFAO.runFrom, <- hlift]
        exact hfinal

theorem reduced_agrees_on_admissible_encodings :
    EquivalentOnAdmissibleEncodings reducedBase4DFAO paperBase4DFAO := by
  intro word hvalid
  obtain ⟨final, hrun, hlift⟩ := reduced_run_is_lift_compatible
    (state := (0 : Fin 21)) (previous := false) word (by decide) hvalid
  simp only [PartialDFAO.evaluate, hrun, Option.map_some, DFAO.evaluate]
  rw [output_compatibility_certificate, hlift]
  simp [liftState]

theorem reduced_ignores_leading_zeroes (word : List Bool) :
    reducedBase4DFAO.evaluate (false :: word) =
      reducedBase4DFAO.evaluate word := by
  rfl

theorem reduced_obeys_zeckendorf_ostrowski_rules :
    ObeysZeckendorfOstrowskiRules reducedBase4DFAO := by
  constructor
  · intro state
    exact ⟨reducedStepZero state, by simp [reducedBase4DFAO]⟩
  · intro state next hstep
    fin_cases state <;> fin_cases next <;>
      simp_all [reducedBase4DFAO, reducedStepOne]
  · intro state next hstep
    fin_cases state <;> fin_cases next <;>
      simp_all [reducedBase4DFAO, reducedStepOne]

def reducedBase4AdmissibleDFAO : AdmissibleDFAO 21 where
  machine := reducedBase4DFAO
  ignoresLeadingZeroes := reduced_ignores_leading_zeroes
  ostrowski := reduced_obeys_zeckendorf_ostrowski_rules

/-- The original 22-state minimality claim is false in its stated domain: the
modern table supplies 21 live states, obeys every convention, and agrees with
the paper table on every admissible encoding (hence on every encoded `4^i`). -/
theorem paper_base4_golden_ratio_dfao_is_not_minimal :
    exists candidate : AdmissibleDFAO 21,
      EquivalentOnAdmissibleEncodings candidate.machine paperBase4DFAO := by
  exact ⟨reducedBase4AdmissibleDFAO,
    reduced_agrees_on_admissible_encodings⟩

end D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality
