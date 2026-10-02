/- GID: D5/S0/Computability/RationalMalformedCleanup
   generality: G
   mirror-B: D5/B/S0/Computability/RationalMalformedCleanup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary response-error stacks clean to the exact zero-output terminal state. -/

import D5.S0.Computability.RationalPostprocessor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic
open Turing StateTransition

/-- Error cleanup empties arbitrary response stacks and resets the finite control. -/
theorem post_error_cleanup (st : PostControl)
    (input quotient shifts : List ResponseSymbol) :
    Nonempty (EvalsToInTime postMachine.step
      (postCfg .badInput st input quotient shifts [])
      (some (haltList postMachine [.zero]))
      (input.length + quotient.length + shifts.length + 3)) := by
  apply Nonempty.intro
  let single : ∀ (a : postMachine.Cfg) (b : Option postMachine.Cfg),
      postMachine.step a = b → EvalsToInTime postMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have clearShifts : ∀ shifts st, EvalsToInTime postMachine.step
      (postCfg .badShifts st [] [] shifts [])
      (some (haltList postMachine [.zero])) (shifts.length + 1) := by
    intro shifts
    induction shifts with
    | nil =>
      intro st
      apply single
      apply congrArg some
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol,
        clearSymbol, haltList]
      congr 1
      funext k
      cases k <;> rfl
    | cons a shifts ih =>
      intro st
      have hs : postMachine.step (postCfg .badShifts st [] [] (a :: shifts) []) =
          some (postCfg .badShifts (clearSymbol st) [] [] shifts []) := by
        cases a <;> apply congrArg some <;>
          dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol,
            clearSymbol] <;> congr 1 <;> funext k <;> cases k <;> rfl
      simpa [List.length_cons, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (shifts.length + 1) _ _ _ (single _ _ hs) (ih _)
  have clearQuotient : ∀ quotient shifts st, EvalsToInTime postMachine.step
      (postCfg .badQuotient st [] quotient shifts [])
      (some (haltList postMachine [.zero])) (quotient.length + shifts.length + 2) := by
    intro quotient
    induction quotient with
    | nil =>
      intro shifts st
      have hs : postMachine.step (postCfg .badQuotient st [] [] shifts []) =
          some (postCfg .badShifts (clearSymbol st) [] [] shifts []) := by
        apply congrArg some
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol, clearSymbol]
        congr 1
        funext k
        cases k <;> rfl
      simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 (shifts.length + 1)
        _ _ _ (single _ _ hs) (clearShifts _ _)
    | cons a quotient ih =>
      intro shifts st
      have hs : postMachine.step (postCfg .badQuotient st [] (a :: quotient) shifts []) =
          some (postCfg .badQuotient (clearSymbol st) [] quotient shifts []) := by
        cases a <;> apply congrArg some <;>
          dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol,
            clearSymbol] <;> congr 1 <;> funext k <;> cases k <;> rfl
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (quotient.length + shifts.length + 2)
          _ _ _ (single _ _ hs) (ih _ _)
  induction input generalizing st with
  | nil =>
    have hs : postMachine.step (postCfg .badInput st [] quotient shifts []) =
        some (postCfg .badQuotient (clearSymbol st) [] quotient shifts []) := by
      apply congrArg some
      dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol, clearSymbol]
      congr 1
      funext k
      cases k <;> rfl
    simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1
      (quotient.length + shifts.length + 2) _ _ _ (single _ _ hs)
      (clearQuotient _ _ _)
  | cons a input ih =>
    have hs : postMachine.step (postCfg .badInput st (a :: input) quotient shifts []) =
        some (postCfg .badInput (clearSymbol st) input quotient shifts []) := by
      cases a <;> apply congrArg some <;>
        dsimp [postMachine, TM2.stepAux, postCfg, postStacks, readSymbol,
          clearSymbol] <;> congr 1 <;> funext k <;> cases k <;> rfl
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ 1 (input.length + quotient.length + shifts.length + 3)
        _ _ _ (single _ _ hs) (ih _)

end PredictiveThermodynamic
