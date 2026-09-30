/- GID: D5/S0/Computability/ClauseMalformedCleanup
   generality: G
   mirror-B: D5/S0/Computability/ClauseMalformedCleanup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: ["D5/S0/Computability/ClauseQueryPreprocessor"]
   utility: none
   digest: Every error-entry configuration cleans all private stacks and emits the zero-count query. -/

import D5.S0.Computability.ClauseQueryPreprocessor

/-!
These are universal symbolic word and execution laws over unbounded inputs. They
are not finite certified instances, bounded enumerations, certificate-checking
soundness applications, or conditional numerical reductions. The utility class
is none; all computational-instance utility fields are inapplicable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic

open Turing StateTransition

/-- The actual fixed program empties arbitrary error-state stacks, resets its
control and returns the valid singleton/empty-clause query. This is independent
of the point at which malformed syntax was detected. -/
theorem pre_error_cleanup (st : PreControl) (input header scratch query : List Bool) :
    Nonempty (EvalsToInTime preMachine.step
      (preCfg .badInput st input header scratch query [])
      (some (haltList preMachine dummyQuery))
      (input.length + header.length + scratch.length + query.length + 5)) := by
  apply Nonempty.intro
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have dummy : ∀ st, EvalsToInTime preMachine.step
      (preCfg .dummy st [] [] [] [] []) (some (haltList preMachine dummyQuery)) 1 := by
    intro st
    apply single
    apply congrArg some
    dsimp [preMachine, FinTM2.decidableEqK, TM2.stepAux, preCfg, preStacks,
      preRead, preMark, preClear, prePush, haltList, dummyQuery]
    simp [prePush, List.reverse_cons, TM2.stepAux, Function.update_apply, preStacks] <;>
      first | rfl | (funext k; cases k <;> simp [Function.update_apply, preStacks])
  have clearQuery : ∀ query st, EvalsToInTime preMachine.step
      (preCfg .badQuery st [] [] [] query [])
      (some (haltList preMachine dummyQuery)) (query.length + 2) := by
    intro query
    induction query with
    | nil =>
      intro st
      have hs : preMachine.step (preCfg .badQuery st [] [] [] [] []) =
          some (preCfg .dummy (preClear st) [] [] [] [] []) := by pre_transition
      exact EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (dummy _)
    | cons b query ih =>
      intro st
      have hs : preMachine.step (preCfg .badQuery st [] [] [] (b :: query) []) =
          some (preCfg .badQuery (preClear st) [] [] [] query []) := by
        cases b <;> pre_transition
      simpa [List.length_cons, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (query.length + 2) _ _ _ (single _ _ hs) (ih _)
  have clearScratch : ∀ scratch query st, EvalsToInTime preMachine.step
      (preCfg .badScratch st [] [] scratch query [])
      (some (haltList preMachine dummyQuery)) (scratch.length + query.length + 3) := by
    intro scratch
    induction scratch with
    | nil =>
      intro query st
      have hs : preMachine.step (preCfg .badScratch st [] [] [] query []) =
          some (preCfg .badQuery (preClear st) [] [] [] query []) := by pre_transition
      simpa [Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (query.length + 2) _ _ _ (single _ _ hs) (clearQuery _ _)
    | cons b scratch ih =>
      intro query st
      have hs : preMachine.step (preCfg .badScratch st [] [] (b :: scratch) query []) =
          some (preCfg .badScratch (preClear st) [] [] scratch query []) := by
        cases b <;> pre_transition
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (scratch.length + query.length + 3)
          _ _ _ (single _ _ hs) (ih _ _)
  have clearHeader : ∀ header scratch query st, EvalsToInTime preMachine.step
      (preCfg .badHeader st [] header scratch query [])
      (some (haltList preMachine dummyQuery))
      (header.length + scratch.length + query.length + 4) := by
    intro header
    induction header with
    | nil =>
      intro scratch query st
      have hs : preMachine.step (preCfg .badHeader st [] [] scratch query []) =
          some (preCfg .badScratch (preClear st) [] [] scratch query []) := by pre_transition
      simpa [Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (scratch.length + query.length + 3)
          _ _ _ (single _ _ hs) (clearScratch _ _ _)
    | cons b header ih =>
      intro scratch query st
      have hs : preMachine.step (preCfg .badHeader st [] (b :: header) scratch query []) =
          some (preCfg .badHeader (preClear st) [] header scratch query []) := by
        cases b <;> pre_transition
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (header.length + scratch.length + query.length + 4)
          _ _ _ (single _ _ hs) (ih _ _ _)
  induction input generalizing st with
  | nil =>
    have hs : preMachine.step (preCfg .badInput st [] header scratch query []) =
        some (preCfg .badHeader (preClear st) [] header scratch query []) := by pre_transition
    simpa [Nat.add_assoc] using
      EvalsToInTime.trans _ 1 (header.length + scratch.length + query.length + 4)
        _ _ _ (single _ _ hs) (clearHeader _ _ _ _)
  | cons b input ih =>
    have hs : preMachine.step (preCfg .badInput st (b :: input) header scratch query []) =
        some (preCfg .badInput (preClear st) input header scratch query []) := by
      cases b <;> pre_transition
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ 1
        (input.length + header.length + scratch.length + query.length + 5)
        _ _ _ (single _ _ hs) (ih _)

end PredictiveThermodynamic
