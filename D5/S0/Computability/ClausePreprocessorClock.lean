/- GID: D5/S0/Computability/ClausePreprocessorClock
   generality: G
   mirror-B: D5/B/S0/Computability/ClausePreprocessorClock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A decreasing actual-step clock for all raw inputs of the fixed clause machine. -/

import D5.S0.Computability.ClauseQueryPreprocessor
import D5.S0.Computability.PhysicalDivider.StackGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Universal symbolic execution and word-size laws, rather than finite certified
instances, bounded enumeration, certificate checking or numerical reductions.
-/

namespace PredictiveThermodynamic
open Turing StateTransition

/-- The phase constants pay for jumps that do not consume an input symbol. -/
def prePhaseCredit : PreLabel → Nat
  | .first | .coefficient | .index => 13
  | .restoreCoefficient | .restoreIndex => 11
  | .endInput | .badInput => 5
  | .badHeader => 4
  | .badScratch => 3
  | .clearHeader | .badQuery => 2
  | .reverse | .dummy => 1
  | _ => 10

/-- Copying credit differs from the restoration credit. -/
def preHeaderCredit : PreLabel → Nat
  | .coefficient => 5
  | _ => 1

/-- Header copying uses a larger credit before moving symbols into backups. -/
def preClock (N : Nat) (c : preMachine.Cfg) : Nat :=
  match (c.l : Option PreLabel) with
  | none => 0
  | some label =>
    (4 * N + 20) * (c.stk .input).length +
    (preHeaderCredit label) * (c.stk .header).length +
    3 * (c.stk .scratch).length + (c.stk .query).length + prePhaseCredit label

/-- Live phase invariants describe empty tapes; arbitrary raw input is allowed. -/
def preFrame (c : preMachine.Cfg) : Prop :=
  match (c.l : Option PreLabel) with
  | none => c.var = preMachine.initialState ∧ c.stk .input = [] ∧
      c.stk .header = [] ∧ c.stk .scratch = [] ∧ c.stk .query = []
  | some .first => c.stk .header = [] ∧ c.stk .scratch = [] ∧
      c.stk .query = [] ∧ c.stk .output = []
  | some .header | some .formulaZero | some .formulaTag | some .clauseOne |
      some .clauseTag | some .polarity | some .endInput =>
      c.stk .scratch = [] ∧ c.stk .output = []
  | some .clearHeader => c.stk .input = [] ∧ c.stk .scratch = [] ∧ c.stk .output = []
  | some .reverse => c.stk .input = [] ∧ c.stk .header = [] ∧ c.stk .scratch = []
  | some .badHeader => c.stk .input = [] ∧ c.stk .output = []
  | some .badScratch => c.stk .input = [] ∧ c.stk .header = [] ∧ c.stk .output = []
  | some .badQuery => c.stk .input = [] ∧ c.stk .header = [] ∧
      c.stk .scratch = [] ∧ c.stk .output = []
  | some .dummy => c.stk .input = [] ∧ c.stk .header = [] ∧
      c.stk .scratch = [] ∧ c.stk .query = [] ∧ c.stk .output = []
  | _ => c.stk .output = []

/-- Every raw word has a clean terminal run with a direct polynomial clock.
The output bound charges ordinary written symbols; it does not assert decoding. -/
theorem pre_total_clock (w : List Bool) :
    ∃ out : List Bool,
      Nonempty (TM2OutputsInTime preMachine w (some out)
        ((4 * w.length + 20) * w.length + 13)) ∧
      out.length ≤ ((4 * w.length + 20) * w.length + 13) *
        (@Lax51Proofs.RamToTM.programPushBound PreStack PreLabel PreControl
          (fun _ => Bool) inferInstance preMachine.m) := by
  have advance : ∀ (N : Nat) (label : PreLabel) (st : PreControl)
      (input header scratch query output : List Bool),
      preFrame (preCfg label st input header scratch query output) →
      input.length + header.length + scratch.length ≤ N →
      let next := TM2.stepAux (preMachine.m label) st
        (preStacks input header scratch query output)
      preFrame next ∧
        (next.stk .input).length + (next.stk .header).length +
          (next.stk .scratch).length ≤ N ∧
        preClock N next < preClock N (preCfg label st input header scratch query output) := by
    intro N label st input header scratch query output frame capacity
    cases label with
    | first =>
      all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
        preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
        Function.update_apply, Nat.mul_add, Nat.add_mul]
      all_goals try split_ifs
      all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
        preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
        Function.update_apply, Nat.mul_add, Nat.add_mul]
      all_goals omega
    | header =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | true =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
    | formulaZero =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | true =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
    | formulaTag =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | true =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
    | coefficient =>
      cases header with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_header tail_header =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | restoreCoefficient =>
      cases scratch with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_scratch tail_scratch =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | clauseOne =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | true =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
    | clauseTag =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | true =>
          change scratch = [] ∧ output = [] at frame
          rcases frame with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.add_zero] at capacity
          by_cases h : st.literals.val < 3 <;>
            simp [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, h,
              Function.update_apply, Nat.mul_add, Nat.add_mul] <;> omega
    | polarity =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | index =>
      cases input with
      | nil =>
        cases header with
        | nil =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
        | cons bit_header tail_header =>
          all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals try split_ifs
          all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
            Function.update_apply, Nat.mul_add, Nat.add_mul]
          all_goals omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          cases header with
          | nil =>
            all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals try split_ifs
            all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals omega
          | cons bit_header tail_header =>
            all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals try split_ifs
            all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals omega
        | true =>
          cases header with
          | nil =>
            all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals try split_ifs
            all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals omega
          | cons bit_header tail_header =>
            all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals try split_ifs
            all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
              Function.update_apply, Nat.mul_add, Nat.add_mul]
            all_goals omega
    | restoreIndex =>
      cases scratch with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_scratch tail_scratch =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | endInput =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | clearHeader =>
      cases header with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_header tail_header =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | reverse =>
      cases query with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_query tail_query =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | badInput =>
      cases input with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_input tail_input =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | badHeader =>
      cases header with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_header tail_header =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | badScratch =>
      cases scratch with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_scratch tail_scratch =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | badQuery =>
      cases query with
      | nil =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
      | cons bit_query tail_query =>
        all_goals simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals try split_ifs
        all_goals try simp_all [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush,
          Function.update_apply, Nat.mul_add, Nat.add_mul]
        all_goals omega
    | dummy =>
      have empty : input = [] ∧ header = [] ∧ scratch = [] ∧ query = [] ∧ output = [] :=
        frame
      rcases empty with ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hs : TM2.stepAux (preMachine.m .dummy) st (preStacks [] [] [] [] []) =
          haltList preMachine dummyQuery := by
        dsimp [preMachine, FinTM2.decidableEqK, TM2.stepAux, preStacks,
          preRead, preMark, preClear, prePush, haltList, dummyQuery]
        simp [prePush, List.reverse_cons, TM2.stepAux, Function.update_apply, preStacks] <;>
          first | rfl | (funext k; cases k <;> simp [Function.update_apply, preStacks])
      dsimp only
      rw [hs]
      simp [preFrame, preClock, prePhaseCredit, preHeaderCredit, preCfg, preStacks,
        haltList, preMachine]
  have terminate : ∀ (N fuel : Nat) (c : preMachine.Cfg),
      preFrame c →
      (c.stk .input).length + (c.stk .header).length + (c.stk .scratch).length ≤ N →
      preClock N c ≤ fuel →
      ∃ out, Nonempty (EvalsToInTime preMachine.step c
        (some (haltList preMachine out)) fuel) := by
    intro N fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro c frame capacity credit
      rcases c with ⟨label, st, tapes⟩
      cases label with
      | none =>
        refine ⟨tapes .output, ⟨?_⟩⟩
        have clean : (⟨none, st, tapes⟩ : preMachine.Cfg) =
            haltList preMachine (tapes .output) := by
          rcases frame with ⟨hs, hi, hh, ht, hq⟩
          change st = preMachine.initialState at hs
          rw [hs]
          congr 1
          funext k; cases k <;> simp_all [haltList, preMachine, Function.update_apply]
        rw [clean]
        exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.zero_le _ }
      | some label =>
        have cfg : (⟨some label, st, tapes⟩ : preMachine.Cfg) =
            preCfg label st (tapes .input) (tapes .header) (tapes .scratch)
              (tapes .query) (tapes .output) := by
          congr 1
          funext k; cases k <;> rfl
        rw [cfg] at frame capacity credit ⊢
        let next := TM2.stepAux (preMachine.m label) st tapes
        have ⟨fr, cap, dec⟩ := advance N label st (tapes .input) (tapes .header)
          (tapes .scratch) (tapes .query) (tapes .output) frame capacity
        have tapesEq : preStacks (tapes .input) (tapes .header)
            (tapes .scratch) (tapes .query) (tapes .output) = tapes := by
          funext k; cases k <;> rfl
        rw [tapesEq] at fr cap dec
        have hn : preClock N next < fuel := lt_of_lt_of_le dec credit
        obtain ⟨out, ⟨tail⟩⟩ := ih (preClock N next) hn next fr cap (le_refl _)
        refine ⟨out, ⟨?_⟩⟩
        have one : EvalsToInTime preMachine.step
            (preCfg label st (tapes .input) (tapes .header) (tapes .scratch)
              (tapes .query) (tapes .output)) (some next) 1 :=
          { steps := 1, evals_in_steps := by rw [← cfg]; rfl, steps_le_m := by decide }
        have run := EvalsToInTime.trans preMachine.step 1 (preClock N next) _ _ _ one tail
        exact { run with steps_le_m := le_trans run.steps_le_m (by omega) }
  have initFrame : preFrame (initList preMachine w) := by
    simp [preFrame, initList, preMachine, Function.update_apply]
  have initCapacity : ((initList preMachine w).stk .input).length +
      ((initList preMachine w).stk .header).length +
      ((initList preMachine w).stk .scratch).length ≤ w.length := by
    simp [initList, preMachine, Function.update_apply]
  have initialCredit : preClock w.length (initList preMachine w) =
      (4 * w.length + 20) * w.length + 13 := by
    simp [preClock, prePhaseCredit, initList, preMachine, Function.update_apply]
  obtain ⟨out, ⟨run⟩⟩ := terminate w.length _ (initList preMachine w)
    initFrame initCapacity (le_of_eq initialCredit)
  refine ⟨out, ⟨run⟩, ?_⟩
  have growth := @Lax51Proofs.RamToTM.iterate_stack_length_le
    PreStack PreLabel PreControl (fun _ => Bool) inferInstance inferInstance inferInstance
    preMachine.m run.steps
    (initList preMachine w) (haltList preMachine out) run.evals_in_steps PreStack.output
  have h := Nat.mul_le_mul_right
    ((@Lax51Proofs.RamToTM.programPushBound PreStack PreLabel PreControl
          (fun _ => Bool) inferInstance preMachine.m)) run.steps_le_m
  simpa [initList, haltList, preMachine, Function.update_apply] using growth.trans (by
    simpa [initList, preMachine, Function.update_apply] using h)

end PredictiveThermodynamic
