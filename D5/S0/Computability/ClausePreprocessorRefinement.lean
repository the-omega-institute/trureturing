/- GID: D5/S0/Computability/ClausePreprocessorRefinement
   generality: G
   mirror-B: D5/S0/Computability/ClausePreprocessorRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: ["D5/S0/Computability/ClauseWordCodec", "D5/S0/Computability/ClauseMalformedCleanup"]
   utility: none
   digest: All raw clause words refine to actual clean physical-query machine runs. -/

import D5.S0.Computability.ClauseWordCodec
import D5.S0.Computability.ClauseMalformedCleanup
import D5.S0.Computability.ClausePreprocessorClock

/-!
The public conclusion identifies actual fixed-machine executions and their total
decoded outputs for every unbounded raw word. The phase predicates are symbolic
invariants over arbitrary configurations; the theorem constructs a real error
prefix and uses deterministic terminal uniqueness. The raw-word recognizer it
consumes has its own checker contract. No finite enumeration or supplied
execution certificate occurs in this operational refinement law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic
open Turing StateTransition ClauseCodec

def preparedFormula (w : List Bool) : Σ n, UnaryFormula n :=
  (readWord false w).getD ⟨0,[[]]⟩

def preparedQuery (w : List Bool) : List Bool :=
  match readWord false w with
  | none => dummyQuery
  | some ⟨_,F⟩ => queryWord F

/-- Raw input determines the actual physical query, including rejection cleanup. -/
theorem pre_word_run (w : List Bool) :
    Nonempty (TM2OutputsInTime preMachine w (some (preparedQuery w))
      ((4*w.length+20)*w.length+13)) ∧
    readWord true (preparedQuery w) = some (preparedFormula w) ∧
    preparedQuery w = encodeWord true (preparedFormula w).2 ∧
    (∀ c ∈ (preparedFormula w).2, c.length ≤ 3) ∧
    (preparedQuery w).length ≤ ((4*w.length+20)*w.length+13) *
      (@Lax51Proofs.RamToTM.programPushBound PreStack PreLabel PreControl
        (fun _ => Bool) inferInstance preMachine.m) ∧
    (readWord false w = none → ∃ (st : PreControl) (input header scratch query : List Bool),
      Nonempty (EvalsToInTime preMachine.step (initList preMachine w)
        (some (preCfg .badInput st input header scratch query []))
        ((4*w.length+20)*w.length+13))) := by
  let Body (n : Nat) (w : List Bool) : Prop := ∃ F : UnaryFormula n,
    w = bodyWord false F ∧ ∀ c ∈ F, c.length ≤ 3
  let Clause (n b : Nat) (w : List Bool) : Prop :=
    ∃ (c : Std.Sat.CNF.Clause (Fin n)) (tail : List Bool),
      w = c.flatMap unaryLiteral ++ [true, false] ++ tail ∧ c.length ≤ b ∧ Body n tail
  let Header (h : Nat) (w : List Bool) : Prop := ∃ j tail,
    w = List.replicate j true ++ false :: tail ∧ Body (h + j) tail
  let Index (n b h : Nat) (w : List Bool) : Prop := ∃ j tail,
    j < h ∧ w = List.replicate j true ++ false :: tail ∧ Clause n b tail
  have bodyCases : ∀ n w, Body n w ↔ w = [false, false] ∨
      ∃ tail, w = false :: true :: tail ∧ Clause n 3 tail := by
    intro n w
    constructor
    · rintro ⟨F, rfl, width⟩
      cases F with
      | nil => exact Or.inl rfl
      | cons c F =>
        refine Or.inr ⟨c.flatMap unaryLiteral ++ [true, false] ++ bodyWord false F, ?_,
          c, bodyWord false F, rfl, width c (by simp), F, rfl, ?_⟩
        · simp [bodyWord, termWord, List.append_assoc]
        · intro d hd; exact width d (by simp [hd])
    · rintro (rfl | ⟨tail, rfl, c, rest, rfl, hc, F, rfl, hf⟩)
      · exact ⟨[], rfl, by simp⟩
      · refine ⟨c :: F, ?_, ?_⟩
        · simp [bodyWord, termWord, List.append_assoc]
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hc
          · exact hf d hd
  have clauseCases : ∀ n b w, Clause n b w ↔
      (∃ tail, w = true :: false :: tail ∧ Body n tail) ∨
      ∃ (i : Fin n) (p : Bool) (tail : List Bool), 0 < b ∧
        w = true :: true :: p :: (List.replicate i.val true ++ false :: tail) ∧
        Clause n (b - 1) tail := by
    intro n b w
    constructor
    · rintro ⟨c, tail, rfl, hc, ht⟩
      cases c with
      | nil => exact Or.inl ⟨tail, rfl, ht⟩
      | cons literal c =>
        rcases literal with ⟨i, p⟩
        refine Or.inr ⟨i, p, c.flatMap unaryLiteral ++ [true, false] ++ tail,
          by simp only [List.length_cons] at hc; omega, ?_, c, tail, rfl, ?_, ht⟩
        · simp [unaryLiteral, List.append_assoc]
        · simp only [List.length_cons] at hc; omega
    · rintro (⟨tail, rfl, ht⟩ | ⟨i, p, rest, hb, rfl, c, tail, rfl, hc, ht⟩)
      · exact ⟨[], tail, rfl, Nat.zero_le _, ht⟩
      · refine ⟨(i,p) :: c, tail, ?_, ?_, ht⟩
        · simp [unaryLiteral, List.append_assoc]
        · simp only [List.length_cons]; omega
  have bodyNil : ∀ n, ¬ Body n [] := by intro n; rw [bodyCases]; simp
  have bodyShort : ∀ n, ¬ Body n [false] := by
    intro n; rw [bodyCases]; simp
  have bodyTrue : ∀ n w, ¬ Body n (true :: w) := by intro n w; rw [bodyCases]; simp
  have bodyEnd : ∀ n w, Body n (false :: false :: w) ↔ w = [] := by
    intro n w; rw [bodyCases]; simp
  have bodyClause : ∀ n w, Body n (false :: true :: w) ↔ Clause n 3 w := by
    intro n w; rw [bodyCases]; simp
  have clauseNil : ∀ n b, ¬ Clause n b [] := by intro n b; rw [clauseCases]; simp
  have clauseShort : ∀ n b, ¬ Clause n b [true] := by
    intro n b; rw [clauseCases]; simp
  have clauseFalse : ∀ n b w, ¬ Clause n b (false :: w) := by
    intro n b w; rw [clauseCases]; simp
  have clauseEnd : ∀ n b w, Clause n b (true :: false :: w) ↔ Body n w := by
    intro n b w; rw [clauseCases]; simp
  have clauseNoBudget : ∀ n w, ¬ Clause n 0 (true :: true :: w) := by
    intro n w; rw [clauseCases]; simp
  have clauseNoPolarity : ∀ n b, ¬ Clause n b [true, true] := by
    intro n b; rw [clauseCases]; simp
  have literalIndex : ∀ n b p w,
      Clause n (b + 1) (true :: true :: p :: w) ↔ Index n b n w := by
    intro n b p w
    rw [clauseCases]
    simp only [List.cons.injEq, reduceCtorEq, false_and, true_and, and_false,
      exists_false, false_or, Nat.zero_lt_succ, Nat.add_sub_cancel]
    constructor
    · rintro ⟨i, p', rest, e, hc⟩
      obtain ⟨rfl, e⟩ := e
      exact ⟨i.val, rest, i.isLt, e, hc⟩
    · rintro ⟨i, rest, hi, e, hc⟩
      exact ⟨⟨i,hi⟩, p, rest, ⟨rfl,e⟩, hc⟩
  have headerNil : ∀ h, ¬ Header h [] := by
    intro h; rintro ⟨j, tail, hw, _⟩
    have e := congrArg List.length hw
    simp at e
  have headerFalse : ∀ h w, Header h (false :: w) ↔ Body h w := by
    intro h w
    constructor
    · rintro ⟨j, tail, hw, ht⟩
      cases j with
      | zero => simp only [List.replicate_zero, List.nil_append, List.cons.injEq,
          true_and] at hw; subst tail; exact ht
      | succ j => simp [List.replicate_succ] at hw
    · intro ht; exact ⟨0,w,rfl,ht⟩
  have headerTrue : ∀ h w, Header h (true :: w) ↔ Header (h + 1) w := by
    intro h w
    constructor
    · rintro ⟨j, tail, hw, ht⟩
      cases j with
      | zero => simp at hw
      | succ j =>
        have e : w = List.replicate j true ++ false :: tail := by
          simpa [List.replicate_succ] using hw
        refine ⟨j, tail, e, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    · rintro ⟨j, tail, hw, ht⟩
      refine ⟨j+1,tail,?_,?_⟩
      · simpa [List.replicate_succ] using congrArg (List.cons true) hw
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  have indexNil : ∀ n b h, ¬ Index n b h [] := by
    intro n b h; rintro ⟨j,tail,_,hw,_⟩
    have e := congrArg List.length hw
    simp at e
  have indexFalse : ∀ n b h w, Index n b h (false :: w) ↔ 0 < h ∧ Clause n b w := by
    intro n b h w
    constructor
    · rintro ⟨j,tail,hj,hw,ht⟩
      cases j with
      | zero =>
        have e : w = tail := by simpa using hw
        subst tail; exact ⟨hj,ht⟩
      | succ j => simp [List.replicate_succ] at hw
    · rintro ⟨hh,ht⟩; exact ⟨0,w,hh,rfl,ht⟩
  have indexTrue : ∀ n b h w, Index n b h (true :: w) ↔ 0 < h ∧ Index n b (h - 1) w := by
    intro n b h w
    constructor
    · rintro ⟨j,tail,hj,hw,ht⟩
      cases j with
      | zero => simp at hw
      | succ j =>
        refine ⟨by omega, j,tail,by omega,?_,ht⟩
        simpa [List.replicate_succ] using hw
    · rintro ⟨hh,j,tail,hj,hw,ht⟩
      refine ⟨j+1,tail,by omega,?_,ht⟩
      simpa [List.replicate_succ] using congrArg (List.cons true) hw
  have literalRemaining : ∀ n (l : Fin 4) p w, 0 < l.val →
      (Clause n (4 - l.val) (true :: true :: p :: w) ↔ Index n (3 - l.val) n w) := by
    intro n l p w positive
    have bound := l.isLt
    rw [show 4 - l.val = (3 - l.val) + 1 from by omega]
    exact literalIndex n (3 - l.val) p w
  let Accepted (c : preMachine.Cfg) : Prop :=
    match (c.l : Option PreLabel) with
    | none | some .clearHeader | some .reverse => True
    | some .first => Header 0 (c.stk .input)
    | some .header => Header (c.stk .header).length (c.stk .input)
    | some .formulaZero => Body (c.stk .header).length (c.stk .input)
    | some .formulaTag => Body (c.stk .header).length (false :: c.stk .input)
    | some .coefficient | some .restoreCoefficient =>
      Clause ((c.stk .header).length + (c.stk .scratch).length) 3 (c.stk .input)
    | some .clauseOne => Clause (c.stk .header).length (3 - c.var.literals.val) (c.stk .input)
    | some .clauseTag => Clause (c.stk .header).length (3 - c.var.literals.val)
      (true :: c.stk .input)
    | some .polarity => Clause (c.stk .header).length (4 - c.var.literals.val)
      (true :: true :: c.stk .input)
    | some .index => Index ((c.stk .header).length + (c.stk .scratch).length)
      (3 - c.var.literals.val) (c.stk .header).length (c.stk .input)
    | some .restoreIndex => Clause ((c.stk .header).length + (c.stk .scratch).length)
      (3 - c.var.literals.val) (c.stk .input)
    | some .endInput => c.stk .input = []
    | _ => False
  let Safe (c : preMachine.Cfg) : Prop := preFrame c ∧
    match (c.l : Option PreLabel) with
    | some .first | some .header | some .formulaZero | some .formulaTag |
      some .coefficient | some .restoreCoefficient | some .endInput |
      some .clearHeader | some .reverse => c.var.literals.val = 0
    | some .polarity | some .index | some .restoreIndex => 0 < c.var.literals.val
    | some .badHeader | some .badScratch | some .badQuery | some .dummy => False
    | _ => True
  have phaseStep : ∀ (label : PreLabel) (st : PreControl)
      (input header scratch query output : List Bool),
      Safe (preCfg label st input header scratch query output) → label ≠ .badInput →
      let next := TM2.stepAux (preMachine.m label) st
        (preStacks input header scratch query output)
      Safe next ∧ (Accepted (preCfg label st input header scratch query output) ↔ Accepted next) := by
    intro label st input header scratch query output frame normal
    cases label with
    | first =>
      change (header = [] ∧ scratch = [] ∧ query = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl,rfl,rfl⟩, counter⟩
      all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
        preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
        Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
        bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
        clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals try omega
    | header =>
      change (scratch = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | true =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
    | formulaZero =>
      change (scratch = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | true =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
    | formulaTag =>
      change (scratch = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | true =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
    | coefficient =>
      change (output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨rfl, counter⟩
      cases header with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_header tail_header =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | restoreCoefficient =>
      change (output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨rfl, counter⟩
      cases scratch with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_scratch tail_scratch =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | clauseOne =>
      change (scratch = [] ∧ output = []) ∧ (True) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | true =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
    | clauseTag =>
      change (scratch = [] ∧ output = []) ∧ (True) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | true =>
          rcases st with ⟨seen,mark,literals⟩
          fin_cases literals
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
    | polarity =>
      change (scratch = [] ∧ output = []) ∧ (0 < st.literals.val) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | index =>
      change (output = []) ∧ (0 < st.literals.val) at frame
      rcases frame with ⟨rfl, counter⟩
      cases input with
      | nil =>
        cases header with
        | nil =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
        | cons bit_header tail_header =>
          all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
            preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
            Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
            bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
            clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          all_goals try omega
      | cons bit_input tail_input =>
        cases bit_input with
        | false =>
          cases header with
          | nil =>
            all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
              Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
              bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
              clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            all_goals try omega
          | cons bit_header tail_header =>
            all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
              Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
              bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
              clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            all_goals try omega
        | true =>
          cases header with
          | nil =>
            all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
              Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
              bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
              clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            all_goals try omega
          | cons bit_header tail_header =>
            all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
              preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
              Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
              bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
              clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            all_goals try omega
    | restoreIndex =>
      change (output = []) ∧ (0 < st.literals.val) at frame
      rcases frame with ⟨rfl, counter⟩
      cases scratch with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_scratch tail_scratch =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | endInput =>
      change (scratch = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl⟩, counter⟩
      cases input with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_input tail_input =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | clearHeader =>
      change (input = [] ∧ scratch = [] ∧ output = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl,rfl⟩, counter⟩
      cases header with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_header tail_header =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | reverse =>
      change (input = [] ∧ header = [] ∧ scratch = []) ∧ (st.literals.val = 0) at frame
      rcases frame with ⟨⟨rfl,rfl,rfl⟩, counter⟩
      cases query with
      | nil =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
      | cons bit_query tail_query =>
        all_goals simp [Safe, Accepted, preFrame, preCfg, preStacks,
          preMachine, TM2.stepAux, preRead, preMark, preClear, prePush, counter,
          Function.update_apply, headerNil, headerFalse, headerTrue, bodyNil, bodyTrue,
          bodyEnd, bodyClause, bodyShort, clauseShort, clauseNil, clauseFalse, clauseEnd, clauseNoBudget,
          clauseNoPolarity, indexNil, indexFalse, indexTrue, literalRemaining,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        all_goals try omega
    | badInput => exact (normal rfl).elim
    | badHeader | badScratch | badQuery | dummy => exact frame.2.elim
  have failPrefix : ∀ k (c d : preMachine.Cfg), Safe c → ¬ Accepted c →
      (flip bind preMachine.step)^[k] (some c) = some d → d.l = none →
      ∃ (st : PreControl) (input header scratch query : List Bool),
        Nonempty (EvalsToInTime preMachine.step c
          (some (preCfg .badInput st input header scratch query [])) k) := by
    intro k
    induction k with
    | zero =>
      intro c d frame rejected trace terminal
      have same : c = d := Option.some.inj trace
      subst d
      have good : Accepted c := by simp [Accepted, terminal]
      exact (rejected good).elim
    | succ k ih =>
      intro c d frame rejected trace terminal
      rcases c with ⟨label,st,tapes⟩
      cases label with
      | none =>
        have good : Accepted (⟨none,st,tapes⟩ : preMachine.Cfg) := by trivial
        exact (rejected good).elim
      | some label =>
        have cfg : (⟨some label,st,tapes⟩ : preMachine.Cfg) =
            preCfg label st (tapes .input) (tapes .header) (tapes .scratch)
              (tapes .query) (tapes .output) := by
          congr 1
          funext stack; cases stack <;> rfl
        rw [cfg] at frame rejected trace ⊢
        by_cases error : label = .badInput
        · subst label
          have empty : tapes .output = [] := frame.1
          refine ⟨st,tapes .input,tapes .header,tapes .scratch,tapes .query,⟨?_⟩⟩
          rw [empty]
          exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.zero_le _ }
        · let next := TM2.stepAux (preMachine.m label) st tapes
          have ⟨fr,eqv⟩ := phaseStep label st (tapes .input) (tapes .header)
            (tapes .scratch) (tapes .query) (tapes .output) frame error
          have tapesEq : preStacks (tapes .input) (tapes .header) (tapes .scratch)
              (tapes .query) (tapes .output) = tapes := by
            funext stack; cases stack <;> rfl
          rw [tapesEq] at fr eqv
          have step : preMachine.step (preCfg label st (tapes .input) (tapes .header)
              (tapes .scratch) (tapes .query) (tapes .output)) = some next := by
            rw [← cfg]; rfl
          have tailTrace : (flip bind preMachine.step)^[k] (some next) = some d := by
            simp only [Function.iterate_succ_apply, flip, Option.bind_some] at trace
            change (flip bind preMachine.step)^[k]
              (preMachine.step (preCfg label st (tapes .input) (tapes .header)
                (tapes .scratch) (tapes .query) (tapes .output))) = some d at trace
            rw [step] at trace
            exact trace
          obtain ⟨st',input,header,scratch,query,⟨tail⟩⟩ :=
            ih next d fr (fun h => rejected (eqv.mpr h)) tailTrace terminal
          have head : EvalsToInTime preMachine.step
              (preCfg label st (tapes .input) (tapes .header) (tapes .scratch)
                (tapes .query) (tapes .output)) (some next) 1 :=
            { steps := 1, evals_in_steps := step, steps_le_m := le_refl _ }
          refine ⟨st',input,header,scratch,query,⟨?_⟩⟩
          simpa [Nat.add_comm] using EvalsToInTime.trans preMachine.step 1 k _ _ _ head tail
  have traceReaches : ∀ (f : preMachine.Cfg → Option preMachine.Cfg) k a b,
      (flip bind f)^[k] (some a) = some b → Reaches f a b := by
    intro f
    have noneStable : ∀ k, (flip bind f)^[k] none = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa [Function.iterate_succ_apply, flip] using ih
    intro k
    induction k with
    | zero =>
      intro a b trace
      have he : a = b := Option.some.inj trace
      subst b
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro a b trace
      simp only [Function.iterate_succ_apply, flip, Option.bind_some] at trace
      change (flip bind f)^[k] (f a) = some b at trace
      cases he : f a with
      | none => rw [he, noneStable] at trace; cases trace
      | some a' =>
        rw [he] at trace
        exact Relation.ReflTransGen.head he (ih a' b trace)
  have terminalUnique : ∀ (out out' : List Bool) (m m' : Nat),
      EvalsToInTime preMachine.step (initList preMachine w)
        (some (haltList preMachine out)) m →
      EvalsToInTime preMachine.step (initList preMachine w)
        (some (haltList preMachine out')) m' → out = out' := by
    intro out out' m m' a b
    have same : haltList preMachine out = haltList preMachine out' := by
      apply Part.mem_unique
      · exact mem_eval.mpr ⟨traceReaches _ a.steps _ _ a.evals_in_steps,rfl⟩
      · exact mem_eval.mpr ⟨traceReaches _ b.steps _ _ b.evals_in_steps,rfl⟩
    exact congrArg (fun c : preMachine.Cfg => c.stk .output) same
  obtain ⟨out,⟨run⟩,growth⟩ := pre_total_clock w
  cases decoded : readWord false w with
  | none =>
    have initSafe : Safe (initList preMachine w) := by
      simp [Safe,preFrame,initList,preMachine,Function.update_apply]
    have rejected : ¬ Accepted (initList preMachine w) := by
      change ¬ Header 0 w
      rintro ⟨n,tail,hw,body⟩
      have body' : Body n tail := by simpa only [Nat.zero_add] using body
      rcases body' with ⟨F,ht,width⟩
      have encoded : w = encodeWord false F := by
        rw [hw,ht]
        simp [encodeWord,bodyWord,List.append_assoc]
      have success := (codec_exact false w n F).mpr ⟨encoded,width⟩
      rw [decoded] at success
      cases success
    obtain ⟨st,input,header,scratch,query,⟨errorRun⟩⟩ :=
      failPrefix run.steps (initList preMachine w) (haltList preMachine out)
        initSafe rejected run.evals_in_steps rfl
    obtain ⟨cleanup⟩ := pre_error_cleanup st input header scratch query
    have complete := EvalsToInTime.trans preMachine.step run.steps
      (input.length+header.length+scratch.length+query.length+5) _ _ _ errorRun cleanup
    have identity := terminalUnique out dummyQuery _ _ run complete
    subst out
    have check : readWord true dummyQuery = some ⟨0,[[]]⟩ := by decide
    have formulaEq : preparedFormula w = ⟨0,[[]]⟩ := by
      unfold preparedFormula
      rw [decoded]
      rfl
    have finalCheck : readWord true (preparedQuery w) = some (preparedFormula w) := by
      simpa [preparedQuery,decoded,formulaEq] using check
    have finalSound := (codec_exact true (preparedQuery w)
      (preparedFormula w).1 (preparedFormula w).2).mp finalCheck
    refine ⟨?_,finalCheck,finalSound.1,finalSound.2,?_,?_⟩
    · simpa [preparedQuery,decoded] using Nonempty.intro run
    · simpa [preparedQuery,decoded] using growth
    · intro ignored
      refine ⟨st,input,header,scratch,query,⟨?_⟩⟩
      exact { errorRun with steps_le_m := le_trans errorRun.steps_le_m run.steps_le_m }
  | some value =>
    rcases value with ⟨n,F⟩
    obtain ⟨encoded,width⟩ := (codec_exact false w n F).mp decoded
    have formulaEq : preparedFormula w = ⟨n,F⟩ := by
      unfold preparedFormula
      rw [decoded]
      rfl
    have sourceEq : encodeWord false F = sourceWord F := by
      simp [encodeWord,bodyWord,termWord,sourceWord,List.append_assoc]
      apply congrArg (fun fn : Std.Sat.CNF.Clause (Fin n) → List Bool => F.flatMap fn)
      funext c
      simp [unaryClause,List.append_assoc]
    obtain ⟨valid⟩ := (pre_query_run F width).1
    rw [← sourceEq,← encoded] at valid
    have identity := terminalUnique out (queryWord F) _ _ run valid
    subst out
    have queryEq : queryWord F = encodeWord true F := by
      simp [encodeWord,bodyWord,termWord,queryWord,List.append_assoc]
      apply congrArg (fun fn : Std.Sat.CNF.Clause (Fin n) → List Bool => F.flatMap fn)
      funext c
      simp [queryClause,List.append_assoc]
    have check := (codec_exact true (queryWord F) n F).mpr ⟨queryEq,width⟩
    have finalCheck : readWord true (preparedQuery w) = some (preparedFormula w) := by
      simpa [preparedQuery,decoded,formulaEq] using check
    have finalSound := (codec_exact true (preparedQuery w)
      (preparedFormula w).1 (preparedFormula w).2).mp finalCheck
    refine ⟨?_,finalCheck,finalSound.1,finalSound.2,?_,?_⟩
    · simpa [preparedQuery,decoded] using Nonempty.intro run
    · simpa [preparedQuery,decoded] using growth
    · intro failure
      cases failure

end PredictiveThermodynamic

