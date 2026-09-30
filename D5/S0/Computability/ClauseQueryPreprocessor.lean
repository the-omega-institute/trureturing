/- GID: D5/S0/Computability/ClauseQueryPreprocessor
   generality: G
   mirror-B: D5/S0/Computability/ClauseQueryPreprocessor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: ["mathlib/module/Mathlib.Computability.TuringMachine.Computable"]
   utility: kind=checker; basis=consumer=D5/S0/Computability/ClausePreprocessorRefinement.pre_word_run; instance=D5/S0/Computability/ClauseQueryPreprocessor.dummySource
   digest: A fixed finite stack program validates unary clauses and emits physical queries. -/

import Std.Sat.CNF.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
The fixed program validates raw unary source words and emits physical query
words. Its execution law is consumed by the accepted branch of pre_word_run,
which identifies the exact clean output for every raw input. The concrete source
dummySource is the valid zero-variable formula with one empty clause; its query
output is dummyQuery. Source validation and physical query decoding have distinct
input roles, even though this accepted source shares its output with rejection
cleanup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic

open Turing StateTransition

inductive PreStack
  | input | header | scratch | query | output
  deriving DecidableEq, Fintype, Inhabited

inductive PreLabel
  | first | header | formulaZero | formulaTag | coefficient | restoreCoefficient
  | clauseOne | clauseTag | polarity | index | restoreIndex | endInput
  | clearHeader | reverse | badInput | badHeader | badScratch | badQuery | dummy
  deriving DecidableEq, Fintype, Inhabited

structure PreControl where
  seen : Option Bool := none
  mark : Option Bool := none
  literals : Fin 4 := 0
  deriving DecidableEq, Fintype, Inhabited

def preRead (s : PreControl) (b : Option Bool) : PreControl := { s with seen := b }
def preMark (s : PreControl) (b : Option Bool) : PreControl := { s with mark := b }
def preClear (s : PreControl) : PreControl := { s with seen := none, mark := none }

def prePush (stack : PreStack) (bits : List Bool)
    (next : TM2.Stmt (fun _ : PreStack => Bool) PreLabel PreControl) :
    TM2.Stmt (fun _ : PreStack => Bool) PreLabel PreControl :=
  match bits with
  | [] => next
  | b :: bs => .push stack (fun _ => b) (prePush stack bs next)

def dummyQuery : List Bool :=
  [true, true, false, false, false, false, true,
    false, true, true, false, true, false, false, false]

def preMachine : FinTM2 where
  K := PreStack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := PreLabel
  main := .first
  σ := PreControl
  initialState := (⟨none, none, 0⟩ : PreControl)
  m
    | .first => prePush .query [true, true] (.goto fun _ => .header)
    | .header =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone) (.goto fun _ => .badInput) <|
          .branch (fun s => s.seen.getD false)
            (.push .header (fun _ => true) <| .push .query (fun _ => true) <|
              .load preClear <| .goto fun _ => .header)
            (prePush .query [false, false, false, false, true] <|
              .load preClear <| .goto fun _ => .formulaZero)
    | .formulaZero =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isSome && !(s.seen.getD true))
          (.load preClear <| .goto fun _ => .formulaTag)
          (.goto fun _ => .badInput)
    | .formulaTag =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone) (.goto fun _ => .badInput) <|
          .branch (fun s => s.seen.getD false)
            (prePush .query [false, true, true] <|
              .load (fun s => { (preClear s) with literals := 0 }) <|
                .goto fun _ => .coefficient)
            (.load preClear <| .goto fun _ => .endInput)
    | .coefficient =>
      .pop .header preMark <|
        .branch (fun s => s.mark.isNone)
          (.push .query (fun _ => false) <| .load preClear <|
            .goto fun _ => .restoreCoefficient)
          (.push .scratch (fun _ => true) <| .push .query (fun _ => true) <|
            .load preClear <| .goto fun _ => .coefficient)
    | .restoreCoefficient =>
      .pop .scratch preMark <|
        .branch (fun s => s.mark.isNone)
          (.load preClear <| .goto fun _ => .clauseOne)
          (.push .header (fun _ => true) <| .load preClear <|
            .goto fun _ => .restoreCoefficient)
    | .clauseOne =>
      .pop .input preRead <|
        .branch (fun s => s.seen.getD false)
          (.load preClear <| .goto fun _ => .clauseTag)
          (.goto fun _ => .badInput)
    | .clauseTag =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone) (.goto fun _ => .badInput) <|
          .branch (fun s => s.seen.getD false)
            (.branch (fun s => decide (s.literals.val < 3))
              (prePush .query [true, true] <|
                .load (fun s => { (preClear s) with literals := s.literals + 1 }) <|
                  .goto fun _ => .polarity)
              (.goto fun _ => .badInput))
            (prePush .query [true, false] <|
              .load (fun s => { (preClear s) with literals := 0 }) <|
                .goto fun _ => .formulaZero)
    | .polarity =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone) (.goto fun _ => .badInput)
          (.push .query (fun s => s.seen.getD false) <|
            .load preClear <| .goto fun _ => .index)
    | .index =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone) (.goto fun _ => .badInput) <|
          .branch (fun s => s.seen.getD false)
            (.pop .header preMark <|
              .branch (fun s => s.mark.isNone) (.goto fun _ => .badInput)
                (.push .scratch (fun _ => true) <| .push .query (fun _ => true) <|
                  .load preClear <| .goto fun _ => .index))
            (.peek .header preMark <|
              .branch (fun s => s.mark.isNone) (.goto fun _ => .badInput)
                (.push .query (fun _ => false) <| .load preClear <|
                  .goto fun _ => .restoreIndex))
    | .restoreIndex =>
      .pop .scratch preMark <|
        .branch (fun s => s.mark.isNone)
          (.load preClear <| .goto fun _ => .clauseOne)
          (.push .header (fun _ => true) <| .load preClear <|
            .goto fun _ => .restoreIndex)
    | .endInput =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone)
          (prePush .query [false, false] <| .load preClear <|
            .goto fun _ => .clearHeader)
          (.goto fun _ => .badInput)
    | .clearHeader =>
      .pop .header preMark <|
        .branch (fun s => s.mark.isNone)
          (.load preClear <| .goto fun _ => .reverse)
          (.load preClear <| .goto fun _ => .clearHeader)
    | .reverse =>
      .pop .query preRead <|
        .branch (fun s => s.seen.isNone)
          (.load (fun _ => (⟨none, none, 0⟩ : PreControl)) .halt)
          (.push .output (fun s => s.seen.getD false) <|
            .load preClear <| .goto fun _ => .reverse)
    | .badInput =>
      .pop .input preRead <|
        .branch (fun s => s.seen.isNone)
          (.load preClear <| .goto fun _ => .badHeader)
          (.load preClear <| .goto fun _ => .badInput)
    | .badHeader =>
      .pop .header preMark <|
        .branch (fun s => s.mark.isNone)
          (.load preClear <| .goto fun _ => .badScratch)
          (.load preClear <| .goto fun _ => .badHeader)
    | .badScratch =>
      .pop .scratch preMark <|
        .branch (fun s => s.mark.isNone)
          (.load preClear <| .goto fun _ => .badQuery)
          (.load preClear <| .goto fun _ => .badScratch)
    | .badQuery =>
      .pop .query preRead <|
        .branch (fun s => s.seen.isNone)
          (.load preClear <| .goto fun _ => .dummy)
          (.load preClear <| .goto fun _ => .badQuery)
    | .dummy => prePush .output dummyQuery.reverse (.load (fun _ => (⟨none, none, 0⟩ : PreControl)) .halt)

def preStacks (input header scratch query output : List Bool) : PreStack -> List Bool
  | .input => input
  | .header => header
  | .scratch => scratch
  | .query => query
  | .output => output

def preCfg (label : PreLabel) (state : PreControl)
    (input header scratch query output : List Bool) : preMachine.Cfg :=
  ⟨some label, state, preStacks input header scratch query output⟩

abbrev UnaryFormula (n : Nat) := List (Std.Sat.CNF.Clause (Fin n))

def unaryLiteral {n : Nat} (literal : Fin n × Bool) : List Bool :=
  [true, true, literal.2] ++ List.replicate literal.1.val true ++ [false]

def unaryClause {n : Nat} (c : Std.Sat.CNF.Clause (Fin n)) : List Bool :=
  [false, true] ++ (c.flatMap unaryLiteral) ++ [true, false]

def sourceWord {n : Nat} (F : UnaryFormula n) : List Bool :=
  List.replicate n true ++ [false] ++ F.flatMap unaryClause ++ [false, false]

/-- The valid raw source word 0011000: zero variables and one empty clause. -/
def dummySource : List Bool := sourceWord (n := 0) ([[]] : UnaryFormula 0)

def queryClause {n : Nat} (c : Std.Sat.CNF.Clause (Fin n)) : List Bool :=
  [false, true] ++ List.replicate (n + 1) true ++ [false] ++
    (c.flatMap unaryLiteral) ++ [true, false]

def queryWord {n : Nat} (F : UnaryFormula n) : List Bool :=
  [true, true] ++ List.replicate n true ++ [false, false, false, false, true] ++
    F.flatMap queryClause ++ [false, false]

macro "pre_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    try simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, List.append_nil]
    dsimp [preMachine, TM2.stepAux, preCfg, preStacks, preRead, preMark,
      preClear, prePush, haltList]
    simp [Function.update_apply, preStacks] <;>
      first | rfl | (funext k; cases k <;> simp [Function.update_apply, preStacks])))

private def restoreRun (label : PreLabel)
    (validLabel : label = .restoreCoefficient ∨ label = .restoreIndex)
    (st : PreControl) (input q : List Bool) (t h : Nat) :
    EvalsToInTime preMachine.step
      (preCfg label st input (List.replicate h true) (List.replicate t true) q [])
      (some (preCfg .clauseOne (preClear st) input (List.replicate (h + t) true) [] q []))
      (t + 1) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction t generalizing st h with
  | zero =>
    have hs : preMachine.step (preCfg label st input (List.replicate h true) [] q []) =
        some (preCfg .clauseOne (preClear st) input (List.replicate h true) [] q []) := by
      rcases validLabel with rfl | rfl <;> pre_transition
    exact single _ _ hs
  | succ t ih =>
    have hs : preMachine.step
        (preCfg label st input (List.replicate h true) (List.replicate (t + 1) true) q []) =
        some (preCfg label (preClear st) input (List.replicate (h + 1) true)
          (List.replicate t true) q []) := by
      rcases validLabel with rfl | rfl <;> pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (t + 1) _ _ _ head
      (ih (preClear st) (h + 1))
    simpa [preClear, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

private def coefficientRun (st : PreControl) (input q : List Bool) (n t : Nat) :
    EvalsToInTime preMachine.step
      (preCfg .coefficient st input (List.replicate n true) (List.replicate t true) q [])
      (some (preCfg .clauseOne (preClear st) input (List.replicate (n + t) true) []
        (false :: (List.replicate n true ++ q)) [])) (2 * n + t + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction n generalizing st q t with
  | zero =>
    have hs : preMachine.step (preCfg .coefficient st input [] (List.replicate t true) q []) =
        some (preCfg .restoreCoefficient (preClear st) input [] (List.replicate t true)
          (false :: q) []) := by pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (t + 1) _ _ _ head
      (restoreRun .restoreCoefficient (Or.inl rfl) (preClear st) input (false :: q) t 0)
    simpa [preClear] using run
  | succ n ih =>
    have hs : preMachine.step
        (preCfg .coefficient st input (List.replicate (n + 1) true)
          (List.replicate t true) q []) =
        some (preCfg .coefficient (preClear st) input (List.replicate n true)
          (List.replicate (t + 1) true) (true :: q) []) := by pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (2 * n + (t + 1) + 2) _ _ _ head
      (ih (preClear st) (true :: q) (t + 1))
    have words : List.replicate n true ++ true :: q = List.replicate (n + 1) true ++ q := by
      rw [List.replicate_add]
      simp
    have clock : (2 * n + (t + 1) + 2) + 1 = 2 * (n + 1) + t + 2 := by omega
    rw [clock] at run
    simpa [preClear, words, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

private def indexRun (st : PreControl) (input q : List Bool) (i h t : Nat) (positive : 0 < h) :
    EvalsToInTime preMachine.step
      (preCfg .index st (List.replicate i true ++ false :: input)
        (List.replicate (h + i) true) (List.replicate t true) q [])
      (some (preCfg .clauseOne (preClear st) input (List.replicate (h + i + t) true) []
        (false :: (List.replicate i true ++ q)) [])) (2 * i + t + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction i generalizing st q t with
  | zero =>
    have nonemptyHeader : List.replicate h true = true :: List.replicate (h - 1) true := by
      rw [show h = (h - 1) + 1 from by omega, List.replicate_succ]
      simp
    have hs : preMachine.step
        (preCfg .index st (false :: input) (List.replicate h true)
          (List.replicate t true) q []) =
        some (preCfg .restoreIndex (preClear st) input (List.replicate h true)
          (List.replicate t true) (false :: q) []) := by
      rw [nonemptyHeader]
      pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (t + 1) _ _ _ head
      (restoreRun .restoreIndex (Or.inr rfl) (preClear st) input (false :: q) t h)
    simpa [preClear] using run
  | succ i ih =>
    have hs : preMachine.step
        (preCfg .index st (List.replicate (i + 1) true ++ false :: input)
          (List.replicate (h + i + 1) true) (List.replicate t true) q []) =
        some (preCfg .index (preClear st) (List.replicate i true ++ false :: input)
          (List.replicate (h + i) true) (List.replicate (t + 1) true) (true :: q) []) := by
      pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (2 * i + (t + 1) + 2) _ _ _ head
      (ih (preClear st) (true :: q) (t + 1))
    have words : List.replicate i true ++ true :: q = List.replicate (i + 1) true ++ q := by
      rw [List.replicate_add]
      simp
    have clock : (2 * i + (t + 1) + 2) + 1 = 2 * (i + 1) + t + 2 := by omega
    rw [clock] at run
    simpa [preClear, words, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

private def reverseQueryRun (st : PreControl) (q output : List Bool) :
    EvalsToInTime preMachine.step (preCfg .reverse st [] [] [] q output)
      (some (haltList preMachine (q.reverse ++ output))) (q.length + 1) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction q generalizing st output with
  | nil =>
    have hs : preMachine.step (preCfg .reverse st [] [] [] [] output) =
        some (haltList preMachine output) := by pre_transition
    exact single _ _ hs
  | cons b bs ih =>
    have hs : preMachine.step (preCfg .reverse st [] [] [] (b :: bs) output) =
        some (preCfg .reverse (preClear st) [] [] [] bs (b :: output)) := by
      cases b <;> pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (bs.length + 1) _ _ _ head
      (ih (preClear st) (b :: output))
    simpa [List.reverse_cons, List.append_assoc] using run

private def clearHeaderRun (st : PreControl) (q : List Bool) (n : Nat) :
    EvalsToInTime preMachine.step
      (preCfg .clearHeader st [] (List.replicate n true) [] q [])
      (some (haltList preMachine q.reverse)) (n + q.length + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction n generalizing st with
  | zero =>
    have hs : preMachine.step (preCfg .clearHeader st [] [] [] q []) =
        some (preCfg .reverse (preClear st) [] [] [] q []) := by pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    simpa using EvalsToInTime.trans preMachine.step 1 (q.length + 1) _ _ _ head
      (reverseQueryRun (preClear st) q [])
  | succ n ih =>
    have hs : preMachine.step
        (preCfg .clearHeader st [] (List.replicate (n + 1) true) [] q []) =
        some (preCfg .clearHeader (preClear st) [] (List.replicate n true) [] q []) := by
      pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans preMachine.step 1 (n + q.length + 2) _ _ _ head (ih (preClear st))

private def clauseRun {n : Nat} (c : Std.Sat.CNF.Clause (Fin n))
    (st : PreControl) (input q : List Bool) (width : st.literals.val + c.length ≤ 3) :
    EvalsToInTime preMachine.step
      (preCfg .clauseOne st (c.flatMap unaryLiteral ++ [true, false] ++ input)
        (List.replicate n true) [] q [])
      (some (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) input (List.replicate n true) []
        ([false, true] ++ (c.flatMap unaryLiteral).reverse ++ q) []))
      (2 * (c.flatMap unaryLiteral).length + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction c generalizing st q with
  | nil =>
    have hs : preMachine.step
        (preCfg .clauseOne st (true :: false :: input) (List.replicate n true) [] q []) =
        some (preCfg .clauseTag (preClear st) (false :: input)
          (List.replicate n true) [] q []) := by pre_transition
    have ht : preMachine.step
        (preCfg .clauseTag (preClear st) (false :: input) (List.replicate n true) [] q []) =
        some (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) input (List.replicate n true) []
          (false :: true :: q) []) := by pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    let tail : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ ht
    simpa using EvalsToInTime.trans preMachine.step 1 1 _ _ _ head tail
  | cons literal c ih =>
    rcases literal with ⟨i, b⟩
    have below : st.literals.val < 3 := by simp only [List.length_cons] at width; omega
    let next : PreControl := { (preClear st) with literals := st.literals + 1 }
    let rest := c.flatMap unaryLiteral ++ [true, false] ++ input
    have h0 : preMachine.step
        (preCfg .clauseOne st (true :: true :: b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] q []) =
        some (preCfg .clauseTag (preClear st)
          (true :: b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] q []) := by pre_transition
    have h1 : preMachine.step
        (preCfg .clauseTag (preClear st)
          (true :: b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] q []) =
        some (preCfg .polarity next (b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] (true :: true :: q) []) := by
      apply congrArg some
      dsimp [preMachine, TM2.stepAux, preCfg, preStacks, preRead, preMark,
        preClear, prePush, next]
      simp only [below, decide_true]
      dsimp only [cond]
      simp [Function.update_apply, preStacks] <;>
        first | rfl | (funext k; cases k <;> simp [Function.update_apply, preStacks])
    have h2 : preMachine.step
        (preCfg .polarity next (b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] (true :: true :: q) []) =
        some (preCfg .index (preClear next) (List.replicate i.val true ++ false :: rest)
          (List.replicate n true) [] (b :: true :: true :: q) []) := by
      cases b <;> pre_transition
    let a : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h0
    let bstep : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h1
    let d : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h2
    have positive : 0 < n - i.val := by have := i.isLt; omega
    have idx := indexRun (preClear next) rest (b :: true :: true :: q) i.val (n - i.val) 0 positive
    have hi : n - i.val + i.val = n := Nat.sub_add_cancel (Nat.le_of_lt i.isLt)
    simp only [hi, Nat.add_zero] at idx
    have count : next.literals.val = st.literals.val + 1 := by
      change (st.literals + 1).val = st.literals.val + 1
      simp only [Fin.val_add, show (1 : Fin 4).val = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have widthTail : (preClear (preClear next)).literals.val + c.length ≤ 3 := by
      change next.literals.val + c.length ≤ 3
      rw [count]
      simp only [List.length_cons] at width
      omega
    have tail := ih (preClear (preClear next))
      (false :: (List.replicate i.val true ++ b :: true :: true :: q)) widthTail
    have r3 := EvalsToInTime.trans preMachine.step (2 * i.val + 0 + 2)
      (2 * (c.flatMap unaryLiteral).length + 2) _ _ _ idx tail
    have r2 := EvalsToInTime.trans preMachine.step 1
      ((2 * (c.flatMap unaryLiteral).length + 2) + (2 * i.val + 0 + 2)) _ _ _ d r3
    have r1 := EvalsToInTime.trans preMachine.step 1
      (((2 * (c.flatMap unaryLiteral).length + 2) + (2 * i.val + 0 + 2)) + 1) _ _ _ bstep r2
    have run := EvalsToInTime.trans preMachine.step 1
      ((((2 * (c.flatMap unaryLiteral).length + 2) + (2 * i.val + 0 + 2)) + 1) + 1) _ _ _ a r1
    have words : (unaryLiteral (i, b)).reverse ++ q =
        false :: (List.replicate i.val true ++ b :: true :: true :: q) := by
      simp [unaryLiteral, List.reverse_append, List.append_assoc]
    have run' : EvalsToInTime preMachine.step
        (preCfg .clauseOne st (true :: true :: b :: (List.replicate i.val true ++ false :: rest))
          (List.replicate n true) [] q [])
        (some (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) input (List.replicate n true) []
          ([false, true] ++ (c.flatMap unaryLiteral).reverse ++ (unaryLiteral (i, b)).reverse ++ q) []))
        (2 * ((unaryLiteral (i, b)).length + (c.flatMap unaryLiteral).length) + 2) := by
      rw [List.append_assoc, words]
      refine { run with steps_le_m := ?_ }
      have hb := run.steps_le_m
      simp only [unaryLiteral, List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at ⊢
      omega
    simpa only [rest, List.flatMap_cons, unaryLiteral, List.reverse_append,
      List.append_assoc, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, List.reverse_replicate, List.reverse_cons,
      List.reverse_nil, List.cons_append, List.nil_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.zero_add, Nat.add_zero] using run'

private def headerRun (st : PreControl) (input q : List Bool) (n t : Nat) :
    EvalsToInTime preMachine.step
      (preCfg .header st (List.replicate n true ++ false :: input)
        (List.replicate t true) [] q [])
      (some (preCfg .formulaZero (preClear st) input (List.replicate (n + t) true) []
        ([true, false, false, false, false] ++ List.replicate n true ++ q) [])) (n + 1) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction n generalizing st q t with
  | zero =>
    have hs : preMachine.step (preCfg .header st (false :: input) (List.replicate t true) [] q []) =
        some (preCfg .formulaZero (preClear st) input (List.replicate t true) []
          (true :: false :: false :: false :: false :: q) []) := by pre_transition
    simpa using single _ _ hs
  | succ n ih =>
    have hs : preMachine.step
        (preCfg .header st (List.replicate (n + 1) true ++ false :: input)
          (List.replicate t true) [] q []) =
        some (preCfg .header (preClear st) (List.replicate n true ++ false :: input)
          (List.replicate (t + 1) true) [] (true :: q) []) := by pre_transition
    let head : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ hs
    have run := EvalsToInTime.trans preMachine.step 1 (n + 1) _ _ _ head
      (ih (preClear st) (true :: q) (t + 1))
    have words : List.replicate n true ++ true :: q = List.replicate (n + 1) true ++ q := by
      rw [List.replicate_add]
      simp
    simpa [preClear, List.append_assoc, words, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using run

private def formulaRun {n : Nat} (F : UnaryFormula n) (q : List Bool)
    (width : ∀ c ∈ F, c.length ≤ 3) :
    EvalsToInTime preMachine.step
      (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) (F.flatMap unaryClause ++ [false, false])
        (List.replicate n true) [] q [])
      (some (preCfg .endInput (⟨none, none, 0⟩ : PreControl) [] (List.replicate n true) []
        ((F.flatMap queryClause).reverse ++ q) []))
      (2 * (F.flatMap queryClause).length + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  induction F generalizing q with
  | nil =>
    have h0 : preMachine.step
        (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) [false, false] (List.replicate n true) [] q []) =
        some (preCfg .formulaTag (⟨none, none, 0⟩ : PreControl) [false] (List.replicate n true) [] q []) := by
      pre_transition
    have h1 : preMachine.step
        (preCfg .formulaTag (⟨none, none, 0⟩ : PreControl) [false] (List.replicate n true) [] q []) =
        some (preCfg .endInput (⟨none, none, 0⟩ : PreControl) [] (List.replicate n true) [] q []) := by pre_transition
    let a : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h0
    let b : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h1
    simpa using EvalsToInTime.trans preMachine.step 1 1 _ _ _ a b
  | cons c F ih =>
    let rest := F.flatMap unaryClause ++ [false, false]
    let body := c.flatMap unaryLiteral ++ [true, false] ++ rest
    let coef := false :: (List.replicate n true ++ true :: true :: false :: q)
    have h0 : preMachine.step
        (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) (false :: true :: body) (List.replicate n true) [] q []) =
        some (preCfg .formulaTag (⟨none, none, 0⟩ : PreControl) (true :: body) (List.replicate n true) [] q []) := by
      pre_transition
    have h1 : preMachine.step
        (preCfg .formulaTag (⟨none, none, 0⟩ : PreControl) (true :: body) (List.replicate n true) [] q []) =
        some (preCfg .coefficient (⟨none, none, 0⟩ : PreControl) body (List.replicate n true) []
          (true :: true :: false :: q) []) := by pre_transition
    let a : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h0
    let b : EvalsToInTime preMachine.step _ _ 1 :=
      single _ _ h1
    have copy := coefficientRun (⟨none, none, 0⟩ : PreControl) body (true :: true :: false :: q) n 0
    simp only [Nat.add_zero] at copy
    have localClause := clauseRun c (⟨none, none, 0⟩ : PreControl) rest coef (by simpa using width c (by simp))
    have tail := ih ([false, true] ++ (c.flatMap unaryLiteral).reverse ++ coef)
      (fun d hd => width d (by simp [hd]))
    have r4 := EvalsToInTime.trans preMachine.step
      (2 * (c.flatMap unaryLiteral).length + 2) (2 * (F.flatMap queryClause).length + 2)
      _ _ _ localClause tail
    have r3 := EvalsToInTime.trans preMachine.step (2 * n + 2)
      ((2 * (F.flatMap queryClause).length + 2) + (2 * (c.flatMap unaryLiteral).length + 2))
      _ _ _ copy r4
    have r2 := EvalsToInTime.trans preMachine.step 1
      (((2 * (F.flatMap queryClause).length + 2) + (2 * (c.flatMap unaryLiteral).length + 2)) +
        (2 * n + 2)) _ _ _ b r3
    have run := EvalsToInTime.trans preMachine.step 1
      ((((2 * (F.flatMap queryClause).length + 2) + (2 * (c.flatMap unaryLiteral).length + 2)) +
        (2 * n + 2)) + 1) _ _ _ a r2
    have words : [false, true] ++ (c.flatMap unaryLiteral).reverse ++ coef =
        (queryClause c).reverse ++ q := by
      simp [coef, queryClause, List.reverse_append, List.replicate_succ,
        List.append_assoc]
    have run' : EvalsToInTime preMachine.step
        (preCfg .formulaZero (⟨none, none, 0⟩ : PreControl) (false :: true :: body) (List.replicate n true) [] q [])
        (some (preCfg .endInput (⟨none, none, 0⟩ : PreControl) [] (List.replicate n true) []
          ((F.flatMap queryClause).reverse ++ (queryClause c).reverse ++ q) []))
        (2 * ((queryClause c).length + (F.flatMap queryClause).length) + 2) := by
      rw [List.append_assoc, ← words]
      refine { run with steps_le_m := ?_ }
      have hb := run.steps_le_m
      simp only [queryClause, List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at ⊢
      omega
    simpa [body, rest, List.flatMap_cons, unaryClause, List.reverse_append,
      List.append_assoc] using run'

theorem pre_query_run {n : Nat} (F : UnaryFormula n) (width : ∀ c ∈ F, c.length ≤ 3) :
    Nonempty (TM2OutputsInTime preMachine (sourceWord F) (some (queryWord F))
      (3 * ((sourceWord F).length + 3) ^ 2 + 7)) ∧
    (queryWord F).length = (sourceWord F).length + 6 + F.length * (n + 2) := by
  let single : ∀ (a : preMachine.Cfg) (b : Option preMachine.Cfg),
      preMachine.step a = b → EvalsToInTime preMachine.step a b 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  let framing := [true, false, false, false, false] ++ List.replicate n true ++ [true, true]
  let q := (F.flatMap queryClause).reverse ++ framing
  have first : preMachine.step (initList preMachine (sourceWord F)) =
      some (preCfg .header (⟨none, none, 0⟩ : PreControl) (sourceWord F) [] [] [true, true] []) := by
    apply congrArg some
    dsimp [preMachine, TM2.stepAux, preCfg, preStacks, prePush, initList]
    congr 1
    funext k
    cases k <;> rfl
  let begin : EvalsToInTime preMachine.step _ _ 1 :=
    single _ _ first
  have head := headerRun (⟨none, none, 0⟩ : PreControl) (F.flatMap unaryClause ++ [false, false]) [true, true] n 0
  have middle := formulaRun F framing width
  have last : preMachine.step (preCfg .endInput (⟨none, none, 0⟩ : PreControl) [] (List.replicate n true) [] q []) =
      some (preCfg .clearHeader (⟨none, none, 0⟩ : PreControl) [] (List.replicate n true) [] (false :: false :: q) []) := by
    pre_transition
  let endStep : EvalsToInTime preMachine.step _ _ 1 :=
    single _ _ last
  have finish := clearHeaderRun (⟨none, none, 0⟩ : PreControl) (false :: false :: q) n
  have queryReverse : false :: false :: q = (queryWord F).reverse := by
    simp [q, framing, queryWord, List.reverse_append, List.append_assoc]
  have r4 := EvalsToInTime.trans preMachine.step 1 (n + (false :: false :: q).length + 2)
    _ _ _ endStep finish
  have r3 := EvalsToInTime.trans preMachine.step (2 * (F.flatMap queryClause).length + 2)
    ((n + (false :: false :: q).length + 2) + 1) _ _ _ middle r4
  have r2 := EvalsToInTime.trans preMachine.step (n + 1)
    (((n + (false :: false :: q).length + 2) + 1) + (2 * (F.flatMap queryClause).length + 2))
    _ _ _ head r3
  simp only [List.replicate_zero, Nat.add_zero] at r2
  have sourceShape : List.replicate n true ++
      false :: (F.flatMap unaryClause ++ [false, false]) = sourceWord F := by
    simp [sourceWord, List.append_assoc]
  rw [sourceShape] at r2
  have run := EvalsToInTime.trans preMachine.step 1
    ((((n + (false :: false :: q).length + 2) + 1) + (2 * (F.flatMap queryClause).length + 2)) +
      (n + 1)) _ _ _ begin r2
  have difference : ∀ G : UnaryFormula n,
      (G.flatMap queryClause).length = (G.flatMap unaryClause).length + G.length * (n + 2) := by
    intro G
    induction G with
    | nil => simp
    | cons c G ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, ih,
        queryClause, unaryClause, List.length_replicate, List.length_nil]
      nlinarith
  have sourceLower : ∀ G : UnaryFormula n, 4 * G.length ≤ (G.flatMap unaryClause).length := by
    intro G
    induction G with
    | nil => simp
    | cons c G ih =>
      simp only [List.flatMap_cons, unaryClause, List.length_append, List.length_cons,
        List.length_nil] at ⊢
      omega
  have lengthEquation : (queryWord F).length = (sourceWord F).length + 6 + F.length * (n + 2) := by
    simp only [queryWord, sourceWord, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, difference F]
    omega
  have sourceN : n ≤ (sourceWord F).length := by
    simp [sourceWord]
  have sourceM : F.length ≤ (sourceWord F).length := by
    have h := sourceLower F
    simp only [sourceWord, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate]
    omega
  have growth : (queryWord F).length ≤ ((sourceWord F).length + 3) ^ 2 := by
    rw [lengthEquation]
    have hm := Nat.mul_le_mul sourceM (Nat.add_le_add_right sourceN 2)
    nlinarith
  have output : (false :: false :: q).reverse = queryWord F := by
    rw [queryReverse, List.reverse_reverse]
  constructor
  · refine ⟨?_⟩
    change EvalsToInTime preMachine.step _ _ _
    have run' : EvalsToInTime preMachine.step (initList preMachine (sourceWord F))
        (some (haltList preMachine (queryWord F)))
        (3 * ((sourceWord F).length + 3) ^ 2 + 7) := by
      rw [← output]
      refine { run with steps_le_m := ?_ }
      have hb := run.steps_le_m
      have qlength : (false :: false :: q).length = n + (F.flatMap queryClause).length + 9 := by
        simp [q, framing]
        omega
      have sameLength : (queryWord F).length = (false :: false :: q).length := by
        rw [queryReverse, List.length_reverse]
      rw [sameLength, qlength] at growth
      have bound : n + (false :: false :: q).length + 2 + 1 +
          (2 * (F.flatMap queryClause).length + 2) + (n + 1) + 1 ≤
          3 * ((sourceWord F).length + 3) ^ 2 + 7 := by omega
      exact le_trans hb bound
    exact run'
  · exact lengthEquation

end PredictiveThermodynamic
