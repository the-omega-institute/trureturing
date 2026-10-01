/- GID: D5/S0/Computability/ReverseClauseMachine
   generality: G
   mirror-B: D5/B/S0/Computability/ReverseClauseMachine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/ClausePreprocessorRefinement, D5/S0/Computability/ConventionalClauseWords]
   utility: kind=checker; basis=consumer=D5/S0/Computability/ReverseClauseConversion.reverse_word_run; instance=D5/S0/Computability/ClauseQueryPreprocessor.dummySource
   digest: Actual binary name writing and declared-variable tautology execution. -/

import D5.S0.Computability.ClausePreprocessorRefinement
import D5.S0.Computability.ConventionalClauseWords
import Mathlib.Tactic.DeriveFintype
/-! The actual reverse program parses every raw unary source, reuses the
preprocessor, removes physical coefficient syntax, writes distinct canonical
binary names, and appends consumer tautologies for every explicitly declared
variable. Those tautologies belong only to the conventional clause encoding;
they do not change the raw physical clauses or their Hamiltonian.
The private execution law is consumed by the all-word count and decoding
refinement. DummySource is valid source0011000, whose ordinary output011000 is
one empty clause. Acceptance and rejection are distinguished by the decoder,
even when they share that output. The output bound charges the explicit unary
universe, including every unused declared variable and the zero-variable case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.ConventionalReverse
open Turing StateTransition

inductive ReverseStack
  | pre (k : PreStack) | universeBits | index | saved | reversedOutput | output
  deriving DecidableEq, Fintype, Inhabited
inductive ReverseLabel
  | pre (label : PreLabel)
  | queryStart | header | staticPrefix | bodyFirst | bodySecond | coefficient
  | clauseFirst | clauseSecond | polarity | literalIndex
  | tautology | firstName | secondName | finishClause | clearIndex | returnOutput
  deriving DecidableEq, Fintype, Inhabited
abbrev ReverseControl := Sum PreControl (Option Bool)
def originalControl : ReverseControl → PreControl
  | .inl s => s
  | _ => ⟨none,none,0⟩
def held : ReverseControl → Option Bool
  | .inr b => b
  | _ => none
def read (_ : ReverseControl) (b : Option Bool) : ReverseControl := .inr b

def liftPre : TM2.Stmt (fun _ : PreStack => Bool) PreLabel PreControl →
    TM2.Stmt (fun _ : ReverseStack => Bool) ReverseLabel ReverseControl
  | .push k f next => .push (.pre k) (fun s => f (originalControl s)) (liftPre next)
  | .peek k f next => .peek (.pre k) (fun s b => .inl (f (originalControl s) b)) (liftPre next)
  | .pop k f next => .pop (.pre k) (fun s b => .inl (f (originalControl s) b)) (liftPre next)
  | .load f next => .load (fun s => .inl (f (originalControl s))) (liftPre next)
  | .branch f yes no => .branch (fun s => f (originalControl s)) (liftPre yes) (liftPre no)
  | .goto f => .goto (fun s => .pre (f (originalControl s)))
  | .halt => .load (fun _ => .inr none) <| .goto fun _ => .queryStart

-- Every use below writes one fixed finite block in its label statement.
def writeBits (bits : List Bool)
    (next : TM2.Stmt (fun _ : ReverseStack => Bool) ReverseLabel ReverseControl) :
    TM2.Stmt (fun _ : ReverseStack => Bool) ReverseLabel ReverseControl :=
  match bits with
  | [] => next
  | b::bits => .push .reversedOutput (fun _ => b) (writeBits bits next)

def reverseMachine : FinTM2 where
  K := ReverseStack
  k₀ := .pre .input
  k₁ := .output
  Γ _ := Bool
  Λ := ReverseLabel
  main := .pre .first
  σ := ReverseControl
  initialState := .inl ⟨none,none,0⟩
  m
    | .pre label => liftPre (preMachine.m label)
    | .queryStart => .pop (.pre .output) read <| .pop (.pre .output) read <|
        .load (fun _ => .inr none) <| .goto fun _ => .header
    | .header => .pop (.pre .output) read <|
        .branch (fun s => (held s).getD false)
          (.push .universeBits (fun _ => true) <| .load (fun _ => .inr none) <|
            .goto fun _ => .header)
          (.load (fun _ => .inr none) <| .goto fun _ => .staticPrefix)
    | .staticPrefix => .pop (.pre .output) read <| .pop (.pre .output) read <|
        .pop (.pre .output) read <| .pop (.pre .output) read <|
          .load (fun _ => .inr none) <| .goto fun _ => .bodyFirst
    | .bodyFirst => .pop (.pre .output) read <|
        .load (fun _ => .inr none) <| .goto fun _ => .bodySecond
    | .bodySecond => .pop (.pre .output) read <|
        .branch (fun s => (held s).getD false)
          (writeBits [false,true] <| .load (fun _ => .inr none) <|
            .goto fun _ => .coefficient)
          (.load (fun _ => .inr none) <| .goto fun _ => .tautology)
    | .coefficient => .pop (.pre .output) read <|
        .branch (fun s => (held s).getD false)
          (.load (fun _ => .inr none) <| .goto fun _ => .coefficient)
          (.load (fun _ => .inr none) <| .goto fun _ => .clauseFirst)
    | .clauseFirst => .pop (.pre .output) read <|
        .load (fun _ => .inr none) <| .goto fun _ => .clauseSecond
    | .clauseSecond => .pop (.pre .output) read <|
        .branch (fun s => (held s).getD false)
          (writeBits [true,true] <| .load (fun _ => .inr none) <|
            .goto fun _ => .polarity)
          (writeBits [true,false] <| .load (fun _ => .inr none) <|
            .goto fun _ => .bodyFirst)
    | .polarity => .pop (.pre .output) read <|
        .push .reversedOutput (fun s => (held s).getD false) <|
          writeBits [true,true] <| .load (fun _ => .inr none) <|
            .goto fun _ => .literalIndex
    | .literalIndex => .pop (.pre .output) read <|
        .branch (fun s => (held s).getD false)
          (writeBits [true,false] <| .load (fun _ => .inr none) <|
            .goto fun _ => .literalIndex)
          (writeBits [false] <| .load (fun _ => .inr none) <|
            .goto fun _ => .clauseFirst)
    | .tautology => .pop .universeBits read <|
        .branch (fun s => (held s).isNone)
          (.load (fun _ => .inr none) <| .goto fun _ => .clearIndex)
          (writeBits [false,true,true,true,true,true,true] <|
            .load (fun _ => .inr none) <| .goto fun _ => .firstName)
    | .firstName => .pop .index read <|
        .branch (fun s => (held s).isNone)
          (writeBits [false,true,true,false,true,true] <|
            .load (fun _ => .inr none) <| .goto fun _ => .secondName)
          (.push .saved (fun _ => true) <| writeBits [true,false] <|
            .load (fun _ => .inr none) <| .goto fun _ => .firstName)
    | .secondName => .pop .saved read <|
        .branch (fun s => (held s).isNone)
          (.load (fun _ => .inr none) <| .goto fun _ => .finishClause)
          (.push .index (fun _ => true) <| writeBits [true,false] <|
            .load (fun _ => .inr none) <| .goto fun _ => .secondName)
    | .finishClause => writeBits [false,true,false] <|
        .push .index (fun _ => true) <| .load (fun _ => .inr none) <|
          .goto fun _ => .tautology
    | .clearIndex => .pop .index read <|
        .branch (fun s => (held s).isNone)
          (writeBits [false,false] <| .load (fun _ => .inr none) <|
            .goto fun _ => .returnOutput)
          (.load (fun _ => .inr none) <| .goto fun _ => .clearIndex)
    | .returnOutput => .pop .reversedOutput read <|
        .branch (fun s => (held s).isNone)
          (.load (fun _ => .inl ⟨none,none,0⟩) .halt)
          (.push .output (fun s => (held s).getD false) <|
            .load (fun _ => .inr none) <| .goto fun _ => .returnOutput)

-- Data specifications do not occur in the finite program's control.
def variableName (i : Nat) : Conventional.Name := true :: List.replicate i false

def saturatedFormula {n : Nat} (F : UnaryFormula n) : Conventional.Formula :=
  F.map (fun clause => clause.map (fun literal => (variableName literal.1.val,literal.2))) ++
    (List.finRange n).map (fun i => [(variableName i.val,true),(variableName i.val,false)])

def convertedWord (w : List Bool) : List Bool :=
  Conventional.formulaWord (saturatedFormula (preparedFormula w).2)

def reverseWords (query universeBits index saved reversed output : List Bool) :
    ReverseStack → List Bool
  | .pre .output => query
  | .universeBits => universeBits
  | .index => index
  | .saved => saved
  | .reversedOutput => reversed
  | .output => output
  | _ => []
def reverseCfg (label : ReverseLabel)
    (query universeBits index saved reversed output : List Bool) : reverseMachine.Cfg :=
  ⟨some label,.inr none,reverseWords query universeBits index saved reversed output⟩
macro "reverse_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [reverseMachine,TM2.stepAux,reverseCfg,reverseWords,read,held,writeBits]
    all_goals simp [Function.update_apply,reverseWords] <;>
      first | rfl | (funext k; cases k with
        | pre k => cases k <;> simp [Function.update_apply,reverseWords]
        | universeBits | index | saved | reversedOutput | output =>
            simp [Function.update_apply,reverseWords])))

def renamedLiteral {n : Nat} (literal : Fin n × Bool) : Conventional.Name × Bool :=
  (variableName literal.1.val,literal.2)
def renamedClause {n : Nat} (c : Std.Sat.CNF.Clause (Fin n)) := c.map renamedLiteral
def queryClauseClock {n : Nat} (c : Std.Sat.CNF.Clause (Fin n)) : Nat :=
  n+6+(c.map (fun literal => literal.1.val+4)).sum

def tautologies (offset count : Nat) : Conventional.Formula :=
  (List.range count).map (fun j =>
    [(variableName (offset+j),true),(variableName (offset+j),false)])

def preWords (words : PreStack → List Bool) : ReverseStack → List Bool
  | .pre k => words k
  | _ => []

def reverseClock (w : List Bool) : Nat :=
  (4*w.length+20)*w.length+13 +
    (((preparedFormula w).2.map queryClauseClock).sum+2+
      (preparedFormula w).1*((preparedFormula w).1+3)+2*(preparedFormula w).1+6+
      (convertedWord w).length)

/-- Actual translated preprogram, coefficient scanning, binary-name writing,
universe tautologies, reversal and scratch cleanup. -/
def reverseExecution (w : List Bool) : Nonempty (EvalsToInTime reverseMachine.step
    (initList reverseMachine w) (some (haltList reverseMachine (convertedWord w)))
    (reverseClock w)) := by
  have query : ∀ n (F : UnaryFormula n),
      EvalsToInTime reverseMachine.step
        (reverseCfg .queryStart (queryWord F) [] [] [] [] [])
        (some (haltList reverseMachine (Conventional.formulaWord (saturatedFormula F))))
        ((F.map queryClauseClock).sum+2+n*(n+3)+2*n+6+
          (Conventional.formulaWord (saturatedFormula F)).length) := by
    intro n F
    let single : ∀ (x : reverseMachine.Cfg) (y : Option reverseMachine.Cfg),
        reverseMachine.step x = y → EvalsToInTime reverseMachine.step x y 1 :=
      fun x y h => {steps := 1,evals_in_steps := h,steps_le_m := by decide}
    have name : ∀ (i : Nat) (tail universeBits reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .literalIndex (List.replicate i true ++ false::tail)
            universeBits [] [] reversed [])
          (some (reverseCfg .clauseFirst tail universeBits [] []
            ((Conventional.nameWord (List.replicate i false)).reverse ++ reversed) []))
          (i+1) := by
      intro i
      induction i with
      | zero => intro tail universeBits reversed; apply single; dsimp [Conventional.nameWord]; reverse_transition
      | succ i ih =>
        intro tail universeBits reversed
        have first : reverseMachine.step
            (reverseCfg .literalIndex (List.replicate (i+1) true ++ false::tail)
              universeBits [] [] reversed []) =
            some (reverseCfg .literalIndex (List.replicate i true ++ false::tail)
              universeBits [] [] (false::true::reversed) []) := by
          simp only [List.replicate_succ,List.cons_append]
          reverse_transition
        convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
          (ih tail universeBits (false::true::reversed)) using 1 <;>
            simp [Conventional.nameWord,List.replicate_succ,List.flatMap_cons,
              List.reverse_append,List.append_assoc] <;> omega
    have clause : ∀ (c : Std.Sat.CNF.Clause (Fin n)) (tail universeBits reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .clauseFirst (c.flatMap unaryLiteral ++ [true,false] ++ tail)
            universeBits [] [] reversed [])
          (some (reverseCfg .bodyFirst tail universeBits [] []
            (((c.map renamedLiteral).flatMap Conventional.literalWord ++ [true,false]).reverse ++
              reversed) []))
          ((c.map (fun literal => literal.1.val+4)).sum+2) := by
      intro c
      induction c with
      | nil =>
        intro tail universeBits reversed
        have first : reverseMachine.step
            (reverseCfg .clauseFirst (true::false::tail) universeBits [] [] reversed []) =
            some (reverseCfg .clauseSecond (false::tail) universeBits [] [] reversed []) := by
          reverse_transition
        have second : reverseMachine.step
            (reverseCfg .clauseSecond (false::tail) universeBits [] [] reversed []) =
            some (reverseCfg .bodyFirst tail universeBits [] [] (false::true::reversed) []) := by
          reverse_transition
        simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
      | cons literal c ih =>
        intro tail universeBits reversed
        let input := c.flatMap unaryLiteral ++ [true,false] ++ tail
        have first : reverseMachine.step
            (reverseCfg .clauseFirst (unaryLiteral literal ++ input) universeBits [] [] reversed []) =
            some (reverseCfg .clauseSecond
              (true::literal.2::List.replicate literal.1.val true ++ false::input)
              universeBits [] [] reversed []) := by
          dsimp [unaryLiteral]; reverse_transition
        have second : reverseMachine.step
            (reverseCfg .clauseSecond
              (true::literal.2::List.replicate literal.1.val true ++ false::input)
              universeBits [] [] reversed []) =
            some (reverseCfg .polarity
              (literal.2::List.replicate literal.1.val true ++ false::input)
              universeBits [] [] (true::true::reversed) []) := by
          reverse_transition
        have third : reverseMachine.step
            (reverseCfg .polarity
              (literal.2::List.replicate literal.1.val true ++ false::input)
              universeBits [] [] (true::true::reversed) []) =
            some (reverseCfg .literalIndex
              (List.replicate literal.1.val true ++ false::input)
              universeBits [] [] (true::true::literal.2::true::true::reversed) []) := by
          rcases literal with ⟨i,p⟩; cases p <;> reverse_transition
        have r1 := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        have r2 := EvalsToInTime.trans _ 2 1 _ _ _ r1 (single _ _ third)
        have r3 := EvalsToInTime.trans _ 3 _ _ _ _ r2
          (name literal.1.val input universeBits (true::true::literal.2::true::true::reversed))
        have r4 := EvalsToInTime.trans _ _ _ _ _ _ r3
          (ih tail universeBits
            ((Conventional.nameWord (List.replicate literal.1.val false)).reverse ++
              true::true::literal.2::true::true::reversed))
        convert r4 using 1 <;>
          simp [input,unaryLiteral,renamedLiteral,variableName,Conventional.literalWord,
            Conventional.nameWord,List.reverse_append,List.append_assoc] <;> omega
    have coefficient : ∀ (k : Nat) (input universeBits reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .coefficient (List.replicate k true ++ false::input)
            universeBits [] [] reversed [])
          (some (reverseCfg .clauseFirst input universeBits [] [] reversed [])) (k+1) := by
      intro k
      induction k with
      | zero => intro input universeBits reversed; apply single; reverse_transition
      | succ k ih =>
        intro input universeBits reversed
        have first : reverseMachine.step
            (reverseCfg .coefficient (List.replicate (k+1) true ++ false::input)
              universeBits [] [] reversed []) =
            some (reverseCfg .coefficient (List.replicate k true ++ false::input)
              universeBits [] [] reversed []) := by
          simp only [List.replicate_succ,List.cons_append]; reverse_transition
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih input universeBits reversed)
    have body : ∀ (G : UnaryFormula n) (universeBits reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .bodyFirst (G.flatMap queryClause ++ [false,false])
            universeBits [] [] reversed [])
          (some (reverseCfg .tautology [] universeBits [] []
            (((G.map renamedClause).flatMap Conventional.clauseWord).reverse ++ reversed) []))
          ((G.map queryClauseClock).sum+2) := by
      intro G
      induction G with
      | nil =>
        intro universeBits reversed
        have first : reverseMachine.step
            (reverseCfg .bodyFirst [false,false] universeBits [] [] reversed []) =
            some (reverseCfg .bodySecond [false] universeBits [] [] reversed []) := by
          reverse_transition
        have second : reverseMachine.step
            (reverseCfg .bodySecond [false] universeBits [] [] reversed []) =
            some (reverseCfg .tautology [] universeBits [] [] reversed []) := by
          reverse_transition
        simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
      | cons c G ih =>
        intro universeBits reversed
        let tail := G.flatMap queryClause ++ [false,false]
        let input := List.replicate (n+1) true ++ false::(c.flatMap unaryLiteral ++ [true,false] ++ tail)
        have first : reverseMachine.step
            (reverseCfg .bodyFirst (false::true::input) universeBits [] [] reversed []) =
            some (reverseCfg .bodySecond (true::input) universeBits [] [] reversed []) := by
          reverse_transition
        have second : reverseMachine.step
            (reverseCfg .bodySecond (true::input) universeBits [] [] reversed []) =
            some (reverseCfg .coefficient input universeBits [] [] (true::false::reversed) []) := by
          reverse_transition
        have r1 := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        have r2 := EvalsToInTime.trans _ 2 (n+2) _ _ _ r1
          (coefficient (n+1) (c.flatMap unaryLiteral ++ [true,false] ++ tail)
            universeBits (true::false::reversed))
        have r3 := EvalsToInTime.trans _ _ _ _ _ _ r2
          (clause c tail universeBits (true::false::reversed))
        have r4 := EvalsToInTime.trans _ _ _ _ _ _ r3
          (ih universeBits
            (((c.map renamedLiteral).flatMap Conventional.literalWord ++ [true,false]).reverse ++
              true::false::reversed))
        convert r4 using 1 <;>
          simp [tail,input,queryClause,queryClauseClock,renamedClause,Conventional.clauseWord,
            List.reverse_append,List.append_assoc] <;> omega
    have header : ∀ (k : Nat) (input universeBits reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .header (List.replicate k true ++ false::input)
            universeBits [] [] reversed [])
          (some (reverseCfg .staticPrefix input (List.replicate k true ++ universeBits)
            [] [] reversed [])) (k+1) := by
      intro k
      induction k with
      | zero => intro input universeBits reversed; apply single; reverse_transition
      | succ k ih =>
        intro input universeBits reversed
        have first : reverseMachine.step
            (reverseCfg .header (List.replicate (k+1) true ++ false::input)
              universeBits [] [] reversed []) =
            some (reverseCfg .header (List.replicate k true ++ false::input)
              (true::universeBits) [] [] reversed []) := by
          simp only [List.replicate_succ,List.cons_append]; reverse_transition
        convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
          (ih input (true::universeBits) reversed) using 1 <;>
            simp [List.replicate_add,List.append_assoc] <;> omega
    let escapedZeros (i : Nat) := (List.replicate i false).flatMap (fun b => [true,b])
    have firstName : ∀ (i : Nat) (universeBits saved reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .firstName [] universeBits (List.replicate i true) saved reversed [])
          (some (reverseCfg .secondName [] universeBits [] (List.replicate i true ++ saved)
            ([false,true,true,false,true,true].reverse ++ (escapedZeros i).reverse ++ reversed) []))
          (i+1) := by
      intro i
      induction i with
      | zero => intro universeBits saved reversed; apply single; simp only [escapedZeros]; reverse_transition
      | succ i ih =>
        intro universeBits saved reversed
        have first : reverseMachine.step
            (reverseCfg .firstName [] universeBits (List.replicate (i+1) true) saved reversed []) =
            some (reverseCfg .firstName [] universeBits (List.replicate i true) (true::saved)
              (false::true::reversed) []) := by
          simp only [List.replicate_succ]; reverse_transition
        have escaped : escapedZeros (i+1) = [true,false] ++ escapedZeros i := by
          simp only [escapedZeros,List.replicate_succ,List.flatMap_cons]
        convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
          (ih universeBits (true::saved) (false::true::reversed)) using 1 <;>
            simp [escaped,List.replicate_succ',List.reverse_append,List.append_assoc] <;> omega
    have secondName : ∀ (i : Nat) (universeBits index reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .secondName [] universeBits index (List.replicate i true) reversed [])
          (some (reverseCfg .finishClause [] universeBits (List.replicate i true ++ index) []
            ((escapedZeros i).reverse ++ reversed) [])) (i+1) := by
      intro i
      induction i with
      | zero => intro universeBits index reversed; apply single; simp only [escapedZeros]; reverse_transition
      | succ i ih =>
        intro universeBits index reversed
        have first : reverseMachine.step
            (reverseCfg .secondName [] universeBits index (List.replicate (i+1) true) reversed []) =
            some (reverseCfg .secondName [] universeBits (true::index) (List.replicate i true)
              (false::true::reversed) []) := by
          simp only [List.replicate_succ]; reverse_transition
        have escaped : escapedZeros (i+1) = [true,false] ++ escapedZeros i := by
          simp only [escapedZeros,List.replicate_succ,List.flatMap_cons]
        convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
          (ih universeBits (true::index) (false::true::reversed)) using 1 <;>
            simp [escaped,List.replicate_succ',List.reverse_append,List.append_assoc] <;> omega
    have tautology : ∀ (count offset : Nat) (reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .tautology [] (List.replicate count true) (List.replicate offset true)
            [] reversed [])
          (some (reverseCfg .clearIndex [] [] (List.replicate (offset+count) true) []
            (((tautologies offset count).flatMap Conventional.clauseWord).reverse ++ reversed) []))
          (count*(2*offset+count+3)+1) := by
      intro count
      induction count with
      | zero =>
        intro offset reversed
        simp only [tautologies,List.range_zero,List.map_nil,List.flatMap_nil,
          List.reverse_nil,List.nil_append,Nat.add_zero,Nat.zero_mul,Nat.zero_add,
          List.replicate_zero]
        apply single
        reverse_transition
      | succ count ih =>
        intro offset reversed
        let block := [false,true,true,true,true,true,true]
        have first : reverseMachine.step
            (reverseCfg .tautology [] (List.replicate (count+1) true) (List.replicate offset true)
              [] reversed []) =
            some (reverseCfg .firstName [] (List.replicate count true) (List.replicate offset true)
              [] (block.reverse ++ reversed) []) := by
          simp only [List.replicate_succ]; dsimp [block]; reverse_transition
        have r1 := EvalsToInTime.trans _ 1 (offset+1) _ _ _ (single _ _ first)
          (firstName offset (List.replicate count true) [] (block.reverse ++ reversed))
        let out := [false,true,true,false,true,true].reverse ++
          ((escapedZeros offset).reverse ++ (block.reverse ++ reversed))
        simp only [List.append_nil,List.append_assoc] at r1
        have r2 := EvalsToInTime.trans _ _ (offset+1) _ _ _ r1
          (secondName offset (List.replicate count true) [] out)
        simp only [List.append_nil] at r2
        have finish : reverseMachine.step
            (reverseCfg .finishClause [] (List.replicate count true) (List.replicate offset true)
              [] ((escapedZeros offset).reverse ++ out) []) =
            some (reverseCfg .tautology [] (List.replicate count true)
              (List.replicate (offset+1) true) []
              ([false,true,false].reverse ++ (escapedZeros offset).reverse ++ out) []) := by
          simp only [List.replicate_succ]; reverse_transition
        have r3 := EvalsToInTime.trans _ _ 1 _ _ _ r2 (single _ _ finish)
        have r4 := EvalsToInTime.trans _ _ _ _ _ _ r3
          (ih (offset+1)
            ([false,true,false].reverse ++ (escapedZeros offset).reverse ++ out))
        have specification : tautologies offset (count+1) =
            [(variableName offset,true),(variableName offset,false)] ::
              tautologies (offset+1) count := by
          simp [tautologies,List.range_succ_eq_map,List.map_map,Nat.add_assoc,
            Nat.add_comm,Nat.add_left_comm]
        have indexEq : offset+1+count = offset+(count+1) := by omega
        rw [indexEq] at r4
        convert r4 using 1 <;>
          (try simp [specification,Conventional.clauseWord,Conventional.literalWord,
            Conventional.nameWord,variableName,escapedZeros,block,out,
            List.reverse_append,List.append_assoc]) <;> ring
    have clear : ∀ (i : Nat) (reversed : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .clearIndex [] [] (List.replicate i true) [] reversed [])
          (some (reverseCfg .returnOutput [] [] [] [] (false::false::reversed) [])) (i+1) := by
      intro i
      induction i with
      | zero => intro reversed; apply single; reverse_transition
      | succ i ih =>
        intro reversed
        have first : reverseMachine.step
            (reverseCfg .clearIndex [] [] (List.replicate (i+1) true) [] reversed []) =
            some (reverseCfg .clearIndex [] [] (List.replicate i true) [] reversed []) := by
          simp only [List.replicate_succ]; reverse_transition
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih reversed)
    have returnOutput : ∀ (reversed output : List Bool),
        EvalsToInTime reverseMachine.step
          (reverseCfg .returnOutput [] [] [] [] reversed output)
          (some (haltList reverseMachine (reversed.reverse ++ output))) (reversed.length+1) := by
      intro reversed
      induction reversed with
      | nil =>
        intro output
        apply single
        apply congrArg some
        dsimp [FinTM2.step,TM2.step,reverseMachine,TM2.stepAux,reverseCfg,reverseWords,read,held,haltList]
        congr 1
        funext k
        cases k with
        | pre k => cases k <;> simp [Function.update_apply,reverseWords]
        | universeBits | index | saved | reversedOutput | output =>
            simp [Function.update_apply,reverseWords]
      | cons b reversed ih =>
        intro output
        have first : reverseMachine.step
            (reverseCfg .returnOutput [] [] [] [] (b::reversed) output) =
            some (reverseCfg .returnOutput [] [] [] [] reversed (b::output)) := by
          cases b <;> reverse_transition
        simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih (b::output))
    let input := [false,false,false,true] ++ F.flatMap queryClause ++ [false,false]
    have first : reverseMachine.step (reverseCfg .queryStart (queryWord F) [] [] [] [] []) =
        some (reverseCfg .header (List.replicate n true ++ false::input) [] [] [] [] []) := by
      dsimp [queryWord,input]
      reverse_transition
    have leadingRun : reverseMachine.step
        (reverseCfg .staticPrefix input (List.replicate n true) [] [] [] []) =
        some (reverseCfg .bodyFirst (F.flatMap queryClause ++ [false,false])
          (List.replicate n true) [] [] [] []) := by
      dsimp [input]; reverse_transition
    have r1 := EvalsToInTime.trans _ 1 (n+1) _ _ _ (single _ _ first) (header n input [] [])
    simp only [List.append_nil] at r1
    have r2 := EvalsToInTime.trans _ _ 1 _ _ _ r1 (single _ _ leadingRun)
    have r3 := EvalsToInTime.trans _ _ _ _ _ _ r2 (body F (List.replicate n true) [])
    simp only [List.append_nil] at r3
    have tailRun := tautology n 0 (((F.map renamedClause).flatMap Conventional.clauseWord).reverse)
    simp only [List.replicate_zero,Nat.zero_add,Nat.mul_zero,Nat.zero_add] at tailRun
    have r4 := EvalsToInTime.trans _ _ _ _ _ _ r3 tailRun
    let reversed := ((tautologies 0 n).flatMap Conventional.clauseWord).reverse ++
      ((F.map renamedClause).flatMap Conventional.clauseWord).reverse
    have r5 := EvalsToInTime.trans _ _ _ _ _ _ r4 (clear n reversed)
    have r6 := EvalsToInTime.trans _ _ _ _ _ _ r5 (returnOutput (false::false::reversed) [])
    have enumeration : (List.finRange n).map (fun i =>
        [(variableName i.val,true),(variableName i.val,false)]) = tautologies 0 n := by
      apply List.ext_getElem
      · simp [tautologies]
      · intro i hi hj
        simp [tautologies]
    have formula : F.map renamedClause ++ tautologies 0 n = saturatedFormula F := by
      rw [← enumeration]
      rfl
    have output : (false::false::reversed).reverse =
        Conventional.formulaWord (saturatedFormula F) := by
      rw [← formula]
      simp [reversed,Conventional.formulaWord,List.flatMap_append,List.reverse_append,
        List.append_assoc]
    rw [output] at r6
    convert r6 using 1 <;> simp [reversed,← output,List.length_reverse] <;> ring
  have pre : Nonempty (EvalsToInTime reverseMachine.step
      (initList reverseMachine w)
      (some (reverseCfg .queryStart (preparedQuery w) [] [] [] [] []))
      ((4*w.length+20)*w.length+13)) := by
    let lift (c : preMachine.Cfg) : reverseMachine.Cfg :=
      ⟨some (c.l.map ReverseLabel.pre |>.getD .queryStart),
        if c.l.isSome then .inl c.var else .inr none,preWords c.stk⟩
    have slot : ∀ (words : PreStack → List Bool) k,
        preWords words (.pre k) = words k := by intro words k; rfl
    have update : ∀ (words : PreStack → List Bool) k v,
        Function.update (preWords words) (.pre k) v =
          preWords (Function.update words k v) := by
      intro words k v
      funext j
      cases k <;> cases j with
      | pre j => cases j <;> simp [preWords,Function.update_apply]
      | universeBits | index | saved | reversedOutput | output =>
          simp [preWords,Function.update_apply]
    have aux : ∀ (stmt : TM2.Stmt (fun _ : PreStack => Bool) PreLabel PreControl) state words,
        TM2.stepAux (liftPre stmt) (.inl state) (preWords words) =
          lift (TM2.stepAux stmt state words) := by
      intro stmt
      induction stmt with
      | push k f next ih =>
        intro state words
        simpa only [liftPre,TM2.stepAux,originalControl,slot,update]
          using ih state (Function.update words k (f state::words k))
      | peek k f next ih =>
        intro state words
        simpa only [liftPre,TM2.stepAux,originalControl,slot]
          using ih (f state (words k).head?) words
      | pop k f next ih =>
        intro state words
        simpa only [liftPre,TM2.stepAux,originalControl,slot,update]
          using ih (f state (words k).head?) (Function.update words k (words k).tail)
      | load f next ih =>
        intro state words
        simpa only [liftPre,TM2.stepAux,originalControl] using ih (f state) words
      | branch f yes no iy ino =>
        intro state words
        cases hf : f state <;>
          simpa only [liftPre,TM2.stepAux,originalControl,hf,cond_false,cond_true]
            using (by first | exact ino state words | exact iy state words)
      | goto f => intro state words; rfl
      | halt => intro state words; rfl
    have one : ∀ c d, preMachine.step c = some d →
        reverseMachine.step (lift c) = some (lift d) := by
      intro c d hc
      rcases c with ⟨label,state,words⟩
      cases label with
      | none => simp [FinTM2.step,TM2.step] at hc
      | some label =>
        simp only [FinTM2.step,TM2.step,Option.some.injEq] at hc
        rw [← hc]
        exact congrArg some (aux (preMachine.m label) state words)
    have noneStable : ∀ t, (flip bind preMachine.step)^[t] none = none := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simpa [Function.iterate_succ_apply,flip] using ih
    have liftRun : ∀ t c d, (flip bind preMachine.step)^[t] (some c) = some d →
        (flip bind reverseMachine.step)^[t] (some (lift c)) = some (lift d) := by
      intro t
      induction t with
      | zero => intro c d h; simpa using congrArg (Option.map lift) h
      | succ t ih =>
        intro c d h
        rw [Function.iterate_succ_apply] at h ⊢
        change (flip bind preMachine.step)^[t] (preMachine.step c) = some d at h
        change (flip bind reverseMachine.step)^[t] (reverseMachine.step (lift c)) = some (lift d)
        cases hs : preMachine.step c with
        | none => rw [hs,noneStable] at h; cases h
        | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
    let run := Classical.choice (pre_word_run w).1
    have lifted := liftRun _ _ _ run.evals_in_steps
    have start : lift (initList preMachine w) = initList reverseMachine w := by
      dsimp [lift,initList,preMachine,reverseMachine,preWords]
      congr 1
      funext k
      cases k with
      | pre k => cases k <;> rfl
      | universeBits | index | saved | reversedOutput | output => rfl
    have finish : lift (haltList preMachine (preparedQuery w)) =
        reverseCfg .queryStart (preparedQuery w) [] [] [] [] [] := by
      dsimp [lift,haltList,preMachine,preWords,reverseCfg,reverseWords]
      congr 1
      funext k
      cases k with
      | pre k => cases k <;> rfl
      | universeBits | index | saved | reversedOutput | output => rfl
    refine ⟨{steps := run.steps,steps_le_m := run.steps_le_m,evals_in_steps := ?_}⟩
    rwa [start,finish] at lifted
  have prepared : preparedQuery w = queryWord (preparedFormula w).2 := by
    unfold preparedFormula
    cases h : ClauseCodec.readWord false w with
    | none => simp [preparedQuery,preparedFormula,h,dummyQuery,queryWord,queryClause]
    | some value => cases value with
      | mk n F => simp [preparedQuery,preparedFormula,h]
  let leadingRun := Classical.choice pre
  have suffix := query (preparedFormula w).1 (preparedFormula w).2
  rw [← prepared] at suffix
  have done := EvalsToInTime.trans _ _ _ _ _ _ leadingRun suffix
  refine ⟨{steps := done.steps,evals_in_steps := ?_,steps_le_m := ?_}⟩
  · simpa [convertedWord] using done.evals_in_steps
  · simpa [reverseClock,convertedWord,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
      using done.steps_le_m

end PredictiveThermodynamic.ConventionalReverse
