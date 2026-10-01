/- GID: D5/S0/Computability/DenseClauseMachine
   generality: G
   mirror-B: D5/B/S0/Computability/DenseClauseMachine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/BinaryNameDeduplication, D5/S0/Computability/ClauseWordCodec]
   utility: kind=checker; basis=consumer=D5/S0/Computability/DenseClauseExecution.denseExecution; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Actual finite parser translation and whole-word grammar refinement. -/

import D5.S0.Computability.BinaryNameDeduplication
import D5.S0.Computability.ClauseWordCodec
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! The parser execution and raw grammar laws are consumed by the complete
word execution and count-preserving semantic refinement.
ComparisonSource is the canonical one-name positive/negative clause; its two
occurrences test restored comparison, rightmost deduplication, and dense lookup.
The output has an explicit unary universe. Malformed words produce the valid
zero-variable one-empty-clause source, preserving the total raw count zero.
All dictionaries, names, counters and output words reside on ordinary stacks.
The control, labels, stacks and Bool alphabets are fixed independently of input.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.BinaryNames
open Turing StateTransition

inductive DensePhase
  | bodyFirst | bodySecond | clauseFirst | clauseSecond | polarity | nameTag | nameBit
  deriving DecidableEq, Fintype, Inhabited

abbrev DenseControl := Sum Conventional.ParseControl (Sum DictionaryControl (Option Bool × DensePhase))

inductive DenseStack
  | parser (k : Conventional.ParseStack) | lookup (k : DictionaryStack)
  | dimension | nameBackup | reversedOutput | output
  deriving DecidableEq, Fintype, Inhabited

inductive DenseLabel
  | parser (label : Conventional.ParseLabel) | builder (label : BuilderLabel)
  | lookup (label : DictionaryLabel)
  | parseReturn | header | copy | nameTag | nameBit | reverseName | dispatch | emitIndex
  | clearQuery | drainDictionary | returnOutput | badDrain
  deriving DecidableEq, Fintype, Inhabited

def denseLookupStack : DictionaryStack → DenseStack
  | .operand .frame => .parser .frame
  | k => .lookup k

def denseBuilderStack : BuilderStack → DenseStack
  | .lookup k => denseLookupStack k
  | .source => .parser .occurrences
  | .dimension => .dimension

def denseParseState : DenseControl → Conventional.ParseControl
  | .inl s => s
  | _ => ⟨.bodyFirst, 0, none, false, .none⟩

def denseDictionaryState : DenseControl → DictionaryControl
  | .inr (.inl s) => s
  | _ => ⟨⟨none,none,true⟩,none,false⟩

def denseWordState : DenseControl → Option Bool × DensePhase
  | .inr (.inr s) => s
  | _ => (none,.bodyFirst)

def denseLocal (phase : DensePhase := .bodyFirst) (held : Option Bool := none) : DenseControl :=
  .inr (.inr (held,phase))

def denseLiftParse :
    TM2.Stmt (fun _ : Conventional.ParseStack => Bool) Conventional.ParseLabel Conventional.ParseControl →
    TM2.Stmt (fun _ : DenseStack => Bool) DenseLabel DenseControl
  | .push k f next => .push (.parser k) (fun s => f (denseParseState s)) (denseLiftParse next)
  | .peek k f next => .peek (.parser k) (fun s b => .inl (f (denseParseState s) b)) (denseLiftParse next)
  | .pop k f next => .pop (.parser k) (fun s b => .inl (f (denseParseState s) b)) (denseLiftParse next)
  | .load f next => .load (fun s => .inl (f (denseParseState s))) (denseLiftParse next)
  | .branch f yes no => .branch (fun s => f (denseParseState s)) (denseLiftParse yes) (denseLiftParse no)
  | .goto f => .goto (fun s => .parser (f (denseParseState s)))
  | .halt => .load (fun _ => denseLocal) <| .goto fun _ => .parseReturn

def denseLiftBuilder : TM2.Stmt (fun _ : BuilderStack => Bool) BuilderLabel DictionaryControl →
    TM2.Stmt (fun _ : DenseStack => Bool) DenseLabel DenseControl
  | .push k f next => .push (denseBuilderStack k) (fun s => f (denseDictionaryState s)) (denseLiftBuilder next)
  | .peek k f next => .peek (denseBuilderStack k) (fun s b => .inr (.inl (f (denseDictionaryState s) b))) (denseLiftBuilder next)
  | .pop k f next => .pop (denseBuilderStack k) (fun s b => .inr (.inl (f (denseDictionaryState s) b))) (denseLiftBuilder next)
  | .load f next => .load (fun s => .inr (.inl (f (denseDictionaryState s)))) (denseLiftBuilder next)
  | .branch f yes no => .branch (fun s => f (denseDictionaryState s)) (denseLiftBuilder yes) (denseLiftBuilder no)
  | .goto f => .goto (fun s => .builder (f (denseDictionaryState s)))
  | .halt => .load (fun _ => denseLocal) <| .goto fun _ => .header

def denseLiftLookup : TM2.Stmt (fun _ : DictionaryStack => Bool) DictionaryLabel DictionaryControl →
    TM2.Stmt (fun _ : DenseStack => Bool) DenseLabel DenseControl
  | .push k f next => .push (denseLookupStack k) (fun s => f (denseDictionaryState s)) (denseLiftLookup next)
  | .peek k f next => .peek (denseLookupStack k) (fun s b => .inr (.inl (f (denseDictionaryState s) b))) (denseLiftLookup next)
  | .pop k f next => .pop (denseLookupStack k) (fun s b => .inr (.inl (f (denseDictionaryState s) b))) (denseLiftLookup next)
  | .load f next => .load (fun s => .inr (.inl (f (denseDictionaryState s)))) (denseLiftLookup next)
  | .branch f yes no => .branch (fun s => f (denseDictionaryState s)) (denseLiftLookup yes) (denseLiftLookup no)
  | .goto f => .goto (fun s => .lookup (f (denseDictionaryState s)))
  | .halt => .load (fun _ => denseLocal .clauseFirst) <| .goto fun _ => .dispatch

/-- All three subprograms are translated instruction by instruction. Source names,
dictionaries, indices and dimension counts occupy ordinary stacks. The finite sum
control contains only the current subprogram control or a grammar phase and bit. -/
def denseMachine : FinTM2 where
  K := DenseStack
  k₀ := .parser .input
  k₁ := .output
  Γ _ := Bool
  Λ := DenseLabel
  main := .parser .scan
  σ := DenseControl
  initialState := .inl ⟨.bodyFirst,0,none,false,.none⟩
  m
    | .parser label => denseLiftParse (Conventional.parseMachine.m label)
    | .builder label => denseLiftBuilder (builderMachine.m label)
    | .lookup label => denseLiftLookup (dictionaryMachine.m label)
    | .parseReturn => .pop (.parser .result) (fun _ b => denseLocal .bodyFirst b) <|
        .branch (fun s => (denseWordState s).1.getD false)
          (.load (fun _ => .inr (.inl ⟨⟨none,none,true⟩,none,false⟩)) <|
            .goto fun _ => .builder .start)
          (.load (fun _ => denseLocal) <| .goto fun _ => .badDrain)
    | .header => .pop .dimension (fun _ b => denseLocal .bodyFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.push .reversedOutput (fun _ => false) <|
            .load (fun _ => denseLocal) <| .goto fun _ => .copy)
          (.push .reversedOutput (fun _ => true) <|
            .load (fun _ => denseLocal) <| .goto fun _ => .header)
    | .copy => .pop (.parser .input) (fun s b => denseLocal (denseWordState s).2 b) <|
        .push .reversedOutput (fun s => (denseWordState s).1.getD false) <|
          .branch (fun s => decide ((denseWordState s).2 = .bodySecond) &&
            !(denseWordState s).1.getD false)
            (.load (fun _ => denseLocal) <| .goto fun _ => .drainDictionary)
            (.branch (fun s => decide ((denseWordState s).2 = .polarity))
              (.load (fun _ => denseLocal .nameTag) <| .goto fun _ => .nameTag)
              (.load (fun s => denseLocal (match (denseWordState s).2 with
                | .bodyFirst => .bodySecond
                | .bodySecond => .clauseFirst
                | .clauseFirst => .clauseSecond
                | .clauseSecond => if (denseWordState s).1.getD false then .polarity else .bodyFirst
                | _ => .bodyFirst)) <| .goto fun _ => .copy))
    | .nameTag => .pop (.parser .input) (fun _ b => denseLocal .nameTag b) <|
        .branch (fun s => (denseWordState s).1.getD false)
          (.load (fun _ => denseLocal .nameBit) <| .goto fun _ => .nameBit)
          (.load (fun _ => denseLocal .nameTag) <| .goto fun _ => .reverseName)
    | .nameBit => .pop (.parser .input) (fun _ b => denseLocal .nameBit b) <|
        .push .nameBackup (fun s => (denseWordState s).1.getD false) <|
          .load (fun _ => denseLocal .nameTag) <| .goto fun _ => .nameTag
    | .reverseName => .pop .nameBackup (fun _ b => denseLocal .nameTag b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.load (fun _ => .inr (.inl ⟨⟨none,none,true⟩,none,false⟩)) <|
            .goto fun _ => .lookup .start)
          (.push (denseLookupStack (.operand .left)) (fun s => (denseWordState s).1.getD false) <|
            .load (fun _ => denseLocal .nameTag) <| .goto fun _ => .reverseName)
    | .dispatch => .pop (denseLookupStack .index) (fun _ _ => denseLocal .clauseFirst) <|
        .goto fun _ => .emitIndex
    | .emitIndex => .pop (denseLookupStack .index) (fun _ b => denseLocal .clauseFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.push .reversedOutput (fun _ => false) <|
            .load (fun _ => denseLocal .clauseFirst) <| .goto fun _ => .clearQuery)
          (.push .reversedOutput (fun _ => true) <|
            .load (fun _ => denseLocal .clauseFirst) <| .goto fun _ => .emitIndex)
    | .clearQuery => .pop (denseLookupStack (.operand .left)) (fun _ b => denseLocal .clauseFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.load (fun _ => denseLocal .clauseFirst) <| .goto fun _ => .copy)
          (.load (fun _ => denseLocal .clauseFirst) <| .goto fun _ => .clearQuery)
    | .drainDictionary => .pop (denseLookupStack .stream) (fun _ b => denseLocal .bodyFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.load (fun _ => denseLocal) <| .goto fun _ => .returnOutput)
          (.load (fun _ => denseLocal) <| .goto fun _ => .drainDictionary)
    | .badDrain => .pop (.parser .input) (fun _ b => denseLocal .bodyFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.push .reversedOutput (fun _ => false) <|
            .push .reversedOutput (fun _ => false) <|
              .push .reversedOutput (fun _ => true) <|
                .push .reversedOutput (fun _ => true) <|
                  .push .reversedOutput (fun _ => false) <|
                    .push .reversedOutput (fun _ => false) <|
                      .push .reversedOutput (fun _ => false) <|
                        .load (fun _ => denseLocal) <| .goto fun _ => .returnOutput)
          (.load (fun _ => denseLocal) <| .goto fun _ => .badDrain)
    | .returnOutput => .pop .reversedOutput (fun _ b => denseLocal .bodyFirst b) <|
        .branch (fun s => (denseWordState s).1.isNone)
          (.load (fun _ => .inl ⟨.bodyFirst,0,none,false,.none⟩) .halt)
          (.push .output (fun s => (denseWordState s).1.getD false) <|
            .load (fun _ => denseLocal) <| .goto fun _ => .returnOutput)

def denseWordStacks (input query stream index backup reversed output : List Bool) :
    DenseStack → List Bool
  | .parser .input => input
  | .lookup (.operand .left) => query
  | .lookup .stream => stream
  | .lookup .index => index
  | .nameBackup => backup
  | .reversedOutput => reversed
  | .output => output
  | _ => []

def denseWordCfg (label : DenseLabel) (phase : DensePhase)
    (input query stream index backup reversed output : List Bool) : denseMachine.Cfg :=
  ⟨some label, denseLocal phase, denseWordStacks input query stream index backup reversed output⟩

macro "dense_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [denseMachine, TM2.stepAux, denseWordCfg, denseWordStacks,
      denseLocal, denseWordState, denseLookupStack]
    all_goals simp [Function.update_apply, denseWordStacks] <;>
      first | rfl | (funext k; cases k with
        | parser k => cases k <;> simp [Function.update_apply, denseWordStacks]
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply, denseWordStacks]
          | stream => simp [Function.update_apply, denseWordStacks]
          | history => simp [Function.update_apply, denseWordStacks]
          | index => simp [Function.update_apply, denseWordStacks]
        | dimension => simp [Function.update_apply, denseWordStacks]
        | nameBackup => simp [Function.update_apply, denseWordStacks]
        | reversedOutput => simp [Function.update_apply, denseWordStacks]
        | output => simp [Function.update_apply, denseWordStacks])))


def denseParserStacks (words : Conventional.ParseStack → List Bool) : DenseStack → List Bool
  | .parser k => words k
  | _ => []

def denseBuilderStacks (words : BuilderStack → List Bool) (input : List Bool) :
    DenseStack → List Bool
  | .parser .input => input
  | .parser .occurrences => words .source
  | .parser .frame => words (.lookup (.operand .frame))
  | .lookup (.operand .frame) => []
  | .lookup k => words (.lookup k)
  | .dimension => words .dimension
  | _ => []


def denseDictionaryStacks (words : DictionaryStack → List Bool)
    (input backup reversed output : List Bool) : DenseStack → List Bool
  | .parser .input => input
  | .parser .frame => words (.operand .frame)
  | .lookup (.operand .frame) => []
  | .lookup k => words k
  | .nameBackup => backup
  | .reversedOutput => reversed
  | .output => output
  | _ => []


def denseLiteralWord (dictionary : List Conventional.Name) (literal : Conventional.Name × Bool) :
    List Bool := [true,true,literal.2] ++ List.replicate (dictionary.idxOf literal.1) true ++ [false]

def denseClauseWord (dictionary : List Conventional.Name) (clause : Std.Sat.CNF.Clause Conventional.Name) :
    List Bool := [false,true] ++ clause.flatMap (denseLiteralWord dictionary) ++ [true,false]

def denseBodyWord (dictionary : List Conventional.Name) (formula : Conventional.Formula) : List Bool :=
  formula.flatMap (denseClauseWord dictionary) ++ [false,false]

def denseRawWord (dictionary : List Conventional.Name) (formula : Conventional.Formula) : List Bool :=
  List.replicate dictionary.length true ++ false :: denseBodyWord dictionary formula

def denseLiteralClock (dictionary : List Conventional.Name) (literal : Conventional.Name × Bool) : Nat :=
  (2*literal.1.length+12)*dictionary.length + 4*(dictionaryStream dictionary).length+3 +
    4*literal.1.length + dictionary.idxOf literal.1 + 8

def denseClauseClock (dictionary : List Conventional.Name) (clause : Std.Sat.CNF.Clause Conventional.Name) :
    Nat := (clause.map (denseLiteralClock dictionary)).sum + 4


def denseHeaderCfg (input stream dimension reversed output : List Bool) : denseMachine.Cfg :=
  ⟨some .header, denseLocal,
    Function.update (denseWordStacks input [] stream [] [] reversed output) .dimension dimension⟩

macro "dense_header_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [denseMachine, TM2.stepAux, denseHeaderCfg, denseWordCfg, denseWordStacks,
      denseLocal, denseWordState]
    all_goals simp [Function.update_apply, denseWordStacks] <;>
      first | rfl | (funext k; cases k with
        | parser k => cases k <;> simp [Function.update_apply, denseWordStacks]
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply, denseWordStacks]
          | stream | history | index => simp [Function.update_apply, denseWordStacks]
        | dimension | nameBackup | reversedOutput | output =>
            simp [Function.update_apply, denseWordStacks])))


def denseConverted (w : List Bool) : List Bool :=
  match Conventional.readWord w with
  | none => [false,false,true,true,false,false,false]
  | some F => denseRawWord (Conventional.dictionary F) F

def denseRunClock (w : List Bool) : Nat :=
  match Conventional.readWord w with
  | none => 5*w.length+15
  | some F =>
      let d := Conventional.dictionary F
      let S := (dictionaryStream (Conventional.occurrences F)).length
      4*w.length+5+1+20*(S+1)^2+(d.length+1)+
        ((F.map (denseClauseClock d)).sum+2)+((dictionaryStream d).length+1)+
        ((denseRawWord d F).length+1)

/-- Actual instruction translation preserves the parser endpoint and restores
its input. The same raw-word grammar induction yields full source spelling and
clause width on every accepted word, including empty clauses and formulae. -/
theorem dense_parser_run (w : List Bool) :
    Nonempty (EvalsToInTime denseMachine.step
      (initList denseMachine w)
      (some ⟨some .parseReturn, denseLocal,
        denseParserStacks (Conventional.parseStacks w [] (Conventional.decodedOccurrences w)
          [(Conventional.readWord w).isSome] [])⟩) (4*w.length+5)) ∧
    (∀ F : Conventional.Formula, Conventional.readWord w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3) := by
  have shape : ∀ (w : List Bool) (F : Conventional.Formula),
      Conventional.readWord w = some F →
    w = Conventional.formulaWord F ∧ ∀ clause ∈ F, clause.length ≤ 3 := by
    intro w F accepted
    have bitsExact : ∀ word bits tail,
        Conventional.readBits word = some (bits,tail) →
          word = Conventional.nameWord bits ++ tail := by
      intro word
      induction word using List.twoStepInduction with
      | nil => intro bits tail h; cases h
      | singleton b =>
        intro bits tail h
        cases b with
        | false =>
          simp only [Conventional.readBits, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          rfl
        | true => cases h
      | cons_cons tag b word ih _ =>
        intro bits tail h
        cases tag with
        | false =>
          simp only [Conventional.readBits, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          rfl
        | true =>
          cases hr : Conventional.readBits word with
          | none => simp [Conventional.readBits,hr] at h
          | some pair =>
            rcases pair with ⟨bits',tail'⟩
            simp [Conventional.readBits,hr] at h
            obtain ⟨rfl,rfl⟩ := h
            simpa [Conventional.nameWord, List.flatMap_cons, List.append_assoc]
              using congrArg (fun t => true::b::t) (ih bits' tail' hr)
    have nameExact : ∀ word name tail,
        Conventional.readName word = some (name,tail) →
          word = Conventional.nameWord name ++ tail := by
      intro word name tail h
      cases hr : Conventional.readBits word with
      | none => simp [Conventional.readName,hr] at h
      | some pair =>
        rcases pair with ⟨bits,rest⟩
        by_cases canonical : bits.head? = some true
        · simp [Conventional.readName,hr,canonical] at h
          obtain ⟨rfl,rfl⟩ := h
          exact bitsExact word bits rest hr
        · simp [Conventional.readName,hr,canonical] at h
    have clauseExact : ∀ budget word clause tail,
        Conventional.readClause budget word = some (clause,tail) →
          word = clause.flatMap Conventional.literalWord ++ [true,false] ++ tail ∧
            clause.length ≤ budget := by
      intro budget
      induction budget with
      | zero =>
        intro word clause tail h
        cases word with
        | nil => cases h
        | cons tag word => cases tag with
          | false => cases h
          | true => cases word with
            | nil => cases h
            | cons tag word => cases tag with
              | false =>
                simp only [Conventional.readClause, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl,rfl⟩ := h
                exact ⟨rfl,by simp⟩
              | true => cases word <;> simp [Conventional.readClause] at h
      | succ budget ih =>
        intro word clause tail h
        cases word with
        | nil => cases h
        | cons tag word => cases tag with
          | false => cases h
          | true => cases word with
            | nil => cases h
            | cons tag word => cases tag with
              | false =>
                simp only [Conventional.readClause, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl,rfl⟩ := h
                exact ⟨rfl,by simp⟩
              | true => cases word with
                | nil => cases h
                | cons polarity word =>
                  cases hn : Conventional.readName word with
                  | none => simp [Conventional.readClause,hn] at h
                  | some pair =>
                    rcases pair with ⟨name,rest⟩
                    cases hc : Conventional.readClause budget rest with
                    | none => simp [Conventional.readClause,hn,hc] at h
                    | some pair =>
                      rcases pair with ⟨c,remaining⟩
                      simp [Conventional.readClause,hn,hc] at h
                      obtain ⟨rfl,rfl⟩ := h
                      obtain ⟨shape,width⟩ := ih rest c remaining hc
                      have nameShape := nameExact word name rest hn
                      refine ⟨?_,by simpa using Nat.succ_le_succ width⟩
                      rw [nameShape,shape]
                      simp [Conventional.literalWord, List.append_assoc]
    have bodyExact : ∀ fuel word formula,
        Conventional.readBody fuel word = some formula →
          word = Conventional.formulaWord formula ∧ ∀ clause ∈ formula, clause.length ≤ 3 := by
      intro fuel
      induction fuel with
      | zero => intro word formula h; cases h
      | succ fuel ih =>
        intro word formula h
        cases word with
        | nil => cases h
        | cons tag word => cases tag with
          | true => cases h
          | false => cases word with
            | nil => cases h
            | cons tag word => cases tag with
              | false =>
                cases word with
                | nil =>
                  simp only [Conventional.readBody, Option.some.injEq] at h
                  subst formula
                  exact ⟨rfl,by simp⟩
                | cons b word => cases h
              | true =>
                cases hc : Conventional.readClause 3 word with
                | none => simp [Conventional.readBody,hc] at h
                | some pair =>
                  rcases pair with ⟨clause,rest⟩
                  cases hb : Conventional.readBody fuel rest with
                  | none => simp [Conventional.readBody,hc,hb] at h
                  | some formula' =>
                    simp [Conventional.readBody,hc,hb] at h
                    subst formula
                    obtain ⟨clauseShape,width⟩ := clauseExact 3 word clause rest hc
                    obtain ⟨bodyShape,widths⟩ := ih rest formula' hb
                    refine ⟨?_,?_⟩
                    · rw [clauseShape,bodyShape]
                      simp [Conventional.formulaWord,Conventional.clauseWord,List.append_assoc]
                    · intro c member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact width
                      · exact widths c member
    exact bodyExact (w.length+1) w F accepted
  have parser : ∀ (w : List Bool),
    Nonempty (EvalsToInTime denseMachine.step
      (initList denseMachine w)
      (some ⟨some .parseReturn, denseLocal,
        denseParserStacks (Conventional.parseStacks w [] (Conventional.decodedOccurrences w)
          [(Conventional.readWord w).isSome] [])⟩) (4*w.length+5)) := by
    intro w
    let lift (c : Conventional.parseMachine.Cfg) : denseMachine.Cfg :=
      ⟨some (c.l.map DenseLabel.parser |>.getD .parseReturn),
        if c.l.isSome then .inl c.var else denseLocal, denseParserStacks c.stk⟩
    have update : ∀ (words : Conventional.ParseStack → List Bool) k v,
        Function.update (denseParserStacks words) (.parser k) v =
          denseParserStacks (Function.update words k v) := by
      intro words k v
      funext j
      cases j with
      | parser j => simp [denseParserStacks, Function.update_apply]
      | lookup j => simp [denseParserStacks, Function.update_apply]
      | dimension => simp [denseParserStacks, Function.update_apply]
      | nameBackup => simp [denseParserStacks, Function.update_apply]
      | reversedOutput => simp [denseParserStacks, Function.update_apply]
      | output => simp [denseParserStacks, Function.update_apply]
    have aux : ∀ (stmt : TM2.Stmt (fun _ : Conventional.ParseStack => Bool)
        Conventional.ParseLabel Conventional.ParseControl) state words,
        TM2.stepAux (denseLiftParse stmt) (.inl state) (denseParserStacks words) =
          lift (TM2.stepAux stmt state words) := by
      intro stmt
      induction stmt with
      | push k f next ih =>
        intro state words
        simpa only [denseLiftParse, TM2.stepAux, denseParserStacks, denseParseState, update]
          using ih state (Function.update words k (f state :: words k))
      | peek k f next ih =>
        intro state words
        simpa only [denseLiftParse, TM2.stepAux, denseParserStacks, denseParseState]
          using ih (f state (words k).head?) words
      | pop k f next ih =>
        intro state words
        simpa only [denseLiftParse, TM2.stepAux, denseParserStacks, denseParseState, update]
          using ih (f state (words k).head?) (Function.update words k (words k).tail)
      | load f next ih =>
        intro state words
        simpa only [denseLiftParse, TM2.stepAux, denseParseState] using ih (f state) words
      | branch f yes no iy ino =>
        intro state words
        cases hf : f state <;>
          simpa only [denseLiftParse, TM2.stepAux, denseParseState, hf, cond_false, cond_true]
            using (by first | exact ino state words | exact iy state words)
      | goto f => intro state words; rfl
      | halt => intro state words; rfl
    have one : ∀ c d, Conventional.parseMachine.step c = some d →
        denseMachine.step (lift c) = some (lift d) := by
      intro c d hc
      rcases c with ⟨label,state,words⟩
      cases label with
      | none => simp [FinTM2.step, TM2.step] at hc
      | some label =>
        simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
        rw [← hc]
        exact congrArg some (aux (Conventional.parseMachine.m label) state words)
    have noneStable : ∀ t, (flip bind Conventional.parseMachine.step)^[t] none = none := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
    have liftRun : ∀ t c d,
        (flip bind Conventional.parseMachine.step)^[t] (some c) = some d →
        (flip bind denseMachine.step)^[t] (some (lift c)) = some (lift d) := by
      intro t
      induction t with
      | zero => intro c d h; simpa using congrArg (Option.map lift) h
      | succ t ih =>
        intro c d h
        rw [Function.iterate_succ_apply] at h ⊢
        change (flip bind Conventional.parseMachine.step)^[t]
          (Conventional.parseMachine.step c) = some d at h
        change (flip bind denseMachine.step)^[t] (denseMachine.step (lift c)) = some (lift d)
        cases hs : Conventional.parseMachine.step c with
        | none => rw [hs, noneStable] at h; cases h
        | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
    let run := Classical.choice (Conventional.conventional_word_run w [])
    refine ⟨{ steps := run.steps, steps_le_m := run.steps_le_m, evals_in_steps := ?_ }⟩
    have lifted := liftRun _ _ _ run.evals_in_steps
    have start : lift (Conventional.parseCfg (some .scan) .bodyFirst 0 w [] [] [] []) =
        initList denseMachine w := by
      dsimp [lift, Conventional.parseCfg, Conventional.parseStacks, denseParserStacks,
        initList, denseMachine]
      congr 1
      funext k
      cases k with
      | parser k => cases k <;> simp [denseParserStacks,Conventional.parseStacks]
      | lookup k => simp [denseParserStacks,Conventional.parseStacks]
      | dimension => simp [denseParserStacks,Conventional.parseStacks]
      | nameBackup => simp [denseParserStacks,Conventional.parseStacks]
      | reversedOutput => simp [denseParserStacks,Conventional.parseStacks]
      | output => simp [denseParserStacks,Conventional.parseStacks]
    rw [start] at lifted
    exact lifted
  exact ⟨parser w,shape w⟩

end PredictiveThermodynamic.BinaryNames
