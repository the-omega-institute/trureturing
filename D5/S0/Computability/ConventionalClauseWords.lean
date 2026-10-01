/- GID: D5/S0/Computability/ConventionalClauseWords
   generality: G
   mirror-B: D5/B/S0/Computability/ConventionalClauseWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Dedup]
   utility: kind=checker; basis=consumer=D5/S0/Computability/DenseClauseConversion.dense_word_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Independent raw word count over distinct appearing canonical binary names. -/

import Std.Sat.CNF.Relabel
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

/-!
Names are ordinary most significant bit first positive binary spellings. A name
is escaped as pairs `1 b` and terminated by `0`; its first bit must be `1`.
Clause and literal tags are the unary consumer's `01`, `11 polarity` and `10`,
with final `00`, and there is no declared universe header. The total parser
rejects a fourth literal, a missing terminator, a noncanonical name and a suffix.

The count quantifies assignments to exactly the distinct names occurring in the
parsed formula. It is independent of Hamiltonians, partition functions and the
oracle. Dictionary order uses the pinned rightmost-occurrence deduplication;
changing that order cannot introduce assignments for unmentioned names.
The actual parser routine below restores every raw word and materializes its
accepted occurrence stream with a direct linear clock. Complete dense conversion
and assignment transport require the further word program.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.Conventional

abbrev Name := List Bool
abbrev Formula := List (Std.Sat.CNF.Clause Name)

def readBits : List Bool → Option (Name × List Bool)
  | false :: tail => some ([], tail)
  | true :: b :: tail => (readBits tail).map (fun r => (b :: r.1, r.2))
  | _ => none

def readName (w : List Bool) : Option (Name × List Bool) := do
  let (name, tail) ← readBits w
  if name.head? = some true then some (name, tail) else none

def readClause : Nat → List Bool → Option (Std.Sat.CNF.Clause Name × List Bool)
  | _, true :: false :: tail => some ([], tail)
  | budget + 1, true :: true :: polarity :: tail => do
      let (name, rest) ← readName tail
      let (clause, rest) ← readClause budget rest
      some ((name, polarity) :: clause, rest)
  | _, _ => none

def readBody : Nat → List Bool → Option Formula
  | 0, _ => none
  | _ + 1, [false, false] => some []
  | fuel + 1, false :: true :: tail => do
      let (clause, rest) ← readClause 3 tail
      let formula ← readBody fuel rest
      some (clause :: formula)
  | _, _ => none

def readWord (w : List Bool) : Option Formula := readBody (w.length + 1) w

def nameWord (name : Name) : List Bool := name.flatMap (fun b => [true, b]) ++ [false]

def literalWord (literal : Name × Bool) : List Bool :=
  [true, true, literal.2] ++ nameWord literal.1

def clauseWord (clause : Std.Sat.CNF.Clause Name) : List Bool :=
  [false, true] ++ clause.flatMap literalWord ++ [true, false]

def formulaWord (formula : Formula) : List Bool := formula.flatMap clauseWord ++ [false, false]

/-- The original repeated-name and tautology case: a clause containing the two
opposite literals of canonical binary variable 1. This is source data. -/
def comparisonSource : List Bool := formulaWord [[([true], true), ([true], false)]]

def occurrences (formula : Formula) : List Name :=
  formula.flatMap (fun clause => clause.map Prod.fst)

def dictionary (formula : Formula) : List Name := (occurrences formula).dedup

abbrev Appearing (formula : Formula) := { name : Name // name ∈ occurrences formula }

instance (formula : Formula) : Fintype (Appearing formula) :=
  Fintype.ofFinset (occurrences formula).toFinset (by
    intro name
    change name ∈ (occurrences formula).toFinset ↔ name ∈ occurrences formula
    simp)

def extendAssignment (formula : Formula) (assignment : Appearing formula → Bool) : Name → Bool :=
  fun name => if h : name ∈ occurrences formula then assignment ⟨name, h⟩ else false

def evaluate (formula : Formula) (assignment : Appearing formula → Bool) : Bool :=
  formula.all (fun clause => clause.eval (extendAssignment formula assignment))

/-- Assignments are to the appearing-name subtype, not to a relabelled physical
universe. Empty formulas therefore have one assignment; an empty clause rejects
that assignment. Multiplicity and polarity are retained by the ordinary CNF. -/
def satisfyingCount (formula : Formula) : Nat :=
  (Finset.univ.filter (fun assignment : Appearing formula → Bool =>
    evaluate formula assignment = true)).card

/-- The raw-word problem is total, with malformed words assigned zero. -/
def rawCount (w : List Bool) : Nat :=
  match readWord w with
  | none => 0
  | some formula => satisfyingCount formula


open Turing StateTransition

inductive ParsePhase
  | bodyFirst | bodySecond | clauseFirst | clauseSecond | polarity
  | firstTag | firstBit | nameTag | nameBit | ending | dead
  deriving DecidableEq, Fintype, Inhabited

inductive ParseEmission
  | none | delimiter | bit
  deriving DecidableEq, Fintype, Inhabited

structure ParseControl where
  phase : ParsePhase := .bodyFirst
  width : Fin 4 := 0
  held : Option Bool := none
  accepted : Bool := false
  emission : ParseEmission := .none
  deriving DecidableEq, Fintype, Inhabited

inductive ParseStack
  | input | saved | occurrences | result | frame
  deriving DecidableEq, Fintype, Inhabited

inductive ParseLabel
  | scan | clearOccurrences | restore | finish
  deriving DecidableEq, Fintype, Inhabited

def advance (phase : ParsePhase) (width : Fin 4) (b : Bool) : ParseControl :=
  let s : ParseControl := ⟨phase, width, some b, false, .none⟩
  match phase with
  | .bodyFirst => { s with phase := if b then .dead else .bodySecond }
  | .bodySecond => { s with phase := if b then .clauseFirst else .ending, width := 0 }
  | .clauseFirst => { s with phase := if b then .clauseSecond else .dead }
  | .clauseSecond =>
      if b then
        if width = 3 then { s with phase := .dead }
        else { s with phase := .polarity, width := width + 1 }
      else { s with phase := .bodyFirst, width := 0 }
  | .polarity => { s with phase := .firstTag, emission := .delimiter }
  | .firstTag => { s with phase := if b then .firstBit else .dead }
  | .firstBit =>
      { s with
        phase := if b then .nameTag else .dead
        emission := if b then .bit else .none }
  | .nameTag => { s with phase := if b then .nameBit else .clauseFirst }
  | .nameBit => { s with phase := .nameTag, emission := .bit }
  | .ending | .dead => { s with phase := .dead }

def emitTo (emission : ParseEmission) (b : Bool) (occurrences : List Bool) : List Bool :=
  match emission with
  | .none => occurrences
  | .delimiter => false :: occurrences
  | .bit => true :: b :: occurrences

def scanResult : ParsePhase → Fin 4 → List Bool → List Bool → Bool × List Bool
  | phase, _, [], occurrences =>
      if phase = .ending then (true, occurrences) else (false, [])
  | phase, width, b :: tail, occurrences =>
      let next := advance phase width b
      if next.phase = .dead then (false, [])
      else scanResult next.phase next.width tail (emitTo next.emission b occurrences)

def parseMachine : FinTM2 where
  K := ParseStack
  k₀ := .input
  k₁ := .result
  Γ _ := Bool
  Λ := ParseLabel
  main := .scan
  σ := ParseControl
  initialState := ⟨.bodyFirst, 0, none, false, .none⟩
  m
    | .scan => .pop .input (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none, accepted := decide (s.phase = .ending) }) <|
            .branch (fun s => s.accepted)
              (.goto fun _ => .restore) (.goto fun _ => .clearOccurrences))
          (.push .saved (fun s => s.held.getD false) <|
            .load (fun s => advance s.phase s.width (s.held.getD false)) <|
              .branch (fun s => decide (s.phase = .dead))
                (.load (fun s => { s with held := none, emission := .none }) <|
                  .goto fun _ => .clearOccurrences)
                (.branch (fun s => decide (s.emission = .delimiter))
                  (.push .occurrences (fun _ => false) <|
                    .load (fun s => { s with held := none, emission := .none }) <|
                      .goto fun _ => .scan)
                  (.branch (fun s => decide (s.emission = .bit))
                    (.push .occurrences (fun s => s.held.getD false) <|
                      .push .occurrences (fun _ => true) <|
                        .load (fun s => { s with held := none, emission := .none }) <|
                          .goto fun _ => .scan)
                    (.load (fun s => { s with held := none, emission := .none }) <|
                      .goto fun _ => .scan))))
    | .clearOccurrences => .pop .occurrences (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .restore)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .clearOccurrences)
    | .restore => .pop .saved (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .finish)
          (.push .input (fun s => s.held.getD false) <|
            .load (fun s => { s with held := none }) <| .goto fun _ => .restore)
    | .finish => .push .result (fun s => s.accepted) <|
        .load (fun _ => ⟨.bodyFirst, 0, none, false, .none⟩) .halt

def parseStacks (input saved occurrences result frame : List Bool) : ParseStack → List Bool
  | .input => input
  | .saved => saved
  | .occurrences => occurrences
  | .result => result
  | .frame => frame

def parseCfg (label : Option ParseLabel) (phase : ParsePhase) (width : Fin 4)
    (input saved occurrences result frame : List Bool) (accepted : Bool := false) : parseMachine.Cfg :=
  ⟨label, ⟨phase, width, none, accepted, .none⟩,
    parseStacks input saved occurrences result frame⟩

macro "parser_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [parseMachine, TM2.stepAux, parseCfg, parseStacks, advance, emitTo]
    all_goals simp [Function.update_apply, parseStacks, advance, emitTo] <;>
      first | rfl | (funext k; cases k <;> simp [Function.update_apply, parseStacks])))

-- The earning raw-word theorem will keep its grammar/refinement inductions local.

def occurrenceStream (names : List Name) : List Bool :=
  names.flatMap (fun name => nameWord name.reverse)

def decodedOccurrences (w : List Bool) : List Bool :=
  match readWord w with
  | none => []
  | some formula => occurrenceStream (occurrences formula).reverse

/-- All raw words are parsed by the actual fixed finite machine, with restoration
of the source and cleared scratch. The result flag follows the total conventional
decoder; occurrences are materialized only for accepted words. -/
theorem conventional_word_run (w frame : List Bool) :
    Nonempty (EvalsToInTime parseMachine.step
      (parseCfg (some .scan) .bodyFirst 0 w [] [] [] frame)
      (some (parseCfg none .bodyFirst 0 w [] (decodedOccurrences w)
        [(readWord w).isSome] frame)) (4 * w.length + 5)) := by
  let single : ∀ (x : parseMachine.Cfg) (y : Option parseMachine.Cfg),
      parseMachine.step x = y → EvalsToInTime parseMachine.step x y 1 :=
    fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have restore : ∀ saved input occurrence phase width accepted,
      EvalsToInTime parseMachine.step
        (parseCfg (some .restore) phase width input saved occurrence [] frame accepted)
        (some (parseCfg none .bodyFirst 0 (saved.reverse ++ input) [] occurrence [accepted] frame))
        (saved.length + 2) := by
    intro saved
    induction saved with
    | nil =>
      intro input occurrence phase width accepted
      have hs : parseMachine.step (parseCfg (some .restore) phase width input [] occurrence [] frame accepted) =
          some (parseCfg (some .finish) phase width input [] occurrence [] frame accepted) := by
        parser_transition
      have ht : parseMachine.step (parseCfg (some .finish) phase width input [] occurrence [] frame accepted) =
          some (parseCfg none .bodyFirst 0 input [] occurrence [accepted] frame) := by
        parser_transition
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (single _ _ ht)
    | cons b saved ih =>
      intro input occurrence phase width accepted
      have hs : parseMachine.step
          (parseCfg (some .restore) phase width input (b :: saved) occurrence [] frame accepted) =
          some (parseCfg (some .restore) phase width (b :: input) saved occurrence [] frame accepted) := by
        cases b <;> parser_transition
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _ (single _ _ hs)
          (ih (b :: input) occurrence phase width accepted)
  have cleanup : ∀ occurrence input saved phase width,
      EvalsToInTime parseMachine.step
        (parseCfg (some .clearOccurrences) phase width input saved occurrence [] frame)
        (some (parseCfg none .bodyFirst 0 (saved.reverse ++ input) [] [] [false] frame))
        (occurrence.length + saved.length + 3) := by
    intro occurrence
    induction occurrence with
    | nil =>
      intro input saved phase width
      have hs : parseMachine.step
          (parseCfg (some .clearOccurrences) phase width input saved [] [] frame) =
          some (parseCfg (some .restore) phase width input saved [] [] frame) := by
        parser_transition
      simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _
        (single _ _ hs) (restore saved input [] phase width false)
    | cons b occurrence ih =>
      intro input saved phase width
      have hs : parseMachine.step
          (parseCfg (some .clearOccurrences) phase width input saved (b :: occurrence) [] frame) =
          some (parseCfg (some .clearOccurrences) phase width input saved occurrence [] frame) := by
        cases b <;> parser_transition
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (occurrence.length + saved.length + 3) _ _ _ (single _ _ hs) (ih input saved phase width)
  have scan : ∀ input saved occurrence phase width,
      EvalsToInTime parseMachine.step
        (parseCfg (some .scan) phase width input saved occurrence [] frame)
        (some (parseCfg none .bodyFirst 0 (saved.reverse ++ input) []
          (scanResult phase width input occurrence).2 [(scanResult phase width input occurrence).1] frame))
        (4 * input.length + saved.length + occurrence.length + 5) := by
    intro input
    induction input with
    | nil =>
      intro saved occurrence phase width
      by_cases endPhase : phase = .ending
      · have hs : parseMachine.step
            (parseCfg (some .scan) phase width [] saved occurrence [] frame) =
            some (parseCfg (some .restore) phase width [] saved occurrence [] frame true) := by
          subst phase
          parser_transition
        have execution := EvalsToInTime.trans _ 1 (saved.length + 2) _ _ _
          (single _ _ hs) (restore saved [] occurrence phase width true)
        have bound : execution.steps ≤ 4 * ([] : List Bool).length + saved.length + occurrence.length + 5 := by
          have := execution.steps_le_m; simp only [List.length_nil] at *; omega
        exact { steps := execution.steps
                evals_in_steps := by
                  simpa [scanResult, endPhase] using execution.evals_in_steps
                steps_le_m := bound }
      · have hs : parseMachine.step
            (parseCfg (some .scan) phase width [] saved occurrence [] frame) =
            some (parseCfg (some .clearOccurrences) phase width [] saved occurrence [] frame) := by
          cases phase <;> try contradiction
          all_goals parser_transition
        have execution := EvalsToInTime.trans _ 1 (occurrence.length + saved.length + 3) _ _ _
          (single _ _ hs) (cleanup occurrence [] saved phase width)
        have bound : execution.steps ≤ 4 * ([] : List Bool).length + saved.length + occurrence.length + 5 := by
          have := execution.steps_le_m; simp only [List.length_nil] at *; omega
        exact { steps := execution.steps
                evals_in_steps := by
                  simpa [scanResult, endPhase] using execution.evals_in_steps
                steps_le_m := bound }
    | cons b input ih =>
      intro saved occurrence phase width
      let next := advance phase width b
      have hs : parseMachine.step
          (parseCfg (some .scan) phase width (b :: input) saved occurrence [] frame) =
          some (parseCfg (some (if next.phase = .dead then .clearOccurrences else .scan))
            next.phase next.width input (b :: saved)
            (if next.phase = .dead then occurrence else emitTo next.emission b occurrence) [] frame) := by
        cases phase <;> fin_cases width <;> cases b <;>
          simp [next, advance, emitTo] <;> parser_transition
      by_cases bad : next.phase = .dead
      · simp only [bad, ite_true] at hs
        have execution := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ hs)
          (cleanup occurrence input (b :: saved) .dead next.width)
        have bound : execution.steps ≤ 4 * (b :: input).length + saved.length + occurrence.length + 5 := by
          have := execution.steps_le_m; simp only [List.length_cons] at *; omega
        exact { steps := execution.steps
                evals_in_steps := by
                  simpa [scanResult, next, bad, List.reverse_cons, List.append_assoc] using
                    execution.evals_in_steps
                steps_le_m := bound }
      · simp only [bad, ite_false] at hs
        have execution := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ hs)
          (ih (b :: saved) (emitTo next.emission b occurrence) next.phase next.width)
        have emissionBound : (emitTo next.emission b occurrence).length ≤ occurrence.length + 2 := by
          cases next.emission <;> simp [emitTo]
        have bound : execution.steps ≤ 4 * (b :: input).length + saved.length + occurrence.length + 5 := by
          have := execution.steps_le_m; simp only [List.length_cons] at *; omega
        exact { steps := execution.steps
                evals_in_steps := by
                  simpa [scanResult, next, bad, List.reverse_cons, List.append_assoc] using
                    execution.evals_in_steps
                steps_le_m := bound }
  have bitsGrammar : ∀ word width occurrence,
      scanResult .nameTag width word occurrence =
        match readBits word with
        | none => (false, [])
        | some (bits, tail) => scanResult .clauseFirst width tail
            (bits.reverse.flatMap (fun b => [true, b]) ++ occurrence) := by
    intro word
    induction word using List.twoStepInduction with
    | nil => intro width occurrence; rfl
    | singleton b => intro width occurrence; cases b <;> rfl
    | cons_cons tag b word ih _ =>
      intro width occurrence
      cases tag with
      | false => rfl
      | true =>
        have recur := ih width (true :: b :: occurrence)
        cases hr : readBits word with
        | none => simpa [scanResult, advance, emitTo, readBits, hr] using recur
        | some pair =>
          rcases pair with ⟨bits, tail⟩
          simpa [scanResult, advance, emitTo, readBits, hr, List.reverse_cons,
            List.flatMap_append, List.append_assoc] using recur
  have nameGrammar : ∀ word width occurrence,
      scanResult .firstTag width word occurrence =
        match readName word with
        | none => (false, [])
        | some (name, tail) => scanResult .clauseFirst width tail
            (name.reverse.flatMap (fun b => [true, b]) ++ occurrence) := by
    intro word width occurrence
    cases word with
    | nil => rfl
    | cons tag word =>
      cases tag with
      | false => simp [scanResult, advance, readName, readBits]
      | true =>
        cases word with
        | nil => rfl
        | cons b word =>
          cases b with
          | false =>
            cases hr : readBits word with
            | none => simp [scanResult, advance, emitTo, readName, readBits, hr]
            | some pair =>
              rcases pair with ⟨bits, tail⟩
              simp [scanResult, advance, emitTo, readName, readBits, hr]
          | true =>
            have recur := bitsGrammar word width (true :: true :: occurrence)
            cases hr : readBits word with
            | none => simpa [scanResult, advance, emitTo, readName, readBits, hr] using recur
            | some pair =>
              rcases pair with ⟨bits, tail⟩
              simpa [scanResult, advance, emitTo, readName, readBits, hr,
                List.reverse_cons, List.flatMap_append, List.append_assoc] using recur
  have clauseGrammar : ∀ budget width word occurrence, width.val + budget = 3 →
      scanResult .clauseFirst width word occurrence =
        match readClause budget word with
        | none => (false, [])
        | some (clause, tail) => scanResult .bodyFirst 0 tail
            (occurrenceStream (clause.map Prod.fst).reverse ++ occurrence) := by
    intro budget
    induction budget with
    | zero =>
      intro width word occurrence hw
      have widthEq : width = (3 : Fin 4) := Fin.ext (by omega)
      subst width
      cases word with
      | nil => rfl
      | cons tag word =>
        cases tag with
        | false => rfl
        | true => cases word with
          | nil => rfl
          | cons tag word => cases tag <;>
              simp [scanResult, advance, emitTo, readClause, occurrenceStream]
    | succ budget ih =>
      intro width word occurrence hw
      have widthNe : width ≠ (3 : Fin 4) := by
        intro e
        have hv := congrArg Fin.val e
        norm_num at hv
        omega
      have nextWidth : (width + 1).val + budget = 3 := by
        fin_cases width <;> simp_all <;> omega
      cases word with
      | nil => rfl
      | cons tag word =>
        cases tag with
        | false => rfl
        | true => cases word with
          | nil => rfl
          | cons tag word => cases tag with
            | false => simp [scanResult, advance, emitTo, readClause, occurrenceStream]
            | true => cases word with
              | nil => simp [scanResult, advance, emitTo, readClause, widthNe]
              | cons polarity word =>
                have hn := nameGrammar word (width + 1) (false :: occurrence)
                cases hr : readName word with
                | none => simpa [scanResult, advance, emitTo, readClause, widthNe, hr] using hn
                | some pair =>
                  rcases pair with ⟨name, tail⟩
                  have ht := ih (width + 1) tail
                    (name.reverse.flatMap (fun b => [true, b]) ++ false :: occurrence) nextWidth
                  cases hc : readClause budget tail with
                  | none =>
                    simp only [hr] at hn
                    simp only [hc] at ht
                    simpa [scanResult, advance, emitTo, readClause, widthNe, hr, hc] using hn.trans ht
                  | some pair =>
                    rcases pair with ⟨clause, rest⟩
                    simp only [hr] at hn
                    simp only [hc] at ht
                    simpa [scanResult, advance, emitTo, readClause, widthNe, hr, hc,
                      occurrenceStream, nameWord, List.reverse_cons, List.flatMap_append,
                      List.append_assoc] using hn.trans ht
  have bitsSuffix : ∀ word bits tail, readBits word = some (bits, tail) → tail.length ≤ word.length := by
    intro word
    induction word using List.twoStepInduction with
    | nil => intro bits tail h; cases h
    | singleton b =>
      intro bits tail h
      cases b with
      | false => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
                 obtain ⟨rfl, rfl⟩ := h; simp
      | true => cases h
    | cons_cons tag b word ih _ =>
      intro bits tail h
      cases tag with
      | false => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at h
                 obtain ⟨rfl, rfl⟩ := h; simp
      | true =>
        cases hr : readBits word with
        | none => simp [readBits, hr] at h
        | some pair =>
          rcases pair with ⟨name, rest⟩
          simp [readBits, hr] at h
          obtain ⟨rfl, rfl⟩ := h
          have ht := ih name rest hr
          simp only [List.length_cons]
          omega
  have nameSuffix : ∀ word name tail, readName word = some (name, tail) → tail.length ≤ word.length := by
    intro word name tail h
    cases hr : readBits word with
    | none => simp [readName, hr] at h
    | some pair =>
      rcases pair with ⟨bits, rest⟩
      by_cases canonical : bits.head? = some true
      · simp [readName, hr, canonical] at h
        obtain ⟨rfl, rfl⟩ := h
        exact bitsSuffix word bits rest hr
      · simp [readName, hr, canonical] at h
  have clauseSuffix : ∀ budget word clause tail,
      readClause budget word = some (clause, tail) → tail.length ≤ word.length := by
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
              simp [readClause] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [List.length_cons]
              omega
            | true => cases word <;> simp [readClause] at h
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
              simp [readClause] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [List.length_cons]
              omega
            | true => cases word with
              | nil => cases h
              | cons polarity word =>
                cases hr : readName word with
                | none => simp [readClause, hr] at h
                | some pair =>
                  rcases pair with ⟨name, rest⟩
                  cases hc : readClause budget rest with
                  | none => simp [readClause, hr, hc] at h
                  | some pair =>
                    rcases pair with ⟨c, remaining⟩
                    simp [readClause, hr, hc] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hn := nameSuffix word name rest hr
                    have ht := ih rest c remaining hc
                    simp only [List.length_cons]
                    omega
  have bodyGrammar : ∀ fuel word occurrence, word.length < fuel →
      scanResult .bodyFirst 0 word occurrence =
        match readBody fuel word with
        | none => (false, [])
        | some formula => (true, occurrenceStream (occurrences formula).reverse ++ occurrence) := by
    intro fuel
    induction fuel with
    | zero => intro word occurrence h; omega
    | succ fuel ih =>
      intro word occurrence hf
      cases word with
      | nil => rfl
      | cons tag word => cases tag with
        | true => rfl
        | false => cases word with
          | nil => rfl
          | cons tag word => cases tag with
            | false => cases word with
              | nil => simp [scanResult, advance, emitTo, readBody, occurrenceStream, occurrences]
              | cons b word => simp [scanResult, advance, emitTo, readBody]
            | true =>
              have hc := clauseGrammar 3 0 word occurrence (by decide)
              cases hr : readClause 3 word with
              | none => simpa [scanResult, advance, emitTo, readBody, hr] using hc
              | some pair =>
                rcases pair with ⟨clause, rest⟩
                have hrest := clauseSuffix 3 word clause rest hr
                have fuelBound : rest.length < fuel := by
                  simp only [List.length_cons] at hf
                  omega
                have ht := ih rest (occurrenceStream (clause.map Prod.fst).reverse ++ occurrence) fuelBound
                cases hb : readBody fuel rest with
                | none =>
                  simp only [hr] at hc
                  simp only [hb] at ht
                  simpa [scanResult, advance, emitTo, readBody, hr, hb] using hc.trans ht
                | some formula =>
                  simp only [hr] at hc
                  simp only [hb] at ht
                  simpa [scanResult, advance, emitTo, readBody, hr, hb,
                    occurrences, List.reverse_append, occurrenceStream, List.flatMap_append,
                    List.append_assoc] using hc.trans ht
  have fidelity := bodyGrammar (w.length + 1) w [] (by omega)
  have finalSpec : scanResult .bodyFirst 0 w [] = ((readWord w).isSome, decodedOccurrences w) := by
    rw [fidelity]
    change (match readWord w with
      | none => (false, [])
      | some formula => (true, occurrenceStream (occurrences formula).reverse ++ [])) = _
    cases hr : readWord w <;> simp [decodedOccurrences, hr]
  have execution := scan w [] [] .bodyFirst 0
  exact ⟨by simpa [finalSpec] using execution⟩

end PredictiveThermodynamic.Conventional
