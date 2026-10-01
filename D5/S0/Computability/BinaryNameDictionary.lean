/- GID: D5/S0/Computability/BinaryNameDictionary
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryNameDictionary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S0/Computability/BinaryNameDeduplication.dictionary_build_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: A fixed finite dictionary scan with paid name comparison and restoration. -/

import D5.S0.Computability.BinaryNameComparison
import D5.S0.Computability.ConventionalClauseWords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.BinaryNames

open Turing StateTransition

inductive DictionaryStack
  | operand (k : CompareStack) | stream | history | index
  deriving DecidableEq, Fintype, Inhabited

inductive DictionaryLabel
  | comparison (label : CompareLabel)
  | start | tag | bit | ready | dispatch | clearRight | rewind | finish
  deriving DecidableEq, Fintype, Inhabited

structure DictionaryControl where
  comparison : CompareControl := ⟨none, none, true⟩
  held : Option Bool := none
  found : Bool := false
  deriving DecidableEq, Fintype, Inhabited

/-- This is a finite syntactic translation of statements, not a machine call or
an operation on unbounded data held in control. Every source push and pop remains
an actual native instruction. The source's return enters the caller's dispatch. -/
def liftComparison : TM2.Stmt (fun _ : CompareStack => Bool) CompareLabel CompareControl →
    TM2.Stmt (fun _ : DictionaryStack => Bool) DictionaryLabel DictionaryControl
  | .push k f next => .push (.operand k) (fun s => f s.comparison) (liftComparison next)
  | .peek k f next => .peek (.operand k)
      (fun s b => { s with comparison := f s.comparison b }) (liftComparison next)
  | .pop k f next => .pop (.operand k)
      (fun s b => { s with comparison := f s.comparison b }) (liftComparison next)
  | .load f next => .load (fun s => { s with comparison := f s.comparison }) (liftComparison next)
  | .branch f yes no => .branch (fun s => f s.comparison) (liftComparison yes) (liftComparison no)
  | .goto f => .goto (fun s => .comparison (f s.comparison))
  | .halt => .goto (fun _ => .dispatch)

def dictionaryMachine : FinTM2 where
  K := DictionaryStack
  k₀ := .stream
  k₁ := .index
  Γ _ := Bool
  Λ := DictionaryLabel
  main := .start
  σ := DictionaryControl
  initialState := ⟨⟨none, none, true⟩, none, false⟩
  m
    | .comparison label => liftComparison (compareMachine.m label)
    | .start => .peek .stream (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .rewind)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .tag)
    | .tag => .pop .stream (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.goto fun _ => .clearRight)
          (.push .history (fun s => s.held.getD false) <|
            .branch (fun s => s.held.getD false)
              (.load (fun s => { s with held := none }) <| .goto fun _ => .bit)
              (.load (fun s => { s with held := none }) <| .goto fun _ => .ready))
    | .bit => .pop .stream (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.goto fun _ => .clearRight)
          (.push .history (fun s => s.held.getD false) <|
            .push (.operand .right) (fun s => s.held.getD false) <|
              .load (fun s => { s with held := none }) <| .goto fun _ => .tag)
    | .ready => .load (fun s => { s with comparison := ⟨none, none, true⟩ }) <|
        .goto fun _ => .comparison .compare
    | .dispatch => .pop (.operand .output) (fun s b => { s with held := b }) <|
        .load (fun s => { s with held := none, found := s.held.getD false }) <|
          .goto fun _ => .clearRight
    | .clearRight => .pop (.operand .right) (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <|
            .branch (fun s => s.found)
              (.goto fun _ => .rewind)
              (.push .index (fun _ => true) <| .goto fun _ => .start))
          (.load (fun s => { s with held := none }) <| .goto fun _ => .clearRight)
    | .rewind => .pop .history (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .finish)
          (.push .stream (fun s => s.held.getD false) <|
            .load (fun s => { s with held := none }) <| .goto fun _ => .rewind)
    | .finish => .push .index (fun s => s.found) <|
        .load (fun _ => ⟨⟨none, none, true⟩, none, false⟩) .halt

/-- The private dictionary stores reversed binary names, so serial extraction
onto the candidate stack restores their ordinary spelling. -/
def dictionaryStream (names : List Conventional.Name) : List Bool :=
  names.flatMap (fun name => Conventional.nameWord name.reverse)

def dictionaryStacks (operands : CompareStack → List Bool)
    (stream history index : List Bool) : DictionaryStack → List Bool
  | .operand k => operands k
  | .stream => stream
  | .history => history
  | .index => index

def dictionaryCfg (label : Option DictionaryLabel) (s : DictionaryControl)
    (operands : CompareStack → List Bool) (stream history index : List Bool) : dictionaryMachine.Cfg :=
  ⟨label, s, dictionaryStacks operands stream history index⟩

def lookupCfg (label : DictionaryLabel) (query candidate savedQuery savedCandidate frame
    stream history index : List Bool) (found : Bool := false) : dictionaryMachine.Cfg :=
  dictionaryCfg (some label) ⟨⟨none, none, true⟩, none, found⟩
    (compareStacks query candidate savedQuery savedCandidate [] frame) stream history index

macro "dictionary_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [dictionaryMachine, TM2.stepAux, lookupCfg, dictionaryCfg,
      dictionaryStacks, compareStacks]
    all_goals simp [Function.update_apply, dictionaryStacks, compareStacks] <;>
      first | rfl | (funext k; cases k with
        | operand k => cases k <;> simp [Function.update_apply, dictionaryStacks, compareStacks]
        | stream => simp [Function.update_apply, dictionaryStacks]
        | history => simp [Function.update_apply, dictionaryStacks]
        | index => simp [Function.update_apply, dictionaryStacks])))

/-- A physical dictionary lookup compares whole binary names without expanding
their numeric values. Its unary position is the first occurrence in the supplied
dictionary order, with length as the absent sentinel. Both the query and the
entire serialized dictionary are restored; all scratch and comparison output
are empty at return. The polynomial clock includes those restorations. -/
theorem dictionary_lookup_run (query : List Bool) (names : List Conventional.Name)
    (frame : List Bool) :
    Nonempty (EvalsToInTime dictionaryMachine.step
      (lookupCfg .start query [] [] [] frame (dictionaryStream names) [] [])
      (some (dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
        (compareStacks query [] [] [] [] frame) (dictionaryStream names) []
        (decide (query ∈ names) :: List.replicate (names.idxOf query) true)))
      ((2 * query.length + 12) * names.length +
        4 * (dictionaryStream names).length + 3)) := by
  let single : ∀ (x : dictionaryMachine.Cfg) (y : Option dictionaryMachine.Cfg),
      dictionaryMachine.step x = y → EvalsToInTime dictionaryMachine.step x y 1 :=
    fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have rewind : ∀ history stream index found, EvalsToInTime dictionaryMachine.step
      (lookupCfg .rewind query [] [] [] frame stream history index found)
      (some (dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
        (compareStacks query [] [] [] [] frame) (history.reverse ++ stream) []
        (found :: index))) (history.length + 2) := by
    intro history
    induction history with
    | nil =>
      intro stream index found
      have hs : dictionaryMachine.step
          (lookupCfg .rewind query [] [] [] frame stream [] index found) =
          some (lookupCfg .finish query [] [] [] frame stream [] index found) := by
        dictionary_transition
      have ht : dictionaryMachine.step
          (lookupCfg .finish query [] [] [] frame stream [] index found) =
          some (dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
            (compareStacks query [] [] [] [] frame) stream [] (found :: index)) := by
        dictionary_transition
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (single _ _ ht)
    | cons b history ih =>
      intro stream index found
      have hs : dictionaryMachine.step
          (lookupCfg .rewind query [] [] [] frame stream (b :: history) index found) =
          some (lookupCfg .rewind query [] [] [] frame (b :: stream) history index found) := by
        cases b <;> dictionary_transition
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (history.length + 2) _ _ _ (single _ _ hs)
          (ih (b :: stream) index found)
  have clearCandidate : ∀ candidate stream history index found,
      EvalsToInTime dictionaryMachine.step
        (lookupCfg .clearRight query candidate [] [] frame stream history index found)
        (some (lookupCfg (if found then .rewind else .start) query [] [] [] frame
          stream history (if found then index else true :: index) found))
        (candidate.length + 1) := by
    intro candidate
    induction candidate with
    | nil =>
      intro stream history index found
      apply single
      cases found <;> dictionary_transition
    | cons b candidate ih =>
      intro stream history index found
      have hs : dictionaryMachine.step
          (lookupCfg .clearRight query (b :: candidate) [] [] frame stream history index found) =
          some (lookupCfg .clearRight query candidate [] [] frame stream history index found) := by
        cases b <;> dictionary_transition
      simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 (candidate.length + 1)
        _ _ _ (single _ _ hs) (ih stream history index found)
  have extract : ∀ bits candidate stream history index,
      EvalsToInTime dictionaryMachine.step
        (lookupCfg .tag query candidate [] [] frame
          (Conventional.nameWord bits ++ stream) history index)
        (some (lookupCfg .ready query (bits.reverse ++ candidate) [] [] frame stream
          ((Conventional.nameWord bits).reverse ++ history) index)) (2 * bits.length + 1) := by
    intro bits
    induction bits with
    | nil =>
      intro candidate stream history index
      apply single
      dsimp [Conventional.nameWord]
      dictionary_transition
    | cons b bits ih =>
      intro candidate stream history index
      let rest := Conventional.nameWord bits ++ stream
      have hs : dictionaryMachine.step
          (lookupCfg .tag query candidate [] [] frame (true :: b :: rest) history index) =
          some (lookupCfg .bit query candidate [] [] frame (b :: rest) (true :: history) index) := by
        dictionary_transition
      have ht : dictionaryMachine.step
          (lookupCfg .bit query candidate [] [] frame (b :: rest) (true :: history) index) =
          some (lookupCfg .tag query (b :: candidate) [] [] frame rest (b :: true :: history) index) := by
        cases b <;> dictionary_transition
      have head := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (single _ _ ht)
      have run := EvalsToInTime.trans _ 2 (2 * bits.length + 1) _ _ _ head
        (ih (b :: candidate) stream (b :: true :: history) index)
      simpa [Conventional.nameWord, rest, List.reverse_append, List.reverse_cons,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run
  have compare : ∀ candidate stream history index,
      EvalsToInTime dictionaryMachine.step
        (lookupCfg (.comparison .compare) query candidate [] [] frame stream history index)
        (some (dictionaryCfg (some .dispatch) ⟨⟨none, none, true⟩, none, false⟩
          (compareStacks query candidate [] [] [decide (query = candidate)] frame)
          stream history index)) (2 * (query.length + candidate.length) + 4) := by
    intro candidate stream history index
    let lift (c : compareMachine.Cfg) : dictionaryMachine.Cfg :=
      dictionaryCfg (some (c.l.map DictionaryLabel.comparison |>.getD .dispatch))
        ⟨c.var, none, false⟩ c.stk stream history index
    have update : ∀ (words : CompareStack → List Bool) k v,
        Function.update (dictionaryStacks words stream history index) (.operand k) v =
          dictionaryStacks (Function.update words k v) stream history index := by
      intro words k v
      funext j
      cases j with
      | operand j => simp [dictionaryStacks, Function.update_apply]
      | stream => simp [dictionaryStacks, Function.update_apply]
      | history => simp [dictionaryStacks, Function.update_apply]
      | index => simp [dictionaryStacks, Function.update_apply]
    have aux : ∀ (stmt : TM2.Stmt (fun _ : CompareStack => Bool) CompareLabel CompareControl)
        state words,
        TM2.stepAux (liftComparison stmt) (⟨state, none, false⟩ : DictionaryControl)
          (dictionaryStacks words stream history index) =
        lift (TM2.stepAux stmt state words) := by
      intro stmt
      induction stmt with
      | push k f next ih =>
        intro state words
        simpa only [liftComparison, TM2.stepAux, dictionaryStacks, update] using
          ih state (Function.update words k (f state :: words k))
      | peek k f next ih =>
        intro state words
        simpa only [liftComparison, TM2.stepAux, dictionaryStacks] using
          ih (f state (words k).head?) words
      | pop k f next ih =>
        intro state words
        simpa only [liftComparison, TM2.stepAux, dictionaryStacks, update] using
          ih (f state (words k).head?) (Function.update words k (words k).tail)
      | load f next ih =>
        intro state words
        simpa only [liftComparison, TM2.stepAux] using ih (f state) words
      | branch f yes no iy ino =>
        intro state words
        cases hf : f state <;>
          simpa only [liftComparison, TM2.stepAux, hf, cond_false, cond_true] using
            (by first | exact ino state words | exact iy state words)
      | goto f => intro state words; rfl
      | halt => intro state words; rfl
    have one : ∀ c d, compareMachine.step c = some d →
        dictionaryMachine.step (lift c) = some (lift d) := by
      intro c d hc
      rcases c with ⟨label, state, words⟩
      cases label with
      | none => simp [FinTM2.step, TM2.step] at hc
      | some label =>
        simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
        rw [← hc]
        exact congrArg some (aux (compareMachine.m label) state words)
    have noneStable : ∀ t, (flip bind compareMachine.step)^[t] none = none := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
    have liftRun : ∀ t c d,
        (flip bind compareMachine.step)^[t] (some c) = some d →
        (flip bind dictionaryMachine.step)^[t] (some (lift c)) = some (lift d) := by
      intro t
      induction t with
      | zero =>
        intro c d h
        simpa using congrArg (Option.map lift) h
      | succ t ih =>
        intro c d h
        rw [Function.iterate_succ_apply] at h ⊢
        change (flip bind compareMachine.step)^[t] (compareMachine.step c) = some d at h
        change (flip bind dictionaryMachine.step)^[t] (dictionaryMachine.step (lift c)) =
          some (lift d)
        cases hs : compareMachine.step c with
        | none =>
          rw [hs, noneStable] at h
          cases h
        | some next =>
          have hn := one c next hs
          rw [hn]
          exact ih next d (by rwa [hs] at h)
    let run := Classical.choice (name_compare_run query candidate [] frame)
    refine { steps := run.steps, steps_le_m := run.steps_le_m, evals_in_steps := ?_ }
    exact liftRun _ _ _ run.evals_in_steps
  have nameSize : ∀ bits, (Conventional.nameWord bits).length = 2 * bits.length + 1 := by
    intro bits
    induction bits with
    | nil => rfl
    | cons b bits ih =>
      simp only [Conventional.nameWord, List.flatMap_cons, List.cons_append,
        List.nil_append, List.length_cons] at ih ⊢
      omega
  have lookup : ∀ names history index,
      EvalsToInTime dictionaryMachine.step
        (lookupCfg .start query [] [] [] frame (dictionaryStream names) history index)
        (some (dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
          (compareStacks query [] [] [] [] frame)
          (history.reverse ++ dictionaryStream names) []
          (decide (query ∈ names) :: (List.replicate (names.idxOf query) true ++ index))))
        ((2 * query.length + 12) * names.length +
          4 * (dictionaryStream names).length + history.length + 3) := by
    intro names
    induction names with
    | nil =>
      intro history index
      have hs : dictionaryMachine.step
          (lookupCfg .start query [] [] [] frame [] history index) =
          some (lookupCfg .rewind query [] [] [] frame [] history index) := by
        dictionary_transition
      have run := EvalsToInTime.trans _ 1 (history.length + 2) _ _ _ (single _ _ hs)
        (rewind history [] index false)
      simpa [dictionaryStream] using
        (show EvalsToInTime dictionaryMachine.step _ _ (history.length + 3) from run)
    | cons candidate names ih =>
      intro history index
      let word := Conventional.nameWord candidate.reverse
      let stream := dictionaryStream names
      let saved := word.reverse ++ history
      have nonempty : word ≠ [] := by simp [word, Conventional.nameWord]
      have parts := List.exists_cons_of_ne_nil nonempty
      let bit := parts.choose
      let rest := parts.choose_spec.choose
      have hw : word = bit :: rest := parts.choose_spec.choose_spec
      have hs : dictionaryMachine.step
          (lookupCfg .start query [] [] [] frame (word ++ stream) history index) =
          some (lookupCfg .tag query [] [] [] frame (word ++ stream) history index) := by
        rw [hw]
        cases bit <;> dictionary_transition
      have ex := extract candidate.reverse [] stream history index
      simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at ex
      have ready : dictionaryMachine.step
          (lookupCfg .ready query candidate [] [] frame stream saved index) =
          some (lookupCfg (.comparison .compare) query candidate [] [] frame stream saved index) := by
        dictionary_transition
      have cmp := compare candidate stream saved index
      have dispatch : dictionaryMachine.step
          (dictionaryCfg (some .dispatch) ⟨⟨none, none, true⟩, none, false⟩
            (compareStacks query candidate [] [] [decide (query = candidate)] frame)
            stream saved index) =
          some (lookupCfg .clearRight query candidate [] [] frame stream saved index
            (decide (query = candidate))) := by
        by_cases h : query = candidate <;> simp only [h, decide_true, decide_false] <;>
          dictionary_transition
      have tail := clearCandidate candidate stream saved index (decide (query = candidate))
      have r5 := EvalsToInTime.trans _ 1 (candidate.length + 1) _ _ _
        (single _ _ dispatch) tail
      have r4 := EvalsToInTime.trans _ (2 * (query.length + candidate.length) + 4)
        (candidate.length + 1 + 1) _ _ _ cmp r5
      have r3 := EvalsToInTime.trans _ 1
        (candidate.length + 1 + 1 + (2 * (query.length + candidate.length) + 4))
        _ _ _ (single _ _ ready) r4
      have r2 := EvalsToInTime.trans _ (2 * candidate.length + 1)
        (candidate.length + 1 + 1 + (2 * (query.length + candidate.length) + 4) + 1)
        _ _ _ ex r3
      have head := EvalsToInTime.trans _ 1
        (candidate.length + 1 + 1 + (2 * (query.length + candidate.length) + 4) + 1 +
          (2 * candidate.length + 1)) _ _ _ (single _ _ hs) r2
      have size : word.length = 2 * candidate.length + 1 := by
        simpa [word] using nameSize candidate.reverse
      have encoded : dictionaryStream (candidate :: names) = word ++ stream := by
        simp [dictionaryStream, word, stream]
      by_cases hit : query = candidate
      · subst candidate
        simp only [decide_true, Bool.true_eq, ite_true] at head
        have last := rewind saved stream index true
        have run := EvalsToInTime.trans _ _ _ _ _ _ head last
        have clock : run.steps ≤ (2 * query.length + 12) * (query :: names).length +
            4 * (dictionaryStream (query :: names)).length + history.length + 3 := by
          have hb := run.steps_le_m
          simp only [saved, List.length_append, List.length_reverse] at hb
          rw [size] at hb
          simp only [encoded, List.length_cons, List.length_append, size,
            Nat.mul_add, Nat.mul_one]
          dsimp only [stream]
          omega
        have bounded := { run with steps_le_m := clock }
        simpa [encoded, saved, List.reverse_append, List.append_assoc] using bounded
      · simp only [hit, decide_false, Bool.false_eq_true, ite_false] at head
        have last := ih saved (true :: index)
        have run := EvalsToInTime.trans _ _ _ _ _ _ head last
        have clock : run.steps ≤ (2 * query.length + 12) * (candidate :: names).length +
            4 * (dictionaryStream (candidate :: names)).length + history.length + 3 := by
          have hb := run.steps_le_m
          simp only [saved, List.length_append, List.length_reverse] at hb
          rw [size] at hb
          simp only [encoded, List.length_cons, List.length_append, size,
            Nat.mul_add, Nat.mul_one]
          dsimp only [stream]
          omega
        have bounded := { run with steps_le_m := clock }
        simpa [encoded, saved, List.reverse_append, List.append_assoc, hit, Ne.symm hit,
          List.idxOf_cons, List.replicate_succ', stream, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using bounded
  exact ⟨by simpa using lookup names [] []⟩

end PredictiveThermodynamic.BinaryNames
