/- GID: D5/S0/Computability/BinaryNameDeduplication
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryNameDeduplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/BinaryNameDictionary]
   utility: kind=checker; basis=consumer=D5/S0/Computability/DenseClauseConversion.dense_word_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: A finite occurrence-stream dictionary builder with actual paid lookup and writing. -/

import D5.S0.Computability.BinaryNameDictionary
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.BinaryNames

open Turing StateTransition

inductive BuilderStack
  | lookup (k : DictionaryStack) | source | dimension
  deriving DecidableEq, Fintype, Inhabited

inductive BuilderLabel
  | lookup (label : DictionaryLabel)
  | start | tag | bit | ready | dispatch | clearIndex | clearQuery | insert | finish
  deriving DecidableEq, Fintype, Inhabited

/-- A finite program translation. A returned lookup enters dispatch; it does
not materialize a whole dictionary, operand or configuration in one step. -/
def liftLookup : TM2.Stmt (fun _ : DictionaryStack => Bool) DictionaryLabel DictionaryControl →
    TM2.Stmt (fun _ : BuilderStack => Bool) BuilderLabel DictionaryControl
  | .push k f next => .push (.lookup k) f (liftLookup next)
  | .peek k f next => .peek (.lookup k) f (liftLookup next)
  | .pop k f next => .pop (.lookup k) f (liftLookup next)
  | .load f next => .load f (liftLookup next)
  | .branch f yes no => .branch f (liftLookup yes) (liftLookup no)
  | .goto f => .goto (fun s => .lookup (f s))
  | .halt => .goto (fun _ => .dispatch)

/-- Occurrences are scanned from right to left. An unseen name is written at
the head of the dictionary, giving the pinned rightmost-occurrence order. The
dimension stack receives one symbol per actual insertion. -/
def builderMachine : FinTM2 where
  K := BuilderStack
  k₀ := .source
  k₁ := .lookup .stream
  Γ _ := Bool
  Λ := BuilderLabel
  main := .start
  σ := DictionaryControl
  initialState := ⟨⟨none, none, true⟩, none, false⟩
  m
    | .lookup label => liftLookup (dictionaryMachine.m label)
    | .start => .peek .source (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .finish)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .tag)
    | .tag => .pop .source (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.getD false)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .bit)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .ready)
    | .bit => .pop .source (fun s b => { s with held := b }) <|
        .push (.lookup (.operand .left)) (fun s => s.held.getD false) <|
          .load (fun s => { s with held := none }) <| .goto fun _ => .tag
    | .ready => .goto fun _ => .lookup .start
    | .dispatch => .pop (.lookup .index) (fun s b => { s with held := b }) <|
        .load (fun s => { s with held := none, found := s.held.getD false }) <|
          .goto fun _ => .clearIndex
    | .clearIndex => .pop (.lookup .index) (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <|
            .branch (fun s => s.found)
              (.goto fun _ => .clearQuery)
              (.push (.lookup .stream) (fun _ => false) <|
                .push .dimension (fun _ => true) <| .goto fun _ => .insert))
          (.load (fun s => { s with held := none }) <| .goto fun _ => .clearIndex)
    | .clearQuery => .pop (.lookup (.operand .left)) (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun _ => ⟨⟨none, none, true⟩, none, false⟩) <| .goto fun _ => .start)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .clearQuery)
    | .insert => .pop (.lookup (.operand .left)) (fun s b => { s with held := b }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun _ => ⟨⟨none, none, true⟩, none, false⟩) <| .goto fun _ => .start)
          (.push (.lookup .stream) (fun s => s.held.getD false) <|
            .push (.lookup .stream) (fun _ => true) <|
              .load (fun s => { s with held := none }) <| .goto fun _ => .insert)
    | .finish => .load (fun _ => ⟨⟨none, none, true⟩, none, false⟩) .halt

def builderStacks (words : DictionaryStack → List Bool)
    (source dimension : List Bool) : BuilderStack → List Bool
  | .lookup k => words k
  | .source => source
  | .dimension => dimension

def builderCfg (label : Option BuilderLabel) (s : DictionaryControl)
    (words : DictionaryStack → List Bool) (source dimension : List Bool) : builderMachine.Cfg :=
  ⟨label, s, builderStacks words source dimension⟩

def buildCfg (label : BuilderLabel) (query stream index source dimension frame : List Bool)
    (found : Bool := false) : builderMachine.Cfg :=
  builderCfg (some label) ⟨⟨none, none, true⟩, none, found⟩
    (dictionaryStacks (compareStacks query [] [] [] [] frame) stream [] index) source dimension

def buildNames : List Conventional.Name → List Conventional.Name → List Conventional.Name
  | [], dictionary => dictionary
  | name :: tail, dictionary =>
      buildNames tail (if name ∈ dictionary then dictionary else name :: dictionary)

/-- This clock is the sum of actual extraction, lookup, index drain and
name writing costs. It is not an input-dependent fuel in the finite control. -/
def buildClock : List Conventional.Name → List Conventional.Name → Nat
  | [], _ => 2
  | name :: tail, dictionary =>
      (2 * name.length + 12) * dictionary.length + 4 * (dictionaryStream dictionary).length +
        dictionary.idxOf name + 3 * name.length + 9 +
        buildClock tail (if name ∈ dictionary then dictionary else name :: dictionary)

macro "builder_transition" : tactic =>
  `(tactic| (
    apply congrArg some
    dsimp [builderMachine, TM2.stepAux, buildCfg, builderCfg, builderStacks,
      dictionaryStacks, compareStacks]
    all_goals simp [Function.update_apply, builderStacks, dictionaryStacks, compareStacks] <;>
      first | rfl | (funext k; cases k with
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply, builderStacks,
              dictionaryStacks, compareStacks]
          | stream => simp [Function.update_apply, builderStacks, dictionaryStacks]
          | history => simp [Function.update_apply, builderStacks, dictionaryStacks]
          | index => simp [Function.update_apply, builderStacks, dictionaryStacks]
        | source => simp [Function.update_apply, builderStacks]
        | dimension => simp [Function.update_apply, builderStacks])))

/-- Actual dictionary construction on a serialized occurrence stream. No
deduplication or dictionary execution certificate is a premise. Lookup's flag
is consumed by the live insert/discard branch. Arbitrary caller frame and
dimension suffix are preserved; every scratch stack is cleared at return. -/
theorem dictionary_build_run (names : List Conventional.Name) (frame dimension : List Bool) :
    Nonempty (EvalsToInTime builderMachine.step
      (buildCfg .start [] [] [] (dictionaryStream names.reverse) dimension frame)
      (some (builderCfg none ⟨⟨none, none, true⟩, none, false⟩
        (dictionaryStacks (compareStacks [] [] [] [] [] frame)
          (dictionaryStream names.dedup) [] []) []
        (List.replicate names.dedup.length true ++ dimension)))
      (20 * ((dictionaryStream names).length + 1) ^ 2)) := by
  let single : ∀ (x : builderMachine.Cfg) (y : Option builderMachine.Cfg),
      builderMachine.step x = y → EvalsToInTime builderMachine.step x y 1 :=
    fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have insert : ∀ query stream source dimension,
      EvalsToInTime builderMachine.step
        (buildCfg .insert query stream [] source dimension frame false)
        (some (buildCfg .start []
          (query.reverse.flatMap (fun b => [true, b]) ++ stream) [] source dimension frame))
        (query.length + 1) := by
    intro query
    induction query with
    | nil =>
      intro stream source dimension
      apply single
      builder_transition
    | cons b query ih =>
      intro stream source dimension
      have hs : builderMachine.step
          (buildCfg .insert (b :: query) stream [] source dimension frame) =
          some (buildCfg .insert query (true :: b :: stream) [] source dimension frame) := by
        cases b <;> builder_transition
      simpa [List.reverse_cons, List.flatMap_append, List.append_assoc, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (query.length + 1) _ _ _ (single _ _ hs)
          (ih (true :: b :: stream) source dimension)
  have discard : ∀ query stream source dimension,
      EvalsToInTime builderMachine.step
        (buildCfg .clearQuery query stream [] source dimension frame true)
        (some (buildCfg .start [] stream [] source dimension frame)) (query.length + 1) := by
    intro query
    induction query with
    | nil =>
      intro stream source dimension
      apply single
      builder_transition
    | cons b query ih =>
      intro stream source dimension
      have hs : builderMachine.step
          (buildCfg .clearQuery (b :: query) stream [] source dimension frame true) =
          some (buildCfg .clearQuery query stream [] source dimension frame true) := by
        cases b <;> builder_transition
      simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 (query.length + 1)
        _ _ _ (single _ _ hs) (ih stream source dimension)
  have clearIndex : ∀ index query stream source dimension found,
      EvalsToInTime builderMachine.step
        (buildCfg .clearIndex query stream index source dimension frame found)
        (some (buildCfg (if found then .clearQuery else .insert) query
          (if found then stream else false :: stream) [] source
          (if found then dimension else true :: dimension) frame found)) (index.length + 1) := by
    intro index
    induction index with
    | nil =>
      intro query stream source dimension found
      apply single
      cases found <;> builder_transition
    | cons b index ih =>
      intro query stream source dimension found
      have hs : builderMachine.step
          (buildCfg .clearIndex query stream (b :: index) source dimension frame found) =
          some (buildCfg .clearIndex query stream index source dimension frame found) := by
        cases b <;> builder_transition
      simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 (index.length + 1)
        _ _ _ (single _ _ hs) (ih query stream source dimension found)
  have extract : ∀ bits query source stream dimension,
      EvalsToInTime builderMachine.step
        (buildCfg .tag query stream [] (Conventional.nameWord bits ++ source) dimension frame)
        (some (buildCfg .ready (bits.reverse ++ query) stream [] source dimension frame))
        (2 * bits.length + 1) := by
    intro bits
    induction bits with
    | nil =>
      intro query source stream dimension
      apply single
      dsimp [Conventional.nameWord]
      builder_transition
    | cons b bits ih =>
      intro query source stream dimension
      let rest := Conventional.nameWord bits ++ source
      have hs : builderMachine.step
          (buildCfg .tag query stream [] (true :: b :: rest) dimension frame) =
          some (buildCfg .bit query stream [] (b :: rest) dimension frame) := by
        builder_transition
      have ht : builderMachine.step
          (buildCfg .bit query stream [] (b :: rest) dimension frame) =
          some (buildCfg .tag (b :: query) stream [] rest dimension frame) := by
        cases b <;> builder_transition
      have head := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (single _ _ ht)
      simpa [Conventional.nameWord, rest, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 2 (2 * bits.length + 1) _ _ _ head
          (ih (b :: query) source stream dimension)
  have lookup : ∀ query dictionary source dimension,
      EvalsToInTime builderMachine.step
        (buildCfg (.lookup .start) query (dictionaryStream dictionary) [] source dimension frame)
        (some (buildCfg .dispatch query (dictionaryStream dictionary)
          (decide (query ∈ dictionary) :: List.replicate (dictionary.idxOf query) true)
          source dimension frame))
        ((2 * query.length + 12) * dictionary.length +
          4 * (dictionaryStream dictionary).length + 3) := by
    intro query dictionary source dimension
    let lift (c : dictionaryMachine.Cfg) : builderMachine.Cfg :=
      builderCfg (some (c.l.map BuilderLabel.lookup |>.getD .dispatch)) c.var c.stk source dimension
    have update : ∀ (words : DictionaryStack → List Bool) k v,
        Function.update (builderStacks words source dimension) (.lookup k) v =
          builderStacks (Function.update words k v) source dimension := by
      intro words k v
      funext j
      cases j with
      | lookup j => simp [builderStacks, Function.update_apply]
      | source => simp [builderStacks, Function.update_apply]
      | dimension => simp [builderStacks, Function.update_apply]
    have aux : ∀ (stmt : TM2.Stmt (fun _ : DictionaryStack => Bool)
        DictionaryLabel DictionaryControl) state words,
        TM2.stepAux (liftLookup stmt) state (builderStacks words source dimension) =
          lift (TM2.stepAux stmt state words) := by
      intro stmt
      induction stmt with
      | push k f next ih =>
        intro state words
        simpa only [liftLookup, TM2.stepAux, builderStacks, update] using
          ih state (Function.update words k (f state :: words k))
      | peek k f next ih =>
        intro state words
        simpa only [liftLookup, TM2.stepAux, builderStacks] using ih (f state (words k).head?) words
      | pop k f next ih =>
        intro state words
        simpa only [liftLookup, TM2.stepAux, builderStacks, update] using
          ih (f state (words k).head?) (Function.update words k (words k).tail)
      | load f next ih => intro state words; simpa only [liftLookup, TM2.stepAux] using ih (f state) words
      | branch f yes no iy ino =>
        intro state words
        cases hf : f state <;>
          simpa only [liftLookup, TM2.stepAux, hf, cond_false, cond_true] using
            (by first | exact ino state words | exact iy state words)
      | goto f => intro state words; rfl
      | halt => intro state words; rfl
    have one : ∀ c d, dictionaryMachine.step c = some d →
        builderMachine.step (lift c) = some (lift d) := by
      intro c d hc
      rcases c with ⟨label, state, words⟩
      cases label with
      | none => simp [FinTM2.step, TM2.step] at hc
      | some label =>
        simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
        rw [← hc]
        exact congrArg some (aux (dictionaryMachine.m label) state words)
    have noneStable : ∀ t, (flip bind dictionaryMachine.step)^[t] none = none := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
    have liftRun : ∀ t c d,
        (flip bind dictionaryMachine.step)^[t] (some c) = some d →
        (flip bind builderMachine.step)^[t] (some (lift c)) = some (lift d) := by
      intro t
      induction t with
      | zero => intro c d h; simpa using congrArg (Option.map lift) h
      | succ t ih =>
        intro c d h
        rw [Function.iterate_succ_apply] at h ⊢
        change (flip bind dictionaryMachine.step)^[t] (dictionaryMachine.step c) = some d at h
        change (flip bind builderMachine.step)^[t] (builderMachine.step (lift c)) = some (lift d)
        cases hs : dictionaryMachine.step c with
        | none => rw [hs, noneStable] at h; cases h
        | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
    let run := Classical.choice (dictionary_lookup_run query dictionary frame)
    refine { steps := run.steps, steps_le_m := run.steps_le_m, evals_in_steps := ?_ }
    exact liftRun _ _ _ run.evals_in_steps
  have lengthMono : ∀ names dictionary,
      dictionary.length ≤ (buildNames names dictionary).length := by
    intro names
    induction names with
    | nil => intro dictionary; rfl
    | cons name names ih =>
      intro dictionary
      simp only [buildNames]
      split
      · exact ih dictionary
      · exact le_trans (by simp) (ih (name :: dictionary))
  have run : ∀ names dictionary dimension,
      EvalsToInTime builderMachine.step
        (buildCfg .start [] (dictionaryStream dictionary) [] (dictionaryStream names) dimension frame)
        (some (builderCfg none ⟨⟨none, none, true⟩, none, false⟩
          (dictionaryStacks (compareStacks [] [] [] [] [] frame)
            (dictionaryStream (buildNames names dictionary)) [] []) []
          (List.replicate ((buildNames names dictionary).length - dictionary.length) true ++ dimension)))
        (buildClock names dictionary) := by
    intro names
    induction names with
    | nil =>
      intro dictionary dimension
      have hs : builderMachine.step
          (buildCfg .start [] (dictionaryStream dictionary) [] [] dimension frame) =
          some (buildCfg .finish [] (dictionaryStream dictionary) [] [] dimension frame) := by
        builder_transition
      have ht : builderMachine.step
          (buildCfg .finish [] (dictionaryStream dictionary) [] [] dimension frame) =
          some (builderCfg none ⟨⟨none, none, true⟩, none, false⟩
            (dictionaryStacks (compareStacks [] [] [] [] [] frame) (dictionaryStream dictionary) [] [])
            [] dimension) := by builder_transition
      simpa [buildNames, buildClock, dictionaryStream] using
        EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ hs) (single _ _ ht)
    | cons name names ih =>
      intro dictionary dimension
      let word := Conventional.nameWord name.reverse
      let source := dictionaryStream names
      let stream := dictionaryStream dictionary
      have ne : word ≠ [] := by simp [word, Conventional.nameWord]
      let parts := List.exists_cons_of_ne_nil ne
      let b := parts.choose
      let rest := parts.choose_spec.choose
      have hb : word = b :: rest := parts.choose_spec.choose_spec
      have hs : builderMachine.step
          (buildCfg .start [] stream [] (word ++ source) dimension frame) =
          some (buildCfg .tag [] stream [] (word ++ source) dimension frame) := by
        rw [hb]
        cases b <;> builder_transition
      have ex := extract name.reverse [] source stream dimension
      simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at ex
      have ready : builderMachine.step
          (buildCfg .ready name stream [] source dimension frame) =
          some (buildCfg (.lookup .start) name stream [] source dimension frame) := by
        builder_transition
      have cmp := lookup name dictionary source dimension
      have dispatch : builderMachine.step
          (buildCfg .dispatch name stream
            (decide (name ∈ dictionary) :: List.replicate (dictionary.idxOf name) true)
            source dimension frame) =
          some (buildCfg .clearIndex name stream (List.replicate (dictionary.idxOf name) true)
            source dimension frame (decide (name ∈ dictionary))) := by
        by_cases h : name ∈ dictionary <;> simp only [h, decide_true, decide_false] <;>
          builder_transition
      have clear := clearIndex (List.replicate (dictionary.idxOf name) true)
        name stream source dimension (decide (name ∈ dictionary))
      have r4 := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ dispatch) clear
      have r3 := EvalsToInTime.trans _ _ _ _ _ _ cmp r4
      have r2 := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ ready) r3
      have r1 := EvalsToInTime.trans _ _ _ _ _ _ ex r2
      have head := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ hs) r1
      by_cases hit : name ∈ dictionary
      · simp only [hit, decide_true, Bool.true_eq, ite_true] at head
        have tail := discard name stream source dimension
        have first := EvalsToInTime.trans _ _ _ _ _ _ head tail
        have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih dictionary dimension)
        convert all using 1 <;>
          simp [buildNames, buildClock, dictionaryStream, word, source, stream, hit,
            List.length_replicate] <;> omega
      · simp only [hit, decide_false, Bool.false_eq_true, ite_false] at head
        have tail := insert name (false :: stream) source (true :: dimension)
        have first := EvalsToInTime.trans _ _ _ _ _ _ head tail
        have encoded : name.reverse.flatMap (fun b => [true, b]) ++ false :: stream =
            dictionaryStream (name :: dictionary) := by
          simp [dictionaryStream, Conventional.nameWord, stream, List.append_assoc]
        rw [encoded] at first
        have all := EvalsToInTime.trans _ _ _ _ _ _ first (ih (name :: dictionary) (true :: dimension))
        have hm := lengthMono names (name :: dictionary)
        have hl : (buildNames names (name :: dictionary)).length - dictionary.length =
            ((buildNames names (name :: dictionary)).length - (name :: dictionary).length) + 1 := by
          simp only [List.length_cons] at hm ⊢
          omega
        have dimensionEq (k : Nat) :
            List.replicate k true ++ true :: dimension =
              List.replicate (k + 1) true ++ dimension := by
          simp [List.replicate_add, List.append_assoc]
        rw [dimensionEq] at all
        convert all using 1 <;>
          simp [buildNames, buildClock, dictionaryStream, word, source, stream, hit, hl,
            List.length_replicate] <;> omega
  have appendBuild : ∀ xs ys dictionary,
      buildNames (xs ++ ys) dictionary = buildNames ys (buildNames xs dictionary) := by
    intro xs
    induction xs with
    | nil => intro ys dictionary; rfl
    | cons x xs ih =>
      intro ys dictionary
      change buildNames (xs ++ ys) (if x ∈ dictionary then dictionary else x :: dictionary) =
        buildNames ys (buildNames xs (if x ∈ dictionary then dictionary else x :: dictionary))
      exact ih ys (if x ∈ dictionary then dictionary else x :: dictionary)
  have spec : ∀ names dictionary, dictionary.Nodup →
      buildNames names.reverse dictionary = (names ++ dictionary).dedup := by
    intro names
    induction names with
    | nil => intro dictionary hd; simpa [buildNames] using hd.dedup.symm
    | cons name names ih =>
      intro dictionary hd
      rw [List.reverse_cons, appendBuild, ih dictionary hd]
      simp [buildNames, List.dedup_cons]
  let mass (names : List Conventional.Name) : Nat := (names.map List.length).sum
  have streamSize : ∀ names,
      (dictionaryStream names).length = 2 * mass names + names.length := by
    intro names
    induction names with
    | nil => rfl
    | cons name names ih =>
      have wordSize : ∀ bits : List Bool,
          (Conventional.nameWord bits).length = 2 * bits.length + 1 := by
        intro bits
        induction bits with
        | nil => rfl
        | cons b bits ih =>
          simp only [Conventional.nameWord, List.flatMap_cons, List.cons_append,
            List.nil_append, List.length_cons] at ih ⊢
          omega
      simp only [dictionaryStream, List.flatMap_cons, List.length_append] at ih ⊢
      rw [wordSize, List.length_reverse]
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at *
      omega
  have clockBound : ∀ names dictionary,
      buildClock names dictionary ≤
        (2 * mass names + 13 * names.length) * (dictionary.length + names.length) +
        4 * ((dictionaryStream names).length + (dictionaryStream dictionary).length) * names.length +
        3 * mass names + 9 * names.length + 2 := by
    intro names
    induction names with
    | nil => intro dictionary; simp [buildClock, mass, dictionaryStream]
    | cons name names ih =>
      intro dictionary
      let next := if name ∈ dictionary then dictionary else name :: dictionary
      have nextLength : next.length ≤ dictionary.length + 1 := by
        dsimp [next]; split <;> simp
      have nextStream : (dictionaryStream next).length ≤
          (dictionaryStream dictionary).length + 2 * name.length + 1 := by
        rw [streamSize, streamSize]
        dsimp [next]; split <;> simp [mass] <;> omega
      have hi : dictionary.idxOf name ≤ dictionary.length := List.idxOf_le_length
      have hih := ih next
      have first := Nat.mul_le_mul_left (2 * mass names + 13 * names.length)
        (Nat.add_le_add_right nextLength names.length)
      have second := Nat.mul_le_mul_right names.length
        (Nat.mul_le_mul_left 4 (Nat.add_le_add_left nextStream (dictionaryStream names).length))
      have currentSize : (dictionaryStream (name :: names)).length =
          (dictionaryStream names).length + 2 * name.length + 1 := by
        rw [streamSize, streamSize]
        simp only [mass, List.map_cons, List.sum_cons, List.length_cons]
        omega
      simp only [buildClock]
      change _ + buildClock names next ≤ _
      rw [currentSize]
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at hih first ⊢
      nlinarith [Nat.zero_le (name.length * names.length),
        Nat.zero_le ((dictionaryStream names).length * names.length)]
  have hm : mass names.reverse = mass names := by simp [mass, List.map_reverse]
  have hs : (dictionaryStream names.reverse).length = (dictionaryStream names).length := by
    rw [streamSize, streamSize, hm, List.length_reverse]
  have hb := clockBound names.reverse []
  simp only [dictionaryStream, List.flatMap_nil, List.length_nil, Nat.zero_add,
    Nat.add_zero, List.length_reverse, hm] at hb
  have hn : names.length ≤ (dictionaryStream names).length := by rw [streamSize]; omega
  have hmass : mass names ≤ (dictionaryStream names).length := by rw [streamSize]; omega
  have bounded : buildClock names.reverse [] ≤ 20 * ((dictionaryStream names).length + 1) ^ 2 := by
    change buildClock names.reverse [] ≤ _
    change buildClock names.reverse [] ≤
      (2 * mass names + 13 * names.length) * names.length +
        4 * (dictionaryStream names.reverse).length * names.length +
        3 * mass names + 9 * names.length + 2 at hb
    rw [hs] at hb
    nlinarith [Nat.mul_le_mul hn hn, Nat.mul_le_mul hmass hn,
      Nat.mul_le_mul_left (dictionaryStream names).length hn]
  let execution := run names.reverse [] dimension
  have terminal : buildNames names.reverse [] = names.dedup := by simpa using spec names [] (by simp)
  have runBound := le_trans execution.steps_le_m bounded
  exact ⟨{ steps := execution.steps
           evals_in_steps := by
             simpa [terminal, dictionaryStream] using execution.evals_in_steps
           steps_le_m := runBound }⟩

end PredictiveThermodynamic.BinaryNames
