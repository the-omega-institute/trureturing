/- GID: D5/S0/Computability/DenseClauseExecution
   generality: G
   mirror-B: D5/B/S0/Computability/DenseClauseExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/DenseClauseMachine]
   utility: kind=checker; basis=consumer=D5/S0/Computability/DenseClauseConversion.dense_word_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Actual restored dictionary lookup and clean dense word execution. -/

import D5.S0.Computability.DenseClauseMachine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.BinaryNames
open Turing StateTransition

/-- Actual parser, rightmost dictionary builder, restored lookup, dense-index
writing, and reversal execution. The decoder grammar invariant is proved by
induction on the same raw word and is shared with the semantic refinement. -/
def denseExecution (w : List Bool) :
    Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
      (some (haltList denseMachine (denseConverted w))) (denseRunClock w)) ∧
    (∀ F : Conventional.Formula, Conventional.readWord w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3) := by
  have shape : ∀ (w : List Bool) (F : Conventional.Formula),
      Conventional.readWord w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3 :=
    fun w => (dense_parser_run w).2
  have operational : ∀ w : List Bool,
      Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
        (some (haltList denseMachine (denseConverted w))) (denseRunClock w)) := by
    intro w
    let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
        denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
      fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
    have parser : ∀ (w : List Bool),
      Nonempty (EvalsToInTime denseMachine.step
        (initList denseMachine w)
        (some ⟨some .parseReturn, denseLocal,
          denseParserStacks (Conventional.parseStacks w [] (Conventional.decodedOccurrences w)
            [(Conventional.readWord w).isSome] [])⟩) (4*w.length+5)) :=
      fun w => (dense_parser_run w).1
    have builder : ∀ (names : List Conventional.Name) (input : List Bool),
      Nonempty (EvalsToInTime denseMachine.step
        ⟨some (.builder .start), .inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
          denseBuilderStacks (builderStacks
            (dictionaryStacks (compareStacks [] [] [] [] [] []) [] [] [])
            (dictionaryStream names.reverse) []) input⟩
        (some ⟨some .header, denseLocal,
          denseBuilderStacks (builderStacks
            (dictionaryStacks (compareStacks [] [] [] [] [] [])
              (dictionaryStream names.dedup) [] []) []
            (List.replicate names.dedup.length true)) input⟩)
        (20 * ((dictionaryStream names).length + 1)^2)) := by
      intro names input
      let lift (c : builderMachine.Cfg) : denseMachine.Cfg :=
        ⟨some (c.l.map DenseLabel.builder |>.getD .header),
          if c.l.isSome then .inr (.inl c.var) else denseLocal,
          denseBuilderStacks c.stk input⟩
      have slot : ∀ (words : BuilderStack → List Bool) k,
          denseBuilderStacks words input (denseBuilderStack k) = words k := by
        intro words k
        cases k with
        | lookup k => cases k with
          | operand k => cases k <;> rfl
          | stream | history | index => rfl
        | source | dimension => rfl
      have update : ∀ (words : BuilderStack → List Bool) k v,
          Function.update (denseBuilderStacks words input) (denseBuilderStack k) v =
            denseBuilderStacks (Function.update words k v) input := by
        intro words k v
        funext j
        cases k with
        | lookup k =>
          cases k with
          | operand k =>
            cases k <;> cases j with
            | parser j => cases j <;>
                simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | lookup j => cases j with
              | operand j => cases j <;>
                  simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | stream => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | history => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | index => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | dimension => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | nameBackup => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | reversedOutput => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | output => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
          | stream | history | index =>
            cases j with
            | parser j => cases j <;>
                simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | lookup j => cases j with
              | operand j => cases j <;>
                  simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | stream => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | history => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
              | index => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | dimension => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | nameBackup => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | reversedOutput => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
            | output => simp [denseBuilderStacks, denseBuilderStack, denseLookupStack, Function.update_apply]
        | source | dimension =>
          cases j with
          | parser j => cases j <;> simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
          | lookup j => cases j with
            | operand j => cases j <;> simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
            | stream => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
            | history => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
            | index => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
          | dimension => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
          | nameBackup => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
          | reversedOutput => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
          | output => simp [denseBuilderStacks, denseBuilderStack, Function.update_apply]
      have aux : ∀ (stmt : TM2.Stmt (fun _ : BuilderStack => Bool)
          BuilderLabel DictionaryControl) state words,
          TM2.stepAux (denseLiftBuilder stmt) (.inr (.inl state)) (denseBuilderStacks words input) =
            lift (TM2.stepAux stmt state words) := by
        intro stmt
        induction stmt with
        | push k f next ih =>
          intro state words
          simpa only [denseLiftBuilder, TM2.stepAux, denseDictionaryState, slot, update]
            using ih state (Function.update words k (f state :: words k))
        | peek k f next ih =>
          intro state words
          have slot : denseBuilderStacks words input (denseBuilderStack k) = words k := by
            cases k with
            | lookup k => cases k with
              | operand k => cases k <;> rfl
              | stream | history | index => rfl
            | source | dimension => rfl
          simpa only [denseLiftBuilder, TM2.stepAux, denseDictionaryState, slot]
            using ih (f state (words k).head?) words
        | pop k f next ih =>
          intro state words
          have slot : denseBuilderStacks words input (denseBuilderStack k) = words k := by
            cases k with
            | lookup k => cases k with
              | operand k => cases k <;> rfl
              | stream | history | index => rfl
            | source | dimension => rfl
          simpa only [denseLiftBuilder, TM2.stepAux, denseDictionaryState, slot, update]
            using ih (f state (words k).head?) (Function.update words k (words k).tail)
        | load f next ih =>
          intro state words
          simpa only [denseLiftBuilder, TM2.stepAux, denseDictionaryState] using ih (f state) words
        | branch f yes no iy ino =>
          intro state words
          cases hf : f state <;>
            simpa only [denseLiftBuilder, TM2.stepAux, denseDictionaryState, hf, cond_false, cond_true]
              using (by first | exact ino state words | exact iy state words)
        | goto f => intro state words; rfl
        | halt => intro state words; rfl
      have one : ∀ c d, builderMachine.step c = some d →
          denseMachine.step (lift c) = some (lift d) := by
        intro c d hc
        rcases c with ⟨label,state,words⟩
        cases label with
        | none => simp [FinTM2.step, TM2.step] at hc
        | some label =>
          simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
          rw [← hc]
          exact congrArg some (aux (builderMachine.m label) state words)
      have noneStable : ∀ t, (flip bind builderMachine.step)^[t] none = none := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
      have liftRun : ∀ t c d,
          (flip bind builderMachine.step)^[t] (some c) = some d →
          (flip bind denseMachine.step)^[t] (some (lift c)) = some (lift d) := by
        intro t
        induction t with
        | zero => intro c d h; simpa using congrArg (Option.map lift) h
        | succ t ih =>
          intro c d h
          rw [Function.iterate_succ_apply] at h ⊢
          change (flip bind builderMachine.step)^[t] (builderMachine.step c) = some d at h
          change (flip bind denseMachine.step)^[t] (denseMachine.step (lift c)) = some (lift d)
          cases hs : builderMachine.step c with
          | none => rw [hs, noneStable] at h; cases h
          | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
      let run := Classical.choice (dictionary_build_run names [] [])
      refine ⟨{ steps := run.steps
                steps_le_m := run.steps_le_m
                evals_in_steps := ?_ }⟩
      simpa [lift,buildCfg,builderCfg,List.append_nil] using
        liftRun _ _ _ run.evals_in_steps
    have runBody : ∀ (formula : Conventional.Formula) (reversed : List Bool)
        (dictionary : List Conventional.Name),
      EvalsToInTime denseMachine.step
        (denseWordCfg .copy .bodyFirst (Conventional.formulaWord formula)
          [] (dictionaryStream dictionary) [] [] reversed [])
        (some (denseWordCfg .drainDictionary .bodyFirst [] [] (dictionaryStream dictionary) [] []
          ((denseBodyWord dictionary formula).reverse ++ reversed) []))
        ((formula.map (denseClauseClock dictionary)).sum+2) := by
      intro formula reversed dictionary
      let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
          denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
        fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
    
      have name : ∀ (bits input reversed : List Bool) (dictionary : List Conventional.Name),
        Nonempty (EvalsToInTime denseMachine.step
          (denseWordCfg .nameTag .nameTag (Conventional.nameWord bits ++ input)
            [] (dictionaryStream dictionary) [] [] reversed [])
          (some (denseWordCfg .copy .clauseFirst input [] (dictionaryStream dictionary) [] []
            (false :: List.replicate (dictionary.idxOf bits) true ++ reversed) []))
          ((2*bits.length+12)*dictionary.length + 4*(dictionaryStream dictionary).length+3 +
            4*bits.length + dictionary.idxOf bits + 5)) := by
        intro bits input reversed dictionary
        let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
            denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
          fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
        have extract : ∀ (bits input query stream backup reversed output : List Bool),
            EvalsToInTime denseMachine.step
              (denseWordCfg .nameTag .nameTag (Conventional.nameWord bits ++ input)
                query stream [] backup reversed output)
              (some (denseWordCfg .reverseName .nameTag input query stream []
                (bits.reverse ++ backup) reversed output)) (2*bits.length+1) := by
          intro bits
          induction bits with
          | nil =>
            intro input query stream backup reversed output
            apply single
            dsimp [Conventional.nameWord]
            dense_transition
          | cons b bits ih =>
            intro input query stream backup reversed output
            have first : denseMachine.step
                (denseWordCfg .nameTag .nameTag (Conventional.nameWord (b :: bits) ++ input)
                  query stream [] backup reversed output) =
                some (denseWordCfg .nameBit .nameBit (b :: Conventional.nameWord bits ++ input)
                  query stream [] backup reversed output) := by
              simp only [Conventional.nameWord, List.flatMap_cons, List.cons_append,
                List.nil_append, List.append_assoc]
              dense_transition
            have second : denseMachine.step
                (denseWordCfg .nameBit .nameBit (b :: Conventional.nameWord bits ++ input)
                  query stream [] backup reversed output) =
                some (denseWordCfg .nameTag .nameTag (Conventional.nameWord bits ++ input)
                  query stream [] (b :: backup) reversed output) := by
              cases b <;> dense_transition
            have two := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
            have tail := ih input query stream (b :: backup) reversed output
            convert EvalsToInTime.trans _ 2 _ _ _ _ two tail using 1 <;>
              simp [List.reverse_cons, List.append_assoc] <;> omega
        have clearQuery : ∀ (query input stream reversed output : List Bool),
            EvalsToInTime denseMachine.step
              (denseWordCfg .clearQuery .clauseFirst input query stream [] [] reversed output)
              (some (denseWordCfg .copy .clauseFirst input [] stream [] [] reversed output))
              (query.length+1) := by
          intro query
          induction query with
          | nil => intro input stream reversed output; apply single; dense_transition
          | cons b query ih =>
            intro input stream reversed output
            have first : denseMachine.step
                (denseWordCfg .clearQuery .clauseFirst input (b :: query) stream [] [] reversed output) =
                some (denseWordCfg .clearQuery .clauseFirst input query stream [] [] reversed output) := by
              cases b <;> dense_transition
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih input stream reversed output)
        have emitIndex : ∀ (i : Nat) (input query stream reversed output : List Bool),
            EvalsToInTime denseMachine.step
              (denseWordCfg .emitIndex .clauseFirst input query stream (List.replicate i true)
                [] reversed output)
              (some (denseWordCfg .clearQuery .clauseFirst input query stream [] []
                (false :: List.replicate i true ++ reversed) output)) (i+1) := by
          intro i
          induction i with
          | zero => intro input query stream reversed output; apply single; dense_transition
          | succ i ih =>
            intro input query stream reversed output
            have first : denseMachine.step
                (denseWordCfg .emitIndex .clauseFirst input query stream (List.replicate (i+1) true)
                  [] reversed output) =
                some (denseWordCfg .emitIndex .clauseFirst input query stream (List.replicate i true)
                  [] (true :: reversed) output) := by
              simp only [List.replicate_succ]
              dense_transition
            convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
              (ih input query stream (true :: reversed) output) using 1 <;>
                simp [List.replicate_add, List.append_assoc] <;> omega
        have reverseName : ∀ (backup input query stream reversed output : List Bool),
            EvalsToInTime denseMachine.step
              (denseWordCfg .reverseName .nameTag input query stream [] backup reversed output)
              (some ⟨some (.lookup .start), .inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
                denseWordStacks input (backup.reverse ++ query) stream [] [] reversed output⟩)
              (backup.length+1) := by
          intro backup
          induction backup with
          | nil => intro input query stream reversed output; apply single; dense_transition
          | cons b backup ih =>
            intro input query stream reversed output
            have first : denseMachine.step
                (denseWordCfg .reverseName .nameTag input query stream [] (b::backup) reversed output) =
                some (denseWordCfg .reverseName .nameTag input (b::query) stream [] backup reversed output) := by
              cases b <;> dense_transition
            simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
              EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
                (ih input (b::query) stream reversed output)
        have lookup : ∀ (query : List Bool) (dictionary : List Conventional.Name)
            (input backup reversed output : List Bool),
          Nonempty (EvalsToInTime denseMachine.step
            ⟨some (.lookup .start), .inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
              denseDictionaryStacks
                (dictionaryStacks (compareStacks query [] [] [] [] [])
                  (dictionaryStream dictionary) [] []) input backup reversed output⟩
            (some ⟨some .dispatch, denseLocal .clauseFirst,
              denseDictionaryStacks
                (dictionaryStacks (compareStacks query [] [] [] [] [])
                  (dictionaryStream dictionary) []
                  (decide (query ∈ dictionary) :: List.replicate (dictionary.idxOf query) true))
                input backup reversed output⟩)
            ((2*query.length+12)*dictionary.length + 4*(dictionaryStream dictionary).length+3)) := by
          intro query dictionary input backup reversed output
          let lift (c : dictionaryMachine.Cfg) : denseMachine.Cfg :=
            ⟨some (c.l.map DenseLabel.lookup |>.getD .dispatch),
              if c.l.isSome then .inr (.inl c.var) else denseLocal .clauseFirst,
              denseDictionaryStacks c.stk input backup reversed output⟩
          have slot : ∀ (words : DictionaryStack → List Bool) k,
              denseDictionaryStacks words input backup reversed output (denseLookupStack k) = words k := by
            intro words k
            cases k with
            | operand k => cases k <;> rfl
            | stream | history | index => rfl
          have update : ∀ (words : DictionaryStack → List Bool) k v,
              Function.update (denseDictionaryStacks words input backup reversed output) (denseLookupStack k) v =
                denseDictionaryStacks (Function.update words k v) input backup reversed output := by
            intro words k v
            funext j
            cases k with
            | operand k =>
              cases k <;> cases j with
              | parser j => cases j <;>
                  simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
              | lookup j => cases j with
                | operand j => cases j <;>
                    simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
                | stream | history | index =>
                    simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
              | dimension | nameBackup | reversedOutput | output =>
                  simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
            | stream | history | index =>
              cases j with
              | parser j => cases j <;>
                  simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
              | lookup j => cases j with
                | operand j => cases j <;>
                    simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
                | stream | history | index =>
                    simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
              | dimension | nameBackup | reversedOutput | output =>
                  simp [denseDictionaryStacks,denseLookupStack,Function.update_apply]
          have aux : ∀ (stmt : TM2.Stmt (fun _ : DictionaryStack => Bool)
              DictionaryLabel DictionaryControl) state words,
              TM2.stepAux (denseLiftLookup stmt) (.inr (.inl state))
                (denseDictionaryStacks words input backup reversed output) =
                lift (TM2.stepAux stmt state words) := by
            intro stmt
            induction stmt with
            | push k f next ih =>
              intro state words
              simpa only [denseLiftLookup, TM2.stepAux, denseDictionaryState, slot, update]
                using ih state (Function.update words k (f state :: words k))
            | peek k f next ih =>
              intro state words
              simpa only [denseLiftLookup, TM2.stepAux, denseDictionaryState, slot]
                using ih (f state (words k).head?) words
            | pop k f next ih =>
              intro state words
              simpa only [denseLiftLookup, TM2.stepAux, denseDictionaryState, slot, update]
                using ih (f state (words k).head?) (Function.update words k (words k).tail)
            | load f next ih =>
              intro state words
              simpa only [denseLiftLookup, TM2.stepAux, denseDictionaryState] using ih (f state) words
            | branch f yes no iy ino =>
              intro state words
              cases hf : f state <;>
                simpa only [denseLiftLookup, TM2.stepAux, denseDictionaryState, hf, cond_false, cond_true]
                  using (by first | exact ino state words | exact iy state words)
            | goto f => intro state words; rfl
            | halt => intro state words; rfl
          have one : ∀ c d, dictionaryMachine.step c = some d →
              denseMachine.step (lift c) = some (lift d) := by
            intro c d hc
            rcases c with ⟨label,state,words⟩
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
              (flip bind denseMachine.step)^[t] (some (lift c)) = some (lift d) := by
            intro t
            induction t with
            | zero => intro c d h; simpa using congrArg (Option.map lift) h
            | succ t ih =>
              intro c d h
              rw [Function.iterate_succ_apply] at h ⊢
              change (flip bind dictionaryMachine.step)^[t] (dictionaryMachine.step c) = some d at h
              change (flip bind denseMachine.step)^[t] (denseMachine.step (lift c)) = some (lift d)
              cases hs : dictionaryMachine.step c with
              | none => rw [hs, noneStable] at h; cases h
              | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
          let run := Classical.choice (dictionary_lookup_run query dictionary [])
          refine ⟨{ steps := run.steps
                    steps_le_m := run.steps_le_m
                    evals_in_steps := ?_ }⟩
          exact liftRun _ _ _ run.evals_in_steps
        have lifted := Classical.choice (lookup bits dictionary input [] reversed [])
        have stack : ∀ query index,
            denseDictionaryStacks
              (dictionaryStacks (compareStacks query [] [] [] [] []) (dictionaryStream dictionary) [] index)
              input [] reversed [] = denseWordStacks input query (dictionaryStream dictionary)
                index [] reversed [] := by
          intro query index
          funext k
          cases k with
          | parser k => cases k <;> rfl
          | lookup k => cases k with
            | operand k => cases k <;> rfl
            | stream | history | index => rfl
          | dimension | nameBackup | reversedOutput | output => rfl
        have lr : EvalsToInTime denseMachine.step
            ⟨some (.lookup .start),.inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
              denseWordStacks input bits (dictionaryStream dictionary) [] [] reversed []⟩
            (some (denseWordCfg .dispatch .clauseFirst input bits (dictionaryStream dictionary)
              (decide (bits ∈ dictionary) :: List.replicate (dictionary.idxOf bits) true) [] reversed []))
            ((2*bits.length+12)*dictionary.length+4*(dictionaryStream dictionary).length+3) := by
          refine { steps := lifted.steps
                   steps_le_m := lifted.steps_le_m
                   evals_in_steps := ?_ }
          simpa only [stack,denseWordCfg] using lifted.evals_in_steps
        have dispatch : denseMachine.step
            (denseWordCfg .dispatch .clauseFirst input bits (dictionaryStream dictionary)
              (decide (bits ∈ dictionary) :: List.replicate (dictionary.idxOf bits) true) [] reversed []) =
            some (denseWordCfg .emitIndex .clauseFirst input bits (dictionaryStream dictionary)
              (List.replicate (dictionary.idxOf bits) true) [] reversed []) := by
          dense_transition
        have ex := extract bits input [] (dictionaryStream dictionary) [] reversed []
        simp only [List.append_nil] at ex
        have rev := reverseName bits.reverse input [] (dictionaryStream dictionary) reversed []
        simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at rev
        have first := EvalsToInTime.trans _ _ _ _ _ _ ex rev
        have found := EvalsToInTime.trans _ _ _ _ _ _ first lr
        have ready := EvalsToInTime.trans _ _ 1 _ _ _ found (single _ _ dispatch)
        have emitted := emitIndex (dictionary.idxOf bits) input bits (dictionaryStream dictionary) reversed []
        have printed := EvalsToInTime.trans _ _ _ _ _ _ ready emitted
        have clear := clearQuery bits input (dictionaryStream dictionary)
          (false :: List.replicate (dictionary.idxOf bits) true ++ reversed) []
        have complete := EvalsToInTime.trans _ _ _ _ _ _ printed clear
        refine ⟨{ steps := complete.steps
                  evals_in_steps := complete.evals_in_steps
                  steps_le_m := ?_ }⟩
        have bound := complete.steps_le_m
        omega
      have literal : ∀ (literal : Conventional.Name × Bool) (input reversed : List Bool)
          (dictionary : List Conventional.Name),
          EvalsToInTime denseMachine.step
            (denseWordCfg .copy .clauseFirst (Conventional.literalWord literal ++ input)
              [] (dictionaryStream dictionary) [] [] reversed [])
            (some (denseWordCfg .copy .clauseFirst input [] (dictionaryStream dictionary) [] []
              ((denseLiteralWord dictionary literal).reverse ++ reversed) []))
            (denseLiteralClock dictionary literal) := by
        rintro ⟨bits,polarity⟩ input reversed dictionary
        let rest := Conventional.nameWord bits ++ input
        have first : denseMachine.step
            (denseWordCfg .copy .clauseFirst (true::true::polarity::rest)
              [] (dictionaryStream dictionary) [] [] reversed []) =
            some (denseWordCfg .copy .clauseSecond (true::polarity::rest)
              [] (dictionaryStream dictionary) [] [] (true::reversed) []) := by dense_transition
        have second : denseMachine.step
            (denseWordCfg .copy .clauseSecond (true::polarity::rest)
              [] (dictionaryStream dictionary) [] [] (true::reversed) []) =
            some (denseWordCfg .copy .polarity (polarity::rest)
              [] (dictionaryStream dictionary) [] [] (true::true::reversed) []) := by dense_transition
        have third : denseMachine.step
            (denseWordCfg .copy .polarity (polarity::rest)
              [] (dictionaryStream dictionary) [] [] (true::true::reversed) []) =
            some (denseWordCfg .nameTag .nameTag rest
              [] (dictionaryStream dictionary) [] [] (polarity::true::true::reversed) []) := by
          cases polarity <;> dense_transition
        have tags := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        have leadingRun := EvalsToInTime.trans _ 2 1 _ _ _ tags (single _ _ third)
        have index := Classical.choice (name bits input (polarity::true::true::reversed) dictionary)
        have complete := EvalsToInTime.trans _ 3 _ _ _ _ leadingRun index
        refine { steps := complete.steps
                 evals_in_steps := ?_
                 steps_le_m := ?_ }
        · simpa [Conventional.literalWord,rest,denseLiteralWord,List.reverse_append,
            List.reverse_replicate,List.append_assoc] using complete.evals_in_steps
        · have bound := complete.steps_le_m
          dsimp [denseLiteralClock]
          omega
      have literals : ∀ (clause : Std.Sat.CNF.Clause Conventional.Name)
          (input reversed : List Bool) (dictionary : List Conventional.Name),
          EvalsToInTime denseMachine.step
            (denseWordCfg .copy .clauseFirst
              (clause.flatMap Conventional.literalWord ++ [true,false] ++ input)
              [] (dictionaryStream dictionary) [] [] reversed [])
            (some (denseWordCfg .copy .bodyFirst input [] (dictionaryStream dictionary) [] []
              ((clause.flatMap (denseLiteralWord dictionary) ++ [true,false]).reverse ++ reversed) []))
            ((clause.map (denseLiteralClock dictionary)).sum+2) := by
        intro clause
        induction clause with
        | nil =>
          intro input reversed dictionary
          have first : denseMachine.step
              (denseWordCfg .copy .clauseFirst (true::false::input)
                [] (dictionaryStream dictionary) [] [] reversed []) =
              some (denseWordCfg .copy .clauseSecond (false::input)
                [] (dictionaryStream dictionary) [] [] (true::reversed) []) := by dense_transition
          have second : denseMachine.step
              (denseWordCfg .copy .clauseSecond (false::input)
                [] (dictionaryStream dictionary) [] [] (true::reversed) []) =
              some (denseWordCfg .copy .bodyFirst input
                [] (dictionaryStream dictionary) [] [] (false::true::reversed) []) := by dense_transition
          simpa using EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        | cons l clause ih =>
          intro input reversed dictionary
          have head := literal l (clause.flatMap Conventional.literalWord ++ [true,false] ++ input)
            reversed dictionary
          have tail := ih input ((denseLiteralWord dictionary l).reverse ++ reversed) dictionary
          simpa [List.flatMap_cons,List.map_cons,List.sum_cons,List.reverse_append,
            List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ head tail
      have clause : ∀ (clause : Std.Sat.CNF.Clause Conventional.Name)
          (input reversed : List Bool) (dictionary : List Conventional.Name),
          EvalsToInTime denseMachine.step
            (denseWordCfg .copy .bodyFirst (Conventional.clauseWord clause ++ input)
              [] (dictionaryStream dictionary) [] [] reversed [])
            (some (denseWordCfg .copy .bodyFirst input [] (dictionaryStream dictionary) [] []
              ((denseClauseWord dictionary clause).reverse ++ reversed) []))
            (denseClauseClock dictionary clause) := by
        intro clause input reversed dictionary
        let rest := clause.flatMap Conventional.literalWord ++ [true,false] ++ input
        have first : denseMachine.step
            (denseWordCfg .copy .bodyFirst (false::true::rest)
              [] (dictionaryStream dictionary) [] [] reversed []) =
            some (denseWordCfg .copy .bodySecond (true::rest)
              [] (dictionaryStream dictionary) [] [] (false::reversed) []) := by dense_transition
        have second : denseMachine.step
            (denseWordCfg .copy .bodySecond (true::rest)
              [] (dictionaryStream dictionary) [] [] (false::reversed) []) =
            some (denseWordCfg .copy .clauseFirst rest
              [] (dictionaryStream dictionary) [] [] (true::false::reversed) []) := by dense_transition
        have leadingRun := EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        have content := literals clause input (true::false::reversed) dictionary
        have complete := EvalsToInTime.trans _ 2 _ _ _ _ leadingRun content
        refine { steps := complete.steps
                 evals_in_steps := ?_
                 steps_le_m := ?_ }
        · simpa [Conventional.clauseWord,rest,denseClauseWord,List.reverse_append,
            List.append_assoc] using complete.evals_in_steps
        · have bound := complete.steps_le_m
          dsimp [denseClauseClock]
          omega
      have body : ∀ (formula : Conventional.Formula) (reversed : List Bool)
          (dictionary : List Conventional.Name),
          EvalsToInTime denseMachine.step
            (denseWordCfg .copy .bodyFirst (Conventional.formulaWord formula)
              [] (dictionaryStream dictionary) [] [] reversed [])
            (some (denseWordCfg .drainDictionary .bodyFirst [] [] (dictionaryStream dictionary) [] []
              ((denseBodyWord dictionary formula).reverse ++ reversed) []))
            ((formula.map (denseClauseClock dictionary)).sum+2) := by
        intro formula
        induction formula with
        | nil =>
          intro reversed dictionary
          have first : denseMachine.step
              (denseWordCfg .copy .bodyFirst [false,false]
                [] (dictionaryStream dictionary) [] [] reversed []) =
              some (denseWordCfg .copy .bodySecond [false]
                [] (dictionaryStream dictionary) [] [] (false::reversed) []) := by dense_transition
          have second : denseMachine.step
              (denseWordCfg .copy .bodySecond [false]
                [] (dictionaryStream dictionary) [] [] (false::reversed) []) =
              some (denseWordCfg .drainDictionary .bodyFirst []
                [] (dictionaryStream dictionary) [] [] (false::false::reversed) []) := by dense_transition
          simpa [Conventional.formulaWord,denseBodyWord] using
            EvalsToInTime.trans _ 1 1 _ _ _ (single _ _ first) (single _ _ second)
        | cons c formula ih =>
          intro reversed dictionary
          have head := clause c (Conventional.formulaWord formula) reversed dictionary
          have tail := ih ((denseClauseWord dictionary c).reverse ++ reversed) dictionary
          simpa [Conventional.formulaWord,denseBodyWord,List.flatMap_cons,List.map_cons,
            List.sum_cons,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
              EvalsToInTime.trans _ _ _ _ _ _ head tail
    
      exact body formula reversed dictionary
    have finish : ∀ (reversed output : List Bool),
        EvalsToInTime denseMachine.step
          (denseWordCfg .returnOutput .bodyFirst [] [] [] [] [] reversed output)
          (some (haltList denseMachine (reversed.reverse ++ output))) (reversed.length+1) := by
      let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
          denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
        fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
      intro reversed
      induction reversed with
      | nil =>
        intro output
        apply single
        dsimp [FinTM2.step, TM2.step, denseMachine, haltList, TM2.stepAux, denseWordCfg, denseWordStacks,
          denseLocal, denseWordState]
        congr 2
        funext k
        cases k with
        | parser k => cases k <;> simp [Function.update_apply, denseWordStacks]
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply, denseWordStacks]
          | stream | history | index => simp [Function.update_apply, denseWordStacks]
        | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply, denseWordStacks]
      | cons b reversed ih =>
        intro output
        have first : denseMachine.step
            (denseWordCfg .returnOutput .bodyFirst [] [] [] [] [] (b::reversed) output) =
            some (denseWordCfg .returnOutput .bodyFirst [] [] [] [] [] reversed (b::output)) := by
          cases b <;> dense_transition
        simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
          EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih (b::output))
    have drain : ∀ (stream reversed output : List Bool),
        EvalsToInTime denseMachine.step
          (denseWordCfg .drainDictionary .bodyFirst [] [] stream [] [] reversed output)
          (some (denseWordCfg .returnOutput .bodyFirst [] [] [] [] [] reversed output))
          (stream.length+1) := by
      let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
          denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
        fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
      intro stream
      induction stream with
      | nil => intro reversed output; apply single; dense_transition
      | cons b stream ih =>
        intro reversed output
        have first : denseMachine.step
            (denseWordCfg .drainDictionary .bodyFirst [] [] (b::stream) [] [] reversed output) =
            some (denseWordCfg .drainDictionary .bodyFirst [] [] stream [] [] reversed output) := by
          cases b <;> dense_transition
        simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) (ih reversed output)
    have bad : ∀ (input : List Bool),
        EvalsToInTime denseMachine.step
          (denseWordCfg .badDrain .bodyFirst input [] [] [] [] [] [])
          (some (denseWordCfg .returnOutput .bodyFirst [] [] [] [] []
            [false,false,false,true,true,false,false] [])) (input.length+1) := by
      let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
          denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
        fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
      intro input
      induction input with
      | nil => apply single; dense_transition
      | cons b input ih =>
        have first : denseMachine.step
            (denseWordCfg .badDrain .bodyFirst (b::input) [] [] [] [] [] []) =
            some (denseWordCfg .badDrain .bodyFirst input [] [] [] [] [] []) := by
          cases b <;> dense_transition
        simpa [Nat.add_assoc] using EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) ih
    have header : ∀ (n : Nat) (input stream reversed output : List Bool),
        EvalsToInTime denseMachine.step
          (denseHeaderCfg input stream (List.replicate n true) reversed output)
          (some (denseWordCfg .copy .bodyFirst input [] stream [] []
            (false :: List.replicate n true ++ reversed) output)) (n+1) := by
      let single : ∀ (x : denseMachine.Cfg) (y : Option denseMachine.Cfg),
          denseMachine.step x = y → EvalsToInTime denseMachine.step x y 1 :=
        fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
      intro n
      induction n with
      | zero => intro input stream reversed output; apply single; dense_header_transition
      | succ n ih =>
        intro input stream reversed output
        have first : denseMachine.step
            (denseHeaderCfg input stream (List.replicate (n+1) true) reversed output) =
            some (denseHeaderCfg input stream (List.replicate n true) (true::reversed) output) := by
          simp only [List.replicate_succ]
          dense_header_transition
        convert EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first)
          (ih input stream (true::reversed) output) using 1 <;>
            simp [List.replicate_add, List.append_assoc] <;> omega
    let parsed := Classical.choice (parser w)
    cases read : Conventional.readWord w with
    | none =>
      have dispatch : denseMachine.step
          ⟨some .parseReturn,denseLocal,
            denseParserStacks (Conventional.parseStacks w []
              (Conventional.decodedOccurrences w) [(Conventional.readWord w).isSome] [])⟩ =
          some (denseWordCfg .badDrain .bodyFirst w [] [] [] [] [] []) := by
        apply congrArg some
        dsimp [FinTM2.step,TM2.step,denseMachine,TM2.stepAux,denseLocal,denseWordState,denseParserStacks,
          Conventional.parseStacks,Conventional.decodedOccurrences,read,
          denseWordCfg,denseWordStacks]
        simp only [read,Option.isSome,cond_false,cond_true]
        congr 1
        funext k
        cases k with
        | parser k => cases k <;> simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks]
          | stream | history | index => simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks]
        | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
      have routed := EvalsToInTime.trans _ _ 1 _ _ _ parsed (single _ _ dispatch)
      have cleaned := EvalsToInTime.trans _ _ _ _ _ _ routed (bad w)
      have done := EvalsToInTime.trans _ _ _ _ _ _ cleaned
        (finish [false,false,false,true,true,false,false] [])
      refine ⟨{ steps := done.steps
                evals_in_steps := ?_
                steps_le_m := ?_ }⟩
      · simpa [denseConverted,read] using done.evals_in_steps
      · have bound := done.steps_le_m
        simp [denseRunClock,read] at *
        omega
    | some F =>
      let d := Conventional.dictionary F
      have acceptedShape := (shape w F read).1
      have dispatch : denseMachine.step
          ⟨some .parseReturn,denseLocal,
            denseParserStacks (Conventional.parseStacks w []
              (Conventional.decodedOccurrences w) [(Conventional.readWord w).isSome] [])⟩ =
          some ⟨some (.builder .start), .inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
            denseBuilderStacks (builderStacks
              (dictionaryStacks (compareStacks [] [] [] [] [] []) [] [] [])
              (dictionaryStream (Conventional.occurrences F).reverse) []) w⟩ := by
        apply congrArg some
        dsimp [FinTM2.step,TM2.step,denseMachine,TM2.stepAux,denseLocal,denseWordState,denseParserStacks,
          Conventional.parseStacks,Conventional.decodedOccurrences,read,
          denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks,
          Conventional.occurrenceStream,dictionaryStream]
        simp only [read,Option.isSome,cond_false,cond_true]
        congr 1
        funext k
        cases k with
        | parser k => cases k <;> simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
        | lookup k => cases k with
          | operand k => cases k <;> simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
          | stream | history | index => simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
        | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply,denseParserStacks,Conventional.parseStacks,denseWordStacks,denseBuilderStacks,builderStacks,dictionaryStacks,compareStacks]
      have built := Classical.choice (builder (Conventional.occurrences F) w)
      have ready : EvalsToInTime denseMachine.step
          ⟨some (.builder .start), .inr (.inl ⟨⟨none,none,true⟩,none,false⟩),
            denseBuilderStacks (builderStacks
              (dictionaryStacks (compareStacks [] [] [] [] [] []) [] [] [])
              (dictionaryStream (Conventional.occurrences F).reverse) []) w⟩
          (some (denseHeaderCfg w (dictionaryStream d)
            (List.replicate d.length true) [] []))
          (20*((dictionaryStream (Conventional.occurrences F)).length+1)^2) := by
        convert built using 1
        apply congrArg some
        dsimp only [denseHeaderCfg]
        congr 1
        funext k
        cases k with
        | parser k => cases k <;> simp [denseHeaderCfg,denseWordStacks,denseBuilderStacks,
            builderStacks,dictionaryStacks,compareStacks,Function.update_apply,d,Conventional.dictionary]
        | lookup k => cases k with
          | operand k => cases k <;> simp [denseHeaderCfg,denseWordStacks,denseBuilderStacks,
              builderStacks,dictionaryStacks,compareStacks,Function.update_apply,d,Conventional.dictionary]
          | stream | history | index => simp [denseHeaderCfg,denseWordStacks,denseBuilderStacks,
              builderStacks,dictionaryStacks,compareStacks,Function.update_apply,d,Conventional.dictionary]
        | dimension | nameBackup | reversedOutput | output =>
            simp [denseHeaderCfg,denseWordStacks,denseBuilderStacks,
              builderStacks,dictionaryStacks,compareStacks,Function.update_apply,d,Conventional.dictionary]
      have routed := EvalsToInTime.trans _ _ 1 _ _ _ parsed (single _ _ dispatch)
      have prepared := EvalsToInTime.trans _ _ _ _ _ _ routed ready
      have printedHeader := EvalsToInTime.trans _ _ _ _ _ _ prepared
        (header d.length w (dictionaryStream d) [] [])
      have content := runBody F (false :: List.replicate d.length true) d
      simp only [List.append_nil] at printedHeader
      rw [acceptedShape] at printedHeader
      have printed := EvalsToInTime.trans _ _ _ _ _ _ printedHeader content
      have cleared := EvalsToInTime.trans _ _ _ _ _ _ printed
        (drain (dictionaryStream d)
          ((denseBodyWord d F).reverse ++ false :: List.replicate d.length true) [])
      have done := EvalsToInTime.trans _ _ _ _ _ _ cleared
        (finish ((denseBodyWord d F).reverse ++ false :: List.replicate d.length true) [])
      refine ⟨{ steps := done.steps
                evals_in_steps := ?_
                steps_le_m := ?_ }⟩
      · simpa [← acceptedShape,d,denseConverted,read,denseRawWord,List.reverse_append,List.reverse_cons,
          List.reverse_replicate,List.append_assoc] using done.evals_in_steps
      · have bound := done.steps_le_m
        have outputSize : (denseRawWord d F).length =
            (denseBodyWord d F).length + d.length+1 := by simp [denseRawWord]; omega
        simp [← acceptedShape,d,denseRunClock,read,denseRawWord,List.length_append] at *
        omega
  exact ⟨operational w,shape w⟩

end PredictiveThermodynamic.BinaryNames
