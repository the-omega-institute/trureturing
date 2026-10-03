/- GID: D5/S0/Computability/DenseQueryCompiler
   generality: G
   mirror-B: D5/B/S0/Computability/DenseQueryCompiler
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol.conventional_one_query_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: A fixed finite compiler pays for dense conversion and physical query construction. -/

import D5.S0.Computability.DenseClauseConversion
import D5.S0.Computability.ClausePreprocessorRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.BinaryNames
open Turing StateTransition

inductive QueryCompilerStack
  | dense (k : DenseStack) | pre (k : PreStack)
  deriving DecidableEq, Fintype, Inhabited
inductive QueryCompilerLabel
  | dense (l : DenseLabel) | collect | restore | pre (l : PreLabel)
  deriving DecidableEq, Fintype, Inhabited
abbrev QueryCompilerControl := Sum DenseControl (Sum PreControl (Option Bool))
def compilerDenseState : QueryCompilerControl → DenseControl
  | .inl v => v
  | _ => denseMachine.initialState

def compilerPreState : QueryCompilerControl → PreControl
  | .inr (.inl v) => v
  | _ => preMachine.initialState

def compilerHeld : QueryCompilerControl → Option Bool
  | .inr (.inr b) => b
  | _ => none

def compilerRead (_ : QueryCompilerControl) (b : Option Bool) : QueryCompilerControl := .inr (.inr b)

def compileDense : TM2.Stmt (fun _ : DenseStack => Bool) DenseLabel DenseControl →
    TM2.Stmt (fun _ : QueryCompilerStack => Bool) QueryCompilerLabel QueryCompilerControl
  | .push k f next => .push (.dense k) (fun s => f (compilerDenseState s)) (compileDense next)
  | .peek k f next => .peek (.dense k)
      (fun s b => .inl (f (compilerDenseState s) b)) (compileDense next)
  | .pop k f next => .pop (.dense k)
      (fun s b => .inl (f (compilerDenseState s) b)) (compileDense next)
  | .load f next => .load (fun s => .inl (f (compilerDenseState s))) (compileDense next)
  | .branch f yes no => .branch (fun s => f (compilerDenseState s)) (compileDense yes) (compileDense no)
  | .goto f => .goto (fun s => .dense (f (compilerDenseState s)))
  | .halt => .load (fun _ => .inr (.inr none)) <| .goto fun _ => .collect

def compilePre : TM2.Stmt (fun _ : PreStack => Bool) PreLabel PreControl →
    TM2.Stmt (fun _ : QueryCompilerStack => Bool) QueryCompilerLabel QueryCompilerControl
  | .push k f next => .push (.pre k) (fun s => f (compilerPreState s)) (compilePre next)
  | .peek k f next => .peek (.pre k)
      (fun s b => .inr (.inl (f (compilerPreState s) b))) (compilePre next)
  | .pop k f next => .pop (.pre k)
      (fun s b => .inr (.inl (f (compilerPreState s) b))) (compilePre next)
  | .load f next => .load (fun s => .inr (.inl (f (compilerPreState s)))) (compilePre next)
  | .branch f yes no => .branch (fun s => f (compilerPreState s)) (compilePre yes) (compilePre no)
  | .goto f => .goto (fun s => .pre (f (compilerPreState s)))
  | .halt => .load (fun _ => .inl denseMachine.initialState) .halt

/-- All cross-phase input materialization is ordinary paid stack movement. -/
def queryCompiler : FinTM2 where
  K := QueryCompilerStack
  k₀ := .dense (.parser .input)
  k₁ := .pre .output
  Γ _ := Bool
  Λ := QueryCompilerLabel
  main := .dense denseMachine.main
  σ := QueryCompilerControl
  initialState := .inl denseMachine.initialState
  m
    | .dense label => compileDense (denseMachine.m label)
    | .pre label => compilePre (preMachine.m label)
    | .collect => .pop (.dense .output) compilerRead <|
        .branch (fun s => (compilerHeld s).isNone)
          (.load (fun _ => .inr (.inr none)) <| .goto fun _ => .restore)
          (.push (.dense (.parser .input)) (fun s => (compilerHeld s).getD false) <|
            .load (fun _ => .inr (.inr none)) <| .goto fun _ => .collect)
    | .restore => .pop (.dense (.parser .input)) compilerRead <|
        .branch (fun s => (compilerHeld s).isNone)
          (.load (fun _ => .inr (.inl preMachine.initialState)) <| .goto fun _ => .pre preMachine.main)
          (.push (.pre .input) (fun s => (compilerHeld s).getD false) <|
            .load (fun _ => .inr (.inr none)) <| .goto fun _ => .restore)

def compilerDenseWords (words : DenseStack → List Bool) : QueryCompilerStack → List Bool
  | .dense k => words k
  | .pre _ => []
def compilerPreWords (words : PreStack → List Bool) : QueryCompilerStack → List Bool
  | .dense _ => []
  | .pre k => words k

def compilerTransferWords (input saved output : List Bool) : QueryCompilerStack → List Bool
  | .dense .output => input
  | .dense (.parser .input) => saved
  | .pre .input => output
  | _ => []

def compilerTransferCfg (label : QueryCompilerLabel) (input saved output : List Bool) : queryCompiler.Cfg :=
  ⟨some label, .inr (.inr none), compilerTransferWords input saved output⟩

/-- Complete actual dense-to-physical-query prefix with paid ordinary copying. -/
theorem dense_query_run (w : List Bool) :
    Nonempty (EvalsToInTime queryCompiler.step (initList queryCompiler w)
      (some (haltList queryCompiler (preparedQuery (denseOutput w))))
      (80*(w.length+1)^2+4*(w.length^2+8*w.length+7)^2+
        22*(w.length^2+8*w.length+7)+15)) ∧
    ClauseCodec.readWord true (preparedQuery (denseOutput w)) = some (densePrepared w) ∧
    unaryCount (densePrepared w).2 = Conventional.rawCount w := by
  have execution : Nonempty (EvalsToInTime queryCompiler.step (initList queryCompiler w)
      (some (haltList queryCompiler (preparedQuery (denseOutput w))))
      (80*(w.length+1)^2+2*(denseOutput w).length+2+
        (4*(denseOutput w).length+20)*(denseOutput w).length+13)) := by
    have denseRun : ∀ (w : List Bool),
        Nonempty (EvalsToInTime queryCompiler.step
          (initList queryCompiler w)
          (some (compilerTransferCfg .collect (denseOutput w) [] [])) (80*(w.length+1)^2)) := by
      intro w
      let lift (c : denseMachine.Cfg) : queryCompiler.Cfg := ⟨some (c.l.map QueryCompilerLabel.dense |>.getD .collect),
            if c.l.isSome then .inl c.var else .inr (.inr none),compilerDenseWords c.stk⟩
      have slot : ∀ (words : DenseStack → List Bool) k,
          compilerDenseWords words (.dense k) = words k := by intro words k; rfl
      have update : ∀ (words : DenseStack → List Bool) k v,
          Function.update (compilerDenseWords words) (.dense k) v =
            compilerDenseWords (Function.update words k v) := by
        intro words k v
        funext j
        cases j with
        | dense j => simp [compilerDenseWords,Function.update_apply]
        | pre j => simp [compilerDenseWords,Function.update_apply]
      have aux : ∀ (stmt : TM2.Stmt (fun _ : DenseStack => Bool)
          DenseLabel DenseControl) state words,
          TM2.stepAux (compileDense stmt) (.inl state) (compilerDenseWords words) =
            lift (TM2.stepAux stmt state words) := by
        intro stmt
        induction stmt with
        | push k f next ih =>
          intro state words
          simpa only [compileDense, TM2.stepAux, compilerDenseWords, compilerDenseState, slot, update]
            using ih state (Function.update words k (f state :: words k))
        | peek k f next ih =>
          intro state words
          simpa only [compileDense, TM2.stepAux, compilerDenseWords, compilerDenseState, slot]
            using ih (f state (words k).head?) words
        | pop k f next ih =>
          intro state words
          simpa only [compileDense, TM2.stepAux, compilerDenseWords, compilerDenseState, slot, update]
            using ih (f state (words k).head?) (Function.update words k (words k).tail)
        | load f next ih =>
          intro state words
          simpa only [compileDense, TM2.stepAux, compilerDenseState, slot] using ih (f state) words
        | branch f yes no iy ino =>
          intro state words
          cases hf : f state <;>
            simpa only [compileDense, TM2.stepAux, compilerDenseState, hf, cond_false, cond_true]
              using (by first | exact ino state words | exact iy state words)
        | goto f => intro state words; rfl
        | halt => intro state words; rfl
      have one : ∀ c d, denseMachine.step c = some d →
          queryCompiler.step (lift c) = some (lift d) := by
        intro c d hc
        rcases c with ⟨label,state,words⟩
        cases label with
        | none => simp [FinTM2.step, TM2.step] at hc
        | some label =>
          simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
          rw [← hc]
          exact congrArg some (aux (denseMachine.m label) state words)
      have noneStable : ∀ t, (flip bind denseMachine.step)^[t] none = none := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
      have liftRun : ∀ t c d,
          (flip bind denseMachine.step)^[t] (some c) = some d →
          (flip bind queryCompiler.step)^[t] (some (lift c)) = some (lift d) := by
        intro t
        induction t with
        | zero => intro c d h; simpa using congrArg (Option.map lift) h
        | succ t ih =>
          intro c d h
          rw [Function.iterate_succ_apply] at h ⊢
          change (flip bind denseMachine.step)^[t]
            (denseMachine.step c) = some d at h
          change (flip bind queryCompiler.step)^[t] (queryCompiler.step (lift c)) = some (lift d)
          cases hs : denseMachine.step c with
          | none => rw [hs, noneStable] at h; cases h
          | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
      let run := Classical.choice (dense_word_run w).1
      have lifted := liftRun _ _ _ run.evals_in_steps
      refine ⟨{ steps := run.steps, steps_le_m := run.steps_le_m, evals_in_steps := ?_ }⟩
      have start : lift (initList denseMachine w) = initList queryCompiler w := by
        dsimp [lift,initList,queryCompiler,denseMachine,compilerDenseWords]
        congr 1
        funext k
        cases k with
        | dense k => cases k with
          | parser k => cases k <;> rfl
          | lookup k => cases k <;> rfl
          | dimension | nameBackup | reversedOutput | output => rfl
        | pre k => rfl
      have finish : lift (haltList denseMachine (denseOutput w)) =
          compilerTransferCfg .collect (denseOutput w) [] [] := by
        dsimp [lift,haltList,denseMachine,compilerDenseWords,compilerTransferCfg,compilerTransferWords]
        congr 1
        funext k
        cases k with
        | dense k => cases k with
          | parser k => cases k <;> rfl
          | lookup k => cases k <;> rfl
          | dimension | nameBackup | reversedOutput | output => rfl
        | pre k => cases k <;> rfl
      rwa [start,finish] at lifted
    have preRun : ∀ (word : List Bool),
        Nonempty (EvalsToInTime queryCompiler.step
          (⟨some (.pre preMachine.main),.inr (.inl preMachine.initialState),
            compilerPreWords (initList preMachine word).stk⟩ : queryCompiler.Cfg)
          (some (haltList queryCompiler (preparedQuery word))) ((4*word.length+20)*word.length+13)) := by
      intro word
      let lift (c : preMachine.Cfg) : queryCompiler.Cfg := ⟨c.l.map QueryCompilerLabel.pre,
            if c.l.isSome then .inr (.inl c.var) else .inl denseMachine.initialState,compilerPreWords c.stk⟩
      have slot : ∀ (words : PreStack → List Bool) k,
          compilerPreWords words (.pre k) = words k := by intro words k; rfl
      have update : ∀ (words : PreStack → List Bool) k v,
          Function.update (compilerPreWords words) (.pre k) v =
            compilerPreWords (Function.update words k v) := by
        intro words k v
        funext j
        cases j with
        | pre j => simp [compilerPreWords,Function.update_apply]
        | dense j => simp [compilerPreWords,Function.update_apply]
      have aux : ∀ (stmt : TM2.Stmt (fun _ : PreStack => Bool)
          PreLabel PreControl) state words,
          TM2.stepAux (compilePre stmt) (.inr (.inl state)) (compilerPreWords words) =
            lift (TM2.stepAux stmt state words) := by
        intro stmt
        induction stmt with
        | push k f next ih =>
          intro state words
          simpa only [compilePre, TM2.stepAux, compilerPreWords, compilerPreState, slot, update]
            using ih state (Function.update words k (f state :: words k))
        | peek k f next ih =>
          intro state words
          simpa only [compilePre, TM2.stepAux, compilerPreWords, compilerPreState, slot]
            using ih (f state (words k).head?) words
        | pop k f next ih =>
          intro state words
          simpa only [compilePre, TM2.stepAux, compilerPreWords, compilerPreState, slot, update]
            using ih (f state (words k).head?) (Function.update words k (words k).tail)
        | load f next ih =>
          intro state words
          simpa only [compilePre, TM2.stepAux, compilerPreState, slot] using ih (f state) words
        | branch f yes no iy ino =>
          intro state words
          cases hf : f state <;>
            simpa only [compilePre, TM2.stepAux, compilerPreState, hf, cond_false, cond_true]
              using (by first | exact ino state words | exact iy state words)
        | goto f => intro state words; rfl
        | halt => intro state words; rfl
      have one : ∀ c d, preMachine.step c = some d →
          queryCompiler.step (lift c) = some (lift d) := by
        intro c d hc
        rcases c with ⟨label,state,words⟩
        cases label with
        | none => simp [FinTM2.step, TM2.step] at hc
        | some label =>
          simp only [FinTM2.step, TM2.step, Option.some.injEq] at hc
          rw [← hc]
          exact congrArg some (aux (preMachine.m label) state words)
      have noneStable : ∀ t, (flip bind preMachine.step)^[t] none = none := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih => simpa [Function.iterate_succ_apply, flip] using ih
      have liftRun : ∀ t c d,
          (flip bind preMachine.step)^[t] (some c) = some d →
          (flip bind queryCompiler.step)^[t] (some (lift c)) = some (lift d) := by
        intro t
        induction t with
        | zero => intro c d h; simpa using congrArg (Option.map lift) h
        | succ t ih =>
          intro c d h
          rw [Function.iterate_succ_apply] at h ⊢
          change (flip bind preMachine.step)^[t]
            (preMachine.step c) = some d at h
          change (flip bind queryCompiler.step)^[t] (queryCompiler.step (lift c)) = some (lift d)
          cases hs : preMachine.step c with
          | none => rw [hs, noneStable] at h; cases h
          | some next => rw [one c next hs]; exact ih next d (by rwa [hs] at h)
      let run := Classical.choice (pre_word_run word).1
      have lifted := liftRun _ _ _ run.evals_in_steps
      refine ⟨{ steps := run.steps, steps_le_m := run.steps_le_m, evals_in_steps := ?_ }⟩
      have finish : lift (haltList preMachine (preparedQuery word)) =
          haltList queryCompiler (preparedQuery word) := by
        dsimp [lift,haltList,preMachine,queryCompiler,compilerPreWords]
        congr 1
        funext k
        cases k with
        | dense k => rfl
        | pre k => cases k <;> rfl
      rw [finish] at lifted
      exact lifted
    let single : ∀ (x : queryCompiler.Cfg) (y : Option queryCompiler.Cfg),
        queryCompiler.step x = y → EvalsToInTime queryCompiler.step x y 1 :=
      fun x y h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
    have move : ∀ (input saved output : List Bool),
        EvalsToInTime queryCompiler.step (compilerTransferCfg .collect input saved output)
          (some (compilerTransferCfg .restore [] (input.reverse++saved) output)) (input.length+1) := by
      intro input
      induction input with
      | nil =>
        intro saved output
        apply single
        apply congrArg some
        dsimp [queryCompiler,TM2.stepAux,compilerTransferCfg,compilerTransferWords,compilerRead,compilerHeld]
        congr 1
        funext k
        cases k with
        | pre k => cases k <;> simp [Function.update_apply,compilerTransferWords]
        | dense k => cases k with
          | parser k => cases k <;> simp [Function.update_apply,compilerTransferWords]
          | lookup k => cases k <;> simp [Function.update_apply,compilerTransferWords]
          | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply,compilerTransferWords]
      | cons b input ih =>
        intro saved output
        have step : queryCompiler.step (compilerTransferCfg .collect (b::input) saved output) =
            some (compilerTransferCfg .collect input (b::saved) output) := by
          apply congrArg some
          dsimp [queryCompiler,TM2.stepAux,compilerTransferCfg,compilerTransferWords,compilerRead,compilerHeld]
          congr 1
          funext k
          cases k with
          | pre k => cases k <;> simp [Function.update_apply,compilerTransferWords]
          | dense k => cases k with
            | parser k => cases k <;> simp [Function.update_apply,compilerTransferWords]
            | lookup k => cases k <;> simp [Function.update_apply,compilerTransferWords]
            | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply,compilerTransferWords]
        have first := single _ _ step
        have done := EvalsToInTime.trans _ _ _ _ _ _ first (ih (b::saved) output)
        simpa [List.reverse_cons,List.append_assoc] using done
    have restore : ∀ (saved output : List Bool),
        EvalsToInTime queryCompiler.step (compilerTransferCfg .restore [] saved output)
          (some (⟨some (.pre preMachine.main),.inr (.inl preMachine.initialState),
            compilerPreWords (initList preMachine (saved.reverse++output)).stk⟩ : queryCompiler.Cfg))
          (saved.length+1) := by
      intro saved
      induction saved with
      | nil =>
        intro output
        apply single
        apply congrArg some
        dsimp [queryCompiler,TM2.stepAux,compilerTransferCfg,compilerTransferWords,compilerRead,compilerHeld,
          compilerPreWords,initList,preMachine]
        congr 1
        funext k
        cases k with
        | dense k => cases k with
          | parser k => cases k <;> rfl
          | lookup k => cases k <;> rfl
          | dimension | nameBackup | reversedOutput | output => rfl
        | pre k => cases k <;> rfl
      | cons b saved ih =>
        intro output
        have step : queryCompiler.step (compilerTransferCfg .restore [] (b::saved) output) =
            some (compilerTransferCfg .restore [] saved (b::output)) := by
          apply congrArg some
          dsimp [queryCompiler,TM2.stepAux,compilerTransferCfg,compilerTransferWords,compilerRead,compilerHeld]
          congr 1
          funext k
          cases k with
          | pre k => cases k <;> simp [Function.update_apply,compilerTransferWords]
          | dense k => cases k with
            | parser k => cases k <;> simp [Function.update_apply,compilerTransferWords]
            | lookup k => cases k <;> simp [Function.update_apply,compilerTransferWords]
            | dimension | nameBackup | reversedOutput | output => simp [Function.update_apply,compilerTransferWords]
        have first := single _ _ step
        have done := EvalsToInTime.trans _ _ _ _ _ _ first (ih (b::output))
        simpa [List.reverse_cons,List.append_assoc] using done
    let input := denseOutput w
    let a := Classical.choice (denseRun w)
    have b := move input [] []
    simp only [List.append_nil] at b
    let c := restore input.reverse []
    have c' : EvalsToInTime queryCompiler.step
        (compilerTransferCfg .restore [] input.reverse [])
        (some (⟨some (.pre preMachine.main),.inr (.inl preMachine.initialState),
          compilerPreWords (initList preMachine input).stk⟩ : queryCompiler.Cfg)) (input.length+1) := by
      simpa using c
    let d := Classical.choice (preRun input)
    have ab := EvalsToInTime.trans _ _ _ _ _ _ a b
    have abc := EvalsToInTime.trans _ _ _ _ _ _ ab c'
    have done := EvalsToInTime.trans _ _ _ _ _ _ abc d
    refine ⟨{ steps := done.steps, evals_in_steps := done.evals_in_steps, steps_le_m := ?_ }⟩
    have bound := done.steps_le_m
    dsimp only [input] at bound
    omega
  obtain ⟨_,growth,decoded,_,count⟩ := dense_word_run w
  have prepared : preparedFormula (denseOutput w) = densePrepared w := by
    unfold preparedFormula
    rw [decoded]
    rfl
  have query := (pre_word_run (denseOutput w)).2.1
  rw [prepared] at query
  obtain ⟨run⟩ := execution
  have square := Nat.pow_le_pow_left growth 2
  refine ⟨⟨{
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := ?_
  }⟩,query,count⟩
  nlinarith [run.steps_le_m]
end PredictiveThermodynamic.BinaryNames
