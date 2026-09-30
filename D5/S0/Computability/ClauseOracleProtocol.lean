/- GID: D5/S0/Computability/ClauseOracleProtocol
   generality: G
   mirror-B: D5/B/S0/Computability/ClauseOracleProtocol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual machine traces compose through one ask and paid response writes. -/

/- Utility: the new content is a symbolic execution law for every raw word and
   a phase invariant for every complete run. Its proof constructs unbounded
   stream-writing and reversal traces and charges actual machine transitions.
   It supplies no finite certificate checker, bounded enumeration, certified
   finite instance or conditional numerical estimate. The other utility fields
   are not applicable for kind none. -/

import D5.S0.Computability.ClausePreprocessorRefinement
import D5.S0.Computability.PhysicalRationalResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic
open Turing StateTransition ClauseCodec Physical Lax51Proofs.RamToTM

inductive MaterializeLabel
  | emit | reverse
  deriving DecidableEq, Fintype, Inhabited

/-- The response writer has fixed finite alphabets and control. The oracle's
read-only stream is external to all of these ordinary writable stacks. -/
def materializeMachine : FinTM2 where
  K := PostStack
  k₀ := .output
  k₁ := .input
  Γ _ := ResponseSymbol
  Λ := MaterializeLabel
  main := .emit
  σ := PostControl
  initialState := default
  m
    | .emit => .push .quotient (fun s => s.held.getD .zero) <|
        .load (fun _ => default) <| .goto fun _ => .emit
    | .reverse => .pop .quotient readSymbol <|
        .branch (fun s => s.held.isNone)
          (.load (fun _ => default) .halt)
          (.push .input (fun s => s.held.getD .zero) <|
            .load (fun _ => default) <| .goto fun _ => .reverse)

def materializeCfg (label : Option MaterializeLabel) (held : Option ResponseSymbol)
    (input buffer : List ResponseSymbol) : materializeMachine.Cfg :=
  ⟨label, ⟨0,held,false⟩, postStacks input buffer [] []⟩

/-- The query and remaining reply are tapes, not finite control. An ask exposes
an external response stream; ordinary stack contents are still all empty. -/
inductive ProtocolCfg
  | pre (machine : preMachine.Cfg)
  | ask (query : List Bool)
  | feed (query : List Bool) (port : List ResponseSymbol) (writer : materializeMachine.Cfg)
  | emit (query : List Bool) (port : List ResponseSymbol) (writer : materializeMachine.Cfg)
  | reverse (query : List Bool) (writer : materializeMachine.Cfg)
  | post (machine : postMachine.Cfg)
  | halt (machine : postMachine.Cfg)

def queryReply (query : List Bool) (response : List ResponseSymbol) : Prop :=
  ∃ value : Σ n, UnaryFormula n,
    readWord true query = some value ∧ PhysicalReply value.2 response

/-- Each edge costs one step. The last index records the distinguished ask. -/
inductive ProtocolStep : ProtocolCfg → ProtocolCfg → Nat → Prop
  | pre {a b} (step : preMachine.step a = some b) :
      ProtocolStep (.pre a) (.pre b) 0
  | preDone (q) : ProtocolStep (.pre (haltList preMachine q)) (.ask q) 0
  | ask {q r} (reply : queryReply q r) :
      ProtocolStep (.ask q) (.feed q r (initList materializeMachine [])) 1
  | read (q a r c) : ProtocolStep (.feed q (a::r) c)
      (.emit q r ⟨c.l, ⟨0,some a,false⟩,c.stk⟩) 0
  | emit {q r a b} (step : materializeMachine.step a = some b) :
      ProtocolStep (.emit q r a) (.feed q r b) 0
  | endPort (q c) : ProtocolStep (.feed q [] c)
      (.reverse q ⟨some .reverse, default,c.stk⟩) 0
  | reverse {q a b} (step : materializeMachine.step a = some b) :
      ProtocolStep (.reverse q a) (.reverse q b) 0
  | postStart (q r) : ProtocolStep (.reverse q (haltList materializeMachine r))
      (.post ⟨some postMachine.main,postMachine.initialState,(haltList materializeMachine r).stk⟩) 0
  | post {a b} (step : postMachine.step a = some b) :
      ProtocolStep (.post a) (.post b) 0
  | halt (r) : ProtocolStep (.post (haltList postMachine r))
      (.halt (haltList postMachine r)) 0

inductive ProtocolRun : ProtocolCfg → ProtocolCfg → Nat → Nat → Prop
  | nil (c) : ProtocolRun c c 0 0
  | cons {a b c t asks flag} (step : ProtocolStep a b flag)
      (tail : ProtocolRun b c t asks) : ProtocolRun a c (t+1) (flag+asks)

/-- Every raw source, including rejection, executes one physical ask, writes
its ordinary reply symbol by symbol, and reaches the exact clean post halt.
The count here is over the decoded explicit universe; the conventional name
encoding correspondence is a separate obligation. -/
theorem one_query_run (w : List Bool) :
    ∃ r : List ResponseSymbol,
      queryReply (preparedQuery w) r ∧
      r.length ≤ 2*(w.length+1)^2+w.length+5 ∧
      msbValue (totalPostOutput r) = satisfyingCount (preparedFormula w).2 ∧
      (∃ t ≤ 16*w.length^2+50*w.length+71,
        ProtocolRun (.pre (initList preMachine w))
          (.halt (haltList postMachine (binaryWord (totalPostOutput r)))) t 1) ∧
      (∀ output t asks, ProtocolRun (.pre (initList preMachine w))
        (.halt output) t asks → asks = 1) := by
  classical
  have compose : ∀ {a b c t u x y}, ProtocolRun a b t x → ProtocolRun b c u y →
      ProtocolRun a c (t+u) (x+y) := by
    intro a b c t u x y first last
    induction first with
    | nil => simpa using last
    | cons step tail ih =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        ProtocolRun.cons step (ih last)
  have single : ∀ {a b flag}, ProtocolStep a b flag → ProtocolRun a b 1 flag := by
    intro a b flag h
    simpa using ProtocolRun.cons h (ProtocolRun.nil b)
  have liftTrace : ∀ {α : Type} (f : α → Option α) (node : α → ProtocolCfg),
      (∀ a b, f a = some b → ProtocolStep (node a) (node b) 0) →
      ∀ k a b, (flip bind f)^[k] (some a) = some b → ProtocolRun (node a) (node b) k 0 := by
    intro α f node lift
    have noneStable : ∀ k, (flip bind f)^[k] none = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa [Function.iterate_succ_apply,flip] using ih
    intro k
    induction k with
    | zero =>
      intro a b h
      have h' : a = b := Option.some.inj h
      subst b
      exact ProtocolRun.nil _
    | succ k ih =>
      intro a b h
      simp only [Function.iterate_succ_apply,flip] at h
      change (flip bind f)^[k] (f a) = some b at h
      cases first : f a with
      | none => rw [first,noneStable] at h; cases h
      | some next =>
        rw [first] at h
        simpa using ProtocolRun.cons (lift a next first) (ih next b h)
  have reverseRun : ∀ q buffer input,
      ProtocolRun (.reverse q (materializeCfg (some .reverse) none input buffer))
        (.post (initList postMachine (buffer.reverse++input))) (buffer.length+2) 0 := by
    intro q buffer
    induction buffer with
    | nil =>
      intro input
      have step : materializeMachine.step (materializeCfg (some .reverse) none input []) =
          some (haltList materializeMachine input) := by
        apply congrArg some
        dsimp [materializeMachine,TM2.stepAux,materializeCfg,postStacks,readSymbol,haltList]
        congr 1
        funext k
        cases k <;> rfl
      have handoff : (⟨some postMachine.main,postMachine.initialState,
          (haltList materializeMachine input).stk⟩ : postMachine.Cfg) =
          initList postMachine input := by
        dsimp [initList,haltList]
        rfl
      have complete := compose (single (ProtocolStep.reverse step))
        (single (ProtocolStep.postStart q input))
      rw [handoff] at complete
      simpa using complete
    | cons a buffer ih =>
      intro input
      have step : materializeMachine.step
          (materializeCfg (some .reverse) none input (a::buffer)) =
          some (materializeCfg (some .reverse) none (a::input) buffer) := by
        apply congrArg some
        dsimp [materializeMachine,TM2.stepAux,materializeCfg,postStacks,readSymbol]
        congr 1
        funext k
        cases k <;> rfl
      convert compose (single (ProtocolStep.reverse step)) (ih (a::input)) using 1 <;>
        simp [List.reverse_cons,List.append_assoc] <;> omega
  have feedRun : ∀ q r buffer,
      ProtocolRun (.feed q r (materializeCfg (some .emit) none [] buffer))
        (.post (initList postMachine (buffer.reverse++r))) (3*r.length+buffer.length+3) 0 := by
    intro q r
    induction r with
    | nil =>
      intro buffer
      convert compose
        (single (ProtocolStep.endPort q (materializeCfg (some .emit) none [] buffer)))
        (reverseRun q buffer []) using 1 <;> simp [materializeCfg] <;> omega
    | cons a r ih =>
      intro buffer
      have step : materializeMachine.step
          (materializeCfg (some .emit) (some a) [] buffer) =
          some (materializeCfg (some .emit) none [] (a::buffer)) := by
        apply congrArg some
        dsimp [materializeMachine,TM2.stepAux,materializeCfg,postStacks]
        congr 1
        funext k
        cases k <;> rfl
      have read := single (ProtocolStep.read q a r (materializeCfg (some .emit) none [] buffer))
      have emit := single (ProtocolStep.emit (q:=q) (r:=r) step)
      convert compose read (compose emit (ih (a::buffer))) using 1 <;>
        simp [materializeCfg,List.reverse_cons,List.append_assoc,Nat.mul_add] <;> omega
  obtain ⟨⟨pre⟩,decode,_,_,_,_⟩ := pre_word_run w
  obtain ⟨r,physical,_,length,_,⟨post⟩,count⟩ := physical_reply_run (preparedFormula w).2
  have reply : queryReply (preparedQuery w) r := ⟨preparedFormula w,decode,physical⟩
  have dimensions : (preparedFormula w).1 ≤ w.length ∧
      (preparedFormula w).2.length ≤ w.length+1 := by
    cases parsed : readWord false w with
    | none =>
      have formulaEq : preparedFormula w = ⟨0,[[]]⟩ := by
        unfold preparedFormula
        rw [parsed]
        rfl
      rw [formulaEq]
      simp
    | some value =>
      rcases value with ⟨n,F⟩
      obtain ⟨encoded,_⟩ := (codec_exact false w n F).mp parsed
      have sourceEq : encodeWord false F = sourceWord F := by
        simp [encodeWord,bodyWord,termWord,sourceWord,List.append_assoc]
        apply congrArg (fun fn : Std.Sat.CNF.Clause (Fin n) → List Bool => F.flatMap fn)
        funext c
        simp [unaryClause,List.append_assoc]
      have clauses : F.length ≤ (F.flatMap unaryClause).length := by
        have all : ∀ Fs : UnaryFormula n, Fs.length ≤ (Fs.flatMap unaryClause).length := by
          intro Fs
          induction Fs with
          | nil => simp
          | cons c Fs ih =>
            have nonempty : 1 ≤ (unaryClause c).length := by simp [unaryClause]
            simp only [List.length_cons,List.flatMap_cons,List.length_append]
            omega
        exact all F
      have sourceLength : (sourceWord F).length = n+3+(F.flatMap unaryClause).length := by
        simp [sourceWord,List.length_append,List.length_replicate]
        omega
      have hw : w.length = n+3+(F.flatMap unaryClause).length := by
        rw [encoded,sourceEq,sourceLength]
      have formulaEq : preparedFormula w = ⟨n,F⟩ := by
        unfold preparedFormula
        rw [parsed]
        rfl
      rw [formulaEq]
      change n ≤ w.length ∧ F.length ≤ w.length+1
      constructor <;> omega
  have responseBound : r.length ≤ 2*(w.length+1)^2+w.length+5 := by
    have product := Nat.mul_le_mul (Nat.add_le_add_right dimensions.1 1) dimensions.2
    nlinarith [length]
  have preTrace := liftTrace preMachine.step ProtocolCfg.pre
    (fun _ _ h => ProtocolStep.pre h) pre.steps _ _ pre.evals_in_steps
  have postTrace := liftTrace postMachine.step ProtocolCfg.post
    (fun _ _ h => ProtocolStep.post h) post.steps _ _ post.evals_in_steps
  have feed := feedRun (preparedQuery w) r []
  have initWriter : initList materializeMachine [] = materializeCfg (some .emit) none [] [] := by
    dsimp [initList,materializeMachine,materializeCfg]
    congr 1
    funext k; cases k <;> rfl
  rw [←initWriter] at feed
  simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at feed
  have actual := compose preTrace (compose (single (ProtocolStep.preDone (preparedQuery w)))
    (compose (single (ProtocolStep.ask reply)) (compose feed
      (compose postTrace (single (ProtocolStep.halt (binaryWord (totalPostOutput r))))))))
  have asksInvariant : ∀ {a b t asks}, ProtocolRun a b t asks →
      (match b with | .pre _ | .ask _ => 0 | _ => 1) =
      (match a with | .pre _ | .ask _ => 0 | _ => 1) + asks := by
    intro a b t asks run
    induction run with
    | nil c => cases c <;> rfl
    | cons edge tail ih => cases edge <;> simp_all
  refine ⟨r,reply,responseBound,count,?_,?_⟩
  · refine ⟨pre.steps + (1 + (1 + (3*r.length+3+(post.steps+1)))),?_,?_⟩
    · have p := pre.steps_le_m
      have s := post.steps_le_m
      nlinarith [responseBound]
    · simpa only [Nat.add_assoc,Nat.zero_add,Nat.add_zero] using actual
  · intro output t asks run
    have h := asksInvariant run
    simpa using h.symm

end PredictiveThermodynamic
