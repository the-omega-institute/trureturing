/- GID: D5/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/DenseQueryCompiler, D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol]
   utility: none
   digest: Paid conventional words execute one physical query and return the independent clause count. -/

/- Utility: this is an unbounded execution construction and an invariant of every
complete trace. It lifts the actual fixed finite compiler, extracts the actual
physical Ask suffix and charges response writes, reversal and postprocessing.
It delivers no finite certificate checker, bounded enumeration, certified
finite instance or conditional numerical estimate. -/

import D5.S0.Computability.DenseQueryCompiler
import D5.S3.Quantum.Dynamics.PhysicalProtocol.ClauseOracleProtocol
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.BinaryNames
open Turing StateTransition ClauseCodec Physical Lax51Proofs.RamToTM

inductive BinaryProtocolCfg
  | prefix (machine : queryCompiler.Cfg)
  | physical (machine : ProtocolCfg)

inductive BinaryProtocolStep : BinaryProtocolCfg → BinaryProtocolCfg → Nat → Prop
  | prefix {a b} (step : queryCompiler.step a = some b) :
      BinaryProtocolStep (.prefix a) (.prefix b) 0
  | enter (q) : BinaryProtocolStep (.prefix (haltList queryCompiler q)) (.physical (.ask q)) 0
  | physical {a b flag} (step : ProtocolStep a b flag) :
      BinaryProtocolStep (.physical a) (.physical b) flag

inductive BinaryProtocolRun : BinaryProtocolCfg → BinaryProtocolCfg → Nat → Nat → Prop
  | nil (c) : BinaryProtocolRun c c 0 0
  | cons {a b c t asks flag} (step : BinaryProtocolStep a b flag)
      (tail : BinaryProtocolRun b c t asks) : BinaryProtocolRun a c (t+1) (flag+asks)

/-- Every raw conventional word executes the fixed dense-to-query compiler,
one physical Ask, paid ordinary response materialization and the exact clean
postprocessor halt. The independent appearing-name count is returned within
a directly charged polynomial clock, including every malformed source. -/
theorem conventional_one_query_run (w : List Bool) :
    let B := w.length^2+8*w.length+7
    ∃ r : List ResponseSymbol,
      queryReply (preparedQuery (denseOutput w)) r ∧
      r.length ≤ 2*(B+1)^2+B+5 ∧
      msbValue (totalPostOutput r) = Conventional.rawCount w ∧
      (∃ t ≤ 80*(w.length+1)^2+20*B^2+72*B+87,
        BinaryProtocolRun (.prefix (initList queryCompiler w))
          (.physical (.halt (haltList postMachine (binaryWord (totalPostOutput r))))) t 1) ∧
      (∀ output t asks, BinaryProtocolRun (.prefix (initList queryCompiler w))
        (.physical (.halt output)) t asks → asks = 1) := by
  dsimp only
  have extract : ∀ k a q output t asks,
      (flip bind preMachine.step)^[k] (some a) = some (haltList preMachine q) →
      ProtocolRun (.pre a) (.halt output) t asks →
      ∃ u ≤ t, ProtocolRun (.ask q) (.halt output) u asks := by
    intro k
    induction k with
    | zero =>
      intro a q output t asks trace run
      have same : a = haltList preMachine q := Option.some.inj trace
      cases run with
      | cons edge tail =>
        cases edge with
        | pre step => rw [same] at step; simp [FinTM2.step,TM2.step,haltList] at step
        | preDone query =>
          have queryEq : query = q := by
            have output := congrArg (fun c : preMachine.Cfg => c.stk .output) same
            simpa [haltList,preMachine] using output
          subst query
          refine ⟨_,?_,by simpa using tail⟩
          omega
    | succ k ih =>
      intro a q output t asks trace run
      rw [Function.iterate_succ_apply] at trace
      change (flip bind preMachine.step)^[k] (preMachine.step a) = _ at trace
      cases first : preMachine.step a with
      | none =>
        have stable : ∀ k, (flip bind preMachine.step)^[k] none = none := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih => simpa [Function.iterate_succ_apply,flip] using ih
        rw [first,stable] at trace
        cases trace
      | some next =>
        rw [first] at trace
        cases run with
        | cons edge tail =>
          cases edge with
          | pre step =>
            have same : next = _ := Option.some.inj (first.symm.trans step)
            subst next
            obtain ⟨u,bound,rest⟩ := ih _ q output _ _ trace tail
            exact ⟨u,by omega,by simpa using rest⟩
          | preDone query => simp [FinTM2.step,TM2.step,haltList] at first
  have liftPhysical : ∀ {a b t asks}, ProtocolRun a b t asks →
      BinaryProtocolRun (.physical a) (.physical b) t asks := by
    intro a b t asks run
    induction run with
    | nil c => exact .nil _
    | cons edge tail ih => exact .cons (.physical edge) ih
  have compose : ∀ {a b c t u x y}, BinaryProtocolRun a b t x → BinaryProtocolRun b c u y →
      BinaryProtocolRun a c (t+u) (x+y) := by
    intro a b c t u x y first last
    induction first with
    | nil => simpa using last
    | cons edge tail ih =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using BinaryProtocolRun.cons edge (ih last)
  have liftPrefix : ∀ k a b,
      (flip bind queryCompiler.step)^[k] (some a) = some b →
      BinaryProtocolRun (.prefix a) (.prefix b) k 0 := by
    have stable : ∀ k, (flip bind queryCompiler.step)^[k] none = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa [Function.iterate_succ_apply,flip] using ih
    intro k
    induction k with
    | zero =>
      intro a b trace
      have same : a=b := Option.some.inj trace
      subst b
      exact .nil _
    | succ k ih =>
      intro a b trace
      rw [Function.iterate_succ_apply] at trace
      change (flip bind queryCompiler.step)^[k] (queryCompiler.step a) = _ at trace
      cases first : queryCompiler.step a with
      | none => rw [first,stable] at trace; cases trace
      | some next =>
        rw [first] at trace
        simpa using BinaryProtocolRun.cons (.prefix first) (ih next b trace)
  obtain ⟨⟨compilerRun⟩,decoded,count⟩ := dense_query_run w
  obtain ⟨_,growth,source,_,_⟩ := dense_word_run w
  have prepared : preparedFormula (denseOutput w) = densePrepared w := by
    unfold preparedFormula
    rw [source]
    rfl
  obtain ⟨r,reply,length,result,⟨t,time,run⟩,_⟩ := one_query_run (denseOutput w)
  obtain ⟨⟨pre⟩,_,_,_,_,_⟩ := pre_word_run (denseOutput w)
  obtain ⟨u,short,suffix⟩ := extract pre.steps _ _ _ _ _ pre.evals_in_steps run
  have ordinary : msbValue (totalPostOutput r) = Conventional.rawCount w := by
    rw [prepared] at result
    change msbValue (totalPostOutput r) = unaryCount (densePrepared w).2 at result
    exact result.trans count
  have bound : r.length ≤ 2*(w.length^2+8*w.length+7+1)^2+(w.length^2+8*w.length+7)+5 := by
    have square := Nat.pow_le_pow_left (Nat.add_le_add_right growth 1) 2
    omega
  have leading := liftPrefix compilerRun.steps _ _ compilerRun.evals_in_steps
  have enter : BinaryProtocolRun
      (.prefix (haltList queryCompiler (preparedQuery (denseOutput w))))
      (.physical (.ask (preparedQuery (denseOutput w)))) 1 0 := by
    simpa using BinaryProtocolRun.cons (.enter _) (BinaryProtocolRun.nil _)
  have actual := compose leading (compose enter (liftPhysical suffix))
  let mark : BinaryProtocolCfg → Nat
    | .prefix _ => 0
    | .physical (.pre _) | .physical (.ask _) => 0
    | _ => 1
  have invariant : ∀ {a b t asks}, BinaryProtocolRun a b t asks → mark b = mark a + asks := by
    intro a b t asks run
    induction run with
    | nil c => simp
    | cons edge tail ih =>
      cases edge with
      | «prefix» => simpa [mark] using ih
      | enter => simpa [mark] using ih
      | physical edge => cases edge <;> simp_all [mark]
  refine ⟨r,reply,bound,ordinary,?_,?_⟩
  · refine ⟨compilerRun.steps+(1+u),?_,?_⟩
    · have square := Nat.pow_le_pow_left growth 2
      have p := compilerRun.steps_le_m
      nlinarith
    · simpa only [Nat.zero_add,Nat.add_zero,Nat.add_assoc] using actual
  · intro output t asks run
    have same := invariant run
    simpa [mark] using same.symm
end PredictiveThermodynamic.BinaryNames
